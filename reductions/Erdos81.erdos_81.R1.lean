import FormalConjectures.ErdosProblems.«81»
import Mathlib

/-!
# Reduction of Erdős Problem 81 (Clique Partitions of Chordal Graphs)

Following the chordal (`s = 0`) case of O. Okechukwu, *Clique partitions and bounded simplicial
defect* (arXiv:2609.20871, September 2026), we reduce `Erdos81.erdos_81` to three classic
standalone theorems:
- `H1`: Dirac's simplicial vertex theorem (1961): every non-complete induced subgraph of a chordal
  graph contains two nonadjacent simplicial vertices.
- `H2`: Haxell--Rödl (2001) / Yuster (2005) bounded-clique fractional-to-integral partition
  rounding (stated in dual form, avoiding LP duality inside the reduction).
- `H3`: Core-edge triangle saturation (Okechukwu Lemma 4.1, proved via Galvin's 1995 list
  edge-coloring theorem for complete bipartite graphs).

Inside `main`, we prove unconditionally in Lean 4:
1. Induced `C_4`-freeness, simplicial vertices outside any proper clique, and degeneracy bounds
   from `H1`.
2. Signed fractional localization (Lemmas 3.1--3.2) and fractional stability (Theorem 3.3).
3. Degenerate proper edge-coloring and alternating-path color-class balancing (Lemma 2.4).
4. Random-injection triangle absorption combined with `H3` (Lemma 4.2).
5. The chordal (`s = 0`) normal form `V = C ⊔ R` with zero exceptional vertices (`T = ∅`),
   combined with a minimum-counterexample degree bound `δ(G) ≥ n/3` to deduce
   `cp(G) ≤ n^2 / 6 + C * n`.
-/

-- Credit: @preternatural-tocsin

namespace OMA.R_Erdos81_erdos_81_R1

open SimpleGraph Finset

/-- Dirac's simplicial vertex theorem (1961): every non-complete induced subgraph of a chordal
graph contains two nonadjacent simplicial vertices. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsChordal →
    ∀ S : Finset (Fin n),
      (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬ G.Adj u v) →
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬ G.Adj u v ∧
        G.IsClique ((S.filter (fun w ↦ G.Adj u w)) : Set (Fin n)) ∧
        G.IsClique ((S.filter (fun w ↦ G.Adj v w)) : Set (Fin n))

/-- Haxell--Rödl (2001) / Yuster (2005) bounded-clique fractional-to-integral partition rounding
(dual form): for fixed clique cutoff `L ≥ 3` and `ζ > 0`, if every `K_L`-feasible signed edge
weighting has total weight at most `M`, then `G` admits a clique edge partition of size at most
`M + ζ * n^2`. -/
def H2 : Prop :=
  ∀ (L : ℕ), 3 ≤ L → ∀ ζ : ℝ, 0 < ζ →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (M : ℝ),
      (∀ z : Sym2 (Fin n) → ℝ,
        (∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) →
        ∑ e ∈ G.edgeFinset, z e ≤ M) →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
        (P.card : ℝ) ≤ M + ζ * (n : ℝ) ^ 2

/-- Core-edge triangle saturation (Okechukwu Lemma 4.1, via Galvin's list edge-coloring theorem):
for disjoint vertex sets `C, R` with `|C| ≥ 3`, if every vertex of `C` misses at most `τ` vertices
of `R` and `|R| ≥ 3 * ⌈|C|/2⌉ - 3 + 4 * τ`, then every edge of `G[C]` can be assigned a common
neighbor in `R` so that incident edges of `G[C]` receive distinct vertices of `R`. -/
def H3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C R : Finset (Fin n)) (τ : ℕ),
    Disjoint C R → 3 ≤ C.card →
    (∀ u ∈ C, (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ) →
    3 * ((C.card + 1) / 2) + 4 * τ ≤ R.card + 3 →
    ∃ φ : Sym2 (Fin n) → Fin n,
      (∀ u ∈ C, ∀ v ∈ C, G.Adj u v →
        φ s(u, v) ∈ R ∧ G.Adj u (φ s(u, v)) ∧ G.Adj v (φ s(u, v))) ∧
      (∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C, v ≠ w → G.Adj u v → G.Adj u w →
        φ s(u, v) ≠ φ s(u, w))

/- ### Section 1: Chordal graph primitives from `H1` -/

lemma exists_simplicial_outside_clique (h1 : H1) {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hG : G.IsChordal) (S C : Finset (Fin n)) (_hCS : C ⊆ S) (hC : G.IsClique (C : Set (Fin n)))
    (hne : (S \ C).Nonempty) :
    ∃ v ∈ S \ C, G.IsClique ((S.filter (fun w ↦ G.Adj v w)) : Set (Fin n)) := by
  by_cases hS : G.IsClique (S : Set (Fin n))
  · obtain ⟨v, hv⟩ := hne
    refine ⟨v, hv, ?_⟩
    exact fun x hx y hy hxy ↦ hS (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy
  · have hnon : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬ G.Adj u v := by
      unfold SimpleGraph.IsClique Set.Pairwise at hS
      push Not at hS
      rcases hS with ⟨u, hu, v, hv, huv, hna⟩
      exact ⟨u, hu, v, hv, huv, hna⟩
    obtain ⟨u, huS, v, hvS, huv, hna, huSimp, hvSimp⟩ := h1 n G hG S hnon
    by_cases huC : u ∈ C
    · have hvC : v ∉ C := fun hvC ↦ hna (hC huC hvC huv)
      exact ⟨v, mem_sdiff.mpr ⟨hvS, hvC⟩, hvSimp⟩
    · exact ⟨u, mem_sdiff.mpr ⟨huS, huC⟩, huSimp⟩

lemma chordal_no_c4 {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsChordal)
    {a b w₁ w₂ : Fin n} (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (hw12 : w₁ ≠ w₂) (hnw12 : ¬ G.Adj w₁ w₂)
    (haw1 : G.Adj a w₁) (haw2 : G.Adj a w₂)
    (hbw1 : G.Adj b w₁) (hbw2 : G.Adj b w₂) : False := by
  have haw1_ne : a ≠ w₁ := haw1.ne
  have haw2_ne : a ≠ w₂ := haw2.ne
  have hbw1_ne : b ≠ w₁ := hbw1.ne
  have hbw2_ne : b ≠ w₂ := hbw2.ne
  let f : Fin 4 → Fin n := ![a, w₁, b, w₂]
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals first | exact absurd hij haw1_ne | exact absurd hij hab | exact absurd hij haw2_ne
                    | exact absurd hij.symm haw1_ne | exact absurd hij hbw1_ne.symm
                    | exact absurd hij hw12 | exact absurd hij.symm hab
                    | exact absurd hij hbw1_ne | exact absurd hij hbw2_ne
                    | exact absurd hij.symm haw2_ne | exact absurd hij.symm hw12
                    | exact absurd hij.symm hbw2_ne
  have hnba : ¬ G.Adj b a := fun h ↦ hnab h.symm
  have hnw21 : ¬ G.Adj w₂ w₁ := fun h ↦ hnw12 h.symm
  have hfadj : ∀ i j : Fin 4, G.Adj (f i) (f j) ↔ (cycleGraph 4).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, cycleGraph_adj, hnab, hnba, hnw12, hnw21, haw1, haw2, hbw1, hbw2,
        haw1.symm, haw2.symm, hbw1.symm, hbw2.symm] <;> decide
  exact hG 4 (by norm_num) ⟨⟨⟨f, hfinj⟩, hfadj _ _⟩⟩

lemma clique_edges_le {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {S Q : Finset (Fin n)} (hQS : Q ⊆ S) (hQ : G.IsClique (Q : Set (Fin n))) :
    Q.card.choose 2 ≤ (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).card := by
  by_cases hQ2 : Q.card < 2
  · rw [Nat.choose_eq_zero_of_lt hQ2]
    exact Nat.zero_le _
  have hn_pos : 0 < n := by
    have := card_le_univ Q
    simp at this
    omega
  have hinj : (Q.powersetCard 2).card ≤
      (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).card := by
    refine Finset.card_le_card_of_injOn (fun p ↦ if hp : p.card = 2 then
      s((p.orderEmbOfFin hp ⟨0, by norm_num⟩), (p.orderEmbOfFin hp ⟨1, by norm_num⟩))
      else s(⟨0, hn_pos⟩, ⟨0, hn_pos⟩)) ?_ ?_
    · intro p hp
      have hp2 := mem_powersetCard.mp hp
      have h0 : p.orderEmbOfFin hp2.2 ⟨0, by norm_num⟩ ∈ p := orderEmbOfFin_mem p hp2.2 ⟨0, by norm_num⟩
      have h1 : p.orderEmbOfFin hp2.2 ⟨1, by norm_num⟩ ∈ p := orderEmbOfFin_mem p hp2.2 ⟨1, by norm_num⟩
      have hlt : p.orderEmbOfFin hp2.2 ⟨0, by norm_num⟩ < p.orderEmbOfFin hp2.2 ⟨1, by norm_num⟩ :=
        (p.orderEmbOfFin hp2.2).strictMono (by decide)
      simp only [mem_coe, mem_filter, mem_edgeFinset, dif_pos hp2.2]
      refine ⟨hQ (hp2.1 h0) (hp2.1 h1) (ne_of_lt hlt), ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hQS (hp2.1 h0)
      · exact hQS (hp2.1 h1)
    · intro p₁ hp₁ p₂ hp₂ hEq
      have h1 := mem_powersetCard.mp hp₁
      have h2 := mem_powersetCard.mp hp₂
      simp only [dif_pos h1.2, dif_pos h2.2] at hEq
      have hset : ∀ (p : Finset (Fin n)) (hp : p.card = 2),
          p = {p.orderEmbOfFin hp ⟨0, by norm_num⟩, p.orderEmbOfFin hp ⟨1, by norm_num⟩} := by
        intro p hp
        have hlt : p.orderEmbOfFin hp ⟨0, by norm_num⟩ < p.orderEmbOfFin hp ⟨1, by norm_num⟩ :=
          (p.orderEmbOfFin hp).strictMono (by decide)
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          have hr := range_orderEmbOfFin p hp
          have : x ∈ Set.range (p.orderEmbOfFin hp) := by rw [hr]; exact hx
          rcases this with ⟨idx, rfl⟩
          fin_cases idx <;> simp
        · rw [card_pair (ne_of_lt hlt), hp]
      rw [hset p₁ h1.2, hset p₂ h2.2]
      have := congrArg Sym2.toFinset hEq
      simpa [Sym2.toFinset_mk_eq] using this
  simpa [card_powersetCard] using hinj

/- ### Section 2: Signed fractional localization and stability (`s = 0`) -/

lemma edge_filter_erase_split {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) {v : Fin n} (hv : v ∈ S) (f : Sym2 (Fin n) → ℝ) :
    ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), f e =
      (∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S.erase v), f e) +
      ∑ u ∈ (S.erase v).filter (fun u ↦ G.Adj v u), f s(v, u) := by
  let ES := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)
  let E1 := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S.erase v)
  let E2 := ES.filter (fun e ↦ v ∈ e)
  have h1 : E1 = ES.filter (fun e ↦ v ∉ e) := by
    ext e
    simp only [E1, ES, mem_filter]
    constructor
    · rintro ⟨he, hsub⟩
      refine ⟨⟨he, fun x hx ↦ (mem_erase.mp (hsub x hx)).2⟩, fun hv' ↦ (mem_erase.mp (hsub v hv')).1 rfl⟩
    · rintro ⟨⟨he, hsub⟩, hnv⟩
      exact ⟨he, fun x hx ↦ mem_erase.mpr ⟨fun hxv ↦ hnv (hxv ▸ hx), hsub x hx⟩⟩
  have hsum := (Finset.sum_filter_add_sum_filter_not ES (fun e ↦ v ∈ e) f).symm
  rw [← h1] at hsum
  have hbij : ∑ e ∈ E2, f e = ∑ u ∈ (S.erase v).filter (fun u ↦ G.Adj v u), f s(v, u) := by
    symm
    refine Finset.sum_bij (fun u _ ↦ s(v, u)) ?_ ?_ ?_ ?_
    · intro u hu
      rw [mem_filter, mem_erase] at hu
      rw [mem_filter, mem_filter, mem_edgeFinset]
      refine ⟨⟨hu.2, ?_⟩, by simp⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hv
      · exact hu.1.2
    · intro u₁ hu₁ u₂ hu₂ hEq
      rw [mem_filter, mem_erase] at hu₁ hu₂
      have := (Sym2.eq_iff).mp hEq
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h.symm hu₂.1.1
    · intro e he
      rw [mem_filter, mem_filter, mem_edgeFinset] at he
      induction e using Sym2.ind with
      | h a b =>
        have hab : G.Adj a b := he.1.1
        rcases Sym2.mem_iff.mp he.2 with rfl | rfl
        · refine ⟨b, ?_, rfl⟩
          rw [mem_filter, mem_erase]
          exact ⟨⟨hab.ne.symm, he.1.2 b (by simp)⟩, hab⟩
        · refine ⟨a, ?_, Sym2.eq_swap⟩
          rw [mem_filter, mem_erase]
          exact ⟨⟨hab.ne, he.1.2 a (by simp)⟩, hab.symm⟩
    · intro _ _; rfl
  rw [hsum, add_comm, hbij]

lemma lem_localize_ind (h1 : H1) {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : G.IsChordal) (z : Sym2 (Fin n) → ℝ) (α : ℝ)
    (hα : ∀ (v : Fin n) (Q : Finset (Fin n)), (∀ u ∈ Q, G.Adj v u) →
      G.IsClique (Q : Set (Fin n)) → ∑ u ∈ Q, z s(v, u) ≤ α) :
    ∀ k : ℕ, ∀ S C : Finset (Fin n), (S \ C).card = k → C ⊆ S → G.IsClique (C : Set (Fin n)) →
      (∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), z e) +
      (∑ e ∈ (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C),
        max 0 (-z e)) ≤
      ((S \ C).card : ℝ) * α +
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C), z e := by
  intro k
  induction k with
  | zero =>
    intro S C hk hCS _
    have hSC : S = C := by
      have h0 : S \ C = ∅ := card_eq_zero.mp hk
      exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h0) hCS
    subst hSC
    have hempty : (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ S) = ∅ := by
      ext e; simp only [mem_filter, notMem_empty, iff_false]
      rintro ⟨⟨_, h1⟩, h2⟩; exact h2 h1
    rw [hempty, sum_empty, sdiff_self]
    simp
  | succ k ih =>
    intro S C hk hCS hC
    have hne : (S \ C).Nonempty := card_pos.mp (by omega)
    obtain ⟨v, hvSC, hvSimp⟩ := exists_simplicial_outside_clique h1 hG S C hCS hC hne
    have hvS : v ∈ S := (mem_sdiff.mp hvSC).1
    have hvC : v ∉ C := (mem_sdiff.mp hvSC).2
    let S' := S.erase v
    have hCS' : C ⊆ S' := fun x hx ↦ mem_erase.mpr ⟨fun hxv ↦ hvC (hxv ▸ hx), hCS hx⟩
    have hS'card : (S' \ C).card = k := by
      have heq : S' \ C = (S \ C).erase v := by
        ext x; simp [S', mem_sdiff, mem_erase]; tauto
      rw [heq, card_erase_of_mem hvSC, hk]
      omega
    have hih := ih S' C hS'card hCS' hC
    have hZ := edge_filter_erase_split G S hvS z
    have hN :
        ∑ e ∈ (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C),
          max 0 (-z e) =
        (∑ e ∈ (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S')).filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C),
          max 0 (-z e)) +
        ∑ u ∈ S'.filter (fun u ↦ G.Adj v u), max 0 (-z s(v, u)) := by
      have hsplit := edge_filter_erase_split G S hvS
        (fun e ↦ if ¬ ∀ x ∈ e, x ∈ C then max 0 (-z e) else 0)
      rw [← sum_filter, ← sum_filter] at hsplit
      rw [hsplit]
      congr 1
      refine sum_congr rfl ?_
      intro u hu
      have hnotC : ¬ ∀ x ∈ s(v, u), x ∈ C := fun h ↦ hvC (h v (by simp))
      rw [if_pos hnotC]
    have hstar :
        (∑ u ∈ S'.filter (fun u ↦ G.Adj v u), z s(v, u)) +
        (∑ u ∈ S'.filter (fun u ↦ G.Adj v u), max 0 (-z s(v, u))) ≤ α := by
      rw [← sum_add_distrib]
      let Nv := S'.filter (fun u ↦ G.Adj v u)
      let Npos := Nv.filter (fun u ↦ 0 < z s(v, u))
      have heq : ∑ u ∈ Nv, (z s(v, u) + max 0 (-z s(v, u))) = ∑ u ∈ Npos, z s(v, u) := by
        rw [← sum_filter_add_sum_filter_not Nv (fun u ↦ 0 < z s(v, u))]
        have hpos : ∑ u ∈ Npos, (z s(v, u) + max 0 (-z s(v, u))) = ∑ u ∈ Npos, z s(v, u) := by
          refine sum_congr rfl ?_
          intro u hu
          have h0 : 0 < z s(v, u) := (mem_filter.mp hu).2
          rw [max_eq_left (by linarith : -z s(v, u) ≤ 0), add_zero]
        have hneg : ∑ u ∈ Nv.filter (fun u ↦ ¬ 0 < z s(v, u)),
            (z s(v, u) + max 0 (-z s(v, u))) = 0 := by
          refine sum_eq_zero ?_
          intro u hu
          have h0 : z s(v, u) ≤ 0 := not_lt.mp (mem_filter.mp hu).2
          rw [max_eq_right (by linarith : 0 ≤ -z s(v, u))]
          ring
        rw [hpos, hneg, add_zero]
      rw [heq]
      refine hα v Npos (fun u hu ↦ (mem_filter.mp (mem_filter.mp hu).1).2) ?_
      intro x hx y hy hxy
      have hx1 := mem_filter.mp (mem_filter.mp hx).1
      have hy1 := mem_filter.mp (mem_filter.mp hy).1
      exact hvSimp (mem_filter.mpr ⟨(erase_subset _ _) hx1.1, hx1.2⟩)
        (mem_filter.mpr ⟨(erase_subset _ _) hy1.1, hy1.2⟩) hxy
    have hcard_cast : ((S \ C).card : ℝ) = ((S' \ C).card : ℝ) + 1 := by
      rw [hk, hS'card]; push_cast; ring
    rw [hZ, hN, hcard_cast]
    linarith

lemma hz_edge_of_feas {n L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hL4 : 4 ≤ L) {z : Sym2 (Fin n) → ℝ}
    (hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1)
    {u w : Fin n} (huw : G.Adj u w) : z s(u, w) ≤ 1 := by
  have hQ := hz {u, w} (by rw [card_pair huw.ne]) (by rw [card_pair huw.ne]; omega)
    (by rw [coe_pair]; exact isClique_pair.mpr (fun _ ↦ huw))
  have hfilt : G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ ({u, w} : Finset (Fin n))) = {s(u, w)} := by
    ext e
    simp only [mem_filter, mem_edgeFinset, mem_singleton]
    induction e using Sym2.ind with
    | h a b =>
      constructor
      · rintro ⟨hab, hsub⟩
        have ha := hsub a (by simp)
        have hb := hsub b (by simp)
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab.ne
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hab.ne
      · intro hEq
        rw [hEq]
        refine ⟨huw, fun x hx ↦ ?_⟩
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp
  rw [hfilt, sum_singleton] at hQ
  exact hQ

lemma hz_tri_of_feas {n L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hL4 : 4 ≤ L) {z : Sym2 (Fin n) → ℝ}
    (hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1)
    {a b d : Fin n} (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d) :
    z s(a, b) + z s(a, d) + z s(b, d) ≤ 1 := by
  have hQ := hz {a, b, d}
    (by rw [card_insert_of_notMem (by simp [hab.ne, had.ne]), card_pair hbd.ne]; omega)
    (by rw [card_insert_of_notMem (by simp [hab.ne, had.ne]), card_pair hbd.ne]; omega)
    (by
      intro x hx y hy hxy
      simp only [mem_coe, mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · exact had
      · exact hab.symm
      · exact absurd rfl hxy
      · exact hbd
      · exact had.symm
      · exact hbd.symm
      · exact absurd rfl hxy)
  have hfilt : G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ ({a, b, d} : Finset (Fin n))) =
      {s(a, b), s(a, d), s(b, d)} := by
    ext e
    simp only [mem_filter, mem_edgeFinset, mem_insert, mem_singleton]
    induction e using Sym2.ind with
    | h x y =>
      constructor
      · rintro ⟨hxy, hsub⟩
        have hx := hsub x (by simp)
        have hy := hsub y (by simp)
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy.ne
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl Sym2.eq_swap
        · exact absurd rfl hxy.ne
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl Sym2.eq_swap)
        · exact Or.inr (Or.inr Sym2.eq_swap)
        · exact absurd rfl hxy.ne
      · rintro (hEq | hEq | hEq) <;> rw [hEq]
        · exact ⟨hab, fun w hw ↦ by rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp⟩
        · exact ⟨had, fun w hw ↦ by rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp⟩
        · exact ⟨hbd, fun w hw ↦ by rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp⟩
  rw [hfilt] at hQ
  have hne1 : s(a, b) ≠ s(a, d) := fun h ↦ by
    rcases Sym2.eq_iff.mp h with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact hbd.ne h1
    · exact had.ne h1
  have hne2 : s(a, b) ≠ s(b, d) := fun h ↦ by
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab.ne h1
    · exact had.ne h1
  have hne3 : s(a, d) ≠ s(b, d) := fun h ↦ by
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab.ne h1
    · exact had.ne h1
  rw [sum_insert (by simp [hne1, hne2]), sum_insert (by simp [hne3]), sum_singleton] at hQ
  linarith

lemma lem_localize (h1 : H1) {n L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : G.IsChordal) (hn8 : 8 ≤ n) (hL4 : 4 ≤ L) (z : Sym2 (Fin n) → ℝ)
    (hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) :
    ∃ (v : Fin n) (C : Finset (Fin n)),
      (∀ u ∈ C, G.Adj v u) ∧ G.IsClique (C : Set (Fin n)) ∧
      let c : ℕ := C.card
      let α : ℝ := ∑ u ∈ C, z s(v, u)
      let W : ℝ := ∑ e ∈ G.edgeFinset, z e
      let Nout : ℝ := ∑ e ∈ G.edgeFinset.filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C), max 0 (-z e)
      0 ≤ α ∧ α ≤ (c : ℝ) ∧
      (∀ u ∈ C, 0 < z s(v, u)) ∧
      W + Nout ≤ ((n : ℝ) - (c : ℝ)) * α +
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C), z e ∧
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C), z e ≤
        (c.choose 2 : ℝ) - ((c : ℝ) - 1) * α ∧
      (2 * c ≤ n + 1 →
        ((2 * (n : ℝ) + 1) ^ 2 / 24) - W ≥
          (3 / 2) * ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 +
          ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) + Nout) ∧
      (n + 1 ≤ 2 * c → W + Nout ≤ 25 / 192 * (n : ℝ) ^ 2) := by
  have hz_edge : ∀ u w : Fin n, G.Adj u w → z s(u, w) ≤ 1 := fun _ _ h ↦ hz_edge_of_feas hL4 hz h
  have hz_tri : ∀ a b d : Fin n, G.Adj a b → G.Adj a d → G.Adj b d →
      z s(a, b) + z s(a, d) + z s(b, d) ≤ 1 := fun _ _ _ h1 h2 h3 ↦ hz_tri_of_feas hL4 hz h1 h2 h3
  let cand : Finset (Fin n × Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Finset (Fin n)))).filter
      (fun p ↦ (∀ u ∈ p.2, G.Adj p.1 u) ∧ G.IsClique (p.2 : Set (Fin n)))
  have hcand_ne : cand.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ∅), ?_⟩
    simp [cand]
  obtain ⟨⟨v, C₀⟩, hmem, hmax⟩ := Finset.exists_max_image cand (fun p ↦ ∑ u ∈ p.2, z s(p.1, u)) hcand_ne
  rw [mem_filter] at hmem
  let C := C₀.filter (fun u ↦ 0 < z s(v, u))
  have hC_sub : C ⊆ C₀ := filter_subset _ _
  have hC_adj : ∀ u ∈ C, G.Adj v u := fun u hu ↦ hmem.2.1 u (hC_sub hu)
  have hC_clique : G.IsClique (C : Set (Fin n)) := fun x hx y hy hxy ↦ hmem.2.2 (hC_sub hx) (hC_sub hy) hxy
  have hC_pos : ∀ u ∈ C, 0 < z s(v, u) := fun u hu ↦ (mem_filter.mp hu).2
  have hC_max : ∀ (v' : Fin n) (Q : Finset (Fin n)), (∀ u ∈ Q, G.Adj v' u) →
      G.IsClique (Q : Set (Fin n)) → ∑ u ∈ Q, z s(v', u) ≤ ∑ u ∈ C, z s(v, u) := by
    intro v' Q hQadj hQcl
    have hQmem : (v', Q) ∈ cand := by
      rw [mem_filter]
      exact ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, hQadj, hQcl⟩
    have hle1 : ∑ u ∈ Q, z s(v', u) ≤ ∑ u ∈ C₀, z s(v, u) := hmax (v', Q) hQmem
    have hle2 : ∑ u ∈ C₀, z s(v, u) ≤ ∑ u ∈ C, z s(v, u) := by
      rw [← sum_filter_add_sum_filter_not C₀ (fun u ↦ 0 < z s(v, u))]
      have hnonpos : ∑ u ∈ C₀.filter (fun u ↦ ¬ 0 < z s(v, u)), z s(v, u) ≤ 0 :=
        sum_nonpos (fun u hu ↦ not_lt.mp (mem_filter.mp hu).2)
      linarith
    exact le_trans hle1 hle2
  refine ⟨v, C, hC_adj, hC_clique, ?_⟩
  dsimp only
  set c : ℕ := C.card
  set α : ℝ := ∑ u ∈ C, z s(v, u)
  set W : ℝ := ∑ e ∈ G.edgeFinset, z e
  set Nout : ℝ := ∑ e ∈ G.edgeFinset.filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C), max 0 (-z e)
  set ZC : ℝ := ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C), z e
  have hα0 : 0 ≤ α := sum_nonneg (fun u hu ↦ (hC_pos u hu).le)
  have hαc : α ≤ (c : ℝ) := by
    calc
      α = ∑ u ∈ C, z s(v, u) := rfl
      _ ≤ ∑ _u ∈ C, (1 : ℝ) := sum_le_sum (fun u hu ↦ hz_edge v u (hC_adj u hu))
      _ = (c : ℝ) := by simp [c]
  have hroot : W + Nout ≤ ((n : ℝ) - (c : ℝ)) * α + ZC := by
    have hloc := lem_localize_ind h1 hG z α hC_max ((Finset.univ : Finset (Fin n)) \ C).card
      Finset.univ C rfl (subset_univ C) hC_clique
    have huniv : G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ (Finset.univ : Finset (Fin n))) =
        G.edgeFinset := by ext e; simp
    have hsdiff : (((Finset.univ : Finset (Fin n)) \ C).card : ℝ) = (n : ℝ) - (c : ℝ) := by
      rw [card_sdiff_of_subset (subset_univ C), card_univ, Fintype.card_fin]
      have hcn : C.card ≤ n := by simpa using card_le_univ C
      rw [Nat.cast_sub hcn]
    simpa [huniv, hsdiff, W, Nout, ZC] using hloc
  have htri_star : ZC ≤ (c.choose 2 : ℝ) - ((c : ℝ) - 1) * α := by
    have hsum_pairs :
        2 * ZC = ∑ u ∈ C, ∑ w ∈ C.erase u, z s(u, w) := by
      have h1 : ∑ u ∈ C, ∑ w ∈ C.erase u, z s(u, w) =
          ∑ p ∈ C.offDiag, z s(p.1, p.2) := by
        have hoff_eq : C.offDiag = C.biUnion (fun u ↦ (C.erase u).image (fun w ↦ (u, w))) := by
          ext ⟨u, w⟩; simp [mem_offDiag, mem_biUnion, mem_image, mem_erase, ne_comm]; tauto
        symm
        rw [hoff_eq, sum_biUnion]
        · refine sum_congr rfl fun u _ ↦ ?_
          rw [sum_image (fun _ _ _ _ h ↦ (Prod.mk.inj h).2)]
        · intro u₁ _ u₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro p hp₁ hp₂
          rcases mem_image.mp hp₁ with ⟨_, _, rfl⟩
          rcases mem_image.mp hp₂ with ⟨_, _, hEq⟩
          exact hne (Prod.mk.inj hEq).1.symm
      have h2 : ∑ p ∈ C.offDiag, z s(p.1, p.2) =
          2 * ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C), z e := by
        have hmap : ∀ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C),
            (C.offDiag.filter (fun p ↦ s(p.1, p.2) = e)).card = 2 := by
          intro e he
          rw [mem_filter, mem_edgeFinset] at he
          induction e using Sym2.ind with
          | h a b =>
            have hab : G.Adj a b := he.1
            have haC : a ∈ C := he.2 a (by simp)
            have hbC : b ∈ C := he.2 b (by simp)
            have hset : C.offDiag.filter (fun p ↦ s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
              ext ⟨x, y⟩
              simp only [mem_filter, mem_offDiag, mem_insert, mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
              constructor
              · rintro ⟨_, h⟩; exact h
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact ⟨⟨haC, hbC, hab.ne⟩, Or.inl ⟨rfl, rfl⟩⟩
                · exact ⟨⟨hbC, haC, hab.ne.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
            rw [hset, card_pair (by intro h; exact hab.ne (Prod.mk.inj h).1)]
        have hfib : ∑ p ∈ C.offDiag, z s(p.1, p.2) =
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C),
              ∑ p ∈ C.offDiag.filter (fun p ↦ s(p.1, p.2) = e), z s(p.1, p.2) := by
          rw [Finset.sum_fiberwise_of_maps_to]
          intro p hp
          rw [mem_offDiag] at hp
          rw [mem_filter, mem_edgeFinset]
          exact ⟨hC_clique hp.1 hp.2.1 hp.2.2, fun x hx ↦ by
            rcases Sym2.mem_iff.mp hx with rfl | rfl
            · exact hp.1
            · exact hp.2.1⟩
        rw [hfib]
        have hcongr : ∀ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C),
            ∑ p ∈ C.offDiag.filter (fun p ↦ s(p.1, p.2) = e), z s(p.1, p.2) = 2 * z e := by
          intro e he
          have hsub : ∑ p ∈ C.offDiag.filter (fun p ↦ s(p.1, p.2) = e), z s(p.1, p.2) =
              ∑ _p ∈ C.offDiag.filter (fun p ↦ s(p.1, p.2) = e), z e :=
            sum_congr rfl (fun p hp ↦ by rw [(mem_filter.mp hp).2])
          rw [hsub, sum_const, hmap e he, nsmul_eq_mul]
          norm_num
        rw [sum_congr rfl hcongr, ← mul_sum]
      linarith
    have htri_sum :
        ∑ u ∈ C, ∑ w ∈ C.erase u, (z s(u, w) + z s(v, u) + z s(v, w)) ≤
          ∑ u ∈ C, ∑ _w ∈ C.erase u, (1 : ℝ) := by
      refine sum_le_sum ?_
      intro u hu
      refine sum_le_sum ?_
      intro w hw
      rw [mem_erase] at hw
      have h1 := hz_tri v u w (hC_adj u hu) (hC_adj w hw.2) (hC_clique hu hw.2 hw.1.symm)
      linarith
    have hsum1 : ∑ u ∈ C, ∑ _w ∈ C.erase u, (1 : ℝ) = (c : ℝ) * ((c : ℝ) - 1) := by
      by_cases hc0 : c = 0
      · have hCe : C = ∅ := card_eq_zero.mp hc0
        rw [hCe, hc0]; simp
      · have h1 : ∑ u ∈ C, ∑ _w ∈ C.erase u, (1 : ℝ) = ∑ u ∈ C, ((c - 1 : ℕ) : ℝ) := by
          refine sum_congr rfl ?_
          intro u hu
          simp [card_erase_of_mem hu, c]
        rw [h1, sum_const, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
    have hsum_vu : ∑ u ∈ C, ∑ _w ∈ C.erase u, z s(v, u) = ((c : ℝ) - 1) * α := by
      by_cases hc0 : c = 0
      · have hCe : C = ∅ := card_eq_zero.mp hc0
        dsimp [α]; rw [hCe, hc0]; simp
      · have h1 : ∑ u ∈ C, ∑ _w ∈ C.erase u, z s(v, u) =
            ∑ u ∈ C, ((c - 1 : ℕ) : ℝ) * z s(v, u) := by
          refine sum_congr rfl ?_
          intro u hu
          rw [sum_const, card_erase_of_mem hu, nsmul_eq_mul]
        rw [h1, ← mul_sum, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
    have hsum_vw : ∑ u ∈ C, ∑ w ∈ C.erase u, z s(v, w) = ((c : ℝ) - 1) * α := by
      have hswap : ∑ u ∈ C, ∑ w ∈ C.erase u, z s(v, w) = ∑ w ∈ C, ∑ _u ∈ C.erase w, z s(v, w) := by
        have h1 : ∀ f : Fin n → Fin n → ℝ,
            ∑ u ∈ C, ∑ w ∈ C.erase u, f u w = ∑ w ∈ C, ∑ u ∈ C.erase w, f u w := by
          intro f
          have hL : ∑ u ∈ C, ∑ w ∈ C.erase u, f u w = ∑ u ∈ C, ∑ w ∈ C, if w ≠ u then f u w else 0 := by
            refine sum_congr rfl ?_
            intro u _
            rw [← sum_filter]
            congr 1; ext w; simp [mem_erase, mem_filter]; tauto
          have hR : ∑ w ∈ C, ∑ u ∈ C.erase w, f u w = ∑ w ∈ C, ∑ u ∈ C, if u ≠ w then f u w else 0 := by
            refine sum_congr rfl ?_
            intro w _
            rw [← sum_filter]
            congr 1; ext u; simp [mem_erase, mem_filter]; tauto
          rw [hL, hR, sum_comm]
          refine sum_congr rfl ?_
          intro u _
          refine sum_congr rfl ?_
          intro w _
          by_cases h : u = w <;> simp [h, ne_comm]
        exact h1 (fun _ w ↦ z s(v, w))
      rw [hswap]
      exact hsum_vu
    have hchoose2 : 2 * (c.choose 2 : ℝ) = (c : ℝ) * ((c : ℝ) - 1) := by
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hnat : 2 * c.choose 2 = c * (c - 1) := by
          rw [Nat.choose_two_right]
          have hev := Nat.even_mul_pred_self c
          rcases hev with ⟨q, hq⟩
          omega
        have hR : ((2 * c.choose 2 : ℕ) : ℝ) = ((c * (c - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast [Nat.cast_sub (by omega : 1 ≤ c)] at hR
        exact hR
    have hexpand :
        ∑ u ∈ C, ∑ w ∈ C.erase u, (z s(u, w) + z s(v, u) + z s(v, w)) =
          (∑ u ∈ C, ∑ w ∈ C.erase u, z s(u, w)) +
          (∑ u ∈ C, ∑ _w ∈ C.erase u, z s(v, u)) +
          (∑ u ∈ C, ∑ w ∈ C.erase u, z s(v, w)) := by
      simp_rw [sum_add_distrib]
    linarith
  refine ⟨hα0, hαc, hC_pos, hroot, htri_star, ?_, ?_⟩
  · intro _hc_le
    have hchoose2 : 2 * (c.choose 2 : ℝ) = (c : ℝ) * ((c : ℝ) - 1) := by
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hnat : 2 * c.choose 2 = c * (c - 1) := by
          rw [Nat.choose_two_right]
          have hev := Nat.even_mul_pred_self c
          rcases hev with ⟨q, hq⟩
          omega
        have hR : ((2 * c.choose 2 : ℕ) : ℝ) = ((c * (c - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast [Nat.cast_sub (by omega : 1 ≤ c)] at hR
        exact hR
    nlinarith
  · intro hc_ge
    have hc4 : 4 ≤ c := by omega
    have hZC_k4 : ZC ≤ (1 / 6 : ℝ) * (c.choose 2 : ℝ) := by
      have hsum4 :
          ∑ Q ∈ C.powersetCard 4, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤
            (C.card.choose 4 : ℝ) := by
        calc
          ∑ Q ∈ C.powersetCard 4, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e
              ≤ ∑ _Q ∈ C.powersetCard 4, (1 : ℝ) := by
                refine sum_le_sum ?_
                intro Q hQ
                rw [mem_powersetCard] at hQ
                exact hz Q (by omega) (by omega) (fun x hx y hy hxy ↦ hC_clique (hQ.1 hx) (hQ.1 hy) hxy)
          _ = (C.card.choose 4 : ℝ) := by simp [card_powersetCard]
      have hdouble :
          ∑ Q ∈ C.powersetCard 4, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
            ((c - 2).choose 2 : ℝ) * ZC := by
        let EC := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C)
        have h1 : ∀ Q ∈ C.powersetCard 4,
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
              ∑ e ∈ EC, if ∀ x ∈ e, x ∈ Q then z e else 0 := by
          intro Q hQ
          rw [mem_powersetCard] at hQ
          rw [← sum_filter]
          congr 1
          ext e
          simp only [EC, mem_filter]
          exact ⟨fun ⟨he, hQsub⟩ ↦ ⟨⟨he, fun x hx ↦ hQ.1 (hQsub x hx)⟩, hQsub⟩,
                 fun ⟨⟨he, _⟩, hQsub⟩ ↦ ⟨he, hQsub⟩⟩
        rw [sum_congr rfl h1, sum_comm]
        have h2 : ∀ e ∈ EC,
            ∑ Q ∈ C.powersetCard 4, (if ∀ x ∈ e, x ∈ Q then z e else 0) =
              ((c - 2).choose 2 : ℝ) * z e := by
          intro e he
          rw [mem_filter, mem_edgeFinset] at he
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          congr 1
          induction e using Sym2.ind with
          | h a b =>
            have hab : a ≠ b := he.1.ne
            have haC : a ∈ C := he.2 a (by simp)
            have hbC : b ∈ C := he.2 b (by simp)
            have hbij : ((C.powersetCard 4).filter (fun Q ↦ ∀ x ∈ s(a, b), x ∈ Q)).card =
                ((C \ {a, b}).powersetCard 2).card := by
              symm
              refine Finset.card_bij (fun A _ ↦ {a, b} ∪ A) ?_ ?_ ?_
              · intro A hA
                rw [mem_powersetCard] at hA
                rw [mem_filter, mem_powersetCard]
                have hdisj : Disjoint ({a, b} : Finset (Fin n)) A := disjoint_sdiff.mono_right hA.1
                refine ⟨⟨union_subset (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
                  (hA.1.trans sdiff_subset), ?_⟩, ?_⟩
                · rw [card_union_of_disjoint hdisj, card_pair hab, hA.2]
                · intro x hx; rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp
              · intro A₁ hA₁ A₂ hA₂ hEq
                rw [mem_powersetCard] at hA₁ hA₂
                have hd₁ : Disjoint ({a, b} : Finset (Fin n)) A₁ := disjoint_sdiff.mono_right hA₁.1
                have hd₂ : Disjoint ({a, b} : Finset (Fin n)) A₂ := disjoint_sdiff.mono_right hA₂.1
                have h1' : ({a, b} ∪ A₁) \ {a, b} = A₁ := union_sdiff_cancel_left hd₁
                have h2' : ({a, b} ∪ A₂) \ {a, b} = A₂ := union_sdiff_cancel_left hd₂
                rw [← h1', ← h2', hEq]
              · intro Q hQ
                rw [mem_filter, mem_powersetCard] at hQ
                have hsub : ({a, b} : Finset (Fin n)) ⊆ Q := by
                  intro x hx; simp at hx; rcases hx with rfl | rfl
                  · exact hQ.2 x (by simp)
                  · exact hQ.2 x (by simp)
                refine ⟨Q \ {a, b}, ?_, union_sdiff_of_subset hsub⟩
                rw [mem_powersetCard]
                refine ⟨sdiff_subset_sdiff hQ.1.1 Subset.rfl, ?_⟩
                rw [card_sdiff_of_subset hsub, hQ.1.2, card_pair hab]
            have hsubC : ({a, b} : Finset (Fin n)) ⊆ C := by
              intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
            rw [hbij, card_powersetCard, card_sdiff_of_subset hsubC, card_pair hab]
        rw [sum_congr rfl h2, ← mul_sum]
      have hchoose_id : 6 * c.choose 4 = c.choose 2 * (c - 2).choose 2 := by
        have h := Nat.choose_mul (n := c) (k := 4) (s := 2) (by omega)
        have h42 : (4 : ℕ).choose 2 = 6 := by decide
        rw [h42, mul_comm] at h
        exact h
      have hpos : (0 : ℝ) < ((c - 2).choose 2 : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega : 2 ≤ c - 2)
      have hmul : ((c - 2).choose 2 : ℝ) * (6 * ZC) ≤ ((c - 2).choose 2 : ℝ) * (c.choose 2 : ℝ) := by
        have hR : (6 : ℝ) * (c.choose 4 : ℝ) = (c.choose 2 : ℝ) * ((c - 2).choose 2 : ℝ) := by
          exact_mod_cast hchoose_id
        linarith
      have h6 := le_of_mul_le_mul_left hmul hpos
      linarith
    have hchoose2 : 2 * (c.choose 2 : ℝ) = (c : ℝ) * ((c : ℝ) - 1) := by
      have hnat : 2 * c.choose 2 = c * (c - 1) := by
        rw [Nat.choose_two_right]
        have hev := Nat.even_mul_pred_self c
        rcases hev with ⟨q, hq⟩
        omega
      have hR : ((2 * c.choose 2 : ℕ) : ℝ) = ((c * (c - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ c)] at hR
      exact hR
    have hb1 : W + Nout ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * α + (c.choose 2 : ℝ) := by linarith
    have hb2 : W + Nout ≤ ((n : ℝ) - (c : ℝ)) * α + (1 / 6 : ℝ) * (c.choose 2 : ℝ) := by linarith
    have hc_geR : (n : ℝ) + 1 ≤ 2 * (c : ℝ) := by exact_mod_cast hc_ge
    have hc_leR : (c : ℝ) ≤ (n : ℝ) := by
      have : c ≤ n := by simpa [c] using card_le_univ C
      exact_mod_cast this
    by_cases hα_cmp : α ≤ 5 / 12 * (c : ℝ)
    · have : W + Nout ≤ ((n : ℝ) - (c : ℝ)) * (5 / 12 * (c : ℝ)) + (1 / 6 : ℝ) * (c.choose 2 : ℝ) := by
        nlinarith
      nlinarith [sq_nonneg (8 * (c : ℝ) - 5 * (n : ℝ) + 1)]
    · have : W + Nout ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * (5 / 12 * (c : ℝ)) + (c.choose 2 : ℝ) := by
        nlinarith
      nlinarith [sq_nonneg (8 * (c : ℝ) - 5 * (n : ℝ) + 1)]

lemma lem_signedcover_step {n L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hL4 : 4 ≤ L) (z : Sym2 (Fin n) → ℝ)
    (hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1)
    {v : Fin n} {U : Finset (Fin n)} (hvU : v ∉ U) (hUadj : ∀ u ∈ U, G.Adj v u)
    (hUcl : G.IsClique (U : Set (Fin n))) (hU2 : 2 ≤ U.card) :
    ∑ u ∈ U, z s(v, u) ≤
      (U.card : ℝ) / ((L : ℝ) - 1) + 1 +
      ((L : ℝ) - 2) / ((U.card : ℝ) - 1) *
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e) := by
  let k := U.card
  let m := L - 1
  have hm_pos : 0 < m := by omega
  have hm_ge3 : 3 ≤ m := by omega
  let q := (k + m - 1) / m
  have hq_le : (q : ℝ) ≤ (k : ℝ) / (m : ℝ) + 1 := by
    have hnat : q * m ≤ k + m - 1 := Nat.div_mul_le_self (k + m - 1) m
    have hR : (q : ℝ) * (m : ℝ) ≤ (k : ℝ) + (m : ℝ) := by
      have : ((q * m : ℕ) : ℝ) ≤ ((k + m : ℕ) : ℝ) := by exact_mod_cast (by omega : q * m ≤ k + m)
      push_cast at this; linarith
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have : (q : ℝ) ≤ ((k : ℝ) + (m : ℝ)) / (m : ℝ) := (le_div_iff₀ hmR).mpr hR
    have heq : ((k : ℝ) + (m : ℝ)) / (m : ℝ) = (k : ℝ) / (m : ℝ) + 1 := by
      field_simp [ne_of_gt hmR]
    linarith
  let eqv0 : Fin k ≃ U := (Fintype.equivFinOfCardEq (by simp [k])).symm
  have hfor_perm : ∀ σ : Equiv.Perm (Fin k),
      ∑ u ∈ U, z s(v, u) ≤ (q : ℝ) +
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U),
          if ∃ a b : Fin k, a ≠ b ∧ a.val / m = b.val / m ∧
              e = s((eqv0 (σ a)).1, (eqv0 (σ b)).1)
          then max 0 (-z e) else 0 := by
    intro σ
    let blk : ℕ → Finset (Fin n) := fun j ↦
      ((Finset.univ : Finset (Fin k)).filter (fun a ↦ a.val / m = j)).image (fun a ↦ (eqv0 (σ a)).1)
    have hblk_card : ∀ j, (blk j).card ≤ m := by
      intro j
      refine le_trans Finset.card_image_le ?_
      have hsub : ((Finset.univ : Finset (Fin k)).filter (fun a ↦ a.val / m = j)).image Fin.val ⊆
          Finset.Ico (j * m) ((j + 1) * m) := by
        intro x hx
        rcases mem_image.mp hx with ⟨a, ha, rfl⟩
        rw [mem_filter] at ha
        rw [Finset.mem_Ico]
        have h1 := Nat.div_mul_le_self a.val m
        have h2 := Nat.lt_div_mul_add (a := a.val) (b := m) hm_pos
        rw [ha.2] at h1 h2
        exact ⟨by linarith, by linarith⟩
      calc
        ((Finset.univ : Finset (Fin k)).filter (fun a ↦ a.val / m = j)).card
            = (((Finset.univ : Finset (Fin k)).filter (fun a ↦ a.val / m = j)).image Fin.val).card :=
              (card_image_of_injective _ Fin.val_injective).symm
        _ ≤ (Finset.Ico (j * m) ((j + 1) * m)).card := card_le_card hsub
        _ = (j + 1) * m - j * m := Nat.card_Ico _ _
        _ = m := by rw [add_mul, one_mul, Nat.add_sub_cancel_left]
    have hblk_sub : ∀ j, blk j ⊆ U := by
      intro j x hx
      rcases mem_image.mp hx with ⟨a, _, rfl⟩
      exact (eqv0 (σ a)).2
    have hblk_ineq : ∀ j < q,
        ∑ u ∈ blk j, z s(v, u) ≤ 1 +
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), max 0 (-z e) := by
      intro j _
      by_cases hne : (blk j).Nonempty
      · let Q := insert v (blk j)
        have hvB : v ∉ blk j := fun h ↦ hvU (hblk_sub j h)
        have hQcard2 : 2 ≤ Q.card := by
          rw [card_insert_of_notMem hvB]
          have := card_pos.mpr hne
          omega
        have hQcardL : Q.card ≤ L := by
          rw [card_insert_of_notMem hvB]
          have := hblk_card j
          omega
        have hQcl : G.IsClique (Q : Set (Fin n)) := by
          intro x hx y hy hxy
          rw [mem_coe, mem_insert] at hx hy
          rcases hx with rfl | hxB <;> rcases hy with rfl | hyB
          · exact absurd rfl hxy
          · exact hUadj y (hblk_sub j hyB)
          · exact (hUadj x (hblk_sub j hxB)).symm
          · exact hUcl (hblk_sub j hxB) (hblk_sub j hyB) hxy
        have hQz := hz Q hQcard2 hQcardL hQcl
        have hsplit := edge_filter_erase_split G Q (mem_insert_self v (blk j)) z
        have herase : Q.erase v = blk j := erase_insert hvB
        rw [herase] at hsplit
        have hfilt_adj : (blk j).filter (fun u ↦ G.Adj v u) = blk j := by
          ext u; simp only [mem_filter, and_iff_left_iff_imp]; exact fun hu ↦ hUadj u (hblk_sub j hu)
        rw [hfilt_adj] at hsplit
        have hneg_le : -(∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), z e) ≤
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), max 0 (-z e) := by
          rw [← sum_neg_distrib]
          exact sum_le_sum (fun e _ ↦ le_max_right 0 (-z e))
        linarith
      · rw [not_nonempty_iff_eq_empty] at hne
        rw [hne, sum_empty]
        have hnonneg : 0 ≤ ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ (∅ : Finset (Fin n))), max 0 (-z e) :=
          sum_nonneg (fun _ _ ↦ le_max_left 0 _)
        linarith
    have hU_part : U = (Finset.range q).biUnion blk := by
      ext u
      simp only [mem_biUnion, mem_range, blk, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · intro hu
        let a := σ.symm (eqv0.symm ⟨u, hu⟩)
        refine ⟨a.val / m, ?_, a, rfl, ?_⟩
        · have ha : a.val < k := a.isLt
          have hqdef : q = (k + m - 1) / m := rfl
          rw [hqdef]
          exact Nat.div_lt_of_lt_mul (by
            have h1 := Nat.div_add_mod (k + m - 1) m
            have h2 := Nat.mod_lt (k + m - 1) hm_pos
            omega)
        · simp [a]
      · rintro ⟨_, _, a, _, rfl⟩
        exact (eqv0 (σ a)).2
    have hblk_disj : Set.PairwiseDisjoint (Finset.range q : Set ℕ) blk := by
      intro j₁ _ j₂ _ hne
      change Disjoint (blk j₁) (blk j₂)
      rw [Finset.disjoint_left]
      intro u hu₁ hu₂
      rcases mem_image.mp hu₁ with ⟨a₁, ha₁, rfl⟩
      rcases mem_image.mp hu₂ with ⟨a₂, ha₂, hEq⟩
      have h12 : a₁ = a₂ := σ.injective (eqv0.injective (Subtype.ext hEq.symm))
      rw [mem_filter] at ha₁ ha₂
      rw [h12] at ha₁
      exact hne (ha₁.2.symm.trans ha₂.2)
    have hsum_U : ∑ u ∈ U, z s(v, u) = ∑ j ∈ Finset.range q, ∑ u ∈ blk j, z s(v, u) := by
      conv_lhs => rw [hU_part]
      exact Finset.sum_biUnion hblk_disj
    have hsum_neg :
        ∑ j ∈ Finset.range q, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), max 0 (-z e) ≤
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U),
          if ∃ a b : Fin k, a ≠ b ∧ a.val / m = b.val / m ∧
              e = s((eqv0 (σ a)).1, (eqv0 (σ b)).1)
          then max 0 (-z e) else 0 := by
      have hdisj_e : Set.PairwiseDisjoint (Finset.range q : Set ℕ)
          (fun j ↦ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j)) := by
        intro j₁ hj₁ j₂ hj₂ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        rw [mem_filter, mem_edgeFinset] at he₁ he₂
        induction e using Sym2.ind with
        | h x y =>
          exact Finset.disjoint_left.mp (hblk_disj hj₁ hj₂ hne) (he₁.2 x (by simp)) (he₂.2 x (by simp))
      rw [← Finset.sum_biUnion hdisj_e, ← sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ le_max_left 0 _)
      intro e he
      rcases mem_biUnion.mp he with ⟨j, hj, hej⟩
      rw [mem_filter, mem_edgeFinset] at hej
      rw [mem_filter, mem_filter, mem_edgeFinset]
      refine ⟨⟨hej.1, fun x hx ↦ hblk_sub j (hej.2 x hx)⟩, ?_⟩
      induction e using Sym2.ind with
      | h x y =>
        have hxB : x ∈ blk j := hej.2 x (by simp)
        have hyB : y ∈ blk j := hej.2 y (by simp)
        rcases mem_image.mp hxB with ⟨a, ha, rfl⟩
        rcases mem_image.mp hyB with ⟨b, hb, rfl⟩
        rw [mem_filter] at ha hb
        refine ⟨a, b, ?_, ha.2.trans hb.2.symm, rfl⟩
        intro hab; subst hab; exact hej.1.ne rfl
    calc
      ∑ u ∈ U, z s(v, u) = ∑ j ∈ Finset.range q, ∑ u ∈ blk j, z s(v, u) := hsum_U
      _ ≤ ∑ j ∈ Finset.range q, (1 + ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), max 0 (-z e)) :=
            sum_le_sum (fun j hj ↦ hblk_ineq j (mem_range.mp hj))
      _ = (q : ℝ) + ∑ j ∈ Finset.range q, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ blk j), max 0 (-z e) := by
            rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
      _ ≤ (q : ℝ) + ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U),
            if ∃ a b : Fin k, a ≠ b ∧ a.val / m = b.val / m ∧
                e = s((eqv0 (σ a)).1, (eqv0 (σ b)).1)
            then max 0 (-z e) else 0 := by linarith
  -- Average `hfor_perm` over all `σ : Equiv.Perm (Fin k)`.
  let Np := Fintype.card (Equiv.Perm (Fin k))
  have hNp_pos : (0 : ℝ) < (Np : ℝ) := by exact_mod_cast Fintype.card_pos (α := Equiv.Perm (Fin k))
  have havg := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin k))))
    (fun σ _ ↦ hfor_perm σ)
  rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    sum_comm] at havg
  have hpair_prob : ∀ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U),
      (∑ σ : Equiv.Perm (Fin k),
        if ∃ a b : Fin k, a ≠ b ∧ a.val / m = b.val / m ∧
            e = s((eqv0 (σ a)).1, (eqv0 (σ b)).1)
        then max 0 (-z e) else 0) ≤
      (Np : ℝ) * (((L : ℝ) - 2) / ((k : ℝ) - 1)) * max 0 (-z e) := by
    intro e he
    rw [mem_filter, mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h x y =>
      have hxU : x ∈ U := he.2 x (by simp)
      have hyU : y ∈ U := he.2 y (by simp)
      let i₁ : Fin k := eqv0.symm ⟨x, hxU⟩
      let i₂ : Fin k := eqv0.symm ⟨y, hyU⟩
      have hi12 : i₁ ≠ i₂ := fun h ↦ he.1.ne (congrArg Subtype.val (eqv0.symm.injective h))
      have hcond : ∀ σ : Equiv.Perm (Fin k),
          (∃ a b : Fin k, a ≠ b ∧ a.val / m = b.val / m ∧
            s(x, y) = s((eqv0 (σ a)).1, (eqv0 (σ b)).1)) ↔
          (σ.symm i₁).val / m = (σ.symm i₂).val / m := by
        intro σ
        constructor
        · rintro ⟨a, b, _, hdiv, hEq⟩
          have hxy := Sym2.eq_iff.mp hEq
          rcases hxy with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
          · have ha : σ a = i₁ := by
              have : eqv0 (σ a) = ⟨x, hxU⟩ := Subtype.ext hx'.symm
              exact eqv0.eq_symm_apply.mpr this
            have hb : σ b = i₂ := by
              have : eqv0 (σ b) = ⟨y, hyU⟩ := Subtype.ext hy'.symm
              exact eqv0.eq_symm_apply.mpr this
            rw [← ha, ← hb, σ.symm_apply_apply, σ.symm_apply_apply]
            exact hdiv
          · have ha : σ a = i₂ := by
              have : eqv0 (σ a) = ⟨y, hyU⟩ := Subtype.ext hy'.symm
              exact eqv0.eq_symm_apply.mpr this
            have hb : σ b = i₁ := by
              have : eqv0 (σ b) = ⟨x, hxU⟩ := Subtype.ext hx'.symm
              exact eqv0.eq_symm_apply.mpr this
            rw [← ha, ← hb, σ.symm_apply_apply, σ.symm_apply_apply]
            exact hdiv.symm
        · intro hdiv
          refine ⟨σ.symm i₁, σ.symm i₂, fun h ↦ hi12 (σ.symm.injective h), hdiv, ?_⟩
          simp [i₁, i₂]
      simp_rw [hcond]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      -- Count `σ` with `(σ.symm i₁).val / m = (σ.symm i₂).val / m`:
      -- Map `σ ↦ (σ.symm i₁, σ.symm i₂)`; every ordered pair `(p, q)` with `p ≠ q` has equal fiber size!
      let goodPairs : Finset (Fin k × Fin k) :=
        (Finset.univ : Finset (Fin k)).offDiag.filter (fun p ↦ p.1.val / m = p.2.val / m)
      have hgood_card : goodPairs.card ≤ k * (m - 1) := by
        have hfib : goodPairs.card = ∑ a : Fin k,
            (((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).card := by
          have h1 : goodPairs = (Finset.univ : Finset (Fin k)).biUnion
              (fun a ↦ (((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).image (fun b ↦ (a, b))) := by
            ext ⟨a, b⟩
            simp [goodPairs, mem_biUnion, mem_image, mem_filter, mem_offDiag, mem_erase, ne_comm]
          rw [h1, card_biUnion]
          · refine sum_congr rfl ?_
            intro a _
            exact card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2)
          · intro a₁ _ a₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro p hp₁ hp₂
            rcases mem_image.mp hp₁ with ⟨_, _, rfl⟩
            rcases mem_image.mp hp₂ with ⟨_, _, hEq⟩
            exact hne (Prod.mk.inj hEq).1.symm
        rw [hfib]
        calc
          ∑ a : Fin k, (((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).card
              ≤ ∑ _a : Fin k, (m - 1) := by
                refine sum_le_sum ?_
                intro a _
                let j := a.val / m
                have hsub : ((((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).image Fin.val) ⊆
                    (Finset.Ico (j * m) ((j + 1) * m)).erase a.val := by
                  intro x hx
                  rcases mem_image.mp hx with ⟨b, hb, rfl⟩
                  rw [mem_filter, mem_erase] at hb
                  rw [mem_erase, Finset.mem_Ico]
                  have h1 := Nat.div_mul_le_self b.val m
                  have h2 := Nat.lt_div_mul_add (a := b.val) (b := m) hm_pos
                  rw [← hb.2] at h1 h2
                  exact ⟨fun h ↦ hb.1.1 (Fin.ext h), by dsimp [j]; omega, by dsimp [j]; rw [add_mul, one_mul]; omega⟩
                have ha_mem : a.val ∈ Finset.Ico (j * m) ((j + 1) * m) := by
                  rw [Finset.mem_Ico]
                  have h1 := Nat.div_mul_le_self a.val m
                  have h2 := Nat.lt_div_mul_add (a := a.val) (b := m) hm_pos
                  exact ⟨by dsimp [j]; omega, by dsimp [j]; rw [add_mul, one_mul]; omega⟩
                calc
                  (((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).card
                      = ((((Finset.univ : Finset (Fin k)).erase a).filter (fun b ↦ a.val / m = b.val / m)).image Fin.val).card :=
                        (card_image_of_injective _ Fin.val_injective).symm
                  _ ≤ ((Finset.Ico (j * m) ((j + 1) * m)).erase a.val).card := card_le_card hsub
                  _ = (Finset.Ico (j * m) ((j + 1) * m)).card - 1 := card_erase_of_mem ha_mem
                  _ = m - 1 := by rw [Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left]
          _ = k * (m - 1) := by simp
      have hcount_perm :
          ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
            (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card * (k * (k - 1)) =
          goodPairs.card * Np := by
        let fiber : (Fin k × Fin k) → Finset (Equiv.Perm (Fin k)) := fun p ↦
          (Finset.univ : Finset (Equiv.Perm (Fin k))).filter (fun σ ↦ σ.symm i₁ = p.1 ∧ σ.symm i₂ = p.2)
        have hfib_eq : ∀ p₁ p₂ : Fin k × Fin k, p₁ ∈ (Finset.univ : Finset (Fin k)).offDiag →
            p₂ ∈ (Finset.univ : Finset (Fin k)).offDiag → (fiber p₁).card = (fiber p₂).card := by
          intro p₁ p₂ hp₁ hp₂
          rw [mem_offDiag] at hp₁ hp₂
          -- Build an explicit permutation `τ` mapping `p₁.1 ↦ p₂.1` and `p₁.2 ↦ p₂.2`.
          have hτ : ∃ τ : Equiv.Perm (Fin k), τ p₁.1 = p₂.1 ∧ τ p₁.2 = p₂.2 := by
            let τ₁ := Equiv.swap p₁.1 p₂.1
            have hne' : τ₁ p₁.2 ≠ p₂.1 := by
              intro h
              have : p₁.2 = p₁.1 := τ₁.injective (by simpa [τ₁] using h)
              exact hp₁.2.2 this.symm
            let τ₂ := Equiv.swap (τ₁ p₁.2) p₂.2
            refine ⟨τ₁.trans τ₂, ?_, ?_⟩
            · simp only [Equiv.trans_apply]
              have h1 : τ₁ p₁.1 = p₂.1 := Equiv.swap_apply_left _ _
              rw [h1]
              exact Equiv.swap_apply_of_ne_of_ne hne'.symm hp₂.2.2
            · simp only [Equiv.trans_apply]
              exact Equiv.swap_apply_left _ _
          obtain ⟨τ, hτ1, hτ2⟩ := hτ
          refine Finset.card_bij (fun σ _ ↦ τ.symm.trans σ) ?_ ?_ ?_
          · intro σ hσ
            rw [mem_filter] at hσ ⊢
            refine ⟨mem_univ _, ?_, ?_⟩
            · simp [hσ.2.1, hτ1]
            · simp [hσ.2.2, hτ2]
          · intro σ₁ _ σ₂ _ hEq
            refine Equiv.ext (fun a ↦ ?_)
            have := congrArg (fun ρ : Equiv.Perm (Fin k) ↦ ρ (τ a)) hEq
            simpa using this
          · intro σ hσ
            rw [mem_filter] at hσ
            refine ⟨τ.trans σ, ?_, Equiv.ext (fun a ↦ by simp)⟩
            rw [mem_filter]
            refine ⟨mem_univ _, ?_, ?_⟩
            · simp [hσ.2.1, ← hτ1]
            · simp [hσ.2.2, ← hτ2]
        have hNp_sum : Np = ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag, (fiber p).card := by
          have h1 : (Finset.univ : Finset (Equiv.Perm (Fin k))).card =
              ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
                ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
                  (fun σ ↦ (σ.symm i₁, σ.symm i₂) = p)).card := by
            refine Finset.card_eq_sum_card_fiberwise ?_
            intro σ _
            rw [mem_coe, mem_offDiag]
            exact ⟨mem_univ _, mem_univ _, fun h ↦ hi12 (σ.symm.injective h)⟩
          dsimp [Np]
          rw [← card_univ, h1]
          refine sum_congr rfl ?_
          intro p _
          congr 1; ext σ; simp [fiber, Prod.ext_iff]
        have hgood_sum :
            ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
              (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card =
            ∑ p ∈ goodPairs, (fiber p).card := by
          have h1 :
              ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
                (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card =
              ∑ p ∈ goodPairs,
                (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
                  (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).filter
                  (fun σ ↦ (σ.symm i₁, σ.symm i₂) = p)).card := by
            refine Finset.card_eq_sum_card_fiberwise ?_
            intro σ hσ
            rw [mem_coe, mem_filter] at hσ
            rw [mem_coe, mem_filter, mem_offDiag]
            exact ⟨⟨mem_univ _, mem_univ _, fun h ↦ hi12 (σ.symm.injective h)⟩, hσ.2⟩
          rw [h1]
          refine sum_congr rfl ?_
          intro p hp
          rw [mem_filter] at hp
          congr 1; ext σ
          simp only [fiber, mem_filter, mem_univ, true_and, Prod.ext_iff]
          constructor
          · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, h2]; exact hp.2, h1, h2⟩
        have hp0 : (i₁, i₂) ∈ (Finset.univ : Finset (Fin k)).offDiag :=
          mem_offDiag.mpr ⟨mem_univ _, mem_univ _, hi12⟩
        have hoff_card : ((Finset.univ : Finset (Fin k)).offDiag).card = k * (k - 1) := by
          rw [Finset.offDiag_card, card_univ, Fintype.card_fin]
          have : k * k - k = k * (k - 1) := by rw [Nat.mul_sub_left_distrib, mul_one]
          exact this
        have hNp_eq : Np = k * (k - 1) * (fiber (i₁, i₂)).card := by
          rw [hNp_sum, sum_congr rfl (fun p hp ↦ hfib_eq p (i₁, i₂) hp hp0), sum_const,
            hoff_card, smul_eq_mul]
        have hgood_eq :
            ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
              (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card =
            goodPairs.card * (fiber (i₁, i₂)).card := by
          rw [hgood_sum, sum_congr rfl (fun p hp ↦ hfib_eq p (i₁, i₂) (filter_subset _ _ hp) hp0),
            sum_const, smul_eq_mul]
        rw [hgood_eq, hNp_eq]
        ring
      have hcount_le :
          (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
            (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card : ℝ) ≤
          (Np : ℝ) * (((L : ℝ) - 2) / ((k : ℝ) - 1)) := by
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hU2
          linarith
        have hR : (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
            (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card : ℝ) *
            ((k : ℝ) * ((k : ℝ) - 1)) = (goodPairs.card : ℝ) * (Np : ℝ) := by
          have h1 : ((((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
              (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card * (k * (k - 1)) : ℕ) : ℝ) =
              ((goodPairs.card * Np : ℕ) : ℝ) := by exact_mod_cast hcount_perm
          push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at h1
          exact h1
        have hgpR : (goodPairs.card : ℝ) ≤ (k : ℝ) * ((L : ℝ) - 2) := by
          have h1 : (goodPairs.card : ℝ) ≤ ((k * (m - 1) : ℕ) : ℝ) := by exact_mod_cast hgood_card
          push_cast [Nat.cast_sub (by omega : 1 ≤ m)] at h1
          have hmR : (m : ℝ) - 1 = (L : ℝ) - 2 := by
            dsimp [m]; rw [Nat.cast_sub (by omega : 1 ≤ L)]; push_cast; ring
          rw [hmR] at h1
          exact h1
        have hmul : (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
            (fun σ ↦ (σ.symm i₁).val / m = (σ.symm i₂).val / m)).card : ℝ) *
            ((k : ℝ) * ((k : ℝ) - 1)) ≤
            ((Np : ℝ) * (((L : ℝ) - 2) / ((k : ℝ) - 1))) * ((k : ℝ) * ((k : ℝ) - 1)) := by
          have hrhs : ((Np : ℝ) * (((L : ℝ) - 2) / ((k : ℝ) - 1))) * ((k : ℝ) * ((k : ℝ) - 1)) =
              ((k : ℝ) * ((L : ℝ) - 2)) * (Np : ℝ) := by
            field_simp [ne_of_gt hk1_pos]
          rw [hR, hrhs]
          exact mul_le_mul_of_nonneg_right hgpR hNp_pos.le
        exact le_of_mul_le_mul_right hmul (mul_pos hk_pos hk1_pos)
      exact mul_le_mul_of_nonneg_right hcount_le (le_max_left 0 _)
  have hsum_all := Finset.sum_le_sum hpair_prob
  rw [← mul_sum] at hsum_all
  have hdiv_all :
      (Np : ℝ) * (∑ u ∈ U, z s(v, u)) ≤
        (Np : ℝ) * ((q : ℝ) + ((L : ℝ) - 2) / ((k : ℝ) - 1) *
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e)) := by
    linarith
  have hfinal := le_of_mul_le_mul_left hdiv_all hNp_pos
  have hm_eq : (m : ℝ) = (L : ℝ) - 1 := by
    dsimp [m]; rw [Nat.cast_sub (by omega : 1 ≤ L)]; push_cast; ring
  rw [hm_eq] at hq_le
  linarith

lemma lem_signedcover (h1 : H1) {n L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : G.IsChordal) (hL4 : 4 ≤ L) (z : Sym2 (Fin n) → ℝ)
    (hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ) (hn_pos : 0 < n) (H : Finset (Fin n)) :
    ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ H), z e ≤
      (H.card : ℝ) * (ξ * (n : ℝ) + 1) +
      ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ H)).card : ℝ) / ((L : ℝ) - 1) +
      (H.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) *
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ H), max 0 (-z e) := by
  have hz_edge : ∀ u w : Fin n, G.Adj u w → z s(u, w) ≤ 1 := fun _ _ h ↦ hz_edge_of_feas hL4 hz h
  have hmain : ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k →
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), z e ≤
        (S.card : ℝ) * (ξ * (n : ℝ) + 1) +
        ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).card : ℝ) / ((L : ℝ) - 1) +
        (S.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) *
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) := by
    intro k
    induction k with
    | zero =>
      intro S hS
      have hSe : S = ∅ := card_eq_zero.mp hS
      subst hSe
      have hfe : G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ (∅ : Finset (Fin n))) = ∅ := by
        ext e; simp only [mem_filter, notMem_empty, iff_false, not_and]
        intro he hsub
        induction e using Sym2.ind with
        | h a _ => exact hsub a (by simp)
      rw [hfe]
      simp
    | succ k ih =>
      intro S hS
      have hne : (S \ ∅).Nonempty := by simpa using card_pos.mp (by omega : 0 < S.card)
      obtain ⟨v, hvS, hvSimp⟩ := exists_simplicial_outside_clique h1 hG S ∅ (empty_subset S) (by simp) hne
      rw [sdiff_empty] at hvS
      let S' := S.erase v
      have hS'card : S'.card = k := by rw [card_erase_of_mem hvS, hS]; omega
      have hih := ih S' hS'card
      let U := S'.filter (fun u ↦ G.Adj v u)
      have hvU : v ∉ U := fun h ↦ (mem_erase.mp (mem_filter.mp h).1).1 rfl
      have hUadj : ∀ u ∈ U, G.Adj v u := fun u hu ↦ (mem_filter.mp hu).2
      have hUcl : G.IsClique (U : Set (Fin n)) :=
        fun x hx y hy hxy ↦ hvSimp (mem_filter.mpr ⟨(erase_subset _ _) (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
          (mem_filter.mpr ⟨(erase_subset _ _) (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩) hxy
      have hZ := edge_filter_erase_split G S hvS z
      have hEcard :
          ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).card : ℝ) =
            ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S')).card : ℝ) + (U.card : ℝ) := by
        have h1 := edge_filter_erase_split G S hvS (fun _ ↦ (1 : ℝ))
        dsimp [S', U]
        rw [sum_const, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
          mul_one, mul_one, mul_one] at h1
        exact h1
      have hN_mono :
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S'), max 0 (-z e) ≤
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ le_max_left 0 _)
        intro e he
        rw [mem_filter] at he ⊢
        exact ⟨he.1, fun x hx ↦ (erase_subset _ _) (he.2 x hx)⟩
      have hN_U :
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e) ≤
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ le_max_left 0 _)
        intro e he
        rw [mem_filter] at he ⊢
        exact ⟨he.1, fun x hx ↦ (erase_subset _ _) ((filter_subset _ _) (he.2 x hx))⟩
      have hL1_pos : (0 : ℝ) < (L : ℝ) - 1 := by
        have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
        linarith
      have hL2_nonneg : (0 : ℝ) ≤ (L : ℝ) - 2 := by
        have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
        linarith
      have hξn_pos : (0 : ℝ) < ξ * (n : ℝ) := mul_pos hξ (by exact_mod_cast hn_pos)
      have hstep :
          ∑ u ∈ U, z s(v, u) ≤
            (ξ * (n : ℝ) + 1) + (U.card : ℝ) / ((L : ℝ) - 1) +
            ((L : ℝ) - 2) / (ξ * (n : ℝ)) *
              ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) := by
        by_cases hUsmall : (U.card : ℝ) < ξ * (n : ℝ) + 1
        · have h1 : ∑ u ∈ U, z s(v, u) ≤ (U.card : ℝ) := by
            calc
              ∑ u ∈ U, z s(v, u) ≤ ∑ _u ∈ U, (1 : ℝ) := sum_le_sum (fun u hu ↦ hz_edge v u (hUadj u hu))
              _ = (U.card : ℝ) := by simp
          have h2 : 0 ≤ (U.card : ℝ) / ((L : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hL1_pos.le
          have h3 : 0 ≤ ((L : ℝ) - 2) / (ξ * (n : ℝ)) *
              ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) :=
            mul_nonneg (div_nonneg hL2_nonneg hξn_pos.le) (sum_nonneg (fun _ _ ↦ le_max_left 0 _))
          linarith
        · push Not at hUsmall
          have hU2 : 2 ≤ U.card := by
            by_contra hlt
            have hU1 : (U.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : U.card ≤ 1)
            linarith
          have hsc := lem_signedcover_step hL4 z hz hvU hUadj hUcl hU2
          have hden : ξ * (n : ℝ) ≤ (U.card : ℝ) - 1 := by linarith
          have hfrac : ((L : ℝ) - 2) / ((U.card : ℝ) - 1) ≤ ((L : ℝ) - 2) / (ξ * (n : ℝ)) :=
            div_le_div_of_nonneg_left hL2_nonneg hξn_pos hden
          have hmul1 :
              ((L : ℝ) - 2) / ((U.card : ℝ) - 1) *
                ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e) ≤
              ((L : ℝ) - 2) / (ξ * (n : ℝ)) *
                ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) := by
            calc
              ((L : ℝ) - 2) / ((U.card : ℝ) - 1) *
                  ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e)
                  ≤ ((L : ℝ) - 2) / (ξ * (n : ℝ)) *
                    ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ U), max 0 (-z e) :=
                    mul_le_mul_of_nonneg_right hfrac (sum_nonneg (fun _ _ ↦ le_max_left 0 _))
              _ ≤ ((L : ℝ) - 2) / (ξ * (n : ℝ)) *
                    ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) :=
                    mul_le_mul_of_nonneg_left hN_U (div_nonneg hL2_nonneg hξn_pos.le)
          linarith
      have hScard : (S.card : ℝ) = (S'.card : ℝ) + 1 := by
        rw [hS, hS'card]; push_cast; ring
      have hih_N :
          (S'.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) *
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S'), max 0 (-z e) ≤
          (S'.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) *
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S), max 0 (-z e) :=
        mul_le_mul_of_nonneg_left hN_mono (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL2_nonneg hξn_pos.le))
      have hdiv_add :
          ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S)).card : ℝ) / ((L : ℝ) - 1) =
            ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ S')).card : ℝ) / ((L : ℝ) - 1) +
            (U.card : ℝ) / ((L : ℝ) - 1) := by
        rw [hEcard, add_div]
      rw [hZ, hScard, hdiv_add]
      linarith
  exact hmain H.card H rfl

set_option maxHeartbeats 800000 in
lemma thm_fracstability (h1 : H1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ (L : ℕ) (η₀ : ℝ) (n₀ : ℕ), 4 ≤ L ∧ 0 < η₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsChordal →
        ∀ z : Sym2 (Fin n) → ℝ,
          (∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
            ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) →
          (1 / 6 - η₀) * (n : ℝ) ^ 2 ≤ ∑ e ∈ G.edgeFinset, z e →
          ∃ C : Finset (Fin n), G.IsClique (C : Set (Fin n)) ∧
            |(C.card : ℝ) - (n : ℝ) / 3| ≤ ε * (n : ℝ) ∧
            ((C.card * (n - C.card) -
                (G.edgeFinset.filter (fun e ↦ (∃ u ∈ C, u ∈ e) ∧ (∃ r ∈ Finset.univ \ C, r ∈ e))).card : ℕ) : ℝ) +
              ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Finset.univ \ C)).card : ℝ) ≤
              ε * (n : ℝ) ^ 2 := by
  let ξ : ℝ := ε / 264
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  let L : ℕ := max 4 (Nat.ceil (132 / ε) + 2)
  have hL4 : 4 ≤ L := le_max_left _ _
  have hL_bound : 33 * (ξ + 1 / (2 * ((L : ℝ) - 1))) < ε / 4 := by
    have hLgt : 132 / ε < (L : ℝ) - 1 := by
      have h1' : Nat.ceil (132 / ε) + 2 ≤ L := le_max_right _ _
      have h1R : (Nat.ceil (132 / ε) : ℝ) + 2 ≤ (L : ℝ) := by exact_mod_cast h1'
      have hc := Nat.le_ceil (132 / ε)
      linarith
    have hL1pos : (0 : ℝ) < (L : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
      linarith
    have hinv : 1 / (2 * ((L : ℝ) - 1)) < ε / 264 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      have := (div_lt_iff₀ hε0).mp hLgt
      linarith
    dsimp [ξ]
    linarith
  let A₀ : ℝ := ((L : ℝ) - 2) / ξ
  have hA₀ : 0 ≤ A₀ := by
    have hL2 : (0 : ℝ) ≤ (L : ℝ) - 2 := by
      have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
      linarith
    exact div_nonneg hL2 hξ.le
  let γ : ℝ := min (1 / 1000) (min (3 * ε ^ 2 / 32) (ε / (4 * (33 * (7 + A₀) + 2) + 1)))
  have hγ : 0 < γ := by
    have h1' : (0 : ℝ) < 1 / 1000 := by norm_num
    have h2' : (0 : ℝ) < 3 * ε ^ 2 / 32 := by positivity
    have h3' : (0 : ℝ) < ε / (4 * (33 * (7 + A₀) + 2) + 1) := by positivity
    exact lt_min h1' (lt_min h2' h3')
  let η₀ : ℝ := min (γ / 2) (1 / 100)
  have hη₀ : 0 < η₀ := lt_min (by linarith) (by norm_num)
  let n₀ : ℕ := max 8 (max (Nat.ceil (1 / γ) + 1) (max (Nat.ceil (800 / ε) + 1) (Nat.ceil (1 / (ε / 4)) + 1)))
  refine ⟨L, η₀, n₀, hL4, hη₀, ?_⟩
  intro n hn G _ hG z hz hW_ge
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  obtain ⟨v, C, hCadj, hCcl, hα0, hαc, _hCpos, hroot, htri, hlow, hhigh⟩ :=
    lem_localize h1 hG hn8 hL4 z hz
  set c : ℕ := C.card
  set α : ℝ := ∑ u ∈ C, z s(v, u)
  set W : ℝ := ∑ e ∈ G.edgeFinset, z e
  set Nout : ℝ := ∑ e ∈ G.edgeFinset.filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C), max 0 (-z e)
  have hNout0 : 0 ≤ Nout := sum_nonneg (fun _ _ ↦ le_max_left 0 _)
  have hc_le_half : 2 * c ≤ n + 1 := by
    by_contra hgt
    push Not at hgt
    have hh := hhigh (by omega)
    have hη_le : η₀ ≤ 1 / 100 := min_le_right _ _
    nlinarith [sq_nonneg (n : ℝ)]
  have hdef := hlow hc_le_half
  set ϱ : ℝ := (2 * (n : ℝ) + 1) ^ 2 / 24 - W
  have hϱ0 : 0 ≤ ϱ := by
    have h1' : 0 ≤ (3 / 2 : ℝ) * ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 := by positivity
    have h2' : 0 ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) := by
      have : 2 * (c : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc_le_half
      exact mul_nonneg (by linarith) (by linarith)
    linarith
  have hϱ_le : ϱ ≤ γ * (n : ℝ) ^ 2 := by
    have h1' : ϱ ≤ η₀ * (n : ℝ) ^ 2 + (n : ℝ) / 6 + 1 / 24 := by
      dsimp [ϱ]; linarith
    have h2' : η₀ ≤ γ / 2 := min_le_left _ _
    have hn_ge_invγ : 1 / γ ≤ (n : ℝ) := by
      have hle : Nat.ceil (1 / γ) + 1 ≤ n :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
      have hleR : (Nat.ceil (1 / γ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
      linarith [Nat.le_ceil (1 / γ)]
    have hγn : 1 ≤ γ * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hn_ge_invγ hγ.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hγ)] at this
    have hnR8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    nlinarith
  have hγ_le_1000 : γ ≤ 1 / 1000 := min_le_left _ _
  have hγ_sq : γ ≤ 3 * ε ^ 2 / 32 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hγ_lin : γ ≤ ε / (4 * (33 * (7 + A₀) + 2) + 1) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hc_dist_sq : ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 ≤ 2 * ϱ / 3 := by
    have h2' : 0 ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) := by
      have : 2 * (c : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc_le_half
      exact mul_nonneg (by linarith) (by linarith)
    linarith
  have hc_dist : |(c : ℝ) - (n : ℝ) / 3| ≤ ε * (n : ℝ) := by
    have hsq : ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 ≤ (ε / 4 * (n : ℝ)) ^ 2 := by
      calc
        ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 ≤ 2 * ϱ / 3 := hc_dist_sq
        _ ≤ 2 * (γ * (n : ℝ) ^ 2) / 3 := by linarith
        _ ≤ 2 * ((3 * ε ^ 2 / 32) * (n : ℝ) ^ 2) / 3 := by
              have : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
              nlinarith
        _ = (ε / 4 * (n : ℝ)) ^ 2 := by ring
    have habs : |(c : ℝ) - (2 * (n : ℝ) + 1) / 6| ≤ ε / 4 * (n : ℝ) := by
      have h1 := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (by positivity : 0 ≤ ε / 4 * (n : ℝ))] at h1
    have h16 : (1 / 6 : ℝ) ≤ ε / 4 * (n : ℝ) := by
      have hle : Nat.ceil (1 / (ε / 4)) + 1 ≤ n :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
      have hleR : (Nat.ceil (1 / (ε / 4)) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
      have h1 : 1 / (ε / 4) ≤ (n : ℝ) := by linarith [Nat.le_ceil (1 / (ε / 4))]
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ε / 4 by positivity)
      rw [mul_div_cancel₀ _ (by positivity)] at h2
      linarith
    have htri_abs : |(c : ℝ) - (n : ℝ) / 3| ≤ |(c : ℝ) - (2 * (n : ℝ) + 1) / 6| + 1 / 6 := by
      have heq : (c : ℝ) - (n : ℝ) / 3 = ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) + 1 / 6 := by ring
      rw [heq]
      exact le_trans (abs_add_le _ _) (by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)])
    linarith
  have hc_range : (n : ℝ) / 4 ≤ (c : ℝ) ∧ (c : ℝ) ≤ 5 * (n : ℝ) / 12 := by
    have h1 := abs_le.mp hc_dist
    constructor <;> nlinarith
  have hca_le : (c : ℝ) - α ≤ 6 * ϱ / (n : ℝ) := by
    have h1 : ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) ≤ ϱ := by
      have hsq0 : 0 ≤ (3 / 2 : ℝ) * ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 := by positivity
      linarith
    have h2 : (n : ℝ) / 6 ≤ (n : ℝ) - 2 * (c : ℝ) + 1 := by linarith [hc_range.2]
    have h3 : (n : ℝ) / 6 * ((c : ℝ) - α) ≤ ϱ := by
      calc
        (n : ℝ) / 6 * ((c : ℝ) - α) ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        _ ≤ ϱ := h1
    rw [le_div_iff₀ hnR_pos]
    linarith
  have hNout_le : Nout ≤ ϱ := by
    have hsq0 : 0 ≤ (3 / 2 : ℝ) * ((c : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 := by positivity
    have h2' : 0 ≤ ((n : ℝ) - 2 * (c : ℝ) + 1) * ((c : ℝ) - α) := by
      have : 2 * (c : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc_le_half
      exact mul_nonneg (by linarith) (by linarith)
    linarith
  -- Now bound `B` and `D_C + e(G[R])` as in Okechukwu Theorem 3.3.
  let R := (Finset.univ : Finset (Fin n)) \ C
  have hRcard : R.card = n - c := by
    rw [card_sdiff_of_subset (subset_univ C), card_univ, Fintype.card_fin]
  have hcn : c ≤ n := by simpa [c] using card_le_univ C
  have hz_edge : ∀ u w : Fin n, G.Adj u w → z s(u, w) ≤ 1 := fun _ _ h ↦ hz_edge_of_feas hL4 hz h
  let bx : Fin n → ℝ := fun x ↦ (c : ℝ) - ∑ u ∈ C.filter (fun u ↦ G.Adj x u), z s(x, u)
  let B : ℝ := ∑ x ∈ R, bx x
  have hbx_ge_miss : ∀ x ∈ R, ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) ≤ bx x := by
    intro x _
    have hsum_le : ∑ u ∈ C.filter (fun u ↦ G.Adj x u), z s(x, u) ≤
        ((C.filter (fun u ↦ G.Adj x u)).card : ℝ) := by
      calc
        ∑ u ∈ C.filter (fun u ↦ G.Adj x u), z s(x, u)
            ≤ ∑ _u ∈ C.filter (fun u ↦ G.Adj x u), (1 : ℝ) :=
              sum_le_sum (fun u hu ↦ hz_edge x u (mem_filter.mp hu).2)
        _ = ((C.filter (fun u ↦ G.Adj x u)).card : ℝ) := by simp
    have hpart : ((C.filter (fun u ↦ G.Adj x u)).card : ℝ) +
        ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) = (c : ℝ) := by
      have hnat : (C.filter (fun u ↦ G.Adj x u)).card +
          (C.filter (fun u ↦ ¬ G.Adj x u)).card = c := by
        simpa [c] using Finset.sum_filter_add_sum_filter_not C (fun u ↦ G.Adj x u) (fun _ ↦ (1 : ℕ))
      exact_mod_cast hnat
    dsimp [bx]
    linarith
  have hbx_nonneg : ∀ x ∈ R, 0 ≤ bx x := fun x hx ↦ le_trans (Nat.cast_nonneg _) (hbx_ge_miss x hx)
  let EC := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C)
  let ER := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)
  let ECR := G.edgeFinset.filter (fun e ↦ (∃ u ∈ C, u ∈ e) ∧ (∃ r ∈ R, r ∈ e))
  have hECR_sum : ∑ e ∈ ECR, z e = ∑ x ∈ R, ∑ u ∈ C.filter (fun u ↦ G.Adj x u), z s(x, u) := by
    have hdisj_bi : Set.PairwiseDisjoint (R : Set (Fin n))
        (fun x ↦ (C.filter (fun u ↦ G.Adj x u)).image (fun u ↦ (x, u))) := by
      intro x₁ _ x₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      rcases mem_image.mp hp₁ with ⟨_, _, rfl⟩
      rcases mem_image.mp hp₂ with ⟨_, _, hEq⟩
      exact hne (Prod.mk.inj hEq).1.symm
    have hbi_eq : ∑ x ∈ R, ∑ u ∈ C.filter (fun u ↦ G.Adj x u), z s(x, u) =
        ∑ p ∈ R.biUnion (fun x ↦ (C.filter (fun u ↦ G.Adj x u)).image (fun u ↦ (x, u))),
          z s(p.1, p.2) := by
      rw [sum_biUnion hdisj_bi]
      refine sum_congr rfl fun x _ ↦ ?_
      rw [sum_image (fun _ _ _ _ h ↦ (Prod.mk.inj h).2)]
    rw [hbi_eq]
    symm
    refine Finset.sum_bij (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      rcases mem_biUnion.mp hp with ⟨x, hxR, hpx⟩
      rcases mem_image.mp hpx with ⟨u, hu, rfl⟩
      rw [mem_filter] at hu
      rw [mem_filter, mem_edgeFinset]
      exact ⟨hu.2, ⟨u, hu.1, by simp⟩, ⟨x, hxR, by simp⟩⟩
    · intro p₁ hp₁ p₂ hp₂ hEq
      rcases mem_biUnion.mp hp₁ with ⟨x₁, hx₁R, hp₁x⟩
      rcases mem_image.mp hp₁x with ⟨u₁, hu₁, rfl⟩
      rcases mem_biUnion.mp hp₂ with ⟨x₂, hx₂R, hp₂x⟩
      rcases mem_image.mp hp₂x with ⟨u₂, hu₂, rfl⟩
      have hu₂C : u₂ ∈ C := (mem_filter.mp hu₂).1
      rcases Sym2.eq_iff.mp hEq with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Prod.ext h1 h2
      · simp only at h1
        exact absurd hu₂C (mem_sdiff.mp (h1 ▸ hx₁R)).2
    · intro e he
      rw [mem_filter, mem_edgeFinset] at he
      rcases he.2.1 with ⟨u, huC, hue⟩
      rcases he.2.2 with ⟨x, hxR, hxe⟩
      have hux : u ≠ x := fun h ↦ (mem_sdiff.mp (h ▸ hxR)).2 huC
      have he_eq : e = s(x, u) := (Sym2.mem_and_mem_iff hux.symm).mp ⟨hxe, hue⟩
      refine ⟨(x, u), ?_, he_eq.symm⟩
      refine mem_biUnion.mpr ⟨x, hxR, mem_image.mpr ⟨u, mem_filter.mpr ⟨huC, ?_⟩, rfl⟩⟩
      rw [he_eq] at he
      exact he.1
    · intro _ _; rfl
  have hECR_card :
      ((c * (n - c) - ECR.card : ℕ) : ℝ) = ∑ x ∈ R, ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) := by
    have hsum_adj : ECR.card = ∑ x ∈ R, (C.filter (fun u ↦ G.Adj x u)).card := by
      have hcard_bij : ECR.card =
          ((R.biUnion (fun x ↦ (C.filter (fun u ↦ G.Adj x u)).image (fun u ↦ (x, u))))).card := by
        symm
        refine Finset.card_bij (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_
        · intro p hp
          rcases mem_biUnion.mp hp with ⟨x, hxR, hpx⟩
          rcases mem_image.mp hpx with ⟨u, hu, rfl⟩
          rw [mem_filter] at hu
          rw [mem_filter, mem_edgeFinset]
          exact ⟨hu.2, ⟨u, hu.1, by simp⟩, ⟨x, hxR, by simp⟩⟩
        · intro p₁ hp₁ p₂ hp₂ hEq
          rcases mem_biUnion.mp hp₁ with ⟨x₁, hx₁R, hp₁x⟩
          rcases mem_image.mp hp₁x with ⟨u₁, hu₁, rfl⟩
          rcases mem_biUnion.mp hp₂ with ⟨x₂, hx₂R, hp₂x⟩
          rcases mem_image.mp hp₂x with ⟨u₂, hu₂, rfl⟩
          have hu₂C : u₂ ∈ C := (mem_filter.mp hu₂).1
          rcases Sym2.eq_iff.mp hEq with ⟨h1, h2⟩ | ⟨h1, _⟩
          · exact Prod.ext h1 h2
          · simp only at h1
            exact absurd hu₂C (mem_sdiff.mp (h1 ▸ hx₁R)).2
        · intro e he
          rw [mem_filter, mem_edgeFinset] at he
          rcases he.2.1 with ⟨u, huC, hue⟩
          rcases he.2.2 with ⟨x, hxR, hxe⟩
          have hux : u ≠ x := fun h ↦ (mem_sdiff.mp (h ▸ hxR)).2 huC
          have he_eq : e = s(x, u) := (Sym2.mem_and_mem_iff hux.symm).mp ⟨hxe, hue⟩
          refine ⟨(x, u), ?_, he_eq.symm⟩
          refine mem_biUnion.mpr ⟨x, hxR, mem_image.mpr ⟨u, mem_filter.mpr ⟨huC, ?_⟩, rfl⟩⟩
          rw [he_eq] at he
          exact he.1
      rw [hcard_bij, card_biUnion]
      · refine sum_congr rfl ?_
        intro x _
        exact card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2)
      · intro x₁ _ x₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp₁ hp₂
        rcases mem_image.mp hp₁ with ⟨_, _, rfl⟩
        rcases mem_image.mp hp₂ with ⟨_, _, hEq⟩
        exact hne (Prod.mk.inj hEq).1.symm
    have hsum_tot :
        (∑ x ∈ R, (C.filter (fun u ↦ G.Adj x u)).card) +
        (∑ x ∈ R, (C.filter (fun u ↦ ¬ G.Adj x u)).card) = c * (n - c) := by
      rw [← sum_add_distrib]
      have hterm : ∀ x ∈ R, (C.filter (fun u ↦ G.Adj x u)).card +
          (C.filter (fun u ↦ ¬ G.Adj x u)).card = c := by
        intro x _
        simpa [c] using Finset.sum_filter_add_sum_filter_not C (fun u ↦ G.Adj x u) (fun _ ↦ (1 : ℕ))
      rw [sum_congr rfl hterm, sum_const, hRcard, smul_eq_mul, mul_comm]
    have hsub : c * (n - c) - ECR.card = ∑ x ∈ R, (C.filter (fun u ↦ ¬ G.Adj x u)).card := by omega
    rw [hsub]
    exact_mod_cast rfl
  have hDC_le_B : ((c * (n - c) - ECR.card : ℕ) : ℝ) ≤ B := by
    rw [hECR_card]
    exact sum_le_sum hbx_ge_miss
  have hW_decomp : W = (∑ e ∈ EC, z e) + (∑ e ∈ ECR, z e) + (∑ e ∈ ER, z e) := by
    have hpart : G.edgeFinset = EC ∪ ECR ∪ ER := by
      ext e
      simp only [EC, ECR, ER, mem_union, mem_filter]
      constructor
      · intro he
        induction e using Sym2.ind with
        | h a b =>
          by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
          · left; left
            exact ⟨he, fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
          · left; right
            exact ⟨he, ⟨a, ha, by simp⟩, ⟨b, mem_sdiff.mpr ⟨mem_univ _, hb⟩, by simp⟩⟩
          · left; right
            exact ⟨he, ⟨b, hb, by simp⟩, ⟨a, mem_sdiff.mpr ⟨mem_univ _, ha⟩, by simp⟩⟩
          · right
            exact ⟨he, fun x hx ↦ by
              rcases Sym2.mem_iff.mp hx with rfl | rfl <;> exact mem_sdiff.mpr ⟨mem_univ _, by assumption⟩⟩
      · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
    have hd1 : Disjoint EC ECR := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      rcases (mem_filter.mp he2).2.2 with ⟨r, hrR, hre⟩
      exact (mem_sdiff.mp hrR).2 ((mem_filter.mp he1).2 r hre)
    have hd2 : Disjoint (EC ∪ ECR) ER := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      rcases mem_union.mp he1 with h | h
      · rw [mem_filter, mem_edgeFinset] at h
        induction e using Sym2.ind with
        | h a _ =>
          exact (mem_sdiff.mp ((mem_filter.mp he2).2 a (by simp))).2 (h.2 a (by simp))
      · rcases (mem_filter.mp h).2.1 with ⟨u, huC, hue⟩
        exact (mem_sdiff.mp ((mem_filter.mp he2).2 u hue)).2 huC
    dsimp [W]
    rw [hpart, sum_union hd2, sum_union hd1]
  have hB_eq : B = (c : ℝ) * ((n : ℝ) - (c : ℝ)) - ∑ e ∈ ECR, z e := by
    dsimp [B, bx]
    rw [sum_sub_distrib, sum_const, hRcard, nsmul_eq_mul, Nat.cast_sub hcn, hECR_sum]
    ring
  have hB_le : B ≤ 7 * ϱ + ∑ e ∈ ER, z e := by
    have hchoose2 : 2 * (c.choose 2 : ℝ) = (c : ℝ) * ((c : ℝ) - 1) := by
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hnat : 2 * c.choose 2 = c * (c - 1) := by
          rw [Nat.choose_two_right]
          have hev := Nat.even_mul_pred_self c
          rcases hev with ⟨q, hq⟩
          omega
        have hR : ((2 * c.choose 2 : ℕ) : ℝ) = ((c * (c - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast [Nat.cast_sub (by omega : 1 ≤ c)] at hR
        exact hR
    have hBn_le : (c : ℝ) * ((n : ℝ) - (c : ℝ)) - (c.choose 2 : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 / 24 := by
      nlinarith [sq_nonneg ((c : ℝ) - (2 * (n : ℝ) + 1) / 6)]
    have hc1_ca : ((c : ℝ) - 1) * ((c : ℝ) - α) ≤ 6 * ϱ := by
      have hc1_le_n : (c : ℝ) - 1 ≤ (n : ℝ) := by linarith [hc_range.2]
      calc
        ((c : ℝ) - 1) * ((c : ℝ) - α) ≤ (n : ℝ) * (6 * ϱ / (n : ℝ)) := by
          have h1' : 0 ≤ (c : ℝ) - α := by linarith
          calc
            ((c : ℝ) - 1) * ((c : ℝ) - α) ≤ (n : ℝ) * ((c : ℝ) - α) :=
              mul_le_mul_of_nonneg_right hc1_le_n h1'
            _ ≤ (n : ℝ) * (6 * ϱ / (n : ℝ)) := mul_le_mul_of_nonneg_left hca_le hnR_pos.le
        _ = 6 * ϱ := by field_simp [ne_of_gt hnR_pos]
    have hW_upper : W ≤ (c : ℝ) * ((n : ℝ) - (c : ℝ)) - (c.choose 2 : ℝ) - B +
        ((c : ℝ) - 1) * ((c : ℝ) - α) + ∑ e ∈ ER, z e := by
      have hEC_tri : ∑ e ∈ EC, z e ≤ (c.choose 2 : ℝ) - ((c : ℝ) - 1) * α := htri
      linarith
    dsimp [ϱ] at hc1_ca ⊢
    linarith
  have hZR_le : ∑ e ∈ ER, z e ≤ (ξ + 1 / (2 * ((L : ℝ) - 1))) * (n : ℝ) ^ 2 + 3 * (n : ℝ) + A₀ * Nout := by
    have hcov := lem_signedcover h1 hG hL4 z hz hξ hn_pos R
    have hRn : (R.card : ℝ) ≤ (n : ℝ) := by
      have : R.card ≤ n := by rw [hRcard]; omega
      exact_mod_cast this
    have hER_card : (ER.card : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
      have h1 : ER.card ≤ n.choose 2 := by
        have hsub : ER ⊆ G.edgeFinset := filter_subset _ _
        have h2 : G.edgeFinset.card ≤ n.choose 2 := by
          have := G.card_edgeFinset_le_card_choose_two
          simpa using this
        exact le_trans (card_le_card hsub) h2
      have h2 : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
        have hnat : 2 * n.choose 2 = n * (n - 1) := by
          rw [Nat.choose_two_right]
          have hev := Nat.even_mul_pred_self n
          rcases hev with ⟨q, hq⟩
          omega
        have hR : (2 : ℝ) * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
          have h' : ((2 * n.choose 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
          push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h'
          exact h'
        nlinarith
      exact le_trans (by exact_mod_cast h1) h2
    have hNR_le : ∑ e ∈ ER, max 0 (-z e) ≤ Nout := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ le_max_left 0 _)
      intro e he
      rw [mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      intro hsub
      induction e using Sym2.ind with
      | h a _ => exact (mem_sdiff.mp (he.2 a (by simp))).2 (hsub a (by simp))
    have hL1_pos : (0 : ℝ) < (L : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
      linarith
    have hterm1 : (R.card : ℝ) * (ξ * (n : ℝ) + 1) ≤ ξ * (n : ℝ) ^ 2 + (n : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hRn (show 0 ≤ ξ * (n : ℝ) + 1 by positivity)
      linarith
    have hterm2 : (ER.card : ℝ) / ((L : ℝ) - 1) ≤ (n : ℝ) ^ 2 / (2 * ((L : ℝ) - 1)) := by
      rw [div_le_div_iff₀ hL1_pos (by linarith)]
      have h1 := mul_le_mul_of_nonneg_right hER_card hL1_pos.le
      linarith
    have hterm3 : (R.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) * ∑ e ∈ ER, max 0 (-z e) ≤ A₀ * Nout := by
      have hfrac_le : (R.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) ≤ A₀ := by
        dsimp [A₀]
        have hL2 : 0 ≤ (L : ℝ) - 2 := by
          have : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
          linarith
        have h1' : (R.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) ≤
            (n : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hRn (by positivity)
        have heq : (n : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) = ((L : ℝ) - 2) / ξ := by
          field_simp [ne_of_gt hnR_pos, ne_of_gt hξ]
        linarith
      calc
        (R.card : ℝ) * (((L : ℝ) - 2) / (ξ * (n : ℝ))) * ∑ e ∈ ER, max 0 (-z e)
            ≤ A₀ * ∑ e ∈ ER, max 0 (-z e) :=
              mul_le_mul_of_nonneg_right hfrac_le (sum_nonneg (fun _ _ ↦ le_max_left 0 _))
        _ ≤ A₀ * Nout := mul_le_mul_of_nonneg_left hNR_le hA₀
    have heq_rhs : (ξ + 1 / (2 * ((L : ℝ) - 1))) * (n : ℝ) ^ 2 =
        ξ * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 / (2 * ((L : ℝ) - 1)) := by ring
    linarith
  -- Bound `e(G[R]) ≤ 32 B + 2 ϱ` as in eq:structuralbudget.
  let Rbad := R.filter (fun x ↦ (c : ℝ) / 8 ≤ bx x)
  have hRbad_card : (Rbad.card : ℝ) ≤ 32 * B / (n : ℝ) := by
    have hsum : (Rbad.card : ℝ) * ((c : ℝ) / 8) ≤ B := by
      calc
        (Rbad.card : ℝ) * ((c : ℝ) / 8) = ∑ _x ∈ Rbad, (c : ℝ) / 8 := by simp
        _ ≤ ∑ x ∈ Rbad, bx x := sum_le_sum (fun x hx ↦ (mem_filter.mp hx).2)
        _ ≤ ∑ x ∈ R, bx x := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x hx _ ↦ hbx_nonneg x hx)
    rw [le_div_iff₀ hnR_pos]
    have hmul : (Rbad.card : ℝ) * (n : ℝ) ≤ (Rbad.card : ℝ) * (4 * (c : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hc_range.1]) (Nat.cast_nonneg _)
    linarith
  let ER_bad := ER.filter (fun e ↦ ∃ x ∈ Rbad, x ∈ e)
  let ER_good := ER.filter (fun e ↦ ¬ ∃ x ∈ Rbad, x ∈ e)
  have hER_bad : (ER_bad.card : ℝ) ≤ 32 * B := by
    have hsub : ER_bad ⊆ Rbad.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))) := by
      intro e he
      rw [mem_filter] at he
      rcases he.2 with ⟨x, hxR, hxe⟩
      induction e using Sym2.ind with
      | h a b =>
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact mem_biUnion.mpr ⟨x, hxR, mem_image.mpr ⟨b, mem_univ b, rfl⟩⟩
        · exact mem_biUnion.mpr ⟨x, hxR, mem_image.mpr ⟨a, mem_univ a, Sym2.eq_swap⟩⟩
    have hcard : ER_bad.card ≤ Rbad.card * n := by
      calc
        ER_bad.card ≤ (Rbad.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y)))).card :=
          card_le_card hsub
        _ ≤ ∑ x ∈ Rbad, ((Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))).card := card_biUnion_le
        _ ≤ ∑ _x ∈ Rbad, n := sum_le_sum (fun x _ ↦ le_trans card_image_le (by simp))
        _ = Rbad.card * n := by simp
    have hcardR : (ER_bad.card : ℝ) ≤ (Rbad.card : ℝ) * (n : ℝ) := by exact_mod_cast hcard
    have hmul := mul_le_mul_of_nonneg_right hRbad_card hnR_pos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hnR_pos)] at hmul
    linarith
  have hER_good : (ER_good.card : ℝ) ≤ 2 * ϱ := by
    have hneg_good : ∀ e ∈ ER_good, 3 / 4 < -z e := by
      intro e he
      rw [mem_filter, mem_filter, mem_edgeFinset] at he
      induction e using Sym2.ind with
      | h x y =>
        have hxR : x ∈ R := he.1.2 x (by simp)
        have hyR : y ∈ R := he.1.2 y (by simp)
        have hxb : bx x < (c : ℝ) / 8 := by
          by_contra hge
          push Not at hge
          exact he.2 ⟨x, mem_filter.mpr ⟨hxR, hge⟩, by simp⟩
        have hyb : bx y < (c : ℝ) / 8 := by
          by_contra hge
          push Not at hge
          exact he.2 ⟨y, mem_filter.mpr ⟨hyR, hge⟩, by simp⟩
        have hc_pos : (0 : ℝ) < (c : ℝ) := by linarith [hc_range.1]
        -- Find `u ∈ C` with both edges `x-u`, `y-u` present and `z_{xu} + z_{yu} > 7/4`.
        let def_u : Fin n → ℝ := fun u ↦
          (if G.Adj x u then 1 - z s(x, u) else 1) + (if G.Adj y u then 1 - z s(y, u) else 1)
        have hsum_def : ∑ u ∈ C, def_u u = bx x + bx y := by
          have h1 : ∀ w : Fin n, ∑ u ∈ C, (if G.Adj w u then 1 - z s(w, u) else 1) = bx w := by
            intro w
            rw [← sum_filter_add_sum_filter_not C (fun u ↦ G.Adj w u)]
            have hA : ∑ u ∈ C.filter (fun u ↦ G.Adj w u), (if G.Adj w u then 1 - z s(w, u) else 1) =
                ((C.filter (fun u ↦ G.Adj w u)).card : ℝ) - ∑ u ∈ C.filter (fun u ↦ G.Adj w u), z s(w, u) := by
              rw [sum_congr rfl (fun u hu ↦ if_pos (mem_filter.mp hu).2), sum_sub_distrib, sum_const,
                nsmul_eq_mul, mul_one]
            have hB : ∑ u ∈ C.filter (fun u ↦ ¬ G.Adj w u), (if G.Adj w u then 1 - z s(w, u) else 1) =
                ((C.filter (fun u ↦ ¬ G.Adj w u)).card : ℝ) := by
              rw [sum_congr rfl (fun u hu ↦ if_neg (mem_filter.mp hu).2), sum_const, nsmul_eq_mul, mul_one]
            have hpart : ((C.filter (fun u ↦ G.Adj w u)).card : ℝ) +
                ((C.filter (fun u ↦ ¬ G.Adj w u)).card : ℝ) = (c : ℝ) := by
              have hnat : (C.filter (fun u ↦ G.Adj w u)).card +
                  (C.filter (fun u ↦ ¬ G.Adj w u)).card = c := by
                simpa [c] using Finset.sum_filter_add_sum_filter_not C (fun u ↦ G.Adj w u) (fun _ ↦ (1 : ℕ))
              exact_mod_cast hnat
            dsimp [bx]; linarith
          dsimp [def_u]
          rw [sum_add_distrib, h1 x, h1 y]
        have hex_u : ∃ u ∈ C, def_u u < 1 / 4 := by
          by_contra hall
          push Not at hall
          have hge : (c : ℝ) * (1 / 4) ≤ ∑ u ∈ C, def_u u := by
            calc
              (c : ℝ) * (1 / 4) = ∑ _u ∈ C, (1 / 4 : ℝ) := by simp [c]
              _ ≤ ∑ u ∈ C, def_u u := sum_le_sum hall
          linarith
        obtain ⟨u, huC, hu_lt⟩ := hex_u
        have hxu : G.Adj x u := by
          by_contra hna
          have h2 : 0 ≤ (if G.Adj y u then 1 - z s(y, u) else 1) := by
            split_ifs with h
            · linarith [hz_edge y u h]
            · norm_num
          dsimp [def_u] at hu_lt
          simp [hna] at hu_lt
          linarith
        have hyu : G.Adj y u := by
          by_contra hna
          have h1 : 0 ≤ (if G.Adj x u then 1 - z s(x, u) else 1) := by
            rw [if_pos hxu]
            linarith [hz_edge x u hxu]
          dsimp [def_u] at hu_lt
          simp [hna] at hu_lt
          linarith
        dsimp [def_u] at hu_lt
        simp only [hxu, hyu, ↓reduceIte] at hu_lt
        have htri_xyu : z s(x, y) + z s(x, u) + z s(y, u) ≤ 1 :=
          hz_tri_of_feas hL4 hz he.1.1 hxu hyu
        linarith
    have hsum_good : (ER_good.card : ℝ) * (3 / 4) ≤ Nout := by
      have hsub : ER_good ⊆ G.edgeFinset.filter (fun e ↦ ¬ ∀ x ∈ e, x ∈ C) := by
        intro e he
        have heR := (filter_subset _ _) he
        rw [mem_filter] at heR ⊢
        refine ⟨heR.1, ?_⟩
        intro hsub
        induction e using Sym2.ind with
        | h a _ => exact (mem_sdiff.mp (heR.2 a (by simp))).2 (hsub a (by simp))
      calc
        (ER_good.card : ℝ) * (3 / 4) = ∑ _e ∈ ER_good, (3 / 4 : ℝ) := by simp
        _ ≤ ∑ e ∈ ER_good, max 0 (-z e) := sum_le_sum (fun e he ↦ le_trans (hneg_good e he).le (le_max_right 0 _))
        _ ≤ Nout := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ le_max_left 0 _)
    linarith
  have hER_split : (ER.card : ℝ) = (ER_bad.card : ℝ) + (ER_good.card : ℝ) := by
    have hnat : ER_bad.card + ER_good.card = ER.card := by
      simpa [ER_bad, ER_good] using Finset.sum_filter_add_sum_filter_not ER (fun e ↦ ∃ x ∈ Rbad, x ∈ e) (fun _ ↦ (1 : ℕ))
    exact_mod_cast hnat.symm
  have hbudget : ((c * (n - c) - ECR.card : ℕ) : ℝ) + (ER.card : ℝ) ≤ 33 * B + 2 * ϱ := by linarith
  have hB_total : 33 * B + 2 * ϱ ≤ ε * (n : ℝ) ^ 2 := by
    have h1 : 33 * B + 2 * ϱ ≤
        33 * (ξ + 1 / (2 * ((L : ℝ) - 1))) * (n : ℝ) ^ 2 + 99 * (n : ℝ) +
        (33 * (7 + A₀) + 2) * ϱ := by
      have := mul_le_mul_of_nonneg_left hNout_le hA₀
      linarith
    have h2 : 33 * (ξ + 1 / (2 * ((L : ℝ) - 1))) * (n : ℝ) ^ 2 ≤ (ε / 4) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hL_bound.le (sq_nonneg _)
    have h3 : 99 * (n : ℝ) ≤ (ε / 4) * (n : ℝ) ^ 2 := by
      have hle : Nat.ceil (800 / ε) + 1 ≤ n :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
      have hleR : (Nat.ceil (800 / ε) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
      have h800 : 800 / ε ≤ (n : ℝ) := by linarith [Nat.le_ceil (800 / ε)]
      have hεn : 800 ≤ ε * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left h800 hε0.le
        rwa [mul_div_cancel₀ _ (ne_of_gt hε0)] at this
      have hmul := mul_le_mul_of_nonneg_right hεn hnR_pos.le
      linarith
    have h4 : (33 * (7 + A₀) + 2) * ϱ ≤ (ε / 4) * (n : ℝ) ^ 2 := by
      have hden_pos : (0 : ℝ) < 4 * (33 * (7 + A₀) + 2) + 1 := by positivity
      have hγ_mul : (33 * (7 + A₀) + 2) * γ ≤ ε / 4 := by
        have := mul_le_mul_of_nonneg_left hγ_lin (show 0 ≤ 33 * (7 + A₀) + 2 by positivity)
        have hfrac : (33 * (7 + A₀) + 2) * (ε / (4 * (33 * (7 + A₀) + 2) + 1)) ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ hden_pos (by norm_num)]
          have h1 : (33 * (7 + A₀) + 2) * ε * 4 ≤ (33 * (7 + A₀) + 2) * ε * 4 + ε := by linarith
          linarith
        linarith
      calc
        (33 * (7 + A₀) + 2) * ϱ ≤ (33 * (7 + A₀) + 2) * (γ * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hϱ_le (by positivity)
        _ = ((33 * (7 + A₀) + 2) * γ) * (n : ℝ) ^ 2 := by ring
        _ ≤ (ε / 4) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hγ_mul (sq_nonneg _)
    linarith
  refine ⟨C, hCcl, hc_dist, by linarith⟩

/- ### Section 3: Degenerate edge coloring and color-class balancing (Lemma 2.4) -/

lemma degenerate_edge_coloring {n d Δ k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hΔk : Δ + d ≤ k) (hk : 1 ≤ k) :
    ∀ m : ℕ, ∀ R : Finset (Fin n), R.card = m →
      (∀ v ∈ R, (R.filter (fun w ↦ G.Adj v w)).card ≤ Δ) →
      (∀ S ⊆ R, S.Nonempty → ∃ v ∈ S, (S.filter (fun w ↦ G.Adj v w)).card ≤ d) →
      ∃ col : Sym2 (Fin n) → Fin k,
        ∀ u ∈ R, ∀ v ∈ R, ∀ w ∈ R, v ≠ w → G.Adj u v → G.Adj u w →
          col s(u, v) ≠ col s(u, w) := by
  intro m
  induction m with
  | zero =>
    intro R hR _ _
    have hRe : R = ∅ := card_eq_zero.mp hR
    subst hRe
    exact ⟨fun _ ↦ ⟨0, hk⟩, by simp⟩
  | succ m ih =>
    intro R hR hΔ hdeg
    have hne : R.Nonempty := card_pos.mp (by omega)
    obtain ⟨v, hvR, hvdeg⟩ := hdeg R Subset.rfl hne
    let R' := R.erase v
    have hR'card : R'.card = m := by rw [card_erase_of_mem hvR, hR]; omega
    have hR'Δ : ∀ u ∈ R', (R'.filter (fun w ↦ G.Adj u w)).card ≤ Δ := by
      intro u hu
      exact le_trans (card_le_card (filter_subset_filter _ (erase_subset _ _))) (hΔ u (erase_subset _ _ hu))
    have hR'deg : ∀ S ⊆ R', S.Nonempty → ∃ u ∈ S, (S.filter (fun w ↦ G.Adj u w)).card ≤ d :=
      fun S hS ↦ hdeg S (hS.trans (erase_subset _ _))
    obtain ⟨col₀, hcol₀⟩ := ih R' hR'card hR'Δ hR'deg
    -- Color the edges from `v` to `Nv = R'.filter (G.Adj v)` greedily one by one.
    let Nv := R'.filter (fun w ↦ G.Adj v w)
    have hNv_card : Nv.card ≤ d := by
      have hsub : Nv ⊆ R.filter (fun w ↦ G.Adj v w) := filter_subset_filter _ (erase_subset _ _)
      exact le_trans (card_le_card hsub) hvdeg
    have hgreedy : ∀ t : ℕ, ∀ A : Finset (Fin n), A ⊆ Nv → A.card = t →
        ∃ col : Sym2 (Fin n) → Fin k,
          (∀ u ∈ R', ∀ w ∈ R', col s(u, w) = col₀ s(u, w)) ∧
          (∀ a ∈ A, ∀ b ∈ A, a ≠ b → col s(v, a) ≠ col s(v, b)) ∧
          (∀ a ∈ A, ∀ w ∈ R', G.Adj a w → col s(v, a) ≠ col s(a, w)) := by
      intro t
      induction t with
      | zero =>
        intro A _ hA
        have hAe : A = ∅ := card_eq_zero.mp hA
        subst hAe
        exact ⟨col₀, fun _ _ _ _ ↦ rfl, by simp, by simp⟩
      | succ t iht =>
        intro A hAsub hAc
        obtain ⟨a, haA⟩ := card_pos.mp (by omega : 0 < A.card)
        let A' := A.erase a
        have hA'card : A'.card = t := by rw [card_erase_of_mem haA, hAc]; omega
        obtain ⟨col₁, hcol₁_R', hcol₁_A', hcol₁_cross⟩ := iht A' ((erase_subset _ _).trans hAsub) hA'card
        have haR' : a ∈ R' := (mem_filter.mp (hAsub haA)).1
        have hva : G.Adj v a := (mem_filter.mp (hAsub haA)).2
        have hused_A' : (A'.image (fun b ↦ col₁ s(v, b))).card ≤ t :=
          le_trans card_image_le (by omega)
        have hused_a : ((R'.filter (fun w ↦ G.Adj a w)).image (fun w ↦ col₁ s(a, w))).card ≤ Δ - 1 := by
          have hv_mem : v ∈ R.filter (fun w ↦ G.Adj a w) := mem_filter.mpr ⟨hvR, hva.symm⟩
          have hsub : R'.filter (fun w ↦ G.Adj a w) ⊆ (R.filter (fun w ↦ G.Adj a w)).erase v := by
            intro w hw
            rw [mem_filter, mem_erase] at hw
            exact mem_erase.mpr ⟨hw.1.1, mem_filter.mpr ⟨hw.1.2, hw.2⟩⟩
          have hle1 : (R'.filter (fun w ↦ G.Adj a w)).card ≤ (R.filter (fun w ↦ G.Adj a w)).card - 1 := by
            rw [← card_erase_of_mem hv_mem]
            exact card_le_card hsub
          have hle2 := hΔ a (erase_subset _ _ haR')
          exact le_trans card_image_le (by omega)
        let forb : Finset (Fin k) :=
          A'.image (fun b ↦ col₁ s(v, b)) ∪ (R'.filter (fun w ↦ G.Adj a w)).image (fun w ↦ col₁ s(a, w))
        have hforb_lt : forb.card < k := by
          have ht_le : t + 1 ≤ d := by
            have := card_le_card hAsub
            omega
          have h1 := card_union_le (A'.image (fun b ↦ col₁ s(v, b)))
            ((R'.filter (fun w ↦ G.Adj a w)).image (fun w ↦ col₁ s(a, w)))
          dsimp [forb]
          omega
        obtain ⟨c, _, hc_not⟩ : ∃ c ∈ (Finset.univ : Finset (Fin k)), c ∉ forb := by
          by_contra hall
          push Not at hall
          have hsub : (Finset.univ : Finset (Fin k)) ⊆ forb := fun x hx ↦ hall x hx
          have hle := card_le_card hsub
          simp at hle
          omega
        let col₂ : Sym2 (Fin n) → Fin k := fun e ↦ if e = s(v, a) then c else col₁ e
        refine ⟨col₂, ?_, ?_, ?_⟩
        · intro u hu w hw
          have hne : s(u, w) ≠ s(v, a) := by
            intro hEq
            rcases Sym2.eq_iff.mp hEq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact (mem_erase.mp hu).1 h1
            · exact (mem_erase.mp hw).1 h2
          simp [col₂, hne, hcol₁_R' u hu w hw]
        · intro b₁ hb₁ b₂ hb₂ hne
          by_cases h1 : b₁ = a
          · subst h1
            have hb₂' : b₂ ∈ A' := mem_erase.mpr ⟨hne.symm, hb₂⟩
            have hne_e : s(v, b₂) ≠ s(v, b₁) := fun h ↦ by
              rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
              · exact hne h'.symm
              · exact hva.ne h'
            simp only [col₂, ↓reduceIte, hne_e]
            intro heq
            exact hc_not (mem_union_left _ (mem_image.mpr ⟨b₂, hb₂', heq.symm⟩))
          · by_cases h2 : b₂ = a
            · subst h2
              have hb₁' : b₁ ∈ A' := mem_erase.mpr ⟨h1, hb₁⟩
              have hne_e : s(v, b₁) ≠ s(v, b₂) := fun h ↦ by
                rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
                · exact hne h'
                · exact hva.ne h'
              simp only [col₂, ↓reduceIte, hne_e]
              intro heq
              exact hc_not (mem_union_left _ (mem_image.mpr ⟨b₁, hb₁', heq⟩))
            · have hb₁' : b₁ ∈ A' := mem_erase.mpr ⟨h1, hb₁⟩
              have hb₂' : b₂ ∈ A' := mem_erase.mpr ⟨h2, hb₂⟩
              have hne1 : s(v, b₁) ≠ s(v, a) := fun h ↦ by
                rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
                · exact h1 h'
                · exact hva.ne h'
              have hne2 : s(v, b₂) ≠ s(v, a) := fun h ↦ by
                rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
                · exact h2 h'
                · exact hva.ne h'
              simp only [col₂, hne1, hne2, ↓reduceIte]
              exact hcol₁_A' b₁ hb₁' b₂ hb₂' hne
        · intro b hb w hw hbw
          have hne_bw : s(b, w) ≠ s(v, a) := fun h ↦ by
            have hbR' : b ∈ R' := (mem_filter.mp (hAsub hb)).1
            rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact (mem_erase.mp hbR').1 h1
            · exact (mem_erase.mp hw).1 h2
          by_cases hba : b = a
          · subst hba
            simp only [col₂, ↓reduceIte, hne_bw]
            intro heq
            exact hc_not (mem_union_right _ (mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, hbw⟩, heq.symm⟩))
          · have hb' : b ∈ A' := mem_erase.mpr ⟨hba, hb⟩
            have hne_vb : s(v, b) ≠ s(v, a) := fun h ↦ by
              rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h', _⟩
              · exact hba h'
              · exact hva.ne h'
            simp only [col₂, hne_vb, hne_bw, ↓reduceIte]
            exact hcol₁_cross b hb' w hw hbw
    obtain ⟨col, hcol_R', hcol_A, hcol_cross⟩ := hgreedy Nv.card Nv Subset.rfl rfl
    refine ⟨col, ?_⟩
    intro u hu x hx y hy hxy hux huy
    by_cases huv : u = v
    · subst huv
      have hxN : x ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨hux.ne.symm, hx⟩, hux⟩
      have hyN : y ∈ Nv := mem_filter.mpr ⟨mem_erase.mpr ⟨huy.ne.symm, hy⟩, huy⟩
      exact hcol_A x hxN y hyN hxy
    · have huR' : u ∈ R' := mem_erase.mpr ⟨huv, hu⟩
      by_cases hxv : x = v
      · subst hxv
        have huN : u ∈ Nv := mem_filter.mpr ⟨huR', hux.symm⟩
        have hyR' : y ∈ R' := mem_erase.mpr ⟨hxy.symm, hy⟩
        rw [Sym2.eq_swap]
        exact hcol_cross u huN y hyR' huy
      · by_cases hyv : y = v
        · subst hyv
          have huN : u ∈ Nv := mem_filter.mpr ⟨huR', huy.symm⟩
          have hxR' : x ∈ R' := mem_erase.mpr ⟨hxv, hx⟩
          rw [Sym2.eq_swap (a := u) (b := y)]
          exact (hcol_cross u huN x hxR' hux).symm
        · have hxR' : x ∈ R' := mem_erase.mpr ⟨hxv, hx⟩
          have hyR' : y ∈ R' := mem_erase.mpr ⟨hyv, hy⟩
          rw [hcol_R' u huR' x hxR', hcol_R' u huR' y hyR']
          exact hcol₀ u huR' x hxR' y hyR' hxy hux huy

lemma matching_swap_step {n : ℕ} :
    ∀ s : ℕ, ∀ M₁ M₂ : Finset (Sym2 (Fin n)),
      M₁.card + M₂.card = s →
      (∀ e ∈ M₁, ¬ e.IsDiag) → (∀ e ∈ M₂, ¬ e.IsDiag) →
      Disjoint M₁ M₂ →
      (∀ e₁ ∈ M₁, ∀ e₂ ∈ M₁, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) →
      (∀ e₁ ∈ M₂, ∀ e₂ ∈ M₂, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) →
      M₂.card < M₁.card →
      ∃ M₁' M₂' : Finset (Sym2 (Fin n)),
        M₁' ∪ M₂' = M₁ ∪ M₂ ∧ Disjoint M₁' M₂' ∧
        M₁'.card = M₁.card - 1 ∧ M₂'.card = M₂.card + 1 ∧
        (∀ e₁ ∈ M₁', ∀ e₂ ∈ M₁', e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) ∧
        (∀ e₁ ∈ M₂', ∀ e₂ ∈ M₂', e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro M₁ M₂ hs hnd1 hnd2 hdisj hm1 hm2 hlt
    -- Find a vertex covered by `M₁` and not by `M₂`.
    let V1 : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ M₁, x ∈ e)
    let V2 : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ M₂, x ∈ e)
    have hVcard : ∀ M : Finset (Sym2 (Fin n)), (∀ e ∈ M, ¬ e.IsDiag) →
        (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) →
        ((Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ M, x ∈ e)).card = 2 * M.card := by
      intro M hnd hm
      have hbi : (Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ M, x ∈ e) =
          M.biUnion Sym2.toFinset := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, Sym2.mem_toFinset]
      rw [hbi, card_biUnion]
      · have h2 : ∀ e ∈ M, e.toFinset.card = 2 := by
          intro e he
          induction e using Sym2.ind with
          | h a b =>
            have hab : a ≠ b := fun h ↦ hnd s(a, b) he (by subst h; simp)
            rw [Sym2.toFinset_mk_eq, card_pair hab]
        rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
      · intro e₁ he₁ e₂ he₂ hne
        change Disjoint e₁.toFinset e₂.toFinset
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        exact hm e₁ he₁ e₂ he₂ hne x (Sym2.mem_toFinset.mp hx₁) (Sym2.mem_toFinset.mp hx₂)
    have hV2_lt_V1 : V2.card < V1.card := by
      rw [hVcard M₁ hnd1 hm1, hVcard M₂ hnd2 hm2]
      omega
    obtain ⟨v₀, hv₀1, hv₀2⟩ : ∃ v₀ ∈ V1, v₀ ∉ V2 := by
      by_contra hall
      push Not at hall
      exact (card_le_card hall).not_gt hV2_lt_V1
    -- Define the connected component `K` of `v₀` in the union graph `H` of `M₁ ∪ M₂`.
    let H : SimpleGraph (Fin n) :=
      SimpleGraph.fromRel (fun a b ↦ s(a, b) ∈ M₁ ∪ M₂)
    have hH_adj : ∀ a b : Fin n, H.Adj a b ↔ a ≠ b ∧ s(a, b) ∈ M₁ ∪ M₂ := by
      intro a b
      simp only [H, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨hab, h | h⟩
        · exact ⟨hab, h⟩
        · exact ⟨hab, by rwa [Sym2.eq_swap]⟩
      · rintro ⟨hab, h⟩
        exact ⟨hab, Or.inl h⟩
    let K : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun x ↦ H.Reachable v₀ x)
    let P1 : Finset (Sym2 (Fin n)) := M₁.filter (fun e ↦ ∀ x ∈ e, x ∈ K)
    let P2 : Finset (Sym2 (Fin n)) := M₂.filter (fun e ↦ ∀ x ∈ e, x ∈ K)
    have hK_closed : ∀ e ∈ M₁ ∪ M₂, (∃ x ∈ e, x ∈ K) → ∀ y ∈ e, y ∈ K := by
      intro e he ⟨x, hxe, hxK⟩ y hye
      rw [mem_filter] at hxK ⊢
      refine ⟨mem_univ y, ?_⟩
      by_cases hxy : x = y
      · subst hxy; exact hxK.2
      · have he_eq : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).mp ⟨hxe, hye⟩
        have hadj : H.Adj x y := (hH_adj x y).mpr ⟨hxy, he_eq ▸ he⟩
        exact hxK.2.trans hadj.reachable
    -- Every vertex of `K` has degree ≤ 2 in `P1 ∪ P2`, and `v₀ ∈ K` has degree 1 (only in `P1`),
    -- so `P1.card ≤ P2.card + 1` and `P2.card ≤ P1.card`.
    -- Specifically, `2 * P1.card = |V(P1)|` and `2 * P2.card = |V(P2)|`.
    -- Since `K` is connected in `P1 ∪ P2`, `|P1| + |P2| ≥ |K| - 1` (tree bound!).
    -- Actually, even simpler: every vertex in `K \ {v₀}` is reached from `v₀` via a walk, so
    -- we can prove `|K| ≤ |P1| + |P2| + 1` by induction on `K`, AND `2 * |P1| ≤ |K|`, `2 * |P2| ≤ |K| - 1`
    -- (since `v₀ ∉ V(P2)`!), which IMMEDIATELY forces:
    -- `2 * |P1| ≤ |K| ≤ |P1| + |P2| + 1 ⟹ |P1| ≤ |P2| + 1`!!
    -- AND `2 * |P2| ≤ |K| - 1 ≤ |P1| + |P2| ⟹ |P2| ≤ |P1|`!!
    have hK_conn_edges : K.card ≤ P1.card + P2.card + 1 := by
      -- Prove for any connected finite graph `H` on `K` (nonempty), `|K| ≤ |E(K)| + 1`.
      -- Induction on `t = |A|` for reachable subsets `A ⊆ K` containing `v₀`:
      -- Start with `A = {v₀}` (`|A| = 1`, `|E(A)| = 0`). While `A ⊂ K`, there is an edge from `A` to `K \ A`,
      -- adding 1 vertex and at least 1 edge!
      have hgrow : ∀ t : ℕ, t ≤ K.card → 1 ≤ t →
          ∃ A ⊆ K, A.card = t ∧ A.card ≤ ((P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ A)).card + 1 := by
        intro t
        induction t with
        | zero => intro _ h; omega
        | succ t iht =>
          intro htK _
          by_cases ht0 : t = 0
          · subst ht0
            refine ⟨{v₀}, ?_, card_singleton v₀, by rw [card_singleton]; omega⟩
            intro x hx
            rw [mem_singleton.mp hx, mem_filter]
            exact ⟨mem_univ _, SimpleGraph.Reachable.refl v₀⟩
          · obtain ⟨A, hAK, hAc, hAedges⟩ := iht (by omega) (by omega)
            have hKA_ne : (K \ A).Nonempty := by
              have hcard : (K \ A).card = K.card - A.card := card_sdiff_of_subset hAK
              exact card_pos.mp (by omega)
            obtain ⟨z, hzKA⟩ := hKA_ne
            have hzK : z ∈ K := (mem_sdiff.mp hzKA).1
            have hzA : z ∉ A := (mem_sdiff.mp hzKA).2
            have hv₀A : v₀ ∈ A ∨ v₀ ∉ A := em _
            -- Since `K` is a connected component of `H` and `A ⊂ K` is nonempty, there is an edge between `A` and `K \ A`.
            have hbridge : ∃ a ∈ A, ∃ b ∈ K \ A, H.Adj a b := by
              obtain ⟨a₀, ha₀⟩ := card_pos.mp (by omega : 0 < A.card)
              have hreach : H.Reachable a₀ z :=
                ((mem_filter.mp (hAK ha₀)).2).symm.trans (mem_filter.mp hzK).2
              obtain ⟨w⟩ := hreach
              have hwalk : ∀ {u v : Fin n} (p : H.Walk u v), u ∈ A → v ∉ A →
                  ∃ a ∈ A, ∃ b ∉ A, H.Adj a b := by
                intro u v p
                induction p with
                | nil => intro hu hv; exact absurd hu hv
                | @cons x y z hxy p' ihp =>
                  intro hxA hzA'
                  by_cases hyA : y ∈ A
                  · exact ihp hyA hzA'
                  · exact ⟨x, hxA, y, hyA, hxy⟩
              obtain ⟨a, haA, b, hbA, hab⟩ := hwalk w ha₀ hzA
              have hbK : b ∈ K := mem_filter.mpr ⟨mem_univ b, (mem_filter.mp (hAK haA)).2.trans hab.reachable⟩
              exact ⟨a, haA, b, mem_sdiff.mpr ⟨hbK, hbA⟩, hab⟩
            obtain ⟨a, haA, b, hbKA, hab⟩ := hbridge
            have hbK : b ∈ K := (mem_sdiff.mp hbKA).1
            have hbA : b ∉ A := (mem_sdiff.mp hbKA).2
            let A' := insert b A
            have hA'K : A' ⊆ K := insert_subset hbK hAK
            have hA'c : A'.card = t + 1 := by rw [card_insert_of_notMem hbA, hAc]
            have hab_mem : s(a, b) ∈ (P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ A') := by
              rw [mem_filter]
              refine ⟨?_, fun x hx ↦ ?_⟩
              · have h1 := (hH_adj a b).mp hab
                rcases mem_union.mp h1.2 with hM1 | hM2
                · exact mem_union_left _ (mem_filter.mpr ⟨hM1, fun x hx ↦ by
                    rcases Sym2.mem_iff.mp hx with rfl | rfl
                    · exact hAK haA
                    · exact hbK⟩)
                · exact mem_union_right _ (mem_filter.mpr ⟨hM2, fun x hx ↦ by
                    rcases Sym2.mem_iff.mp hx with rfl | rfl
                    · exact hAK haA
                    · exact hbK⟩)
              · rcases Sym2.mem_iff.mp hx with rfl | rfl
                · exact mem_insert_of_mem haA
                · exact mem_insert_self x A
            have hab_not : s(a, b) ∉ (P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ A) := by
              intro hmem
              exact hbA ((mem_filter.mp hmem).2 b (by simp))
            have hsub_e : insert s(a, b) ((P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ A)) ⊆
                (P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ A') := by
              intro e he
              rcases mem_insert.mp he with rfl | heA
              · exact hab_mem
              · rw [mem_filter] at heA ⊢
                exact ⟨heA.1, fun x hx ↦ mem_insert_of_mem (heA.2 x hx)⟩
            have hcard_e := card_le_card hsub_e
            rw [card_insert_of_notMem hab_not] at hcard_e
            refine ⟨A', hA'K, hA'c, by omega⟩
      have hK_pos : 1 ≤ K.card := card_pos.mpr ⟨v₀, mem_filter.mpr ⟨mem_univ _, SimpleGraph.Reachable.refl v₀⟩⟩
      obtain ⟨A, hAK, hAc, hAe⟩ := hgrow K.card le_rfl hK_pos
      have hAK_eq : A = K := Finset.eq_of_subset_of_card_le hAK (by omega)
      subst hAK_eq
      have hfilt_eq : (P1 ∪ P2).filter (fun e ↦ ∀ x ∈ e, x ∈ K) = P1 ∪ P2 := by
        ext e; simp only [mem_filter, and_iff_left_iff_imp]
        intro he
        rcases mem_union.mp he with h | h <;> exact (mem_filter.mp h).2
      rw [hfilt_eq, card_union_of_disjoint (hdisj.mono (filter_subset _ _) (filter_subset _ _))] at hAe
      exact hAe
    have hP1_bound : 2 * P1.card ≤ K.card := by
      have hsub : (Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ P1, x ∈ e) ⊆ K := by
        intro x hx
        rcases (mem_filter.mp hx).2 with ⟨e, he, hxe⟩
        exact (mem_filter.mp he).2 x hxe
      have hle := card_le_card hsub
      rw [hVcard P1 (fun e he ↦ hnd1 e (filter_subset _ _ he))
        (fun e₁ he₁ e₂ he₂ ↦ hm1 e₁ (filter_subset _ _ he₁) e₂ (filter_subset _ _ he₂))] at hle
      exact hle
    have hP2_bound : 2 * P2.card + 1 ≤ K.card := by
      have hv₀K : v₀ ∈ K := mem_filter.mpr ⟨mem_univ _, SimpleGraph.Reachable.refl v₀⟩
      have hsub : (Finset.univ : Finset (Fin n)).filter (fun x ↦ ∃ e ∈ P2, x ∈ e) ⊆ K.erase v₀ := by
        intro x hx
        rcases (mem_filter.mp hx).2 with ⟨e, he, hxe⟩
        refine mem_erase.mpr ⟨?_, (mem_filter.mp he).2 x hxe⟩
        intro hxv
        subst hxv
        exact hv₀2 (mem_filter.mpr ⟨mem_univ _, e, filter_subset _ _ he, hxe⟩)
      have hle := card_le_card hsub
      rw [hVcard P2 (fun e he ↦ hnd2 e (filter_subset _ _ he))
        (fun e₁ he₁ e₂ he₂ ↦ hm2 e₁ (filter_subset _ _ he₁) e₂ (filter_subset _ _ he₂)),
        card_erase_of_mem hv₀K] at hle
      have hKpos : 1 ≤ K.card := card_pos.mpr ⟨v₀, hv₀K⟩
      omega
    have hP1_pos : 1 ≤ P1.card := by
      rcases (mem_filter.mp hv₀1).2 with ⟨e₀, he₀, hv₀e⟩
      have hv₀K : v₀ ∈ K := mem_filter.mpr ⟨mem_univ _, SimpleGraph.Reachable.refl v₀⟩
      have he₀P : e₀ ∈ P1 := mem_filter.mpr ⟨he₀, hK_closed e₀ (mem_union_left _ he₀) ⟨v₀, hv₀e, hv₀K⟩⟩
      exact card_pos.mpr ⟨e₀, he₀P⟩
    have hP1_le : P1.card ≤ P2.card + 1 := by omega
    have hP2_le : P2.card ≤ P1.card := by omega
    by_cases hodd : P1.card = P2.card + 1
    · -- Swap `P1` and `P2`!
      let M₁' := (M₁ \ P1) ∪ P2
      let M₂' := (M₂ \ P2) ∪ P1
      have hP1sub : P1 ⊆ M₁ := filter_subset _ _
      have hP2sub : P2 ⊆ M₂ := filter_subset _ _
      have hd_1_2 : Disjoint (M₁ \ P1) P2 := hdisj.mono sdiff_subset hP2sub
      have hd_2_1 : Disjoint (M₂ \ P2) P1 := hdisj.symm.mono sdiff_subset hP1sub
      have hno_cross : ∀ e ∈ (M₁ \ P1) ∪ (M₂ \ P2), ∀ x ∈ e, x ∉ K := by
        intro e he x hxe hxK
        have heM : e ∈ M₁ ∪ M₂ := by
          rcases mem_union.mp he with h | h
          · exact mem_union_left _ (sdiff_subset h)
          · exact mem_union_right _ (sdiff_subset h)
        have hallK := hK_closed e heM ⟨x, hxe, hxK⟩
        rcases mem_union.mp he with h | h
        · exact (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1, hallK⟩)
        · exact (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1, hallK⟩)
      refine ⟨M₁', M₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ext e
        simp only [M₁', M₂', mem_union, mem_sdiff]
        by_cases h1 : e ∈ P1 <;> by_cases h2 : e ∈ P2
        · exact absurd (hP2sub h2) (Finset.disjoint_left.mp hdisj (hP1sub h1))
        · simp [h1, h2, hP1sub h1]
        · simp [h1, h2, hP2sub h2]
        · simp [h1, h2]
      · rw [Finset.disjoint_left]
        intro e he1 he2
        rcases mem_union.mp he1 with h1 | h1 <;> rcases mem_union.mp he2 with h2 | h2
        · exact Finset.disjoint_left.mp hdisj (sdiff_subset h1) (sdiff_subset h2)
        · exact (mem_sdiff.mp h1).2 h2
        · exact (mem_sdiff.mp h2).2 h1
        · exact Finset.disjoint_left.mp hdisj (hP1sub h2) (hP2sub h1)
      · rw [card_union_of_disjoint hd_1_2, card_sdiff_of_subset hP1sub]
        have : P1.card ≤ M₁.card := card_le_card hP1sub
        omega
      · rw [card_union_of_disjoint hd_2_1, card_sdiff_of_subset hP2sub]
        have : P2.card ≤ M₂.card := card_le_card hP2sub
        omega
      · intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        rcases mem_union.mp he₁ with h1 | h1 <;> rcases mem_union.mp he₂ with h2 | h2
        · exact hm1 e₁ (sdiff_subset h1) e₂ (sdiff_subset h2) hne x hx₁ hx₂
        · exact hno_cross e₁ (mem_union_left _ h1) x hx₁ ((mem_filter.mp h2).2 x hx₂)
        · exact hno_cross e₂ (mem_union_left _ h2) x hx₂ ((mem_filter.mp h1).2 x hx₁)
        · exact hm2 e₁ (hP2sub h1) e₂ (hP2sub h2) hne x hx₁ hx₂
      · intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        rcases mem_union.mp he₁ with h1 | h1 <;> rcases mem_union.mp he₂ with h2 | h2
        · exact hm2 e₁ (sdiff_subset h1) e₂ (sdiff_subset h2) hne x hx₁ hx₂
        · exact hno_cross e₁ (mem_union_right _ h1) x hx₁ ((mem_filter.mp h2).2 x hx₂)
        · exact hno_cross e₂ (mem_union_right _ h2) x hx₂ ((mem_filter.mp h1).2 x hx₁)
        · exact hm1 e₁ (hP1sub h1) e₂ (hP1sub h2) hne x hx₁ hx₂
    · -- `P1.card = P2.card`: delete `P1, P2`, apply IH to `M₁ \ P1, M₂ \ P2`, and put `P1, P2` back!
      have heven : P1.card = P2.card := by omega
      have hP1sub : P1 ⊆ M₁ := filter_subset _ _
      have hP2sub : P2 ⊆ M₂ := filter_subset _ _
      have hs' : (M₁ \ P1).card + (M₂ \ P2).card < s := by
        rw [card_sdiff_of_subset hP1sub, card_sdiff_of_subset hP2sub]
        have : P1.card ≤ M₁.card := card_le_card hP1sub
        have : P2.card ≤ M₂.card := card_le_card hP2sub
        omega
      have hlt' : (M₂ \ P2).card < (M₁ \ P1).card := by
        rw [card_sdiff_of_subset hP1sub, card_sdiff_of_subset hP2sub]
        have : P1.card ≤ M₁.card := card_le_card hP1sub
        have : P2.card ≤ M₂.card := card_le_card hP2sub
        omega
      obtain ⟨Q1, Q2, hQunion, hQdisj, hQ1c, hQ2c, hQ1m, hQ2m⟩ :=
        ih ((M₁ \ P1).card + (M₂ \ P2).card) hs' (M₁ \ P1) (M₂ \ P2) rfl
          (fun e he ↦ hnd1 e (sdiff_subset he)) (fun e he ↦ hnd2 e (sdiff_subset he))
          (hdisj.mono sdiff_subset sdiff_subset)
          (fun e₁ he₁ e₂ he₂ ↦ hm1 e₁ (sdiff_subset he₁) e₂ (sdiff_subset he₂))
          (fun e₁ he₁ e₂ he₂ ↦ hm2 e₁ (sdiff_subset he₁) e₂ (sdiff_subset he₂))
          hlt'
      have hno_cross : ∀ e ∈ Q1 ∪ Q2, ∀ x ∈ e, x ∉ K := by
        intro e he x hxe hxK
        rw [hQunion] at he
        have heM : e ∈ M₁ ∪ M₂ := by
          rcases mem_union.mp he with h | h
          · exact mem_union_left _ (sdiff_subset h)
          · exact mem_union_right _ (sdiff_subset h)
        have hallK := hK_closed e heM ⟨x, hxe, hxK⟩
        rcases mem_union.mp he with h | h
        · exact (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1, hallK⟩)
        · exact (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1, hallK⟩)
      have hdQ1P1 : Disjoint Q1 P1 := by
        rw [Finset.disjoint_left]
        intro e heQ heP
        have : e ∈ (M₁ \ P1) ∪ (M₂ \ P2) := by rw [← hQunion]; exact mem_union_left _ heQ
        rcases mem_union.mp this with h | h
        · exact (mem_sdiff.mp h).2 heP
        · exact Finset.disjoint_left.mp hdisj (hP1sub heP) (sdiff_subset h)
      have hdQ2P2 : Disjoint Q2 P2 := by
        rw [Finset.disjoint_left]
        intro e heQ heP
        have : e ∈ (M₁ \ P1) ∪ (M₂ \ P2) := by rw [← hQunion]; exact mem_union_right _ heQ
        rcases mem_union.mp this with h | h
        · exact Finset.disjoint_left.mp hdisj (sdiff_subset h) (hP2sub heP)
        · exact (mem_sdiff.mp h).2 heP
      refine ⟨Q1 ∪ P1, Q2 ∪ P2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ext e
        have hmemQ : e ∈ Q1 ∪ Q2 ↔ e ∈ (M₁ \ P1) ∪ (M₂ \ P2) := by rw [hQunion]
        simp only [mem_union] at hmemQ ⊢
        by_cases h1 : e ∈ P1 <;> by_cases h2 : e ∈ P2
        · exact absurd (hP2sub h2) (Finset.disjoint_left.mp hdisj (hP1sub h1))
        · simp [h1, h2, hP1sub h1]
        · simp [h1, h2, hP2sub h2]
        · constructor
          · rintro ((h | h) | (h | h))
            · have := hmemQ.mp (Or.inl h)
              rcases this with hm | hm
              · exact Or.inl (sdiff_subset hm)
              · exact Or.inr (sdiff_subset hm)
            · exact absurd h h1
            · have := hmemQ.mp (Or.inr h)
              rcases this with hm | hm
              · exact Or.inl (sdiff_subset hm)
              · exact Or.inr (sdiff_subset hm)
            · exact absurd h h2
          · rintro (hm | hm)
            · rcases hmemQ.mpr (Or.inl (mem_sdiff.mpr ⟨hm, h1⟩)) with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
            · rcases hmemQ.mpr (Or.inr (mem_sdiff.mpr ⟨hm, h2⟩)) with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
      · rw [Finset.disjoint_left]
        intro e he1 he2
        rcases mem_union.mp he1 with h1 | h1 <;> rcases mem_union.mp he2 with h2 | h2
        · exact Finset.disjoint_left.mp hQdisj h1 h2
        · have : e ∈ (M₁ \ P1) ∪ (M₂ \ P2) := by rw [← hQunion]; exact mem_union_left _ h1
          rcases mem_union.mp this with h | h
          · exact Finset.disjoint_left.mp hdisj (sdiff_subset h) (hP2sub h2)
          · exact (mem_sdiff.mp h).2 h2
        · have : e ∈ (M₁ \ P1) ∪ (M₂ \ P2) := by rw [← hQunion]; exact mem_union_right _ h2
          rcases mem_union.mp this with h | h
          · exact (mem_sdiff.mp h).2 h1
          · exact Finset.disjoint_left.mp hdisj (hP1sub h1) (sdiff_subset h)
        · exact Finset.disjoint_left.mp hdisj (hP1sub h1) (hP2sub h2)
      · rw [card_union_of_disjoint hdQ1P1, hQ1c, card_sdiff_of_subset hP1sub]
        have hltP : P1.card < M₁.card := by
          rw [card_sdiff_of_subset hP1sub] at hlt'
          omega
        omega
      · rw [card_union_of_disjoint hdQ2P2, hQ2c, card_sdiff_of_subset hP2sub]
        have : P2.card ≤ M₂.card := card_le_card hP2sub
        omega
      · intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        rcases mem_union.mp he₁ with h1 | h1 <;> rcases mem_union.mp he₂ with h2 | h2
        · exact hQ1m e₁ h1 e₂ h2 hne x hx₁ hx₂
        · exact hno_cross e₁ (mem_union_left _ h1) x hx₁ ((mem_filter.mp h2).2 x hx₂)
        · exact hno_cross e₂ (mem_union_left _ h2) x hx₂ ((mem_filter.mp h1).2 x hx₁)
        · exact hm1 e₁ (hP1sub h1) e₂ (hP1sub h2) hne x hx₁ hx₂
      · intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        rcases mem_union.mp he₁ with h1 | h1 <;> rcases mem_union.mp he₂ with h2 | h2
        · exact hQ2m e₁ h1 e₂ h2 hne x hx₁ hx₂
        · exact hno_cross e₁ (mem_union_right _ h1) x hx₁ ((mem_filter.mp h2).2 x hx₂)
        · exact hno_cross e₂ (mem_union_right _ h2) x hx₂ ((mem_filter.mp h1).2 x hx₁)
        · exact hm2 e₁ (hP2sub h1) e₂ (hP2sub h2) hne x hx₁ hx₂

lemma balanced_edge_coloring {n k : ℕ} (hk : 1 ≤ k) (E : Finset (Sym2 (Fin n)))
    (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    (col₀ : Sym2 (Fin n) → Fin k)
    (hcol₀ : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → col₀ e₁ = col₀ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) :
    ∃ col : Sym2 (Fin n) → Fin k,
      (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → col e₁ = col e₂ → ∀ x, x ∈ e₁ → x ∉ e₂) ∧
      ∀ c : Fin k, (E.filter (fun e ↦ col e = c)).card ≤ E.card / k + 1 := by
  let proper : Finset (E → Fin k) :=
    (Finset.univ : Finset (E → Fin k)).filter (fun f ↦
      ∀ e₁ e₂ : E, e₁ ≠ e₂ → f e₁ = f e₂ → ∀ x, x ∈ e₁.1 → x ∉ e₂.1)
  have hne : proper.Nonempty := by
    refine ⟨fun e ↦ col₀ e.1, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    intro e₁ e₂ hne' heq x hx₁
    exact hcol₀ e₁.1 e₁.2 e₂.1 e₂.2 (fun h ↦ hne' (Subtype.ext h)) heq x hx₁
  let energy : (E → Fin k) → ℕ := fun f ↦
    ∑ c : Fin k, ((Finset.univ : Finset E).filter (fun e ↦ f e = c)).card ^ 2
  obtain ⟨f, hfmem, hfmin⟩ := Finset.exists_min_image proper energy hne
  have hfprop : ∀ e₁ e₂ : E, e₁ ≠ e₂ → f e₁ = f e₂ → ∀ x, x ∈ e₁.1 → x ∉ e₂.1 :=
    (mem_filter.mp hfmem).2
  let col : Sym2 (Fin n) → Fin k := fun e ↦ if he : e ∈ E then f ⟨e, he⟩ else ⟨0, hk⟩
  have hcol_sub : ∀ e : E, col e.1 = f e := fun e ↦ by simp [col, e.2]
  have hclass_card : ∀ c : Fin k,
      (E.filter (fun e ↦ col e = c)).card = ((Finset.univ : Finset E).filter (fun e ↦ f e = c)).card := by
    intro c
    symm
    refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
    · intro e he
      rw [mem_filter] at he ⊢
      exact ⟨e.2, by rw [hcol_sub e]; exact he.2⟩
    · intro e₁ _ e₂ _ hEq; exact Subtype.ext hEq
    · intro e he
      rw [mem_filter] at he
      refine ⟨⟨e, he.1⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      rw [← hcol_sub ⟨e, he.1⟩]
      exact he.2
  refine ⟨col, ?_, ?_⟩
  · intro e₁ he₁ e₂ he₂ hne' heq x hx₁
    dsimp [col] at heq
    rw [dif_pos he₁, dif_pos he₂] at heq
    exact hfprop ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ (fun h ↦ hne' (congrArg Subtype.val h)) heq x hx₁
  · intro c₁
    by_contra hgt
    push Not at hgt
    have hsum_c : ∑ c : Fin k, (E.filter (fun e ↦ col e = c)).card = E.card := by
      have := Finset.card_eq_sum_card_fiberwise (s := E) (t := (Finset.univ : Finset (Fin k)))
        (f := col) (fun _ _ ↦ mem_univ _)
      exact this.symm
    have hex_c₂ : ∃ c₂ : Fin k, (E.filter (fun e ↦ col e = c₂)).card ≤ E.card / k := by
      by_contra hall
      push Not at hall
      have hge : ∑ _c : Fin k, (E.card / k + 1) ≤ ∑ c : Fin k, (E.filter (fun e ↦ col e = c)).card :=
        sum_le_sum (fun c _ ↦ hall c)
      rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, hsum_c] at hge
      have hdiv : E.card < k * (E.card / k + 1) := by
        have h1 := Nat.div_add_mod E.card k
        have h2 := Nat.mod_lt E.card (by omega : 0 < k)
        nlinarith
      omega
    obtain ⟨c₂, hc₂⟩ := hex_c₂
    have hc12 : c₁ ≠ c₂ := fun h ↦ by subst h; omega
    let M₁ := E.filter (fun e ↦ col e = c₁)
    let M₂ := E.filter (fun e ↦ col e = c₂)
    have hM12_disj : Disjoint M₁ M₂ := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact hc12 ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    have hM1m : ∀ e₁ ∈ M₁, ∀ e₂ ∈ M₁, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂ := by
      intro e₁ h1 e₂ h2 hne' x hx₁
      rw [mem_filter] at h1 h2
      dsimp [col] at h1 h2
      rw [dif_pos h1.1] at h1
      rw [dif_pos h2.1] at h2
      exact hfprop ⟨e₁, h1.1⟩ ⟨e₂, h2.1⟩ (fun h ↦ hne' (congrArg Subtype.val h)) (h1.2.trans h2.2.symm) x hx₁
    have hM2m : ∀ e₁ ∈ M₂, ∀ e₂ ∈ M₂, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂ := by
      intro e₁ h1 e₂ h2 hne' x hx₁
      rw [mem_filter] at h1 h2
      dsimp [col] at h1 h2
      rw [dif_pos h1.1] at h1
      rw [dif_pos h2.1] at h2
      exact hfprop ⟨e₁, h1.1⟩ ⟨e₂, h2.1⟩ (fun h ↦ hne' (congrArg Subtype.val h)) (h1.2.trans h2.2.symm) x hx₁
    have hM2_lt_M1 : M₂.card + 2 ≤ M₁.card := by
      dsimp [M₁, M₂]
      omega
    obtain ⟨M₁', M₂', hU, hD, h1c, h2c, h1m, h2m⟩ :=
      matching_swap_step (M₁.card + M₂.card) M₁ M₂ rfl
        (fun e he ↦ hnd e (filter_subset _ _ he)) (fun e he ↦ hnd e (filter_subset _ _ he))
        hM12_disj hM1m hM2m (by omega)
    let f' : E → Fin k := fun e ↦
      if e.1 ∈ M₁' then c₁ else if e.1 ∈ M₂' then c₂ else f e
    have hf'_mem : f' ∈ proper := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      intro e₁ e₂ hne' heq x hx₁
      have hne12 : e₁.1 ≠ e₂.1 := fun h ↦ hne' (Subtype.ext h)
      have hcase : ∀ e : E, f' e = c₁ ↔ e.1 ∈ M₁' := by
        intro e
        dsimp [f']
        by_cases h1 : e.1 ∈ M₁'
        · simp [h1]
        · by_cases h2 : e.1 ∈ M₂'
          · simp [h1, h2, hc12.symm]
          · simp only [h1, h2, ↓reduceIte, iff_false]
            intro hfc1
            have : e.1 ∈ M₁ ∪ M₂ := mem_union_left _ (mem_filter.mpr ⟨e.2, (hcol_sub e).trans hfc1⟩)
            rw [← hU] at this
            rcases mem_union.mp this with h | h
            · exact h1 h
            · exact h2 h
      have hcase2 : ∀ e : E, f' e = c₂ ↔ e.1 ∈ M₂' := by
        intro e
        dsimp [f']
        by_cases h1 : e.1 ∈ M₁'
        · simp [h1, hc12, Finset.disjoint_left.mp hD h1]
        · by_cases h2 : e.1 ∈ M₂'
          · simp [h1, h2]
          · simp only [h1, h2, ↓reduceIte, iff_false]
            intro hfc2
            have : e.1 ∈ M₁ ∪ M₂ := mem_union_right _ (mem_filter.mpr ⟨e.2, (hcol_sub e).trans hfc2⟩)
            rw [← hU] at this
            rcases mem_union.mp this with h | h
            · exact h1 h
            · exact h2 h
      by_cases hc : f' e₁ = c₁
      · exact h1m e₁.1 ((hcase e₁).mp hc) e₂.1 ((hcase e₂).mp (heq.symm.trans hc)) hne12 x hx₁
      · by_cases hc' : f' e₁ = c₂
        · exact h2m e₁.1 ((hcase2 e₁).mp hc') e₂.1 ((hcase2 e₂).mp (heq.symm.trans hc')) hne12 x hx₁
        · have h1not1 : e₁.1 ∉ M₁' := fun h ↦ hc ((hcase e₁).mpr h)
          have h1not2 : e₁.1 ∉ M₂' := fun h ↦ hc' ((hcase2 e₁).mpr h)
          have h2not1 : e₂.1 ∉ M₁' := fun h ↦ hc (heq.trans ((hcase e₂).mpr h))
          have h2not2 : e₂.1 ∉ M₂' := fun h ↦ hc' (heq.trans ((hcase2 e₂).mpr h))
          dsimp [f'] at heq
          simp only [h1not1, h1not2, h2not1, h2not2, ↓reduceIte] at heq
          exact hfprop e₁ e₂ hne' heq x hx₁
    have hE_lt : energy f' < energy f := by
      have hc_eq : ∀ c : Fin k, c ≠ c₁ → c ≠ c₂ →
          ((Finset.univ : Finset E).filter (fun e ↦ f' e = c)).card =
          ((Finset.univ : Finset E).filter (fun e ↦ f e = c)).card := by
        intro c h1 h2
        congr 1; ext e
        simp only [mem_filter, mem_univ, true_and, f']
        by_cases hm1' : e.1 ∈ M₁'
        · simp only [hm1', ↓reduceIte, h1.symm, false_iff]
          intro hfc
          have : e.1 ∈ M₁ ∪ M₂ := by rw [← hU]; exact mem_union_left _ hm1'
          rcases mem_union.mp this with hm | hm
          · rw [mem_filter] at hm
            exact h1 (hfc.symm.trans ((hcol_sub e).symm.trans hm.2))
          · rw [mem_filter] at hm
            exact h2 (hfc.symm.trans ((hcol_sub e).symm.trans hm.2))
        · by_cases hm2' : e.1 ∈ M₂'
          · simp only [hm1', hm2', ↓reduceIte, h2.symm, false_iff]
            intro hfc
            have : e.1 ∈ M₁ ∪ M₂ := by rw [← hU]; exact mem_union_right _ hm2'
            rcases mem_union.mp this with hm | hm
            · rw [mem_filter] at hm
              exact h1 (hfc.symm.trans ((hcol_sub e).symm.trans hm.2))
            · rw [mem_filter] at hm
              exact h2 (hfc.symm.trans ((hcol_sub e).symm.trans hm.2))
          · simp [hm1', hm2']
      have hc1_eq : ((Finset.univ : Finset E).filter (fun e ↦ f' e = c₁)).card = M₁'.card := by
        refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
        · intro e he
          rw [mem_filter] at he
          dsimp [f'] at he
          by_cases h1 : e.1 ∈ M₁'
          · exact h1
          · by_cases h2 : e.1 ∈ M₂'
            · simp [h1, h2, hc12.symm] at he
            · simp [h1, h2] at he
              have : e.1 ∈ M₁ ∪ M₂ := mem_union_left _ (mem_filter.mpr ⟨e.2, (hcol_sub e).trans he⟩)
              rw [← hU] at this
              rcases mem_union.mp this with h | h
              · exact absurd h h1
              · exact absurd h h2
        · intro e₁ _ e₂ _ hEq; exact Subtype.ext hEq
        · intro e he
          have heE : e ∈ E := by
            have : e ∈ M₁ ∪ M₂ := by rw [← hU]; exact mem_union_left _ he
            rcases mem_union.mp this with h | h <;> exact (mem_filter.mp h).1
          exact ⟨⟨e, heE⟩, mem_filter.mpr ⟨mem_univ _, by simp [f', he]⟩, rfl⟩
      have hc2_eq : ((Finset.univ : Finset E).filter (fun e ↦ f' e = c₂)).card = M₂'.card := by
        refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
        · intro e he
          rw [mem_filter] at he
          dsimp [f'] at he
          by_cases h1 : e.1 ∈ M₁'
          · simp [h1, hc12] at he
          · by_cases h2 : e.1 ∈ M₂'
            · exact h2
            · simp [h1, h2] at he
              have : e.1 ∈ M₁ ∪ M₂ := mem_union_right _ (mem_filter.mpr ⟨e.2, (hcol_sub e).trans he⟩)
              rw [← hU] at this
              rcases mem_union.mp this with h | h
              · exact absurd h h1
              · exact absurd h h2
        · intro e₁ _ e₂ _ hEq; exact Subtype.ext hEq
        · intro e he
          have heE : e ∈ E := by
            have : e ∈ M₁ ∪ M₂ := by rw [← hU]; exact mem_union_right _ he
            rcases mem_union.mp this with h | h <;> exact (mem_filter.mp h).1
          have hnot1 : e ∉ M₁' := Finset.disjoint_right.mp hD he
          exact ⟨⟨e, heE⟩, mem_filter.mpr ⟨mem_univ _, by simp [f', hnot1, he]⟩, rfl⟩
      have hsplit_e : ∀ g : E → Fin k, energy g =
          ((Finset.univ : Finset E).filter (fun e ↦ g e = c₁)).card ^ 2 +
          ((Finset.univ : Finset E).filter (fun e ↦ g e = c₂)).card ^ 2 +
          ∑ c ∈ ((Finset.univ : Finset (Fin k)).erase c₁).erase c₂,
            ((Finset.univ : Finset E).filter (fun e ↦ g e = c)).card ^ 2 := by
        intro g
        dsimp [energy]
        rw [← add_sum_erase _ _ (mem_univ c₁), ← add_sum_erase _ _ (mem_erase.mpr ⟨hc12.symm, mem_univ c₂⟩)]
        ring
      rw [hsplit_e f', hsplit_e f, hc1_eq, hc2_eq, ← hclass_card c₁, ← hclass_card c₂, h1c, h2c]
      have hrest :
          ∑ c ∈ ((Finset.univ : Finset (Fin k)).erase c₁).erase c₂,
            ((Finset.univ : Finset E).filter (fun e ↦ f' e = c)).card ^ 2 =
          ∑ c ∈ ((Finset.univ : Finset (Fin k)).erase c₁).erase c₂,
            ((Finset.univ : Finset E).filter (fun e ↦ f e = c)).card ^ 2 := by
        refine sum_congr rfl ?_
        intro c hc
        rw [mem_erase, mem_erase] at hc
        rw [hc_eq c hc.2.1 hc.1]
      rw [hrest]
      have hdiff : (M₁.card - 1) ^ 2 + (M₂.card + 1) ^ 2 < M₁.card ^ 2 + M₂.card ^ 2 := by
        zify [show 1 ≤ M₁.card by omega]
        nlinarith
      change (M₁.card - 1) ^ 2 + (M₂.card + 1) ^ 2 + _ < M₁.card ^ 2 + M₂.card ^ 2 + _
      omega
    exact (hfmin f' hf'_mem).not_gt hE_lt

/- ### Section 4: Random-injection triangle absorption (Lemma 4.2) -/

lemma lem_absorption (h3 : H3) {n k σ τ : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (C R : Finset (Fin n)) (hdisj : Disjoint C R) (hCR : C ∪ R = Finset.univ)
    (hCcl : G.IsClique (C : Set (Fin n)))
    (hc3 : 3 ≤ C.card) (hck : C.card ≤ k)
    (hσ : ∀ x ∈ R, (C.filter (fun u ↦ ¬ G.Adj x u)).card ≤ σ)
    (hτ : ∀ u ∈ C, (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ)
    (hcap1 : k ≤ 2 * (C.card - 2 * σ))
    (colR : Sym2 (Fin n) → Fin k)
    (hcolR_prop : ∀ e₁ ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R),
      ∀ e₂ ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R),
      e₁ ≠ e₂ → colR e₁ = colR e₂ → ∀ x, x ∈ e₁ → x ∉ e₂)
    (hcolR_bal : ∀ j : Fin k,
      ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)).filter (fun e ↦ colR e = j)).card ≤
        (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)).card / k + 1)
    (hcap2 : 3 * ((C.card + 1) / 2) + 4 * (τ + 2 * ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)).card / k + 1)) ≤
      R.card + 3) :
    ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
      P.card ≤ C.card * R.card - C.card.choose 2 := by
  let ER := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)
  let EC := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ C)
  let ECR := G.edgeFinset.filter (fun e ↦ (∃ u ∈ C, u ∈ e) ∧ (∃ r ∈ R, r ∈ e))
  have hk_pos : 0 < k := by omega
  -- Average over all injections `ι : C ↪ Fin k` to pick one maximizing covered row edges.
  let injs : Finset (C ↪ Fin k) := Finset.univ
  have hinjs_ne : injs.Nonempty := by
    have hcard_le : Fintype.card C ≤ Fintype.card (Fin k) := by simp [hck]
    exact ⟨Function.Embedding.nonempty_of_card_le hcard_le |>.some, mem_univ _⟩
  let goodEdges : (C ↪ Fin k) → Finset (Sym2 (Fin n)) := fun ι ↦
    ER.filter (fun e ↦ ∃ u : C, ι u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x)
  obtain ⟨ι, _, hι_max⟩ := Finset.exists_max_image injs (fun ι ↦ (goodEdges ι).card) hinjs_ne
  -- Lower bound `(goodEdges ι).card * k ≥ ER.card * (C.card - 2 * σ)` via averaging over `ι`!
  have hgood_bound : ER.card * (C.card - 2 * σ) ≤ (goodEdges ι).card * k := by
    have hsum_le : ∑ ι' ∈ injs, (goodEdges ι').card ≤ injs.card * (goodEdges ι).card := by
      calc
        ∑ ι' ∈ injs, (goodEdges ι').card ≤ ∑ _ι' ∈ injs, (goodEdges ι).card :=
          sum_le_sum (fun ι' hι' ↦ hι_max ι' hι')
        _ = injs.card * (goodEdges ι).card := by simp
    have hsum_eq : ∑ ι' ∈ injs, (goodEdges ι').card =
        ∑ e ∈ ER, (injs.filter (fun ι' ↦ ∃ u : C, ι' u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x)).card := by
      have h1 : ∀ ι' ∈ injs, (goodEdges ι').card =
          ∑ e ∈ ER, if ∃ u : C, ι' u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x then 1 else 0 := by
        intro ι' _
        rw [Finset.sum_boole, Nat.cast_id]
      rw [sum_congr rfl h1, sum_comm]
      refine sum_congr rfl ?_
      intro e _
      rw [Finset.sum_boole, Nat.cast_id]
    have hper_e : ∀ e ∈ ER,
        (C.card - 2 * σ) * injs.card ≤
          (injs.filter (fun ι' ↦ ∃ u : C, ι' u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x)).card * k := by
      intro e he
      rw [mem_filter, mem_edgeFinset] at he
      induction e using Sym2.ind with
      | h x y =>
        have hxR : x ∈ R := he.2 x (by simp)
        have hyR : y ∈ R := he.2 y (by simp)
        let CN : Finset C := (Finset.univ : Finset C).filter (fun u ↦ G.Adj u.1 x ∧ G.Adj u.1 y)
        have hCN_card : C.card - 2 * σ ≤ CN.card := by
          have hmiss : ((Finset.univ : Finset C).filter (fun u ↦ ¬ (G.Adj u.1 x ∧ G.Adj u.1 y))).card ≤ 2 * σ := by
            have hsub : (Finset.univ : Finset C).filter (fun u ↦ ¬ (G.Adj u.1 x ∧ G.Adj u.1 y)) ⊆
                (Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj x u.1) ∪
                (Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj y u.1) := by
              intro u hu
              rw [mem_filter] at hu
              rw [mem_union, mem_filter, mem_filter]
              by_cases h1 : G.Adj u.1 x
              · right; exact ⟨mem_univ _, fun h ↦ hu.2 ⟨h1, h.symm⟩⟩
              · left; exact ⟨mem_univ _, fun h ↦ h1 h.symm⟩
            have hle1 : ((Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj x u.1)).card ≤ σ := by
              have hbij : ((Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj x u.1)).card =
                  (C.filter (fun u ↦ ¬ G.Adj x u)).card := by
                refine Finset.card_bij (fun u _ ↦ u.1) ?_ ?_ ?_
                · intro u hu; rw [mem_filter] at hu ⊢; exact ⟨u.2, hu.2⟩
                · intro u₁ _ u₂ _ h; exact Subtype.ext h
                · intro u hu; rw [mem_filter] at hu; exact ⟨⟨u, hu.1⟩, mem_filter.mpr ⟨mem_univ _, hu.2⟩, rfl⟩
              rw [hbij]; exact hσ x hxR
            have hle2 : ((Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj y u.1)).card ≤ σ := by
              have hbij : ((Finset.univ : Finset C).filter (fun u ↦ ¬ G.Adj y u.1)).card =
                  (C.filter (fun u ↦ ¬ G.Adj y u)).card := by
                refine Finset.card_bij (fun u _ ↦ u.1) ?_ ?_ ?_
                · intro u hu; rw [mem_filter] at hu ⊢; exact ⟨u.2, hu.2⟩
                · intro u₁ _ u₂ _ h; exact Subtype.ext h
                · intro u hu; rw [mem_filter] at hu; exact ⟨⟨u, hu.1⟩, mem_filter.mpr ⟨mem_univ _, hu.2⟩, rfl⟩
              rw [hbij]; exact hσ y hyR
            exact le_trans (card_le_card hsub) (le_trans (card_union_le _ _) (by omega))
          have htot : CN.card + ((Finset.univ : Finset C).filter (fun u ↦ ¬ (G.Adj u.1 x ∧ G.Adj u.1 y))).card = C.card := by
            simpa [CN] using Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset C)
              (fun u ↦ G.Adj u.1 x ∧ G.Adj u.1 y) (fun _ ↦ (1 : ℕ))
          omega
        -- Disjoint events `{ι' | ι' u = colR s(x, y)}` over `u ∈ CN`, each of size `injs.card / k`!
        let c₀ : Fin k := colR s(x, y)
        have hdisj_ev : Set.PairwiseDisjoint (CN : Set C) (fun u ↦ injs.filter (fun ι' ↦ ι' u = c₀)) := by
          intro u₁ _ u₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro ι' h1 h2
          exact hne (ι'.injective ((mem_filter.mp h1).2.trans (mem_filter.mp h2).2.symm))
        have hev_sub : CN.biUnion (fun u ↦ injs.filter (fun ι' ↦ ι' u = c₀)) ⊆
            injs.filter (fun ι' ↦ ∃ u : C, ι' u = c₀ ∧ ∀ w ∈ s(x, y), G.Adj u.1 w) := by
          intro ι' hι'
          rcases mem_biUnion.mp hι' with ⟨u, huCN, hu'⟩
          rw [mem_filter] at huCN hu' ⊢
          refine ⟨hu'.1, u, hu'.2, fun w hw ↦ ?_⟩
          rcases Sym2.mem_iff.mp hw with rfl | rfl
          · exact huCN.2.1
          · exact huCN.2.2
        have hev_card_eq : ∀ u : C, (injs.filter (fun ι' ↦ ι' u = c₀)).card * k = injs.card := by
          intro u
          have hall_eq : ∀ j : Fin k,
              (injs.filter (fun ι' ↦ ι' u = j)).card = (injs.filter (fun ι' ↦ ι' u = c₀)).card := by
            intro j
            let sw : Equiv.Perm (Fin k) := Equiv.swap j c₀
            refine Finset.card_bij (fun ι' _ ↦ ι'.trans sw.toEmbedding) ?_ ?_ ?_
            · intro ι' hι'
              rw [mem_filter] at hι' ⊢
              exact ⟨mem_univ _, by simp [sw, hι'.2]⟩
            · intro ι₁ _ ι₂ _ hEq
              refine Function.Embedding.ext (fun w ↦ ?_)
              have := congrArg (fun f : C ↪ Fin k ↦ sw.symm (f w)) hEq
              simpa using this
            · intro ι' hι'
              rw [mem_filter] at hι'
              refine ⟨ι'.trans sw.symm.toEmbedding, mem_filter.mpr ⟨mem_univ _, by simp [sw, hι'.2]⟩,
                Function.Embedding.ext (fun w ↦ by simp)⟩
          have hfib : injs.card = ∑ j : Fin k, (injs.filter (fun ι' ↦ ι' u = j)).card := by
            exact Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ mem_univ _)
          rw [hfib, sum_congr rfl (fun j _ ↦ hall_eq j), sum_const, card_univ, Fintype.card_fin,
            smul_eq_mul, mul_comm]
        have hbi_card : (CN.biUnion (fun u ↦ injs.filter (fun ι' ↦ ι' u = c₀))).card * k =
            CN.card * injs.card := by
          rw [card_biUnion hdisj_ev, sum_mul]
          rw [sum_congr rfl (fun u _ ↦ hev_card_eq u), sum_const, smul_eq_mul]
        calc
          (C.card - 2 * σ) * injs.card ≤ CN.card * injs.card := Nat.mul_le_mul_right _ hCN_card
          _ = (CN.biUnion (fun u ↦ injs.filter (fun ι' ↦ ι' u = c₀))).card * k := hbi_card.symm
          _ ≤ (injs.filter (fun ι' ↦ ∃ u : C, ι' u = c₀ ∧ ∀ w ∈ s(x, y), G.Adj u.1 w)).card * k :=
                Nat.mul_le_mul_right k (card_le_card hev_sub)
    have htot_sum : ER.card * ((C.card - 2 * σ) * injs.card) ≤
        (injs.card * (goodEdges ι).card) * k := by
      have h1 : ∑ _e ∈ ER, (C.card - 2 * σ) * injs.card ≤
          ∑ e ∈ ER, (injs.filter (fun ι' ↦ ∃ u : C, ι' u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x)).card * k :=
        sum_le_sum hper_e
      rw [sum_const, smul_eq_mul, ← sum_mul, ← hsum_eq] at h1
      exact le_trans h1 (Nat.mul_le_mul_right k hsum_le)
    have hinjs_pos : 0 < injs.card := card_pos.mpr hinjs_ne
    have hmul : injs.card * (ER.card * (C.card - 2 * σ)) ≤ injs.card * ((goodEdges ι).card * k) := by
      linarith
    exact Nat.le_of_mul_le_mul_left hmul hinjs_pos
  -- Therefore `ER.card ≤ 2 * (goodEdges ι).card` (since `k ≤ 2 * (C.card - 2 * σ)`).
  have hER_le_2t : ER.card ≤ 2 * (goodEdges ι).card := by
    have h1 : ER.card * k ≤ ER.card * (2 * (C.card - 2 * σ)) := Nat.mul_le_mul_left ER.card hcap1
    have h2 : ER.card * k ≤ (2 * (goodEdges ι).card) * k := by linarith
    exact Nat.le_of_mul_le_mul_right h2 hk_pos
  -- Build the first triangle family `T1`: for each `e ∈ goodEdges ι`, pair with its unique `u : C`.
  have hn_pos : 0 < n := by
    have := card_le_univ C
    simp at this
    omega
  let uOf : Sym2 (Fin n) → Fin n := fun e ↦
    if he : ∃ u : C, ι u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x then (Classical.choose he).1 else ⟨0, hn_pos⟩
  have huOf_spec : ∀ e ∈ goodEdges ι,
      uOf e ∈ C ∧ (∃ hu : uOf e ∈ C, ι ⟨uOf e, hu⟩ = colR e) ∧ ∀ x ∈ e, G.Adj (uOf e) x := by
    intro e he
    have hex : ∃ u : C, ι u = colR e ∧ ∀ x ∈ e, G.Adj u.1 x := (mem_filter.mp he).2
    dsimp [uOf]
    rw [dif_pos hex]
    have hsp := Classical.choose_spec hex
    exact ⟨(Classical.choose hex).2, ⟨(Classical.choose hex).2, hsp.1⟩, hsp.2⟩
  let T1 : Finset (Finset (Fin n)) := (goodEdges ι).image (fun e ↦ insert (uOf e) e.toFinset)
  -- Define residual graph `G'` obtained by deleting cross edges used by `T1`!
  let usedCross : Finset (Sym2 (Fin n)) :=
    (goodEdges ι).biUnion (fun e ↦ e.toFinset.image (fun x ↦ s(uOf e, x)))
  let G' : SimpleGraph (Fin n) :=
    { Adj := fun a b ↦ G.Adj a b ∧ s(a, b) ∉ usedCross
      symm := ⟨fun a b h ↦ ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun a h ↦ G.loopless.irrefl a h.1⟩ }
  have hG'_tau : ∀ u ∈ C, (R.filter (fun r ↦ ¬ G'.Adj u r)).card ≤ τ + 2 * (ER.card / k + 1) := by
    intro u huC
    have hsub : R.filter (fun r ↦ ¬ G'.Adj u r) ⊆
        R.filter (fun r ↦ ¬ G.Adj u r) ∪
        ((ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩)).biUnion Sym2.toFinset) := by
      intro r hr
      rw [mem_filter] at hr
      by_cases hadj : G.Adj u r
      · refine mem_union_right _ ?_
        have hused : s(u, r) ∈ usedCross := by
          by_contra hnot
          exact hr.2 ⟨hadj, hnot⟩
        rcases mem_biUnion.mp hused with ⟨e, he_good, hmem_e⟩
        rcases mem_image.mp hmem_e with ⟨x, hxe, hEq⟩
        have heR : e ∈ ER := (mem_filter.mp he_good).1
        have hxR : x ∈ R := (mem_filter.mp heR).2 x (Sym2.mem_toFinset.mp hxe)
        have hsp := huOf_spec e he_good
        rcases Sym2.eq_iff.mp hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hu_eq : uOf e = u := h1
          have hr_eq : x = r := h2
          rcases hsp.2.1 with ⟨hu', hι'⟩
          have hcol_eq : colR e = ι ⟨u, huC⟩ := by
            rw [← hι']; congr 1; exact Subtype.ext hu_eq
          exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨heR, hcol_eq⟩, hr_eq ▸ hxe⟩
        · exact absurd huC (Finset.disjoint_right.mp hdisj (h2 ▸ hxR))
      · exact mem_union_left _ (mem_filter.mpr ⟨hr.1, hadj⟩)
    have hbi_le : ((ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩)).biUnion Sym2.toFinset).card ≤
        2 * (ER.card / k + 1) := by
      calc
        ((ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩)).biUnion Sym2.toFinset).card
            ≤ ∑ e ∈ ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩), e.toFinset.card := card_biUnion_le
        _ ≤ ∑ _e ∈ ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩), 2 := by
              refine sum_le_sum ?_
              intro e _
              induction e using Sym2.ind with
              | h a b => rw [Sym2.toFinset_mk_eq]; exact card_le_two
        _ = (ER.filter (fun e ↦ colR e = ι ⟨u, huC⟩)).card * 2 := by simp
        _ ≤ (ER.card / k + 1) * 2 := Nat.mul_le_mul_right 2 (hcolR_bal (ι ⟨u, huC⟩))
        _ = 2 * (ER.card / k + 1) := by ring
    exact le_trans (card_le_card hsub) (le_trans (card_union_le _ _) (Nat.add_le_add (hτ u huC) hbi_le))
  -- Apply `H3` to `G'`!
  obtain ⟨φ, hφ_mem, hφ_inj⟩ := h3 n G' C R (τ + 2 * (ER.card / k + 1)) hdisj hc3 hG'_tau hcap2
  have hG'_C : ∀ u ∈ C, ∀ v ∈ C, G'.Adj u v ↔ G.Adj u v := by
    intro u hu v hv
    simp only [G', and_iff_left_iff_imp]
    intro _ hused
    rcases mem_biUnion.mp hused with ⟨e, he_good, hmem_e⟩
    rcases mem_image.mp hmem_e with ⟨x, hxe, hEq⟩
    have hxR : x ∈ R := (mem_filter.mp (mem_filter.mp he_good).1).2 x (Sym2.mem_toFinset.mp hxe)
    rcases Sym2.eq_iff.mp hEq with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Finset.disjoint_left.mp hdisj hv (h2 ▸ hxR)
    · exact Finset.disjoint_left.mp hdisj hu (h2 ▸ hxR)
  let T2 : Finset (Finset (Fin n)) := EC.image (fun e ↦ insert (φ e) e.toFinset)
  -- Remaining edges not covered by `T1 ∪ T2`:
  let coveredByTri : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ Q ∈ T1 ∪ T2, ∀ x ∈ e, x ∈ Q)
  let T3 : Finset (Finset (Fin n)) := (G.edgeFinset \ coveredByTri).image Sym2.toFinset
  let P : Finset (Finset (Fin n)) := T1 ∪ T2 ∪ T3
  -- Helper: triangles in `T1` and `T2` are edge-disjoint 3-cliques of `G`!
  have hT1_cl : ∀ Q ∈ T1, Q.card = 3 ∧ G.IsClique (Q : Set (Fin n)) ∧
      ∃ e ∈ goodEdges ι, Q = insert (uOf e) e.toFinset := by
    intro Q hQ
    rcases mem_image.mp hQ with ⟨e, he, rfl⟩
    have hsp := huOf_spec e he
    have heR := mem_filter.mp (mem_filter.mp he).1
    have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp heR.1
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := hadj
      have haR : a ∈ R := heR.2 a (by simp)
      have hbR : b ∈ R := heR.2 b (by simp)
      have hua : uOf s(a, b) ≠ a := fun h ↦ Finset.disjoint_left.mp hdisj hsp.1 (by rw [h]; exact haR)
      have hub : uOf s(a, b) ≠ b := fun h ↦ Finset.disjoint_left.mp hdisj hsp.1 (by rw [h]; exact hbR)
      refine ⟨?_, ?_, s(a, b), he, rfl⟩
      · rw [Sym2.toFinset_mk_eq, card_insert_of_notMem (by simp [hua, hub]), card_pair hab.ne]
      · intro x hx y hy hxy
        rw [Sym2.toFinset_mk_eq, mem_coe, mem_insert, mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact hsp.2.2 y (by simp)
        · exact hsp.2.2 y (by simp)
        · exact (hsp.2.2 x (by simp)).symm
        · exact absurd rfl hxy
        · exact hab
        · exact (hsp.2.2 x (by simp)).symm
        · exact hab.symm
        · exact absurd rfl hxy
  have hT2_cl : ∀ Q ∈ T2, Q.card = 3 ∧ G.IsClique (Q : Set (Fin n)) ∧
      ∃ e ∈ EC, Q = insert (φ e) e.toFinset := by
    intro Q hQ
    rcases mem_image.mp hQ with ⟨e, he, rfl⟩
    have heC := mem_filter.mp he
    have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp heC.1
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := hadj
      have huC : u ∈ C := heC.2 u (by simp)
      have hvC : v ∈ C := heC.2 v (by simp)
      have huv' : G'.Adj u v := (hG'_C u huC v hvC).mpr huv
      have hφ := hφ_mem u huC v hvC huv'
      have hru : φ s(u, v) ≠ u := fun h ↦ Finset.disjoint_left.mp hdisj huC (h ▸ hφ.1)
      have hrv : φ s(u, v) ≠ v := fun h ↦ Finset.disjoint_left.mp hdisj hvC (h ▸ hφ.1)
      refine ⟨?_, ?_, s(u, v), he, rfl⟩
      · rw [Sym2.toFinset_mk_eq, card_insert_of_notMem (by simp [hru, hrv]), card_pair huv.ne]
      · intro x hx y hy hxy
        rw [Sym2.toFinset_mk_eq, mem_coe, mem_insert, mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact hφ.2.1.1.symm
        · exact hφ.2.2.1.symm
        · exact hφ.2.1.1
        · exact absurd rfl hxy
        · exact huv
        · exact hφ.2.2.1
        · exact huv.symm
        · exact absurd rfl hxy
  -- Pairwise edge-disjointness of all triangles in `T1 ∪ T2`:
  have hT12_uniq : ∀ Q₁ ∈ T1 ∪ T2, ∀ Q₂ ∈ T1 ∪ T2, ∀ a b : Fin n, a ≠ b →
      a ∈ Q₁ → b ∈ Q₁ → a ∈ Q₂ → b ∈ Q₂ → Q₁ = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂ a b hab ha₁ hb₁ ha₂ hb₂
    have hdisj_T1_T1 : ∀ e₁ ∈ goodEdges ι, ∀ e₂ ∈ goodEdges ι,
        a ∈ insert (uOf e₁) e₁.toFinset → b ∈ insert (uOf e₁) e₁.toFinset →
        a ∈ insert (uOf e₂) e₂.toFinset → b ∈ insert (uOf e₂) e₂.toFinset → e₁ = e₂ := by
      intro e₁ he₁ e₂ he₂ ha1 hb1 ha2 hb2
      have hsp1 := huOf_spec e₁ he₁
      have hsp2 := huOf_spec e₂ he₂
      have he1R := mem_filter.mp (mem_filter.mp he₁).1
      have he2R := mem_filter.mp (mem_filter.mp he₂).1
      by_cases haC : a ∈ C
      · have ha_eq1 : a = uOf e₁ := by
          rcases mem_insert.mp ha1 with h | h
          · exact h
          · exact absurd haC (Finset.disjoint_right.mp hdisj (he1R.2 a (Sym2.mem_toFinset.mp h)))
        have ha_eq2 : a = uOf e₂ := by
          rcases mem_insert.mp ha2 with h | h
          · exact h
          · exact absurd haC (Finset.disjoint_right.mp hdisj (he2R.2 a (Sym2.mem_toFinset.mp h)))
        have hb_e1 : b ∈ e₁ := by
          rcases mem_insert.mp hb1 with h | h
          · exact absurd (ha_eq1.trans h.symm) hab
          · exact Sym2.mem_toFinset.mp h
        have hb_e2 : b ∈ e₂ := by
          rcases mem_insert.mp hb2 with h | h
          · exact absurd (ha_eq2.trans h.symm) hab
          · exact Sym2.mem_toFinset.mp h
        have hcol_eq : colR e₁ = colR e₂ := by
          rcases hsp1.2.1 with ⟨hu1, h1⟩
          rcases hsp2.2.1 with ⟨hu2, h2⟩
          rw [← h1, ← h2]
          congr 1; exact Subtype.ext (ha_eq1.symm.trans ha_eq2)
        by_contra hne
        exact hcolR_prop e₁ (mem_filter.mp he₁).1 e₂ (mem_filter.mp he₂).1 hne hcol_eq b hb_e1 hb_e2
      · by_cases hbC : b ∈ C
        · have hb_eq1 : b = uOf e₁ := by
            rcases mem_insert.mp hb1 with h | h
            · exact h
            · exact absurd hbC (Finset.disjoint_right.mp hdisj (he1R.2 b (Sym2.mem_toFinset.mp h)))
          have hb_eq2 : b = uOf e₂ := by
            rcases mem_insert.mp hb2 with h | h
            · exact h
            · exact absurd hbC (Finset.disjoint_right.mp hdisj (he2R.2 b (Sym2.mem_toFinset.mp h)))
          have ha_e1 : a ∈ e₁ := by
            rcases mem_insert.mp ha1 with h | h
            · exact absurd (h.trans hb_eq1.symm) hab
            · exact Sym2.mem_toFinset.mp h
          have ha_e2 : a ∈ e₂ := by
            rcases mem_insert.mp ha2 with h | h
            · exact absurd (h.trans hb_eq2.symm) hab
            · exact Sym2.mem_toFinset.mp h
          have hcol_eq : colR e₁ = colR e₂ := by
            rcases hsp1.2.1 with ⟨hu1, h1⟩
            rcases hsp2.2.1 with ⟨hu2, h2⟩
            rw [← h1, ← h2]
            congr 1; exact Subtype.ext (hb_eq1.symm.trans hb_eq2)
          by_contra hne
          exact hcolR_prop e₁ (mem_filter.mp he₁).1 e₂ (mem_filter.mp he₂).1 hne hcol_eq a ha_e1 ha_e2
        · have ha_e1 : a ∈ e₁ := by
            rcases mem_insert.mp ha1 with h | h
            · exact absurd (h ▸ hsp1.1) haC
            · exact Sym2.mem_toFinset.mp h
          have hb_e1 : b ∈ e₁ := by
            rcases mem_insert.mp hb1 with h | h
            · exact absurd (h ▸ hsp1.1) hbC
            · exact Sym2.mem_toFinset.mp h
          have ha_e2 : a ∈ e₂ := by
            rcases mem_insert.mp ha2 with h | h
            · exact absurd (h ▸ hsp2.1) haC
            · exact Sym2.mem_toFinset.mp h
          have hb_e2 : b ∈ e₂ := by
            rcases mem_insert.mp hb2 with h | h
            · exact absurd (h ▸ hsp2.1) hbC
            · exact Sym2.mem_toFinset.mp h
          have h1 : e₁ = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha_e1, hb_e1⟩
          have h2 : e₂ = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha_e2, hb_e2⟩
          exact h1.trans h2.symm
    have hdisj_T2_T2 : ∀ e₁ ∈ EC, ∀ e₂ ∈ EC,
        a ∈ insert (φ e₁) e₁.toFinset → b ∈ insert (φ e₁) e₁.toFinset →
        a ∈ insert (φ e₂) e₂.toFinset → b ∈ insert (φ e₂) e₂.toFinset → e₁ = e₂ := by
      intro e₁ he₁ e₂ he₂ ha1 hb1 ha2 hb2
      have h1 := mem_filter.mp he₁
      have h2 := mem_filter.mp he₂
      induction e₁ using Sym2.ind with
      | h u₁ v₁ =>
        induction e₂ using Sym2.ind with
        | h u₂ v₂ =>
          have hu₁C : u₁ ∈ C := h1.2 u₁ (by simp)
          have hv₁C : v₁ ∈ C := h1.2 v₁ (by simp)
          have hu₂C : u₂ ∈ C := h2.2 u₂ (by simp)
          have hv₂C : v₂ ∈ C := h2.2 v₂ (by simp)
          have huv₁ : G.Adj u₁ v₁ := mem_edgeFinset.mp h1.1
          have huv₂ : G.Adj u₂ v₂ := mem_edgeFinset.mp h2.1
          have hφ1 := hφ_mem u₁ hu₁C v₁ hv₁C ((hG'_C u₁ hu₁C v₁ hv₁C).mpr huv₁)
          have hφ2 := hφ_mem u₂ hu₂C v₂ hv₂C ((hG'_C u₂ hu₂C v₂ hv₂C).mpr huv₂)
          by_cases haR : a ∈ R
          · have ha_eq1 : a = φ s(u₁, v₁) := by
              rcases mem_insert.mp ha1 with h | h
              · exact h
              · exact absurd haR (Finset.disjoint_left.mp hdisj (h1.2 a (Sym2.mem_toFinset.mp h)))
            have ha_eq2 : a = φ s(u₂, v₂) := by
              rcases mem_insert.mp ha2 with h | h
              · exact h
              · exact absurd haR (Finset.disjoint_left.mp hdisj (h2.2 a (Sym2.mem_toFinset.mp h)))
            have hb_e1 : b ∈ s(u₁, v₁) := by
              rcases mem_insert.mp hb1 with h | h
              · exact absurd (ha_eq1.trans h.symm) hab
              · exact Sym2.mem_toFinset.mp h
            have hb_e2 : b ∈ s(u₂, v₂) := by
              rcases mem_insert.mp hb2 with h | h
              · exact absurd (ha_eq2.trans h.symm) hab
              · exact Sym2.mem_toFinset.mp h
            rcases Sym2.mem_iff.mp hb_e1 with rfl | rfl <;> rcases Sym2.mem_iff.mp hb_e2 with hEq | hEq
            · subst hEq
              by_cases hvv : v₁ = v₂
              · subst hvv; rfl
              · exact absurd (ha_eq1.symm.trans ha_eq2)
                  (hφ_inj b hu₁C v₁ hv₁C v₂ hv₂C hvv ((hG'_C _ hu₁C _ hv₁C).mpr huv₁) ((hG'_C _ hu₁C _ hv₂C).mpr huv₂))
            · subst hEq
              by_cases hvu : v₁ = u₂
              · subst hvu; exact Sym2.eq_swap
              · have ha2' : a = φ s(b, u₂) := by rwa [Sym2.eq_swap] at ha_eq2
                exact absurd (ha_eq1.symm.trans ha2')
                  (hφ_inj b hu₁C v₁ hv₁C u₂ hu₂C hvu ((hG'_C _ hu₁C _ hv₁C).mpr huv₁) ((hG'_C _ hu₁C _ hu₂C).mpr huv₂.symm))
            · subst hEq
              by_cases huv' : u₁ = v₂
              · subst huv'; exact Sym2.eq_swap
              · have ha1' : a = φ s(b, u₁) := by rwa [Sym2.eq_swap] at ha_eq1
                exact absurd (ha1'.symm.trans ha_eq2)
                  (hφ_inj b hv₁C u₁ hu₁C v₂ hv₂C huv' ((hG'_C _ hv₁C _ hu₁C).mpr huv₁.symm) ((hG'_C _ hv₁C _ hv₂C).mpr huv₂))
            · subst hEq
              by_cases huu : u₁ = u₂
              · subst huu; rfl
              · have ha1' : a = φ s(b, u₁) := by rwa [Sym2.eq_swap] at ha_eq1
                have ha2' : a = φ s(b, u₂) := by rwa [Sym2.eq_swap] at ha_eq2
                exact absurd (ha1'.symm.trans ha2')
                  (hφ_inj b hv₁C u₁ hu₁C u₂ hu₂C huu ((hG'_C _ hv₁C _ hu₁C).mpr huv₁.symm) ((hG'_C _ hv₁C _ hu₂C).mpr huv₂.symm))
          · by_cases hbR : b ∈ R
            · have hb_eq1 : b = φ s(u₁, v₁) := by
                rcases mem_insert.mp hb1 with h | h
                · exact h
                · exact absurd hbR (Finset.disjoint_left.mp hdisj (h1.2 b (Sym2.mem_toFinset.mp h)))
              have hb_eq2 : b = φ s(u₂, v₂) := by
                rcases mem_insert.mp hb2 with h | h
                · exact h
                · exact absurd hbR (Finset.disjoint_left.mp hdisj (h2.2 b (Sym2.mem_toFinset.mp h)))
              have ha_e1 : a ∈ s(u₁, v₁) := by
                rcases mem_insert.mp ha1 with h | h
                · exact absurd (h.trans hb_eq1.symm) hab
                · exact Sym2.mem_toFinset.mp h
              have ha_e2 : a ∈ s(u₂, v₂) := by
                rcases mem_insert.mp ha2 with h | h
                · exact absurd (h.trans hb_eq2.symm) hab
                · exact Sym2.mem_toFinset.mp h
              rcases Sym2.mem_iff.mp ha_e1 with rfl | rfl <;> rcases Sym2.mem_iff.mp ha_e2 with hEq | hEq
              · subst hEq
                by_cases hvv : v₁ = v₂
                · subst hvv; rfl
                · exact absurd (hb_eq1.symm.trans hb_eq2)
                    (hφ_inj a hu₁C v₁ hv₁C v₂ hv₂C hvv ((hG'_C _ hu₁C _ hv₁C).mpr huv₁) ((hG'_C _ hu₁C _ hv₂C).mpr huv₂))
              · subst hEq
                by_cases hvu : v₁ = u₂
                · subst hvu; exact Sym2.eq_swap
                · have hb2' : b = φ s(a, u₂) := by rwa [Sym2.eq_swap] at hb_eq2
                  exact absurd (hb_eq1.symm.trans hb2')
                    (hφ_inj a hu₁C v₁ hv₁C u₂ hu₂C hvu ((hG'_C _ hu₁C _ hv₁C).mpr huv₁) ((hG'_C _ hu₁C _ hu₂C).mpr huv₂.symm))
              · subst hEq
                by_cases huv' : u₁ = v₂
                · subst huv'; exact Sym2.eq_swap
                · have hb1' : b = φ s(a, u₁) := by rwa [Sym2.eq_swap] at hb_eq1
                  exact absurd (hb1'.symm.trans hb_eq2)
                    (hφ_inj a hv₁C u₁ hu₁C v₂ hv₂C huv' ((hG'_C _ hv₁C _ hu₁C).mpr huv₁.symm) ((hG'_C _ hv₁C _ hv₂C).mpr huv₂))
              · subst hEq
                by_cases huu : u₁ = u₂
                · subst huu; rfl
                · have hb1' : b = φ s(a, u₁) := by rwa [Sym2.eq_swap] at hb_eq1
                  have hb2' : b = φ s(a, u₂) := by rwa [Sym2.eq_swap] at hb_eq2
                  exact absurd (hb1'.symm.trans hb2')
                    (hφ_inj a hv₁C u₁ hu₁C u₂ hu₂C huu ((hG'_C _ hv₁C _ hu₁C).mpr huv₁.symm) ((hG'_C _ hv₁C _ hu₂C).mpr huv₂.symm))
            · have ha_e1 : a ∈ s(u₁, v₁) := by
                rcases mem_insert.mp ha1 with h | h
                · exact absurd (h ▸ hφ1.1) haR
                · exact Sym2.mem_toFinset.mp h
              have hb_e1 : b ∈ s(u₁, v₁) := by
                rcases mem_insert.mp hb1 with h | h
                · exact absurd (h ▸ hφ1.1) hbR
                · exact Sym2.mem_toFinset.mp h
              have ha_e2 : a ∈ s(u₂, v₂) := by
                rcases mem_insert.mp ha2 with h | h
                · exact absurd (h ▸ hφ2.1) haR
                · exact Sym2.mem_toFinset.mp h
              have hb_e2 : b ∈ s(u₂, v₂) := by
                rcases mem_insert.mp hb2 with h | h
                · exact absurd (h ▸ hφ2.1) hbR
                · exact Sym2.mem_toFinset.mp h
              have he1 : s(u₁, v₁) = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha_e1, hb_e1⟩
              have he2 : s(u₂, v₂) = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha_e2, hb_e2⟩
              exact he1.trans he2.symm
    have hdisj_T1_T2 : ∀ e₁ ∈ goodEdges ι, ∀ e₂ ∈ EC,
        a ∈ insert (uOf e₁) e₁.toFinset → b ∈ insert (uOf e₁) e₁.toFinset →
        a ∈ insert (φ e₂) e₂.toFinset → b ∈ insert (φ e₂) e₂.toFinset → False := by
      intro e₁ he₁ e₂ he₂ ha1 hb1 ha2 hb2
      have hsp1 := huOf_spec e₁ he₁
      have he1R := mem_filter.mp (mem_filter.mp he₁).1
      have h2 := mem_filter.mp he₂
      induction e₂ using Sym2.ind with
      | h u₂ v₂ =>
        have hu₂C : u₂ ∈ C := h2.2 u₂ (by simp)
        have hv₂C : v₂ ∈ C := h2.2 v₂ (by simp)
        have huv₂ : G.Adj u₂ v₂ := mem_edgeFinset.mp h2.1
        have hφ2 := hφ_mem u₂ hu₂C v₂ hv₂C ((hG'_C u₂ hu₂C v₂ hv₂C).mpr huv₂)
        -- Every pair in `T1` has at least one vertex in `R`, and every pair in `T2` has at least one vertex in `C`.
        -- So one of `a, b` is in `C` (`= uOf e₁`, in `e₂`) and the other is in `R` (`∈ e₁`, `= φ e₂`).
        -- Then `s(a, b)` is in `usedCross` (from `T1`), contradicting `G'.Adj` from `hφ2`!
        by_cases haC : a ∈ C
        · have ha_eq1 : a = uOf e₁ := by
            rcases mem_insert.mp ha1 with h | h
            · exact h
            · exact absurd haC (Finset.disjoint_right.mp hdisj (he1R.2 a (Sym2.mem_toFinset.mp h)))
          have hb_e1 : b ∈ e₁.toFinset := by
            rcases mem_insert.mp hb1 with h | h
            · exact absurd (ha_eq1.trans h.symm) hab
            · exact h
          have hbR : b ∈ R := he1R.2 b (Sym2.mem_toFinset.mp hb_e1)
          have hb_eq2 : b = φ s(u₂, v₂) := by
            rcases mem_insert.mp hb2 with h | h
            · exact h
            · exact absurd hbR (Finset.disjoint_left.mp hdisj (h2.2 b (Sym2.mem_toFinset.mp h)))
          have ha_e2 : a ∈ s(u₂, v₂) := by
            rcases mem_insert.mp ha2 with h | h
            · exact absurd (h.trans hb_eq2.symm) hab
            · exact Sym2.mem_toFinset.mp h
          have hused : s(a, b) ∈ usedCross :=
            mem_biUnion.mpr ⟨e₁, he₁, mem_image.mpr ⟨b, hb_e1, by rw [ha_eq1]⟩⟩
          rcases Sym2.mem_iff.mp ha_e2 with rfl | rfl
          · exact hφ2.2.1.2 (hb_eq2 ▸ hused)
          · exact hφ2.2.2.2 (hb_eq2 ▸ hused)
        · have ha_e1 : a ∈ e₁.toFinset := by
            rcases mem_insert.mp ha1 with h | h
            · exact absurd (h ▸ hsp1.1) haC
            · exact h
          have haR : a ∈ R := he1R.2 a (Sym2.mem_toFinset.mp ha_e1)
          have ha_eq2 : a = φ s(u₂, v₂) := by
            rcases mem_insert.mp ha2 with h | h
            · exact h
            · exact absurd haR (Finset.disjoint_left.mp hdisj (h2.2 a (Sym2.mem_toFinset.mp h)))
          have hb_e2 : b ∈ s(u₂, v₂) := by
            rcases mem_insert.mp hb2 with h | h
            · exact absurd (ha_eq2.trans h.symm) hab
            · exact Sym2.mem_toFinset.mp h
          have hbC : b ∈ C := h2.2 b hb_e2
          have hb_eq1 : b = uOf e₁ := by
            rcases mem_insert.mp hb1 with h | h
            · exact h
            · exact absurd hbC (Finset.disjoint_right.mp hdisj (he1R.2 b (Sym2.mem_toFinset.mp h)))
          have hused : s(b, a) ∈ usedCross :=
            mem_biUnion.mpr ⟨e₁, he₁, mem_image.mpr ⟨a, ha_e1, by rw [hb_eq1]⟩⟩
          rcases Sym2.mem_iff.mp hb_e2 with rfl | rfl
          · exact hφ2.2.1.2 (ha_eq2 ▸ hused)
          · exact hφ2.2.2.2 (ha_eq2 ▸ hused)
    rcases mem_union.mp hQ₁ with h1 | h1 <;> rcases mem_union.mp hQ₂ with h2 | h2
    · obtain ⟨_, _, e₁, he₁, rfl⟩ := hT1_cl Q₁ h1
      obtain ⟨_, _, e₂, he₂, rfl⟩ := hT1_cl Q₂ h2
      rw [hdisj_T1_T1 e₁ he₁ e₂ he₂ ha₁ hb₁ ha₂ hb₂]
    · obtain ⟨_, _, e₁, he₁, rfl⟩ := hT1_cl Q₁ h1
      obtain ⟨_, _, e₂, he₂, rfl⟩ := hT2_cl Q₂ h2
      exact absurd (hdisj_T1_T2 e₁ he₁ e₂ he₂ ha₁ hb₁ ha₂ hb₂) False.elim
    · obtain ⟨_, _, e₁, he₁, rfl⟩ := hT2_cl Q₁ h1
      obtain ⟨_, _, e₂, he₂, rfl⟩ := hT1_cl Q₂ h2
      exact absurd (hdisj_T1_T2 e₂ he₂ e₁ he₁ ha₂ hb₂ ha₁ hb₁) False.elim
    · obtain ⟨_, _, e₁, he₁, rfl⟩ := hT2_cl Q₁ h1
      obtain ⟨_, _, e₂, he₂, rfl⟩ := hT2_cl Q₂ h2
      rw [hdisj_T2_T2 e₁ he₁ e₂ he₂ ha₁ hb₁ ha₂ hb₂]
  -- Verify `G.IsCliqueEdgePartition P`!
  have hP_part : G.IsCliqueEdgePartition P := by
    constructor
    · intro Q hQ
      rcases mem_union.mp hQ with h12 | h3'
      · rcases mem_union.mp h12 with h1 | h2
        · obtain ⟨hc, hcl, _⟩ := hT1_cl Q h1
          exact ⟨by omega, hcl⟩
        · obtain ⟨hc, hcl, _⟩ := hT2_cl Q h2
          exact ⟨by omega, hcl⟩
      · rcases mem_image.mp h3' with ⟨e, he, rfl⟩
        have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp (mem_sdiff.mp he).1
        induction e using Sym2.ind with
        | h a b =>
          rw [Sym2.toFinset_mk_eq, card_pair hadj.ne, coe_pair]
          exact ⟨le_rfl, isClique_pair.mpr (fun _ ↦ hadj)⟩
    · intro a b hab
      by_cases hcov : s(a, b) ∈ coveredByTri
      · rcases (mem_filter.mp hcov).2 with ⟨Q, hQ, hQab⟩
        refine ⟨Q, ⟨mem_union_left _ hQ, hQab a (by simp), hQab b (by simp)⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h12 | h3'
        · exact hT12_uniq Q' h12 Q hQ a b hab.ne haQ' hbQ' (hQab a (by simp)) (hQab b (by simp))
        · rcases mem_image.mp h3' with ⟨e, he, rfl⟩
          have hae : a ∈ e := Sym2.mem_toFinset.mp haQ'
          have hbe : b ∈ e := Sym2.mem_toFinset.mp hbQ'
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp ⟨hae, hbe⟩
          exact absurd (heq ▸ hcov) (mem_sdiff.mp he).2
      · have hmem3 : s(a, b).toFinset ∈ T3 :=
          mem_image.mpr ⟨s(a, b), mem_sdiff.mpr ⟨mem_edgeFinset.mpr hab, hcov⟩, rfl⟩
        refine ⟨s(a, b).toFinset, ⟨mem_union_right _ hmem3, by simp, by simp⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h12 | h3'
        · exfalso
          apply hcov
          rw [mem_filter]
          exact ⟨mem_edgeFinset.mpr hab, Q', h12, fun x hx ↦ by
            rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
        · rcases mem_image.mp h3' with ⟨e, _, rfl⟩
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp
            ⟨Sym2.mem_toFinset.mp haQ', Sym2.mem_toFinset.mp hbQ'⟩
          rw [heq]
  -- Count `P.card`:
  have hT1_card : T1.card = (goodEdges ι).card := by
    rw [card_image_of_injOn]
    intro e₁ he₁ e₂ he₂ hEq
    dsimp only at hEq
    have hsp1 := huOf_spec e₁ he₁
    have he1R := mem_filter.mp (mem_filter.mp he₁).1
    have he2R := mem_filter.mp (mem_filter.mp he₂).1
    have hadj1 : e₁ ∈ G.edgeSet := mem_edgeFinset.mp he1R.1
    induction e₁ using Sym2.ind with
    | h a b =>
      have ha1 : a ∈ insert (uOf s(a, b)) s(a, b).toFinset := by simp
      have hb1 : b ∈ insert (uOf s(a, b)) s(a, b).toFinset := by simp
      have ha2 : a ∈ insert (uOf e₂) e₂.toFinset := hEq ▸ ha1
      have hb2 : b ∈ insert (uOf e₂) e₂.toFinset := hEq ▸ hb1
      have hsp2 := huOf_spec e₂ he₂
      have haR : a ∈ R := he1R.2 a (by simp)
      have hbR : b ∈ R := he1R.2 b (by simp)
      have ha_e2 : a ∈ e₂ := by
        rcases mem_insert.mp ha2 with h | h
        · exact absurd (h ▸ hsp2.1) (Finset.disjoint_right.mp hdisj haR)
        · exact Sym2.mem_toFinset.mp h
      have hb_e2 : b ∈ e₂ := by
        rcases mem_insert.mp hb2 with h | h
        · exact absurd (h ▸ hsp2.1) (Finset.disjoint_right.mp hdisj hbR)
        · exact Sym2.mem_toFinset.mp h
      exact ((Sym2.mem_and_mem_iff hadj1.ne).mp ⟨ha_e2, hb_e2⟩).symm
  have hT2_card : T2.card = EC.card := by
    rw [card_image_of_injOn]
    intro e₁ he₁ e₂ he₂ hEq
    dsimp only at hEq
    have h1 := mem_filter.mp he₁
    have h2 := mem_filter.mp he₂
    have hadj1 : e₁ ∈ G.edgeSet := mem_edgeFinset.mp h1.1
    induction e₁ using Sym2.ind with
    | h u₁ v₁ =>
      have hu₁C : u₁ ∈ C := h1.2 u₁ (by simp)
      have hv₁C : v₁ ∈ C := h1.2 v₁ (by simp)
      have hu1 : u₁ ∈ insert (φ s(u₁, v₁)) s(u₁, v₁).toFinset := by simp
      have hv1 : v₁ ∈ insert (φ s(u₁, v₁)) s(u₁, v₁).toFinset := by simp
      have hu2 : u₁ ∈ insert (φ e₂) e₂.toFinset := hEq ▸ hu1
      have hv2 : v₁ ∈ insert (φ e₂) e₂.toFinset := hEq ▸ hv1
      induction e₂ using Sym2.ind with
      | h u₂ v₂ =>
        have hφ2 := hφ_mem u₂ (h2.2 u₂ (by simp)) v₂ (h2.2 v₂ (by simp))
          ((hG'_C _ (h2.2 u₂ (by simp)) _ (h2.2 v₂ (by simp))).mpr (mem_edgeFinset.mp h2.1))
        have hu_e2 : u₁ ∈ s(u₂, v₂) := by
          rcases mem_insert.mp hu2 with h | h
          · exact absurd (h ▸ hφ2.1) (Finset.disjoint_left.mp hdisj hu₁C)
          · exact Sym2.mem_toFinset.mp h
        have hv_e2 : v₁ ∈ s(u₂, v₂) := by
          rcases mem_insert.mp hv2 with h | h
          · exact absurd (h ▸ hφ2.1) (Finset.disjoint_left.mp hdisj hv₁C)
          · exact Sym2.mem_toFinset.mp h
        exact ((Sym2.mem_and_mem_iff hadj1.ne).mp ⟨hu_e2, hv_e2⟩).symm
  have hT12_disj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro Q h1 h2
    obtain ⟨_, _, e₁, he₁, rfl⟩ := hT1_cl Q h1
    obtain ⟨_, _, e₂, he₂, hEq⟩ := hT2_cl _ h2
    have he1R := mem_filter.mp (mem_filter.mp he₁).1
    have hadj1 : e₁ ∈ G.edgeSet := mem_edgeFinset.mp he1R.1
    induction e₁ using Sym2.ind with
    | h a b =>
      have ha1 : a ∈ insert (uOf s(a, b)) s(a, b).toFinset := by simp
      have hb1 : b ∈ insert (uOf s(a, b)) s(a, b).toFinset := by simp
      have ha2 : a ∈ insert (φ e₂) e₂.toFinset := hEq ▸ ha1
      have hb2 : b ∈ insert (φ e₂) e₂.toFinset := hEq ▸ hb1
      have haR : a ∈ R := he1R.2 a (by simp)
      have hbR : b ∈ R := he1R.2 b (by simp)
      have h2' := mem_filter.mp he₂
      have ha_eq : a = φ e₂ := by
        rcases mem_insert.mp ha2 with h | h
        · exact h
        · exact absurd haR (Finset.disjoint_left.mp hdisj (h2'.2 a (Sym2.mem_toFinset.mp h)))
      have hb_eq : b = φ e₂ := by
        rcases mem_insert.mp hb2 with h | h
        · exact h
        · exact absurd hbR (Finset.disjoint_left.mp hdisj (h2'.2 b (Sym2.mem_toFinset.mp h)))
      exact hadj1.ne (ha_eq.trans hb_eq.symm)
  have hcov_card : coveredByTri.card = 3 * (T1.card + T2.card) := by
    have hbi : coveredByTri =
        (T1 ∪ T2).biUnion (fun Q ↦ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)) := by
      ext e
      simp only [coveredByTri, mem_biUnion, mem_filter]
      constructor
      · rintro ⟨he, Q, hQ, hsub⟩; exact ⟨Q, hQ, he, hsub⟩
      · rintro ⟨Q, hQ, he, hsub⟩; exact ⟨he, Q, hQ, hsub⟩
    rw [hbi, card_biUnion]
    · have h3_each : ∀ Q ∈ T1 ∪ T2, (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)).card = 3 := by
        intro Q hQ
        have hQcl : Q.card = 3 ∧ G.IsClique (Q : Set (Fin n)) := by
          rcases mem_union.mp hQ with h | h
          · exact ⟨(hT1_cl Q h).1, (hT1_cl Q h).2.1⟩
          · exact ⟨(hT2_cl Q h).1, (hT2_cl Q h).2.1⟩
        have hbij : (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)).card = (Q.powersetCard 2).card := by
          refine Finset.card_bij (fun e _ ↦ e.toFinset) ?_ ?_ ?_
          · intro e he
            rw [mem_filter, mem_edgeFinset] at he
            rw [mem_powersetCard]
            induction e using Sym2.ind with
            | h a b =>
              rw [Sym2.toFinset_mk_eq, card_pair he.1.ne]
              exact ⟨fun x hx ↦ he.2 x (by simp at hx; rcases hx with rfl | rfl <;> simp), rfl⟩
          · intro e₁ he₁ e₂ he₂ hEq
            rw [mem_filter, mem_edgeFinset] at he₁ he₂
            induction e₁ using Sym2.ind with
            | h a b =>
              have ha : a ∈ e₂ := Sym2.mem_toFinset.mp (hEq ▸ (by simp))
              have hb : b ∈ e₂ := Sym2.mem_toFinset.mp (hEq ▸ (by simp))
              exact ((Sym2.mem_and_mem_iff he₁.1.ne).mp ⟨ha, hb⟩).symm
          · intro s hs
            rw [mem_powersetCard] at hs
            obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
            refine ⟨s(a, b), ?_, by rw [Sym2.toFinset_mk_eq]⟩
            rw [mem_filter, mem_edgeFinset]
            exact ⟨hQcl.2 (hs.1 (by simp)) (hs.1 (by simp)) hab,
              fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> exact hs.1 (by simp)⟩
        rw [hbij, card_powersetCard, hQcl.1]
        decide
      rw [sum_congr rfl h3_each, sum_const, card_union_of_disjoint hT12_disj, smul_eq_mul, mul_comm]
    · intro Q₁ hQ₁ Q₂ hQ₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      rw [mem_filter, mem_edgeFinset] at he₁ he₂
      induction e using Sym2.ind with
      | h a b =>
        exact hne (hT12_uniq Q₁ hQ₁ Q₂ hQ₂ a b he₁.1.ne
          (he₁.2 a (by simp)) (he₁.2 b (by simp)) (he₂.2 a (by simp)) (he₂.2 b (by simp)))
  have hP_card_le : P.card ≤ G.edgeFinset.card - 2 * ((goodEdges ι).card + EC.card) := by
    have h1 : P.card ≤ (T1 ∪ T2).card + T3.card := card_union_le _ _
    have h2 : T3.card ≤ (G.edgeFinset \ coveredByTri).card := card_image_le
    have h3 : (G.edgeFinset \ coveredByTri).card = G.edgeFinset.card - coveredByTri.card :=
      card_sdiff_of_subset (filter_subset _ _)
    have hcov_le : coveredByTri.card ≤ G.edgeFinset.card := card_le_card (filter_subset _ _)
    rw [card_union_of_disjoint hT12_disj] at h1
    rw [hT1_card, hT2_card] at h1 hcov_card
    omega
  -- Split `G.edgeFinset.card = EC.card + ECR.card + ER.card` with `ECR.card ≤ C.card * R.card` and `EC.card = C.card.choose 2`.
  have hG_split : G.edgeFinset.card = EC.card + ECR.card + ER.card := by
    have hpart : G.edgeFinset = EC ∪ ECR ∪ ER := by
      ext e
      simp only [EC, ECR, ER, mem_union, mem_filter]
      constructor
      · intro he
        induction e using Sym2.ind with
        | h a b =>
          have hmem_CR : ∀ x : Fin n, x ∈ C ∨ x ∈ R := fun x ↦ by
            have : x ∈ C ∪ R := by rw [hCR]; exact mem_univ x
            exact mem_union.mp this
          rcases hmem_CR a with ha | ha <;> rcases hmem_CR b with hb | hb
          · left; left; exact ⟨he, fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
          · left; right; exact ⟨he, ⟨a, ha, by simp⟩, ⟨b, hb, by simp⟩⟩
          · left; right; exact ⟨he, ⟨b, hb, by simp⟩, ⟨a, ha, by simp⟩⟩
          · right; exact ⟨he, fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
      · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
    have hd1 : Disjoint EC ECR := by
      rw [Finset.disjoint_left]; intro e h1 h2
      rcases (mem_filter.mp h2).2.2 with ⟨r, hr, hre⟩
      exact Finset.disjoint_left.mp hdisj ((mem_filter.mp h1).2 r hre) hr
    have hd2 : Disjoint (EC ∪ ECR) ER := by
      rw [Finset.disjoint_left]; intro e h1 h2
      rcases mem_union.mp h1 with h | h
      · induction e using Sym2.ind with
        | h a _ => exact Finset.disjoint_left.mp hdisj ((mem_filter.mp h).2 a (by simp)) ((mem_filter.mp h2).2 a (by simp))
      · rcases (mem_filter.mp h).2.1 with ⟨u, hu, hue⟩
        exact Finset.disjoint_left.mp hdisj hu ((mem_filter.mp h2).2 u hue)
    rw [hpart, card_union_of_disjoint hd2, card_union_of_disjoint hd1]
  have hECR_le : ECR.card ≤ C.card * R.card := by
    have hsub : ECR ⊆ (C ×ˢ R).image (fun p ↦ s(p.1, p.2)) := by
      intro e he
      rcases (mem_filter.mp he).2 with ⟨⟨u, huC, hue⟩, ⟨r, hrR, hre⟩⟩
      have hur : u ≠ r := fun h ↦ Finset.disjoint_left.mp hdisj huC (h ▸ hrR)
      exact mem_image.mpr ⟨(u, r), mem_product.mpr ⟨huC, hrR⟩, ((Sym2.mem_and_mem_iff hur).mp ⟨hue, hre⟩).symm⟩
    exact le_trans (card_le_card hsub) (le_trans card_image_le (by rw [card_product]))
  have hEC_eq : EC.card = C.card.choose 2 := by
    have hbij : EC.card = (C.powersetCard 2).card := by
      refine Finset.card_bij (fun e _ ↦ e.toFinset) ?_ ?_ ?_
      · intro e he
        rw [mem_filter, mem_edgeFinset] at he
        rw [mem_powersetCard]
        induction e using Sym2.ind with
        | h a b =>
          rw [Sym2.toFinset_mk_eq, card_pair he.1.ne]
          exact ⟨fun x hx ↦ he.2 x (by simp at hx; rcases hx with rfl | rfl <;> simp), rfl⟩
      · intro e₁ he₁ e₂ he₂ hEq
        rw [mem_filter, mem_edgeFinset] at he₁ he₂
        induction e₁ using Sym2.ind with
        | h a b =>
          have ha : a ∈ e₂ := Sym2.mem_toFinset.mp (hEq ▸ (by simp))
          have hb : b ∈ e₂ := Sym2.mem_toFinset.mp (hEq ▸ (by simp))
          exact ((Sym2.mem_and_mem_iff he₁.1.ne).mp ⟨ha, hb⟩).symm
      · intro s hs
        rw [mem_powersetCard] at hs
        obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
        refine ⟨s(a, b), ?_, by rw [Sym2.toFinset_mk_eq]⟩
        rw [mem_filter, mem_edgeFinset]
        exact ⟨hCcl (hs.1 (by simp)) (hs.1 (by simp)) hab,
          fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> exact hs.1 (by simp)⟩
    rw [hbij, card_powersetCard]
  refine ⟨P, hP_part, ?_⟩
  omega

/- ### Section 5: Chordal normal form (`T = ∅`) and assembly of `main` -/

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos81.erdos_81 := by
  intro h1 h2 h3
  let ε : ℝ := 1 / (10 : ℝ) ^ 16
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 100 := by dsimp [ε]; norm_num
  obtain ⟨L, η₀, n₁, hL4, hη₀, hfrac⟩ := thm_fracstability h1 hε0 hε1
  obtain ⟨n₂, hround⟩ := h2 L (by omega) (η₀ / 2) (by linarith)
  let N₀ : ℕ := max (max n₁ n₂) 1000000
  let Cconst : ℝ := (N₀ : ℝ) + 10
  refine ⟨Cconst, ?_⟩
  -- Prove by strong induction on `n` that every chordal graph on `Fin n` has `cp(G) ≤ n^2 / 6 + Cconst * n`.
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hG
    classical
    by_cases hn_small : n ≤ N₀
    · obtain ⟨P, hP, hPcard⟩ := G.exists_isCliqueEdgePartition_card_eq
      refine ⟨P, hP, ?_⟩
      have h1' : P.card ≤ n.choose 2 := by
        rw [hPcard]
        simpa using G.card_edgeFinset_le_card_choose_two
      have h2' : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
        by_cases hn0 : n = 0
        · simp [hn0]
        · have hnat : 2 * n.choose 2 = n * (n - 1) := by
            rw [Nat.choose_two_right]
            have hev := Nat.even_mul_pred_self n
            rcases hev with ⟨q, hq⟩
            omega
          have hR : (2 : ℝ) * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
            have h' : ((2 * n.choose 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h'
            exact h'
          nlinarith
      have hleR : (P.card : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast h1'
      have hnN : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hn_small
      dsimp [Cconst]
      nlinarith
    · push Not at hn_small
      have hN₀_lt : max (max n₁ n₂) 1000000 < n := hn_small
      have hn_ge_n1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN₀_lt.le
      have hn_ge_n2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN₀_lt.le
      have hn_ge_M : 1000000 ≤ n := le_trans (le_max_right _ _) hN₀_lt.le
      -- Case 1: Some vertex `v` has degree `d(v) < n / 3`: delete `v` and apply IH!
      by_cases hlowdeg : ∃ v : Fin n, ((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card * 3 < n
      · obtain ⟨v, hvdeg⟩ := hlowdeg
        -- Embed `Fin (n - 1)` into `(Finset.univ : Finset (Fin n)).erase v`.
        let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase v
        have hScard : S.card = n - 1 := by simp [S]
        let emb : Fin (n - 1) ↪ Fin n := (S.orderEmbOfFin hScard).toEmbedding
        let G' : SimpleGraph (Fin (n - 1)) := G.comap emb
        have hG'_ch : G'.IsChordal := by
          intro k hk ⟨f⟩
          exact hG k hk ⟨⟨f.toEmbedding.trans emb, f.map_rel_iff⟩⟩
        obtain ⟨P', hP'_part, hP'_card⟩ := ih (n - 1) (by omega) G' hG'_ch
        let P1 : Finset (Finset (Fin n)) := P'.image (fun Q ↦ Q.map emb)
        let P2 : Finset (Finset (Fin n)) :=
          ((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).image (fun w ↦ ({v, w} : Finset (Fin n)))
        let P := P1 ∪ P2
        have hP_part : G.IsCliqueEdgePartition P := by
          constructor
          · intro Q hQ
            rcases mem_union.mp hQ with h1' | h2'
            · rcases mem_image.mp h1' with ⟨Q', hQ', rfl⟩
              have hq := hP'_part.1 Q' hQ'
              refine ⟨by rw [card_map]; exact hq.1, ?_⟩
              intro x hx y hy hxy
              rw [mem_coe, mem_map] at hx hy
              rcases hx with ⟨a, ha, rfl⟩
              rcases hy with ⟨b, hb, rfl⟩
              exact hq.2 ha hb (fun h ↦ hxy (congrArg emb h))
            · rcases mem_image.mp h2' with ⟨w, hw, rfl⟩
              have hvw : G.Adj v w := (mem_filter.mp hw).2
              rw [card_pair hvw.ne, coe_pair]
              exact ⟨le_rfl, isClique_pair.mpr (fun _ ↦ hvw)⟩
          · intro a b hab
            by_cases hav : a = v
            · subst hav
              refine ⟨{a, b}, ⟨mem_union_right _ (mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hab⟩, rfl⟩),
                by simp, by simp⟩, ?_⟩
              rintro Q ⟨hQP, haQ, hbQ⟩
              rcases mem_union.mp hQP with h1' | h2'
              · rcases mem_image.mp h1' with ⟨Q', _, rfl⟩
                rcases mem_map.mp haQ with ⟨i, _, hi⟩
                have hiS : emb i ∈ S := S.orderEmbOfFin_mem hScard i
                exact absurd hi (mem_erase.mp hiS).1
              · rcases mem_image.mp h2' with ⟨w, hw, rfl⟩
                have hbw : b = w := by
                  rcases mem_insert.mp hbQ with h | h
                  · exact absurd h hab.ne.symm
                  · exact mem_singleton.mp h
                rw [hbw]
            · by_cases hbv : b = v
              · subst hbv
                refine ⟨{b, a}, ⟨mem_union_right _ (mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, hab.symm⟩, rfl⟩),
                  by simp, by simp⟩, ?_⟩
                rintro Q ⟨hQP, haQ, hbQ⟩
                rcases mem_union.mp hQP with h1' | h2'
                · rcases mem_image.mp h1' with ⟨Q', _, rfl⟩
                  rcases mem_map.mp hbQ with ⟨i, _, hi⟩
                  have hiS : emb i ∈ S := S.orderEmbOfFin_mem hScard i
                  exact absurd hi (mem_erase.mp hiS).1
                · rcases mem_image.mp h2' with ⟨w, hw, rfl⟩
                  have haw : a = w := by
                    rcases mem_insert.mp haQ with h | h
                    · exact absurd h hab.ne
                    · exact mem_singleton.mp h
                  rw [haw]
              · have haS : a ∈ S := mem_erase.mpr ⟨hav, mem_univ _⟩
                have hbS : b ∈ S := mem_erase.mpr ⟨hbv, mem_univ _⟩
                have hrange := range_orderEmbOfFin S hScard
                obtain ⟨i, hi⟩ : ∃ i : Fin (n - 1), emb i = a := by
                  have : a ∈ Set.range (S.orderEmbOfFin hScard) := by rw [hrange]; exact haS
                  exact this
                obtain ⟨j, hj⟩ : ∃ j : Fin (n - 1), emb j = b := by
                  have : b ∈ Set.range (S.orderEmbOfFin hScard) := by rw [hrange]; exact hbS
                  exact this
                have hij : G'.Adj i j := by simp [G', hi, hj, hab]
                obtain ⟨Q', ⟨hQ'P, hiQ', hjQ'⟩, hQ'u⟩ := hP'_part.2 i j hij
                refine ⟨Q'.map emb, ⟨mem_union_left _ (mem_image.mpr ⟨Q', hQ'P, rfl⟩),
                  mem_map.mpr ⟨i, hiQ', hi⟩, mem_map.mpr ⟨j, hjQ', hj⟩⟩, ?_⟩
                rintro Q ⟨hQP, haQ, hbQ⟩
                rcases mem_union.mp hQP with h1' | h2'
                · rcases mem_image.mp h1' with ⟨Q'', hQ''P, rfl⟩
                  rcases mem_map.mp haQ with ⟨i', hi'Q'', hi'⟩
                  rcases mem_map.mp hbQ with ⟨j', hj'Q'', hj'⟩
                  have hi_eq : i' = i := emb.injective (hi'.trans hi.symm)
                  have hj_eq : j' = j := emb.injective (hj'.trans hj.symm)
                  rw [hQ'u Q'' ⟨hQ''P, hi_eq ▸ hi'Q'', hj_eq ▸ hj'Q''⟩]
                · rcases mem_image.mp h2' with ⟨w, _, rfl⟩
                  rcases mem_insert.mp haQ with h | h
                  · exact absurd h hav
                  · rcases mem_insert.mp hbQ with h' | h'
                    · exact absurd h' hbv
                    · exact absurd ((mem_singleton.mp h).trans (mem_singleton.mp h').symm) hab.ne
        refine ⟨P, hP_part, ?_⟩
        have hP_le : P.card ≤ P'.card + ((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card := by
          calc
            P.card ≤ P1.card + P2.card := card_union_le P1 P2
            _ ≤ P'.card + ((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card :=
                  Nat.add_le_add card_image_le card_image_le
        have hP_leR : (P.card : ℝ) ≤ (P'.card : ℝ) +
            (((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card : ℝ) := by exact_mod_cast hP_le
        have hdegR : (((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card : ℝ) * 3 ≤ (n : ℝ) := by
          have : ((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj v w)).card * 3 ≤ n := by omega
          exact_mod_cast this
        have hn1R : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        rw [hn1R] at hP'_card
        dsimp [Cconst] at hP'_card ⊢
        nlinarith
      · -- Case 2: Every vertex has `3 * d(v) ≥ n`!
        push Not at hlowdeg
        -- Either `G` already has a clique partition of size `≤ (1/6 - η₀/2) n^2 ≤ n^2/6 + Cconst * n`,
        -- or by `H2` there exists a `K_L`-feasible dual `z` with `∑ z ≥ (1/6 - η₀) n^2`!
        by_cases hdual : ∃ z : Sym2 (Fin n) → ℝ,
            (∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
              ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) ∧
            (1 / 6 - η₀) * (n : ℝ) ^ 2 ≤ ∑ e ∈ G.edgeFinset, z e
        · obtain ⟨z, hz, hW_ge⟩ := hdual
          obtain ⟨A, hAcl, hAcard, hAerr⟩ := hfrac n hn_ge_n1 G hG z hz hW_ge
          -- Chordal normal form (`T = ∅`!):
          let ρ : ℝ := 1 / 10000
          let lam : ℝ := 1 / 100
          let R_A := (Finset.univ : Finset (Fin n)) \ A
          let Abad := A.filter (fun u ↦ (ρ / 4) * (n : ℝ) < ((R_A.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ))
          let A₀ := A \ Abad
          let R₀ := (Finset.univ : Finset (Fin n)) \ A₀
          have hA₀cl : G.IsClique (A₀ : Set (Fin n)) := fun x hx y hy hxy ↦ hAcl (sdiff_subset hx) (sdiff_subset hy) hxy
          have hAbad_card : (Abad.card : ℝ) ≤ (4 * ε / ρ) * (n : ℝ) := by
            have hsum_DA : ∑ u ∈ A, ((R_A.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) =
                ((A.card * (n - A.card) -
                  (G.edgeFinset.filter (fun e ↦ (∃ u ∈ A, u ∈ e) ∧ (∃ r ∈ R_A, r ∈ e))).card : ℕ) : ℝ) := by
              let ERA := G.edgeFinset.filter (fun e ↦ (∃ u ∈ A, u ∈ e) ∧ (∃ r ∈ R_A, r ∈ e))
              have hcard_bij : ERA.card = ∑ u ∈ A, (R_A.filter (fun r ↦ G.Adj u r)).card := by
                have h1 : ERA.card =
                    (A.biUnion (fun u ↦ (R_A.filter (fun r ↦ G.Adj u r)).image (fun r ↦ (u, r)))).card := by
                  symm
                  refine Finset.card_bij (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_
                  · intro p hp
                    rcases mem_biUnion.mp hp with ⟨u, huA, hpu⟩
                    rcases mem_image.mp hpu with ⟨r, hr, rfl⟩
                    rw [mem_filter] at hr
                    rw [mem_filter, mem_edgeFinset]
                    exact ⟨hr.2, ⟨u, huA, by simp⟩, ⟨r, hr.1, by simp⟩⟩
                  · intro p₁ hp₁ p₂ hp₂ hEq
                    rcases mem_biUnion.mp hp₁ with ⟨u₁, hu₁A, hp₁u⟩
                    rcases mem_image.mp hp₁u with ⟨r₁, hr₁, rfl⟩
                    rcases mem_biUnion.mp hp₂ with ⟨u₂, hu₂A, hp₂u⟩
                    rcases mem_image.mp hp₂u with ⟨r₂, hr₂, rfl⟩
                    have hr₂R : r₂ ∈ R_A := (mem_filter.mp hr₂).1
                    rcases Sym2.eq_iff.mp hEq with ⟨h1, h2⟩ | ⟨h1, _⟩
                    · exact Prod.ext h1 h2
                    · simp only at h1
                      exact absurd hu₁A (mem_sdiff.mp (h1.symm ▸ hr₂R)).2
                  · intro e he
                    rw [mem_filter, mem_edgeFinset] at he
                    rcases he.2.1 with ⟨u, huA, hue⟩
                    rcases he.2.2 with ⟨r, hrR, hre⟩
                    have hur : u ≠ r := fun h ↦ (mem_sdiff.mp (h ▸ hrR)).2 huA
                    have heq : e = s(u, r) := (Sym2.mem_and_mem_iff hur).mp ⟨hue, hre⟩
                    refine ⟨(u, r), mem_biUnion.mpr ⟨u, huA, mem_image.mpr ⟨r, mem_filter.mpr ⟨hrR, ?_⟩, rfl⟩⟩, heq.symm⟩
                    rw [heq] at he; exact he.1
                rw [h1, card_biUnion]
                · refine sum_congr rfl (fun u _ ↦ card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2))
                · intro u₁ _ u₂ _ hne
                  change Disjoint _ _
                  rw [Finset.disjoint_left]; intro p hp₁ hp₂
                  rcases mem_image.mp hp₁ with ⟨_, _, rfl⟩
                  rcases mem_image.mp hp₂ with ⟨_, _, hEq⟩
                  exact hne (Prod.mk.inj hEq).1.symm
              have hRA_card : R_A.card = n - A.card := by
                rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_fin]
              have htot : (∑ u ∈ A, (R_A.filter (fun r ↦ G.Adj u r)).card) +
                  (∑ u ∈ A, (R_A.filter (fun r ↦ ¬ G.Adj u r)).card) = A.card * (n - A.card) := by
                rw [← sum_add_distrib]
                have hterm : ∀ u ∈ A, (R_A.filter (fun r ↦ G.Adj u r)).card +
                    (R_A.filter (fun r ↦ ¬ G.Adj u r)).card = n - A.card := by
                  intro u _
                  simpa [hRA_card] using Finset.sum_filter_add_sum_filter_not R_A (fun r ↦ G.Adj u r) (fun _ ↦ (1 : ℕ))
                rw [sum_congr rfl hterm, sum_const, smul_eq_mul]
              have hsub : A.card * (n - A.card) - ERA.card = ∑ u ∈ A, (R_A.filter (fun r ↦ ¬ G.Adj u r)).card := by omega
              rw [hsub]; exact_mod_cast rfl
            have hmarkov : (Abad.card : ℝ) * ((ρ / 4) * (n : ℝ)) ≤ ε * (n : ℝ) ^ 2 := by
              calc
                (Abad.card : ℝ) * ((ρ / 4) * (n : ℝ)) = ∑ _u ∈ Abad, (ρ / 4) * (n : ℝ) := by simp
                _ ≤ ∑ u ∈ Abad, ((R_A.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) :=
                      sum_le_sum (fun u hu ↦ (mem_filter.mp hu).2.le)
                _ ≤ ∑ u ∈ A, ((R_A.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) :=
                      Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
                _ ≤ ε * (n : ℝ) ^ 2 := by
                      rw [hsum_DA]
                      dsimp [R_A]
                      have hnn : (0 : ℝ) ≤ ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Finset.univ \ A)).card : ℝ) :=
                        Nat.cast_nonneg _
                      linarith
            have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
            have hρ4 : (0 : ℝ) < (ρ / 4) * (n : ℝ) := by dsimp [ρ]; positivity
            have heq : (4 * ε / ρ) * (n : ℝ) * ((ρ / 4) * (n : ℝ)) = ε * (n : ℝ) ^ 2 := by
              dsimp [ρ]; ring
            exact le_of_mul_le_mul_right (by linarith) hρ4
          have hA₀_miss : ∀ u ∈ A₀, ((R₀.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) ≤ (ρ / 4) * (n : ℝ) := by
            intro u hu
            have huA : u ∈ A := (mem_sdiff.mp hu).1
            have huNotBad : u ∉ Abad := (mem_sdiff.mp hu).2
            have h1 : ((R_A.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) ≤ (ρ / 4) * (n : ℝ) := by
              by_contra hgt
              push Not at hgt
              exact huNotBad (mem_filter.mpr ⟨huA, hgt⟩)
            have hsub' : R₀.filter (fun r ↦ ¬ G.Adj u r) ⊆ R_A.filter (fun r ↦ ¬ G.Adj u r) := by
              intro r hr
              rw [mem_filter] at hr
              have hru : r ≠ u := fun h ↦ (mem_sdiff.mp hr.1).2 (h ▸ hu)
              have hrnotA : r ∉ A := fun hrA ↦ hr.2 (hAcl huA hrA (Ne.symm hru))
              exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hrnotA⟩, hr.2⟩
            exact le_trans (by exact_mod_cast card_le_card hsub') h1
          have hER₀_card : ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀)).card : ℝ) ≤
              (ε + 4 * ε / ρ) * (n : ℝ) ^ 2 := by
            have hsub : G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀) ⊆
                G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R_A) ∪
                Abad.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))) := by
              intro e he
              rw [mem_filter] at he
              by_cases hRA : ∀ x ∈ e, x ∈ R_A
              · exact mem_union_left _ (mem_filter.mpr ⟨he.1, hRA⟩)
              · push Not at hRA
                rcases hRA with ⟨x, hxe, hxnotRA⟩
                have hxA : x ∈ A := by
                  by_contra hxnotA
                  exact hxnotRA (mem_sdiff.mpr ⟨mem_univ _, hxnotA⟩)
                have hxR₀ : x ∈ R₀ := he.2 x hxe
                have hxAbad : x ∈ Abad := by
                  by_contra hxnot
                  exact (mem_sdiff.mp hxR₀).2 (mem_sdiff.mpr ⟨hxA, hxnot⟩)
                induction e using Sym2.ind with
                | h a b =>
                  rcases Sym2.mem_iff.mp hxe with rfl | rfl
                  · exact mem_union_right _ (mem_biUnion.mpr ⟨x, hxAbad, mem_image.mpr ⟨b, mem_univ _, rfl⟩⟩)
                  · exact mem_union_right _ (mem_biUnion.mpr ⟨x, hxAbad, mem_image.mpr ⟨a, mem_univ _, Sym2.eq_swap⟩⟩)
            have hbi : (Abad.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y)))).card ≤
                Abad.card * n := by
              calc
                (Abad.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y)))).card
                    ≤ ∑ x ∈ Abad, ((Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))).card := card_biUnion_le
                _ ≤ ∑ _x ∈ Abad, n := sum_le_sum (fun x _ ↦ le_trans card_image_le (by simp))
                _ = Abad.card * n := by simp
            have hle1 : ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀)).card : ℝ) ≤
                ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R_A)).card : ℝ) + (Abad.card : ℝ) * (n : ℝ) := by
              have hnat := le_trans (card_le_card hsub) (le_trans (card_union_le _ _) (Nat.add_le_add_left hbi _))
              exact_mod_cast hnat
            have hRA_le : ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R_A)).card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
              dsimp [R_A]
              have hnn : (0 : ℝ) ≤ ((A.card * (n - A.card) -
                (G.edgeFinset.filter (fun e ↦ (∃ u ∈ A, u ∈ e) ∧ (∃ r ∈ Finset.univ \ A, r ∈ e))).card : ℕ) : ℝ) :=
                Nat.cast_nonneg _
              linarith
            have hAb_mul : (Abad.card : ℝ) * (n : ℝ) ≤ (4 * ε / ρ) * (n : ℝ) ^ 2 := by
              have := mul_le_mul_of_nonneg_right hAbad_card (Nat.cast_nonneg n)
              linarith
            rw [add_mul]
            exact le_trans hle1 (add_le_add hRA_le hAb_mul)
          have hωR₀ : ∀ Q ⊆ R₀, G.IsClique (Q : Set (Fin n)) → (Q.card : ℝ) ≤ (1 / 100000 : ℝ) * (n : ℝ) := by
            intro Q hQR₀ hQcl
            have h1 := clique_edges_le hQR₀ hQcl
            have h1R : (Q.card.choose 2 : ℝ) ≤ (ε + 4 * ε / ρ) * (n : ℝ) ^ 2 :=
              le_trans (by exact_mod_cast h1) hER₀_card
            have hch : 2 * (Q.card.choose 2 : ℝ) = (Q.card : ℝ) * ((Q.card : ℝ) - 1) := by
              by_cases hq0 : Q.card = 0
              · simp [hq0]
              · have hnat : 2 * Q.card.choose 2 = Q.card * (Q.card - 1) := by
                  rw [Nat.choose_two_right]
                  have hev := Nat.even_mul_pred_self Q.card
                  rcases hev with ⟨q, hq⟩
                  omega
                have hR : ((2 * Q.card.choose 2 : ℕ) : ℝ) = ((Q.card * (Q.card - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
                push_cast [Nat.cast_sub (by omega : 1 ≤ Q.card)] at hR
                exact hR
            have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
            dsimp [ε, ρ] at h1R
            nlinarith
          -- Every vertex of `Y₀ = {y ∈ R₀ | d_{R₀}(y) ≥ ρ n}` is COMPLETE to `A₀` (no `C_4`!)!
          let Y₀ := R₀.filter (fun y ↦ ρ * (n : ℝ) ≤ ((R₀.filter (fun w ↦ G.Adj y w)).card : ℝ))
          have hY₀_complete : ∀ a ∈ A₀, ∀ y ∈ Y₀, G.Adj a y := by
            intro a haA₀ y hyY₀
            by_contra hna
            have hyR₀ : y ∈ R₀ := (mem_filter.mp hyY₀).1
            have hay_ne : a ≠ y := fun h ↦ (mem_sdiff.mp hyR₀).2 (h ▸ haA₀)
            let CN := R₀.filter (fun w ↦ G.Adj a w ∧ G.Adj y w)
            have hCN_card : (3 / 4) * ρ * (n : ℝ) ≤ (CN.card : ℝ) := by
              have hsub : R₀.filter (fun w ↦ G.Adj y w) ⊆
                  CN ∪ R₀.filter (fun w ↦ ¬ G.Adj a w) := by
                intro w hw
                rw [mem_filter] at hw
                by_cases haw : G.Adj a w
                · exact mem_union_left _ (mem_filter.mpr ⟨hw.1, haw, hw.2⟩)
                · exact mem_union_right _ (mem_filter.mpr ⟨hw.1, haw⟩)
              have hle : ((R₀.filter (fun w ↦ G.Adj y w)).card : ℝ) ≤
                  (CN.card : ℝ) + ((R₀.filter (fun w ↦ ¬ G.Adj a w)).card : ℝ) := by
                exact_mod_cast le_trans (card_le_card hsub) (card_union_le _ _)
              have hydeg := (mem_filter.mp hyY₀).2
              have hamiss := hA₀_miss a haA₀
              dsimp [ρ] at hydeg hamiss ⊢
              linarith
            have hCN_not_cl : ¬ G.IsClique (CN : Set (Fin n)) := by
              intro hcl
              have hle := hωR₀ CN (filter_subset _ _) hcl
              have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
              dsimp [ρ] at hCN_card
              nlinarith
            unfold SimpleGraph.IsClique Set.Pairwise at hCN_not_cl
            push Not at hCN_not_cl
            rcases hCN_not_cl with ⟨w₁, hw₁, w₂, hw₂, hw12, hnw12⟩
            rw [mem_coe, mem_filter] at hw₁ hw₂
            exact chordal_no_c4 hG hay_ne hna hw12 hnw12 hw₁.2.1 hw₂.2.1 hw₁.2.2 hw₂.2.2
          -- Promote `U = {x ∈ R₀ | d_{R₀}(x) > |R₀| - λ n}` into the core!
          let U := R₀.filter (fun x ↦ (R₀.card : ℝ) - lam * (n : ℝ) < ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ))
          have hA₀_card_bounds : (n : ℝ) / 3 - (1 / 10 ^ 10 : ℝ) * (n : ℝ) ≤ (A₀.card : ℝ) ∧
              (A₀.card : ℝ) ≤ (n : ℝ) / 3 + (1 / 10 ^ 10 : ℝ) * (n : ℝ) := by
            have h1 := abs_le.mp hAcard
            have hsub : A₀.card = A.card - Abad.card := card_sdiff_of_subset (filter_subset _ _)
            have hle : Abad.card ≤ A.card := card_le_card (filter_subset _ _)
            have hR : (A₀.card : ℝ) = (A.card : ℝ) - (Abad.card : ℝ) := by
              rw [hsub, Nat.cast_sub hle]
            dsimp [ε, ρ] at h1 hAbad_card
            constructor <;> nlinarith
          have hR₀_card : (R₀.card : ℝ) = (n : ℝ) - (A₀.card : ℝ) := by
            have hle : A₀.card ≤ n := by simpa using card_le_univ A₀
            rw [card_sdiff_of_subset (subset_univ A₀), card_univ, Fintype.card_fin, Nat.cast_sub hle]
          have hU_sub_Y₀ : U ⊆ Y₀ := by
            intro x hx
            rw [mem_filter] at hx ⊢
            have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
            dsimp [ρ, lam] at hx ⊢
            exact ⟨hx.1, by linarith [hA₀_card_bounds.2, hR₀_card]⟩
          have hU_card : (U.card : ℝ) ≤ (1 / 10 ^ 9 : ℝ) * (n : ℝ) := by
            -- `∑_{x ∈ U} d_{R₀}(x) ≤ 2 * e(G[R₀])`
            have hsum_deg : ∑ x ∈ R₀, (R₀.filter (fun w ↦ G.Adj x w)).card =
                2 * (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀)).card := by
              have h1 : ∑ x ∈ R₀, (R₀.filter (fun w ↦ G.Adj x w)).card =
                  ∑ x ∈ R₀, ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ y ∈ e, y ∈ R₀), if x ∈ e then 1 else 0 := by
                refine sum_congr rfl ?_
                intro x hx
                rw [sum_boole, Nat.cast_id]
                refine Finset.card_bij (fun w _ ↦ s(x, w)) ?_ ?_ ?_
                · intro w hw
                  rw [mem_filter] at hw ⊢
                  rw [mem_filter, mem_edgeFinset]
                  refine ⟨⟨hw.2, fun y hy ↦ ?_⟩, by simp⟩
                  rcases Sym2.mem_iff.mp hy with rfl | rfl
                  · exact hx
                  · exact hw.1
                · intro w₁ hw₁ w₂ hw₂ hEq
                  rw [mem_filter] at hw₁ hw₂
                  rcases Sym2.eq_iff.mp hEq with ⟨_, h⟩ | ⟨h, _⟩
                  · exact h
                  · exact absurd h hw₂.2.ne
                · intro e he
                  rw [mem_filter, mem_filter, mem_edgeFinset] at he
                  induction e using Sym2.ind with
                  | h a b =>
                    rcases Sym2.mem_iff.mp he.2 with rfl | rfl
                    · exact ⟨b, mem_filter.mpr ⟨he.1.2 b (by simp), he.1.1⟩, rfl⟩
                    · exact ⟨a, mem_filter.mpr ⟨he.1.2 a (by simp), he.1.1.symm⟩, Sym2.eq_swap⟩
              rw [h1, sum_comm]
              have h2 : ∀ e ∈ G.edgeFinset.filter (fun e ↦ ∀ y ∈ e, y ∈ R₀),
                  ∑ x ∈ R₀, (if x ∈ e then 1 else 0) = 2 := by
                intro e he
                rw [mem_filter, mem_edgeFinset] at he
                rw [sum_boole, Nat.cast_id]
                induction e using Sym2.ind with
                | h a b =>
                  have hfilt : R₀.filter (fun x ↦ x ∈ s(a, b)) = {a, b} := by
                    ext x; simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
                    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by rcases h with rfl | rfl <;> exact he.2 _ (by simp), h⟩⟩
                  rw [hfilt, card_pair he.1.ne]
              rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]
            have hsum_U : (U.card : ℝ) * ((n : ℝ) / 2) ≤
                2 * ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀)).card : ℝ) := by
              calc
                (U.card : ℝ) * ((n : ℝ) / 2) = ∑ _x ∈ U, (n : ℝ) / 2 := by simp
                _ ≤ ∑ x ∈ U, ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) := by
                      refine sum_le_sum ?_
                      intro x hx
                      have h1 := (mem_filter.mp hx).2
                      dsimp [lam] at h1
                      linarith [hA₀_card_bounds.2, hR₀_card]
                _ ≤ ∑ x ∈ R₀, ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) :=
                      Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
                _ = 2 * ((G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀)).card : ℝ) := by exact_mod_cast hsum_deg
            have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
            dsimp [ε, ρ] at hER₀_card
            nlinarith
          let C := A₀ ∪ U
          let R := R₀ \ U
          have hCR_disj : Disjoint C R := by
            rw [Finset.disjoint_left]
            intro x hxC hxR
            rw [mem_sdiff] at hxR
            rcases mem_union.mp hxC with hxA | hxU
            · exact (mem_sdiff.mp hxR.1).2 hxA
            · exact hxR.2 hxU
          have hCR_univ : C ∪ R = Finset.univ := by
            ext x
            simp only [C, R, R₀, mem_union, mem_sdiff, mem_univ, true_and, iff_true]
            by_cases h1 : x ∈ A₀
            · exact Or.inl (Or.inl h1)
            · by_cases h2 : x ∈ U
              · exact Or.inl (Or.inr h2)
              · exact Or.inr ⟨h1, h2⟩
          -- Prove `C = A₀ ∪ U` is a CLIQUE (no `C_4`!)!
          have hC_clique : G.IsClique (C : Set (Fin n)) := by
            intro x hx y hy hxy
            rw [mem_coe, mem_union] at hx hy
            rcases hx with hxA | hxU <;> rcases hy with hyA | hyU
            · exact hA₀cl hxA hyA hxy
            · exact hY₀_complete x hxA y (hU_sub_Y₀ hyU)
            · exact (hY₀_complete y hyA x (hU_sub_Y₀ hxU)).symm
            · by_contra hna
              -- Both `x, y ∈ U` miss at most `λ n` vertices of `R₀`, so they have `≥ |R₀| - 2 λ n` common neighbors in `R₀`!
              let CN := R₀.filter (fun w ↦ G.Adj x w ∧ G.Adj y w)
              have hCN_card : (R₀.card : ℝ) - 2 * lam * (n : ℝ) ≤ (CN.card : ℝ) := by
                have hmiss : ∀ z ∈ U, ((R₀.filter (fun w ↦ ¬ G.Adj z w)).card : ℝ) ≤ lam * (n : ℝ) := by
                  intro z hz
                  have h1 := (mem_filter.mp hz).2
                  have hpart : ((R₀.filter (fun w ↦ G.Adj z w)).card : ℝ) +
                      ((R₀.filter (fun w ↦ ¬ G.Adj z w)).card : ℝ) = (R₀.card : ℝ) := by
                    have hnat : (R₀.filter (fun w ↦ G.Adj z w)).card +
                        (R₀.filter (fun w ↦ ¬ G.Adj z w)).card = R₀.card := by
                      simpa using Finset.sum_filter_add_sum_filter_not R₀ (fun w ↦ G.Adj z w) (fun _ ↦ (1 : ℕ))
                    exact_mod_cast hnat
                  linarith
                have hsub : R₀ ⊆ CN ∪ R₀.filter (fun w ↦ ¬ G.Adj x w) ∪ R₀.filter (fun w ↦ ¬ G.Adj y w) := by
                  intro w hw
                  by_cases h1 : G.Adj x w
                  · by_cases h2 : G.Adj y w
                    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw, h1, h2⟩))
                    · exact mem_union_right _ (mem_filter.mpr ⟨hw, h2⟩)
                  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hw, h1⟩))
                have hle : (R₀.card : ℝ) ≤ (CN.card : ℝ) +
                    ((R₀.filter (fun w ↦ ¬ G.Adj x w)).card : ℝ) +
                    ((R₀.filter (fun w ↦ ¬ G.Adj y w)).card : ℝ) := by
                  exact_mod_cast le_trans (card_le_card hsub)
                    (le_trans (card_union_le _ _) (Nat.add_le_add_right (card_union_le _ _) _))
                linarith [hmiss x hxU, hmiss y hyU]
              have hCN_not_cl : ¬ G.IsClique (CN : Set (Fin n)) := by
                intro hcl
                have hle := hωR₀ CN (filter_subset _ _) hcl
                have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
                dsimp [lam] at hCN_card
                nlinarith [hA₀_card_bounds.2, hR₀_card]
              unfold SimpleGraph.IsClique Set.Pairwise at hCN_not_cl
              push Not at hCN_not_cl
              rcases hCN_not_cl with ⟨w₁, hw₁, w₂, hw₂, hw12, hnw12⟩
              rw [mem_coe, mem_filter] at hw₁ hw₂
              exact chordal_no_c4 hG hxy hna hw12 hnw12 hw₁.2.1 hw₂.2.1 hw₁.2.2 hw₂.2.2
          -- Check normal form numerical parameters for `lem_absorption`!
          have hC_card_eq : (C.card : ℝ) = (A₀.card : ℝ) + (U.card : ℝ) := by
            have hd : Disjoint A₀ U := disjoint_sdiff.mono_right (filter_subset _ _)
            exact_mod_cast card_union_of_disjoint hd
          have hR_card_eq : (R.card : ℝ) = (R₀.card : ℝ) - (U.card : ℝ) := by
            have hle : U.card ≤ R₀.card := card_le_card (filter_subset _ _)
            rw [card_sdiff_of_subset (filter_subset _ _), Nat.cast_sub hle]
          have hU_nn : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
          have hc3 : 3 ≤ C.card := by
            have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
            have hCR : (3 : ℝ) ≤ (C.card : ℝ) := by linarith [hA₀_card_bounds.1, hC_card_eq, hU_nn]
            exact_mod_cast hCR
          let σ : ℕ := Nat.floor (2 * ρ * (n : ℝ))
          let τ : ℕ := Nat.floor (lam * (n : ℝ))
          let wR : ℕ := Nat.floor ((1 / 100000 : ℝ) * (n : ℝ))
          let ΔR : ℕ := Nat.floor ((R.card : ℝ) - (lam / 2) * (n : ℝ))
          have hσ_bound : ∀ x ∈ R, (C.filter (fun u ↦ ¬ G.Adj x u)).card ≤ σ := by
            intro x hxR
            have hxR₀ : x ∈ R₀ := (mem_sdiff.mp hxR).1
            have hR_ineq : ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) ≤ 2 * ρ * (n : ℝ) := by
              by_cases hxY : x ∈ Y₀
              · have hsub : C.filter (fun u ↦ ¬ G.Adj x u) ⊆ U := by
                  intro u hu
                  rw [mem_filter] at hu
                  rcases mem_union.mp hu.1 with huA | huU
                  · exact absurd (hY₀_complete u huA x hxY).symm hu.2
                  · exact huU
                have hle : ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) ≤ (U.card : ℝ) := by
                  exact_mod_cast card_le_card hsub
                dsimp [ρ]; linarith [hU_card]
              · have hdegR₀ : ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) < ρ * (n : ℝ) := by
                  by_contra hge; push Not at hge
                  exact hxY (mem_filter.mpr ⟨hxR₀, hge⟩)
                have hdegG : (n : ℝ) / 3 ≤ (((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj x w)).card : ℝ) := by
                  have h1 := hlowdeg x
                  have h1R : (n : ℝ) ≤ (((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj x w)).card : ℝ) * 3 := by
                    exact_mod_cast h1
                  linarith
                have hdegA₀ : (n : ℝ) / 3 - ρ * (n : ℝ) ≤ ((A₀.filter (fun u ↦ G.Adj x u)).card : ℝ) := by
                  have hsub : (Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj x w) ⊆
                      A₀.filter (fun u ↦ G.Adj x u) ∪ R₀.filter (fun w ↦ G.Adj x w) := by
                    intro w hw
                    rw [mem_filter] at hw
                    by_cases hwA : w ∈ A₀
                    · exact mem_union_left _ (mem_filter.mpr ⟨hwA, hw.2⟩)
                    · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hwA⟩, hw.2⟩)
                  have hle : (((Finset.univ : Finset (Fin n)).filter (fun w ↦ G.Adj x w)).card : ℝ) ≤
                      ((A₀.filter (fun u ↦ G.Adj x u)).card : ℝ) + ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) := by
                    exact_mod_cast le_trans (card_le_card hsub) (card_union_le _ _)
                  have hle' : (n : ℝ) / 3 ≤
                      ((A₀.filter (fun u ↦ G.Adj x u)).card : ℝ) + ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) :=
                    le_trans hdegG hle
                  dsimp [ρ] at hdegR₀ ⊢
                  linarith
                have hmissA₀ : ((A₀.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) ≤
                    (A₀.card : ℝ) - ((n : ℝ) / 3 - ρ * (n : ℝ)) := by
                  have hpart : ((A₀.filter (fun u ↦ G.Adj x u)).card : ℝ) +
                      ((A₀.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) = (A₀.card : ℝ) := by
                    have hnat : (A₀.filter (fun u ↦ G.Adj x u)).card +
                        (A₀.filter (fun u ↦ ¬ G.Adj x u)).card = A₀.card := by
                      simpa using Finset.sum_filter_add_sum_filter_not A₀ (fun u ↦ G.Adj x u) (fun _ ↦ (1 : ℕ))
                    exact_mod_cast hnat
                  linarith
                have hsub : C.filter (fun u ↦ ¬ G.Adj x u) ⊆ A₀.filter (fun u ↦ ¬ G.Adj x u) ∪ U := by
                  intro u hu
                  rw [mem_filter] at hu
                  rcases mem_union.mp hu.1 with huA | huU
                  · exact mem_union_left _ (mem_filter.mpr ⟨huA, hu.2⟩)
                  · exact mem_union_right _ huU
                have hle : ((C.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) ≤
                    ((A₀.filter (fun u ↦ ¬ G.Adj x u)).card : ℝ) + (U.card : ℝ) := by
                  exact_mod_cast le_trans (card_le_card hsub) (card_union_le _ _)
                dsimp [ρ] at hmissA₀ ⊢
                linarith [hA₀_card_bounds.2, hU_card]
            exact Nat.le_floor hR_ineq
          have hτ_bound : ∀ u ∈ C, (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ := by
            intro u huC
            have hR_ineq : ((R.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) ≤ lam * (n : ℝ) := by
              have hsub : R.filter (fun r ↦ ¬ G.Adj u r) ⊆ R₀.filter (fun r ↦ ¬ G.Adj u r) :=
                filter_subset_filter _ sdiff_subset
              have hle : ((R.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) ≤
                  ((R₀.filter (fun r ↦ ¬ G.Adj u r)).card : ℝ) := by exact_mod_cast card_le_card hsub
              rcases mem_union.mp huC with huA | huU
              · dsimp [ρ, lam] at *; linarith [hA₀_miss u huA]
              · have h1 := (mem_filter.mp huU).2
                have hpart : ((R₀.filter (fun w ↦ G.Adj u w)).card : ℝ) +
                    ((R₀.filter (fun w ↦ ¬ G.Adj u w)).card : ℝ) = (R₀.card : ℝ) := by
                  have hnat : (R₀.filter (fun w ↦ G.Adj u w)).card +
                      (R₀.filter (fun w ↦ ¬ G.Adj u w)).card = R₀.card := by
                    simpa using Finset.sum_filter_add_sum_filter_not R₀ (fun w ↦ G.Adj u w) (fun _ ↦ (1 : ℕ))
                  exact_mod_cast hnat
                linarith
            exact Nat.le_floor hR_ineq
          have hΔR_bound : ∀ x ∈ R, (R.filter (fun w ↦ G.Adj x w)).card ≤ ΔR := by
            intro x hxR
            have hxR₀ : x ∈ R₀ := (mem_sdiff.mp hxR).1
            have hxnotU : x ∉ U := (mem_sdiff.mp hxR).2
            have h1 : ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) ≤ (R₀.card : ℝ) - lam * (n : ℝ) := by
              by_contra hgt; push Not at hgt
              exact hxnotU (mem_filter.mpr ⟨hxR₀, hgt⟩)
            have hsub : R.filter (fun w ↦ G.Adj x w) ⊆ R₀.filter (fun w ↦ G.Adj x w) :=
              filter_subset_filter _ sdiff_subset
            have hle : ((R.filter (fun w ↦ G.Adj x w)).card : ℝ) ≤
                (R.card : ℝ) - (lam / 2) * (n : ℝ) := by
              have h2 : ((R.filter (fun w ↦ G.Adj x w)).card : ℝ) ≤
                  ((R₀.filter (fun w ↦ G.Adj x w)).card : ℝ) := by exact_mod_cast card_le_card hsub
              dsimp [lam] at h1 ⊢
              linarith [hR_card_eq, hU_card]
            exact Nat.le_floor hle
          have hdeg_R : ∀ S ⊆ R, S.Nonempty → ∃ v ∈ S, (S.filter (fun w ↦ G.Adj v w)).card ≤ wR := by
            intro S hSR hSne
            have hne' : (S \ ∅).Nonempty := by simpa using hSne
            obtain ⟨v, hvS, hvSimp⟩ := exists_simplicial_outside_clique h1 hG S ∅ (empty_subset S) (by simp) hne'
            rw [sdiff_empty] at hvS
            refine ⟨v, hvS, ?_⟩
            have hsub : S.filter (fun w ↦ G.Adj v w) ⊆ R₀ :=
              (filter_subset _ _).trans (hSR.trans sdiff_subset)
            exact Nat.le_floor (hωR₀ _ hsub hvSimp)
          let k : ℕ := max C.card (ΔR + wR)
          have hck : C.card ≤ k := le_max_left _ _
          have hΔk : ΔR + wR ≤ k := le_max_right _ _
          have hk1 : 1 ≤ k := by omega
          obtain ⟨colR₀, hcolR₀⟩ := degenerate_edge_coloring hΔk hk1 R.card R rfl hΔR_bound hdeg_R
          let ER := G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R)
          have hcolR₀_edge : ∀ e₁ ∈ ER, ∀ e₂ ∈ ER, e₁ ≠ e₂ → colR₀ e₁ = colR₀ e₂ →
              ∀ x, x ∈ e₁ → x ∉ e₂ := by
            intro e₁ he₁ e₂ he₂ hne hceq x hx₁ hx₂
            rw [mem_filter, mem_edgeFinset] at he₁ he₂
            induction e₁ using Sym2.ind with
            | h a₁ b₁ =>
              induction e₂ using Sym2.ind with
              | h a₂ b₂ =>
                have ha₁R : a₁ ∈ R := he₁.2 a₁ (by simp)
                have hb₁R : b₁ ∈ R := he₁.2 b₁ (by simp)
                have ha₂R : a₂ ∈ R := he₂.2 a₂ (by simp)
                have hb₂R : b₂ ∈ R := he₂.2 b₂ (by simp)
                rcases Sym2.mem_iff.mp hx₁ with rfl | rfl <;> rcases Sym2.mem_iff.mp hx₂ with h | h
                · subst h
                  have hne' : b₁ ≠ b₂ := fun hb ↦ hne (by rw [hb])
                  exact hcolR₀ x ha₁R b₁ hb₁R b₂ hb₂R hne' he₁.1 he₂.1 hceq
                · subst h
                  have hne' : b₁ ≠ a₂ := fun hb ↦ hne (by rw [hb, Sym2.eq_swap])
                  exact hcolR₀ x ha₁R b₁ hb₁R a₂ ha₂R hne' he₁.1 he₂.1.symm (by simpa [Sym2.eq_swap] using hceq)
                · subst h
                  have hne' : a₁ ≠ b₂ := fun ha ↦ hne (by rw [ha, Sym2.eq_swap])
                  exact hcolR₀ x hb₁R a₁ ha₁R b₂ hb₂R hne' he₁.1.symm he₂.1 (by simpa [Sym2.eq_swap] using hceq)
                · subst h
                  have hne' : a₁ ≠ a₂ := fun ha ↦ hne (by rw [ha])
                  exact hcolR₀ x hb₁R a₁ ha₁R a₂ ha₂R hne' he₁.1.symm he₂.1.symm (by simpa [Sym2.eq_swap] using hceq)
          have hER_nd : ∀ e ∈ ER, ¬ e.IsDiag := fun e he ↦ G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he).1)
          obtain ⟨colR, hcolR_prop, hcolR_bal⟩ := balanced_edge_coloring hk1 ER hER_nd colR₀ hcolR₀_edge
          -- Check the two numerical capacity bounds `hcap1` and `hcap2`!
          have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_M
          have hσR : (σ : ℝ) ≤ 2 * ρ * (n : ℝ) := Nat.floor_le (by dsimp [ρ]; positivity)
          have hτR : (τ : ℝ) ≤ lam * (n : ℝ) := Nat.floor_le (by dsimp [lam]; positivity)
          have hwRR : (wR : ℝ) ≤ (1 / 100000 : ℝ) * (n : ℝ) := Nat.floor_le (by positivity)
          have hΔRR : (ΔR : ℝ) ≤ (R.card : ℝ) - (lam / 2) * (n : ℝ) :=
            Nat.floor_le (by dsimp [lam]; linarith [hR_card_eq, hR₀_card, hA₀_card_bounds.2, hU_card])
          have hcap1 : k ≤ 2 * (C.card - 2 * σ) := by
            have h2σ : 2 * σ ≤ C.card := by
              have : (2 * (σ : ℝ)) ≤ (C.card : ℝ) := by
                dsimp [ρ] at hσR; linarith [hA₀_card_bounds.1, hC_card_eq, hU_nn]
              exact_mod_cast this
            have hkR : (k : ℝ) ≤ 2 * ((C.card : ℝ) - 2 * (σ : ℝ)) := by
              dsimp [k]
              rw [Nat.cast_max, max_le_iff]
              constructor
              · dsimp [ρ] at hσR; linarith [hA₀_card_bounds.1, hC_card_eq, hU_nn]
              · push_cast
                dsimp [ρ, lam] at hσR hΔRR
                linarith [hA₀_card_bounds.1, hA₀_card_bounds.2, hC_card_eq, hR_card_eq, hR₀_card, hU_card, hwRR]
            have hcast : ((2 * (C.card - 2 * σ) : ℕ) : ℝ) = 2 * ((C.card : ℝ) - 2 * (σ : ℝ)) := by
              push_cast [Nat.cast_sub h2σ]; ring
            exact_mod_cast (hcast ▸ hkR)
          have hcap2 : 3 * ((C.card + 1) / 2) + 4 * (τ + 2 * (ER.card / k + 1)) ≤ R.card + 3 := by
            have hER_le : (ER.card : ℝ) ≤ (ε + 4 * ε / ρ) * (n : ℝ) ^ 2 := by
              have hsub : ER ⊆ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ R₀) := by
                intro e he; rw [mem_filter] at he ⊢
                exact ⟨he.1, fun x hx ↦ sdiff_subset (he.2 x hx)⟩
              exact le_trans (by exact_mod_cast card_le_card hsub) hER₀_card
            have hERk : ((ER.card / k : ℕ) : ℝ) ≤ (1 / 10 ^ 9 : ℝ) * (n : ℝ) := by
              have hmul : (ER.card / k : ℕ) * k ≤ ER.card := Nat.div_mul_le_self ER.card k
              have hmulR : ((ER.card / k : ℕ) : ℝ) * (k : ℝ) ≤ (ER.card : ℝ) := by exact_mod_cast hmul
              have hk_ge : (n : ℝ) / 4 ≤ (k : ℝ) := by
                have : (C.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hck
                linarith [hA₀_card_bounds.1, hC_card_eq, hU_nn]
              have hq1 : ((ER.card / k : ℕ) : ℝ) * ((n : ℝ) / 4) ≤ (ER.card : ℝ) :=
                le_trans (mul_le_mul_of_nonneg_left hk_ge (Nat.cast_nonneg _)) hmulR
              have hq2 : ((ER.card / k : ℕ) : ℝ) * ((n : ℝ) / 4) ≤ ((1 / 10 ^ 9 : ℝ) * (n : ℝ)) * ((n : ℝ) / 4) := by
                dsimp [ε, ρ] at hER_le
                have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
                have hcoeff : (1 / (10 : ℝ) ^ 16 + 4 * (1 / (10 : ℝ) ^ 16) / (1 / 10000)) * (n : ℝ) ^ 2 ≤
                    (1 / (4 * 10 ^ 9 : ℝ)) * (n : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right (by norm_num) hn2
                have hrhs : ((1 / 10 ^ 9 : ℝ) * (n : ℝ)) * ((n : ℝ) / 4) = (1 / (4 * 10 ^ 9 : ℝ)) * (n : ℝ) ^ 2 := by ring
                linarith
              exact le_of_mul_le_mul_right hq2 (by linarith : (0 : ℝ) < (n : ℝ) / 4)
            have hdiv2 : (((C.card + 1) / 2 : ℕ) : ℝ) ≤ ((C.card : ℝ) + 1) / 2 := by
              have hnat : ((C.card + 1) / 2) * 2 ≤ C.card + 1 := Nat.div_mul_le_self (C.card + 1) 2
              have hR : (((C.card + 1) / 2 : ℕ) : ℝ) * 2 ≤ (C.card : ℝ) + 1 := by exact_mod_cast hnat
              linarith
            have hgoalR :
                (3 : ℝ) * (((C.card + 1) / 2 : ℕ) : ℝ) +
                4 * ((τ : ℝ) + 2 * (((ER.card / k : ℕ) : ℝ) + 1)) ≤ (R.card : ℝ) + 3 := by
              dsimp [lam] at hτR
              linarith [hA₀_card_bounds.1, hA₀_card_bounds.2, hC_card_eq, hR_card_eq, hR₀_card, hU_card, hdiv2, hERk]
            exact_mod_cast hgoalR
          obtain ⟨P, hP_part, hP_card⟩ :=
            lem_absorption h3 C R hCR_disj hCR_univ hC_clique hc3 hck hσ_bound hτ_bound hcap1
              colR hcolR_prop hcolR_bal hcap2
          refine ⟨P, hP_part, ?_⟩
          have hP_leR : (P.card : ℝ) ≤ (C.card : ℝ) * (R.card : ℝ) - (C.card.choose 2 : ℝ) := by
            have hle : C.card.choose 2 ≤ C.card * R.card := by
              have h1 : C.card.choose 2 ≤ C.card * C.card := by
                rw [Nat.choose_two_right]
                exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
              have hCR_le : C.card ≤ R.card := by
                have : (C.card : ℝ) ≤ (R.card : ℝ) := by
                  linarith [hA₀_card_bounds.1, hA₀_card_bounds.2, hC_card_eq, hR_card_eq, hR₀_card, hU_card]
                exact_mod_cast this
              exact le_trans h1 (Nat.mul_le_mul_left C.card hCR_le)
            have hR : (P.card : ℝ) ≤ ((C.card * R.card - C.card.choose 2 : ℕ) : ℝ) := by exact_mod_cast hP_card
            rw [Nat.cast_sub hle] at hR
            push_cast at hR
            exact hR
          have hchoose2 : 2 * (C.card.choose 2 : ℝ) = (C.card : ℝ) * ((C.card : ℝ) - 1) := by
            have hnat : 2 * C.card.choose 2 = C.card * (C.card - 1) := by
              rw [Nat.choose_two_right]
              have hev := Nat.even_mul_pred_self C.card
              rcases hev with ⟨q, hq⟩
              omega
            have hR : ((2 * C.card.choose 2 : ℕ) : ℝ) = ((C.card * (C.card - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast [Nat.cast_sub (by omega : 1 ≤ C.card)] at hR
            exact hR
          have hCR_sum : (C.card : ℝ) + (R.card : ℝ) = (n : ℝ) := by
            have hnat : C.card + R.card = n := by
              rw [← card_union_of_disjoint hCR_disj, hCR_univ, card_univ, Fintype.card_fin]
            exact_mod_cast hnat
          have hquad : (C.card : ℝ) * (R.card : ℝ) - (C.card.choose 2 : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 / 24 := by
            have hRsub : (R.card : ℝ) = (n : ℝ) - (C.card : ℝ) := by linarith
            have hch : (C.card.choose 2 : ℝ) = (C.card : ℝ) * ((C.card : ℝ) - 1) / 2 := by linarith
            have hid : (2 * (n : ℝ) + 1) ^ 2 / 24 - ((C.card : ℝ) * ((n : ℝ) - (C.card : ℝ)) -
                (C.card : ℝ) * ((C.card : ℝ) - 1) / 2) =
                (3 / 2 : ℝ) * ((C.card : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 := by ring
            have hsq : (0 : ℝ) ≤ (3 / 2 : ℝ) * ((C.card : ℝ) - (2 * (n : ℝ) + 1) / 6) ^ 2 := by positivity
            rw [hRsub, hch]
            linarith
          have hCconst_ge : (1 : ℝ) ≤ Cconst := by
            dsimp [Cconst]
            have : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
            linarith
          have hlin : (2 * (n : ℝ) + 1) ^ 2 / 24 ≤ (n : ℝ) ^ 2 / 6 + Cconst * (n : ℝ) := by
            have h1' : (n : ℝ) ≤ Cconst * (n : ℝ) := by
              have := mul_le_mul_of_nonneg_right hCconst_ge (show (0 : ℝ) ≤ (n : ℝ) by linarith)
              linarith
            linarith
          linarith
        · -- No dual `z` has value `≥ (1/6 - η₀) n^2`, so `H2` immediately gives a partition `≤ (1/6 - η₀/2) n^2`!
          push Not at hdual
          obtain ⟨P, hP_part, hP_card⟩ :=
            hround n hn_ge_n2 G ((1 / 6 - η₀) * (n : ℝ) ^ 2) (fun z hz ↦ (hdual z hz).le)
          refine ⟨P, hP_part, ?_⟩
          have hCpos : 0 ≤ Cconst * (n : ℝ) := by dsimp [Cconst]; positivity
          nlinarith [sq_nonneg (n : ℝ)]

end OMA.R_Erdos81_erdos_81_R1
