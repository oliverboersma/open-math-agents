import FormalConjectures.ErdosProblems.«1182»

-- Problem: Erdős Problem 1182 — ramsey ge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1182.lean:158 (declaration Erdos1182.erdos_1182.variants.ramsey_ge)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.O1

open SimpleGraph

/-- Complete bipartite graph on `Fin b` with sides `{i | i < n - 1}` and its complement. -/
def bip (n b : ℕ) : SimpleGraph (Fin b) where
  Adj i j := ¬ (i.1 < n - 1 ↔ j.1 < n - 1)
  symm := ⟨fun _ _ h h' => h h'.symm⟩
  loopless := ⟨fun _ h => h Iff.rfl⟩

/-- A triangle-free graph has independent sets of size `k` in any set of size `k(k+1)/2`. -/
theorem indep {N : ℕ} (C : SimpleGraph (Fin N)) (hC : C.CliqueFree 3) :
    ∀ k : ℕ, ∀ s : Finset (Fin N), k * (k + 1) ≤ 2 * s.card →
      ∃ t ⊆ s, t.card = k ∧ ∀ x ∈ t, ∀ y ∈ t, ¬ C.Adj x y := by
  classical
  intro k
  induction k with
  | zero =>
    intro s _
    exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    intro s hs
    have hpos : 0 < s.card := by
      have : 0 < (k + 1) * (k + 1 + 1) := by positivity
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    by_cases hN : k + 1 ≤ (s.filter (fun y => C.Adj v y)).card
    · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hN
      refine ⟨t, hts.trans (Finset.filter_subset _ _), htc, ?_⟩
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp (hts hx)).2
      have hy' := (Finset.mem_filter.mp (hts hy)).2
      exact hC {v, x, y} (is3Clique_triple_iff.mpr ⟨hx', hy', hxy⟩)
    · push Not at hN
      set s' := (s.erase v).filter (fun y => ¬ C.Adj v y) with hs'
      have hsplit : ((s.erase v).filter (fun y => C.Adj v y)).card + s'.card =
          (s.erase v).card := by
        rw [hs']
        exact Finset.card_filter_add_card_filter_not _
      have hsub : ((s.erase v).filter (fun y => C.Adj v y)).card ≤
          (s.filter (fun y => C.Adj v y)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
      have herase : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
      have hA : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * k + 2 := by ring
      rw [hA] at hs
      have hs'c : k * (k + 1) ≤ 2 * s'.card := by
        omega
      obtain ⟨t, hts, htc, hti⟩ := ih s' hs'c
      have hvt : v ∉ t := by
        intro hvt
        have := hts hvt
        rw [hs', Finset.mem_filter, Finset.mem_erase] at this
        exact this.1.1 rfl
      have hnadj : ∀ y ∈ t, ¬ C.Adj v y := by
        intro y hy
        have := hts hy
        rw [hs', Finset.mem_filter] at this
        exact this.2
      refine ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · have := hts hx
          rw [hs', Finset.mem_filter] at this
          exact Finset.mem_of_mem_erase this.1
      · rw [Finset.card_insert_of_notMem hvt, htc]
      · intro x hx y hy
        rcases Finset.mem_insert.mp hx with rfl | hx2 <;>
          rcases Finset.mem_insert.mp hy with rfl | hy2
        · exact C.loopless.irrefl _
        · exact hnadj y hy2
        · intro h
          exact hnadj x hx2 h.symm
        · exact hti x hx2 y hy2

end OMA.O1

open OMA.O1 SimpleGraph

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.ramsey_ge := by
  intro n G hG
  classical
  unfold SimpleGraph.graphRamsey
  have hne : { N : ℕ | ∀ (C : SimpleGraph (Fin N)),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ }.Nonempty := by
    refine ⟨n * (n + 1), ?_⟩
    intro C
    by_cases hC : C.CliqueFree 3
    · right
      obtain ⟨t, -, htc, hti⟩ := indep C hC n Finset.univ (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact Nat.le_mul_of_pos_left _ (by norm_num))
      refine isContained_iff_exists_le_comap.mpr ⟨(t.orderEmbOfFin htc).toEmbedding, ?_⟩
      intro u v huv
      rw [comap_adj, compl_adj]
      refine ⟨?_, ?_⟩
      · intro h
        exact G.ne_of_adj huv ((t.orderEmbOfFin htc).toEmbedding.injective h)
      · exact hti _ (t.orderEmbOfFin_mem htc u) _ (t.orderEmbOfFin_mem htc v)
    · left
      exact (not_cliqueFree_iff_top_isContained 3).mp hC
  apply le_csInf hne
  intro b hb
  by_contra hlt
  push Not at hlt
  obtain ⟨v0⟩ := hG.nonempty
  have hn : 1 ≤ n := by have := v0.isLt; omega
  rcases hb (bip n b) with h | h
  · obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp h
    have h01 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by simp)
    have h12 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by simp)
    have h02 := hf (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by simp)
    simp only [comap_adj, bip] at h01 h12 h02
    tauto
  · obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.mp h
    have key : ∀ u v : Fin n, G.Walk u v → ((f u).1 < n - 1 ↔ (f v).1 < n - 1) := by
      intro u v p
      induction p with
      | nil => exact Iff.rfl
      | cons hadj p ih =>
        have h1 := hf hadj
        simp only [comap_adj, compl_adj, bip] at h1
        exact (not_not.mp h1.2).trans ih
    have side : ∀ v : Fin n, ((f v0).1 < n - 1 ↔ (f v).1 < n - 1) := by
      intro v
      obtain ⟨p⟩ := hG.preconnected v0 v
      exact key v0 v p
    -- Subtract the first index of the common side to embed into Fin (n - 1).
    have tooSmall (offset : ℕ) (bounds : ∀ v, offset ≤ (f v).1 ∧ (f v).1 - offset < n - 1) :
        False := by
      let g (v : Fin n) : Fin (n - 1) := ⟨(f v).1 - offset, (bounds v).2⟩
      have hg : Function.Injective g := by
        intro x y hxy
        apply f.injective
        apply Fin.ext
        have hx := (bounds x).1
        have hy := (bounds y).1
        have eq : (f x).1 - offset = (f y).1 - offset := congrArg Fin.val hxy
        omega
      have := Fintype.card_le_of_injective g hg
      simp at this
      omega
    by_cases h0 : (f v0).1 < n - 1
    · exact tooSmall 0 fun v => ⟨Nat.zero_le _, by simpa using (side v).mp h0⟩
    · apply tooSmall (n - 1)
      intro v
      have lower : n - 1 ≤ (f v).1 := Nat.le_of_not_lt fun h => h0 ((side v).mpr h)
      have upper := (f v).isLt
      omega
