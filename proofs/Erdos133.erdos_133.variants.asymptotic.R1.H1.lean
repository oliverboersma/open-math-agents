import OMAReductions.R_Erdos133_erdos_133_variants_asymptotic_R1
import Mathlib

/-! The asymptotic lower bound (1 - eps) sqrt n <= f(n) for triangle-free graphs of diameter 2.

Credit: this file reuses, unchanged, the merged proof of the solved catalogue variant
Erdos133.erdos_133.variants.lower_bound by @Genbox (pull request 28 of open-math-agents).
Only the final theorem was adapted to the hypothesis. -/

/-! The diameter-two degree bound and its asymptotic consequence. -/

open Filter SimpleGraph

namespace OMA

lemma diameterTwoCardBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (d : ℕ)
    (hdiam : G.diam = 2) (hdeg : ∀ v, G.degree v ≤ d) :
    Fintype.card V ≤ d ^ 2 + 1 := by
  have hed : G.ediam = 2 :=
    (ENat.toNat_eq_iff (by decide : (2 : ℕ) ≠ 0)).mp hdiam
  let branch (u : V) := insert u ((G.neighborFinset u).erase r)
  have hcover : (Finset.univ : Finset V) ⊆ insert r ((G.neighborFinset r).biUnion branch) := by
    intro v _
    by_cases hvr : v = r
    · exact Finset.mem_insert.mpr (Or.inl hvr)
    apply Finset.mem_insert_of_mem
    by_cases hadj : G.Adj r v
    · exact Finset.mem_biUnion.mpr
        ⟨v, (G.mem_neighborFinset r v).mpr hadj, Finset.mem_insert_self _ _⟩
    have hdist : G.edist r v ≤ 2 := hed ▸ edist_le_ediam
    have hcommon : (G.commonNeighbors r v).Nonempty := by
      by_contra h
      exact (not_lt_of_ge hdist) (two_lt_edist_iff.mpr
        ⟨Ne.symm hvr, hadj, Set.not_nonempty_iff_eq_empty.mp h⟩)
    obtain ⟨u, hu⟩ := hcommon
    obtain ⟨hru, hvu⟩ := G.mem_commonNeighbors.mp hu
    exact Finset.mem_biUnion.mpr
      ⟨u, (G.mem_neighborFinset r u).mpr hru, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hvr, (G.mem_neighborFinset u v).mpr hvu.symm⟩)⟩
  have hbranch (u : V) (hu : u ∈ G.neighborFinset r) : (branch u).card ≤ d := by
    have hur : r ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u r).mpr ((G.mem_neighborFinset r u).mp hu).symm
    have hpos : 0 < (G.neighborFinset u).card := Finset.card_pos.mpr ⟨r, hur⟩
    calc
      (branch u).card ≤ ((G.neighborFinset u).erase r).card + 1 := Finset.card_insert_le _ _
      _ = (G.neighborFinset u).card := by rw [Finset.card_erase_of_mem hur]; omega
      _ ≤ d := hdeg u
  calc
    Fintype.card V = (Finset.univ : Finset V).card := (Finset.card_univ).symm
    _ ≤ (insert r ((G.neighborFinset r).biUnion branch)).card := Finset.card_le_card hcover
    _ ≤ ((G.neighborFinset r).biUnion branch).card + 1 := Finset.card_insert_le _ _
    _ ≤ (G.neighborFinset r).card * d + 1 :=
      Nat.add_le_add_right (Finset.card_biUnion_le_card_mul _ _ _ hbranch) 1
    _ ≤ d ^ 2 + 1 := by
      rw [pow_two]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hdeg r)) _

open scoped Classical in
lemma diameterTwoDegreeSet_nonempty (n : ℕ) (hn : 3 ≤ n) :
    {d : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
      ∀ v, G.degree v ≤ d}.Nonempty := by
  classical
  let r : Fin n := ⟨0, by omega⟩
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨2, by omega⟩
  have ha : a ≠ r := by simp [Fin.ext_iff, a, r]
  have hb : b ≠ r := by simp [Fin.ext_iff, b, r]
  have hab : a ≠ b := by simp [Fin.ext_iff, a, b]
  let G := starGraph r
  have hr : G.eccent r ≤ 1 := (eccent_le_one_iff r).mpr
    (fun _ h => starGraph_center_adj h)
  have hup : G.ediam ≤ 2 := by
    calc
      G.ediam ≤ 2 * G.eccent r := ediam_le_two_mul_eccent r
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := by simp
  have hdist : G.edist a b = 2 := by
    apply edist_eq_two_iff.mpr
    refine ⟨hab, ?_, ⟨r, G.mem_commonNeighbors.mpr ⟨starGraph_center_adj' ha.symm,
      starGraph_center_adj' hb.symm⟩⟩⟩
    simp [G, ha, hb]
  have hlo : 2 ≤ G.ediam := by
    rw [← hdist]
    exact edist_le_ediam
  have hdiam : G.diam = 2 := by
    rw [SimpleGraph.diam, le_antisymm hup hlo]
    rfl
  refine ⟨n, G, (isAcyclic_starGraph r).cliqueFree (by decide), hdiam, ?_⟩
  intro v
  letI : DecidableRel G.Adj := fun u w => Classical.propDecidable (G.Adj u w)
  exact Nat.le_of_lt (by simpa using G.degree_lt_card_verts v)

lemma minimumDegreeSqBound (n : ℕ) (hn : 3 ≤ n) :
    n ≤ (Erdos133.f n) ^ 2 + 1 := by
  classical
  let S : Set ℕ := {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧
    ∀ v, G.degree v ≤ d}
  have hmem : sInf S ∈ S := Nat.sInf_mem (diameterTwoDegreeSet_nonempty n hn)
  obtain ⟨G, _, hdiam, hdeg⟩ := hmem
  let r : Fin n := ⟨0, by omega⟩
  have h := diameterTwoCardBound G r (sInf S) hdiam hdeg
  change n ≤ (sInf S) ^ 2 + 1
  simpa only [Fintype.card_fin] using h

end OMA

theorem OMA.solution : OMA.R_Erdos133_erdos_133_variants_asymptotic_R1.H1 := by
  unfold OMA.R_Erdos133_erdos_133_variants_asymptotic_R1.H1
  intro ε hε
  by_cases hε₁ : 1 ≤ ε
  · exact Filter.Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hε₁) (Real.sqrt_nonneg _)).trans
        (Nat.cast_nonneg _)
  have hfactor : 0 ≤ 1 - ε := sub_nonneg.mpr (le_of_not_ge hε₁)
  have hfactorSq : (1 - ε) ^ 2 ≤ 1 - ε := by
    calc
      (1 - ε) ^ 2 = (1 - ε) * (1 - ε) := pow_two _
      _ ≤ 1 * (1 - ε) := mul_le_mul_of_nonneg_right (by linarith) hfactor
      _ = 1 - ε := one_mul _
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / ε)
  filter_upwards [eventually_ge_atTop (3 : ℕ), eventually_ge_atTop N] with n hn hnN
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hmul : 1 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp (hN.trans hNn)
  have hcount : (n : ℝ) ≤ (Erdos133.f n : ℝ) ^ 2 + 1 := by
    exact_mod_cast OMA.minimumDegreeSqBound n hn
  have hsq : ((1 - ε) * Real.sqrt (n : ℝ)) ^ 2 ≤ (Erdos133.f n : ℝ) ^ 2 := by
    calc
      _ = (1 - ε) ^ 2 * (n : ℝ) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      _ ≤ (1 - ε) * (n : ℝ) := mul_le_mul_of_nonneg_right hfactorSq (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith only [hcount, hmul]
  exact (sq_le_sq₀ (mul_nonneg hfactor (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)).mp hsq