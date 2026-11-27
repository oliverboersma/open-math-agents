import OMAStatements.S_arxiv_2003_13166

open DihedralGroup

namespace OMADisproofAux

abbrev D := DihedralGroup 9

def Sf : Finset D := {sr 0, sr 1, sr 3}

def Uf : Finset D := {r 0, r 1, r 3, r 4, r 7, sr 0, sr 2, sr 5, sr 6, sr 8}

lemma key : ∀ u ∈ Uf, (Uf.filter fun v => u ≠ v ∧
    ((∃ s ∈ Sf, v = s * u) ∨ (∃ s ∈ Sf, u = s * v))).card ≤ 1 := by
  decide

lemma closure_top : Subgroup.closure (Sf : Set D) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  have h0 : (sr 0 : D) ∈ Subgroup.closure (Sf : Set D) :=
    Subgroup.subset_closure (by simp [Sf])
  have h1 : (sr 1 : D) ∈ Subgroup.closure (Sf : Set D) :=
    Subgroup.subset_closure (by simp [Sf])
  have hr1 : (r 1 : D) ∈ Subgroup.closure (Sf : Set D) := by
    have : (r 1 : D) = sr 0 * sr 1 := by simp
    rw [this]; exact Subgroup.mul_mem _ h0 h1
  have hr : ∀ i : ZMod 9, (r i : D) ∈ Subgroup.closure (Sf : Set D) := by
    intro i
    rw [← ZMod.natCast_zmod_val i, ← r_one_pow]
    exact Subgroup.pow_mem _ hr1 _
  intro g
  cases g with
  | r i => exact hr i
  | sr i =>
    have : (sr i : D) = sr 0 * r i := by simp
    rw [this]; exact Subgroup.mul_mem _ h0 (hr i)

end OMADisproofAux

open OMADisproofAux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2003_13166.main) := by
  intro h
  have hS1 : (1 : D) ∉ (Sf : Set D) := by
    simp only [Finset.mem_coe]; decide
  have hSinv : ∀ s ∈ (Sf : Set D), s⁻¹ ∈ (Sf : Set D) := by
    simp only [Finset.mem_coe]; decide
  have hU : Nat.card D < 2 * (Uf : Set D).ncard := by
    rw [Set.ncard_coe_finset, Nat.card_eq_fintype_card]; decide
  obtain ⟨u, hu, hle⟩ := h D (Sf : Set D) hS1 hSinv closure_top (Uf : Set D) hU
  rw [Set.ncard_coe_finset] at hle
  have hSc : Sf.card = 3 := by decide
  have hset : {v | v ∈ (Uf : Set D) ∧ (OMA.S_arxiv_2003_13166.cayley (Sf : Set D)).Adj u v} =
      ↑(Uf.filter fun v => u ≠ v ∧
        ((∃ s ∈ Sf, v = s * u) ∨ (∃ s ∈ Sf, u = s * v))) := by
    ext v
    simp [OMA.S_arxiv_2003_13166.cayley, SimpleGraph.fromRel_adj]
  rw [hset, Set.ncard_coe_finset, hSc] at hle
  have hk := key u hu
  have hk' : ((Uf.filter fun v => u ≠ v ∧
        ((∃ s ∈ Sf, v = s * u) ∨ (∃ s ∈ Sf, u = s * v))).card : ℝ) ≤ 1 := by
    exact_mod_cast hk
  have hsq : (1 : ℝ) < Real.sqrt ((3 : ℕ) / 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith
