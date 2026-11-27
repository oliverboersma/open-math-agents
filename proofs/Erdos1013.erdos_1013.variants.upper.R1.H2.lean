import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1
import Mathlib

/-! Take a triangle-free graph `G` on `n` vertices with the largest chromatic number, which is
at least `k`. Keep only the edges among the first `j` vertices. The chromatic number of these
truncations starts at most `1`, ends at `χ(G) ≥ k`, and grows by at most one per step (colour
the new vertex with a fresh colour), so some truncation has chromatic number exactly `k`. It is
triangle-free, hence `h₃(k) ≤ n`. -/

open SimpleGraph

namespace E1013H2

/-- The edges of `G` among the vertices of index below `j`. -/
def trunc {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u.val < j ∧ v.val < j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

lemma trunc_adj {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) (u v : Fin n) :
    (trunc G j).Adj u v ↔ G.Adj u v ∧ u.val < j ∧ v.val < j := Iff.rfl

lemma trunc_le {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) : trunc G j ≤ G :=
  fun u v h => ((trunc_adj G j u v).mp h).1

lemma trunc_n {n : ℕ} (G : SimpleGraph (Fin n)) : trunc G n = G := by
  ext u v
  rw [trunc_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, u.isLt, v.isLt⟩⟩

lemma colorable_zero {n : ℕ} (G : SimpleGraph (Fin n)) : (trunc G 0).Colorable 1 :=
  ⟨Coloring.mk (fun _ => 0) (fun {u v} h => absurd ((trunc_adj G 0 u v).mp h).2.1 (Nat.not_lt_zero _))⟩

lemma colorable_succ {n c : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ)
    (h : (trunc G j).Colorable c) : (trunc G (j + 1)).Colorable (c + 1) := by
  obtain ⟨C⟩ := h
  refine ⟨Coloring.mk (fun u => if u.val = j then Fin.last c else (C u).castSucc) ?_⟩
  intro u v huv
  obtain ⟨hG, hu, hv⟩ := (trunc_adj G (j + 1) u v).mp huv
  by_cases hu' : u.val = j
  · by_cases hv' : v.val = j
    · exact absurd (Fin.ext (hu'.trans hv'.symm)) (G.ne_of_adj hG)
    · rw [if_pos hu', if_neg hv']
      exact (Fin.castSucc_lt_last _).ne'
  · by_cases hv' : v.val = j
    · rw [if_neg hu', if_pos hv']
      exact (Fin.castSucc_lt_last _).ne
    · rw [if_neg hu', if_neg hv']
      intro heq
      exact C.valid ((trunc_adj G j u v).mpr ⟨hG, by omega, by omega⟩)
        (Fin.castSucc_injective _ heq)

end E1013H2

open E1013H2 in
theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1.H2 := by
  intro n k hk hkS
  set S := {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} with hS
  have hbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro χ ⟨G, _, hG⟩
    have := G.chromaticNumber_le_card
    rw [hG, Fintype.card_fin] at this
    exact_mod_cast this
  have hne : S.Nonempty := by
    have h := (⊥ : SimpleGraph (Fin n)).colorable_of_fintype
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (chromaticNumber_ne_top_iff_exists.mpr ⟨_, h⟩)
    exact ⟨m, ⊥, cliqueFree_bot (by norm_num), hm.symm⟩
  obtain ⟨G, hG3, hGχ⟩ := Nat.sSup_mem hne hbdd
  have hfin : ∀ j, (trunc G j).chromaticNumber = ((trunc G j).chromaticNumber.toNat : ℕ∞) := by
    intro j
    exact (ENat.natCast_toNat (chromaticNumber_ne_top_iff_exists.mpr
      ⟨_, (trunc G j).colorable_of_fintype⟩)).symm
  have hc0 : (trunc G 0).chromaticNumber.toNat ≤ 1 := by
    have h := (colorable_zero G).chromaticNumber_le
    rw [hfin 0] at h
    exact_mod_cast h
  have hcn : k ≤ (trunc G n).chromaticNumber.toNat := by
    rw [trunc_n, hGχ, ENat.toNat_natCast]
    exact hkS
  have hstep : ∀ j, (trunc G (j + 1)).chromaticNumber.toNat ≤
      (trunc G j).chromaticNumber.toNat + 1 := by
    intro j
    have h := (colorable_succ G j
      ((trunc G j).colorable_chromaticNumber_of_fintype)).chromaticNumber_le
    rw [hfin (j + 1)] at h
    exact_mod_cast h
  have hex : ∃ j, k ≤ (trunc G j).chromaticNumber.toNat := ⟨n, hcn⟩
  classical
  have hj0 := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ k ≤ (trunc G m).chromaticNumber.toNat :=
    fun m hm => Nat.find_min hex hm
  set j0 := Nat.find hex with hj0def
  have hj0eq : (trunc G j0).chromaticNumber.toNat = k := by
    rcases Nat.eq_zero_or_pos j0 with h | h
    · rw [h] at hj0 ⊢
      omega
    · have hprev := hmin (j0 - 1) (by omega)
      have := hstep (j0 - 1)
      rw [Nat.sub_add_cancel h] at this
      omega
  have hχ : (trunc G j0).chromaticNumber = (k : ℕ∞) := by
    rw [hfin j0, hj0eq]
  exact Erdos1013.h3_le (trunc G j0) (hG3.anti (trunc_le G j0)) hχ
