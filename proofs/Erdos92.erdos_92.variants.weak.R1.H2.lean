import OMAReductions.R_Erdos92_erdos_92_variants_weak_R1
import Mathlib

/-! Peeling bound. Credit: the lemmas neighbors_le_f_exists, directedEdges_erase_bound,
directedEdges_le and unitDistNum_le are reused verbatim (namespace renamed) from the merged
proof proofs/Erdos92.erdos_92.variants.strong.lean by @Halldon (PR #3396). Some point has at
most f |P| unit neighbours; removing it and inducting bounds the directed unit-distance edges
by 2 |P| D, and each unordered unit distance gives a directed edge. -/

open Filter Finset
open scoped EuclideanGeometry Topology

namespace OMA.P2bErdos92Bridge

abbrev Point := EuclideanSpace ℝ (Fin 2)

private noncomputable def neighbors (P : Finset Point) (x : Point) : Finset Point :=
  (P.erase x).filter fun y => dist x y = 1

private noncomputable def directedEdges (P : Finset Point) : Finset (Point × Point) :=
  P.offDiag.filter fun e => dist e.1 e.2 = 1

private theorem neighbors_le_f_exists {P : Finset Point} (hP : P.Nonempty) :
    ∃ x ∈ P, (neighbors P x).card ≤ Erdos92.f P.card := by
  classical
  by_contra! h
  have hproperty : Erdos92.hasMinEquidistantProperty (Erdos92.f P.card + 1) P := by
    refine ⟨hP, fun x hx => (Nat.succ_le_of_lt (h x hx)).trans ?_⟩
    have hnon : (neighbors P x).Nonempty :=
      Finset.card_pos.mp (Nat.zero_lt_of_lt (h x hx))
    obtain ⟨y, hy⟩ := hnon
    have hy₁ := Finset.mem_filter.mp hy
    have hmem : 1 ∈ (P.erase x).image (dist x) :=
      Finset.mem_image.mpr ⟨y, hy₁.1, hy₁.2⟩
    unfold Erdos92.maxEquidistantPointsAt
    refine le_csSup ?_ ?_
    · refine ⟨P.card, ?_⟩
      intro k hk
      change k ∈ ((P.erase x).image (dist x)).image
        (fun d => ((P.erase x).filter fun p => dist x p = d).card) at hk
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.card_filter_le _ _).trans Finset.card_erase_le
    · exact Finset.mem_image.mpr ⟨1, hmem, rfl⟩
  have hf : Erdos92.f P.card + 1 ≤ Erdos92.f P.card :=
    le_csSup (Erdos92.possible_f_values_BddAbove P.card) ⟨P, rfl, hproperty⟩
  omega

private theorem directedEdges_erase_bound {P : Finset Point} (x : Point) :
    (directedEdges P).card ≤ (directedEdges (P.erase x)).card + 2 * (neighbors P x).card := by
  classical
  let L := (neighbors P x).image fun y => (x, y)
  let R := (neighbors P x).image fun y => (y, x)
  have hsub : directedEdges P ⊆ (directedEdges (P.erase x) ∪ L) ∪ R := by
    rintro ⟨y, z⟩ he
    obtain ⟨hpair, hdist⟩ := Finset.mem_filter.mp he
    obtain ⟨hy, hz, hne⟩ := Finset.mem_offDiag.mp hpair
    by_cases hxy : y = x
    · subst y
      exact Finset.mem_union_left R (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hne.symm, hz⟩, hdist⟩, rfl⟩))
    by_cases hxz : z = x
    · subst z
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hxy, hy⟩, by simpa [dist_comm] using hdist⟩, rfl⟩)
    · exact Finset.mem_union_left R (Finset.mem_union_left L (Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr
          ⟨Finset.mem_erase.mpr ⟨hxy, hy⟩, Finset.mem_erase.mpr ⟨hxz, hz⟩, hne⟩, hdist⟩))
  have hL : L.card ≤ (neighbors P x).card := Finset.card_image_le
  have hR : R.card ≤ (neighbors P x).card := Finset.card_image_le
  calc
    _ ≤ ((directedEdges (P.erase x) ∪ L) ∪ R).card := Finset.card_le_card hsub
    _ ≤ (directedEdges (P.erase x) ∪ L).card + R.card := Finset.card_union_le _ _
    _ ≤ (directedEdges (P.erase x)).card + L.card + R.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := by omega

theorem directedEdges_le (P : Finset Point) (D : ℝ)
    (hD : ∀ m ≤ P.card, (Erdos92.f m : ℝ) ≤ D) :
    ((directedEdges P).card : ℝ) ≤ 2 * (P.card : ℝ) * D := by
  classical
  revert hD
  refine Finset.strongInductionOn P ?_
  intro P ih hD
  by_cases hp : P.Nonempty
  · obtain ⟨x, hx, hdeg⟩ := neighbors_le_f_exists hp
    have hlt : P.erase x ⊂ P := Finset.erase_ssubset hx
    have hstep := ih (P.erase x) hlt
      (fun m hm => hD m (hm.trans Finset.card_erase_le))
    have hbound : ((neighbors P x).card : ℝ) ≤ D :=
      (by exact_mod_cast hdeg : ((neighbors P x).card : ℝ) ≤ (Erdos92.f P.card : ℝ)).trans
        (hD P.card le_rfl)
    have hcount : ((directedEdges P).card : ℝ) ≤
        ((directedEdges (P.erase x)).card : ℝ) + 2 * ((neighbors P x).card : ℝ) := by
      exact_mod_cast directedEdges_erase_bound x (P := P)
    have hcard : ((P.erase x).card : ℝ) + 1 = (P.card : ℝ) := by
      rw [Finset.card_erase_of_mem hx]
      exact_mod_cast (Nat.sub_add_cancel (Finset.card_pos.mpr hp))
    calc
      _ ≤ _ := hcount
      _ ≤ 2 * ((P.erase x).card : ℝ) * D + 2 * D := by linarith
      _ = 2 * (((P.erase x).card : ℝ) + 1) * D := by ring
      _ = _ := by rw [hcard]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp]
    simp [directedEdges]

theorem unitDistNum_le (P : Finset Point) : unitDistNum P ≤ (directedEdges P).card := by
  classical
  unfold unitDistNum
  refine Finset.card_le_card_of_injOn (fun z : Sym2 Point => z.out) ?_ ?_
  · intro z hz
    obtain ⟨hzP, hzD⟩ := Finset.mem_filter.mp hz
    have he : s(z.out.1, z.out.2) = z := Quot.out_eq z
    have hxy := Finset.mk_mem_sym2_iff.mp (by rwa [he] :
      s(z.out.1, z.out.2) ∈ P.sym2)
    have hne : z.out.1 ≠ z.out.2 := by
      intro h
      simp [h] at hzD
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hxy.1, hxy.2, hne⟩, hzD⟩
  · intro a _ b _ h
    change a.out = b.out at h
    calc
      a = s(a.out.1, a.out.2) := (Quot.out_eq a).symm
      _ = s(b.out.1, b.out.2) := by rw [h]
      _ = b := Quot.out_eq b

end OMA.P2bErdos92Bridge

theorem OMA.solution : OMA.R_Erdos92_erdos_92_variants_weak_R1.H2 := by
  unfold OMA.R_Erdos92_erdos_92_variants_weak_R1.H2
  intro P D hD
  have hu : (unitDistNum P : ℝ) ≤ ((OMA.P2bErdos92Bridge.directedEdges P).card : ℝ) := by
    exact_mod_cast OMA.P2bErdos92Bridge.unitDistNum_le P
  exact hu.trans (OMA.P2bErdos92Bridge.directedEdges_le P D hD)
