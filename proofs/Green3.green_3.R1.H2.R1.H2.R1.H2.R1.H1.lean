import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1

-- Step Green3.green_3.R1.H2.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Green3.green_3.R1.H2.R1.H2.R1.H2.R1

/-!
The three sets `T ∩ [a, u + 2a)`, `(T ∩ [a, u + a)) + e` and `(T ∩ [a, u]) + (d + e)` are pairwise
disjoint and all lie in `[a, u + 2a)`, an interval with `u + a` elements. Since `u ∈ T`, the
third set has one element more than `T ∩ [a, u)`.
-/

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.H1 := by
  unfold OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.H1
  intro T a u d e hT hu he hde h1 h2 h3
  have hAB : Disjoint (T.filter (fun x => x < u + 2 * a))
      ((T.filter (fun x => x < u + a)).image (fun x => x + e)) := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz2
    obtain ⟨hxT, hxlt⟩ := Finset.mem_filter.1 hx
    have hzT : z ∈ T := (Finset.mem_filter.1 hz).1
    have hxz2 : x + e = z := hxz
    rw [← hxz2] at hzT
    exact h2 x hxT hxlt hzT
  have hAC : Disjoint (T.filter (fun x => x < u + 2 * a))
      ((T.filter (fun x => x ≤ u)).image (fun x => x + (d + e))) := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz2
    obtain ⟨hxT, hxle⟩ := Finset.mem_filter.1 hx
    have hzT : z ∈ T := (Finset.mem_filter.1 hz).1
    have hxz2 : x + (d + e) = z := hxz
    rw [← hxz2] at hzT
    exact h3 x hxT hxle hzT
  have hBC : Disjoint ((T.filter (fun x => x < u + a)).image (fun x => x + e))
      ((T.filter (fun x => x ≤ u)).image (fun x => x + (d + e))) := by
    rw [Finset.disjoint_left]
    intro z hz hz2
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 hz2
    obtain ⟨hxT, _⟩ := Finset.mem_filter.1 hx
    obtain ⟨hyT, hyle⟩ := Finset.mem_filter.1 hy
    have hxz2 : x + e = z := hxz
    have hyz2 : y + (d + e) = z := hyz
    have hxy : x = y + d := by omega
    rw [hxy] at hxT
    exact h1 y hyT hyle hxT
  have hsub : (T.filter (fun x => x < u + 2 * a) ∪
      (T.filter (fun x => x < u + a)).image (fun x => x + e)) ∪
      (T.filter (fun x => x ≤ u)).image (fun x => x + (d + e)) ⊆ Finset.Ico a (u + 2 * a) := by
    intro z hz
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.1 hz with hz1 | hz3
    · rcases Finset.mem_union.1 hz1 with hzA | hzB
      · obtain ⟨hzT, hzlt⟩ := Finset.mem_filter.1 hzA
        exact ⟨hT z hzT, hzlt⟩
      · obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hzB
        obtain ⟨hxT, hxlt⟩ := Finset.mem_filter.1 hx
        have hxz2 : x + e = z := hxz
        have := hT x hxT
        omega
    · obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz3
      obtain ⟨hxT, hxle⟩ := Finset.mem_filter.1 hx
      have hxz2 : x + (d + e) = z := hxz
      have := hT x hxT
      omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico, Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨hAC, hBC⟩),
    Finset.card_union_of_disjoint hAB,
    Finset.card_image_of_injective _ (add_left_injective e),
    Finset.card_image_of_injective _ (add_left_injective (d + e))] at hcard
  have hlt : (T.filter (fun x => x < u)).card < (T.filter (fun x => x ≤ u)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨u, Finset.mem_filter.2 ⟨hu, le_refl u⟩, fun h => lt_irrefl u (Finset.mem_filter.1 h).2⟩
    · intro x hx
      obtain ⟨hxT, hxlt⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hxT, hxlt.le⟩
  omega
