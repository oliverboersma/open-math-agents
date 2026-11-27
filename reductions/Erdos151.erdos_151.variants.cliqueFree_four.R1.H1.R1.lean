import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1
import Mathlib

/-! Upgrading the degeneracy threshold of Erdos 151 (K_4-free) from 6 to 7.
Every 7-degenerate K_4-free graph admits a red-blue edge coloring with no
monochromatic triangle via Bikov's 7-vertex link extension lemma (H2), which
immediately yields cliqueTransversalNumber G <= n - H n. The remaining open
core (H1) has maximum degree < H n and an induced subgraph of minimum degree
at least 8 (pushing the resolved threshold to n <= 35 via R(3,9) = 36). -/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1

/-- Remaining core: K_4-free graphs with maximum degree < H n and an induced
subgraph of minimum degree at least 8. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v ∈ S, 8 ≤ (S.filter (G.Adj v)).card) →
    cliqueTransversalNumber G ≤ n - Erdos151.H n

/-- Bikov's 7-vertex link extension: any symmetric 2-coloring of the edges of a
triangle-free graph on at most 7 vertices extends over a new universal vertex
without creating a monochromatic triangle. -/
def H2 : Prop :=
  ∀ (k : ℕ) (L : SimpleGraph (Fin k)), k ≤ 7 → L.CliqueFree 3 →
    ∀ c : Fin k → Fin k → Bool, (∀ x y, c x y = c y x) →
      ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y)

section Proof

private theorem H_attained {n : ℕ} (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    intro G _
    exact ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hmem : Erdos151.H n ∈ sizes := hnonempty.csSup_mem hfinite
  exact hmem F hF

private theorem edge_coloring_7 (h2 : H2) {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 4)
    (hdegree : ∀ S : Finset (Fin n), S.Nonempty →
      ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 7) :
    ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
      ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
        ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b) := by
  classical
  have aux : ∀ S : Finset (Fin n),
      ∃ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) ∧
        ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G.Adj x y → G.Adj x z → G.Adj y z →
          ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b) := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      swap
      · exact ⟨fun _ _ => false, fun _ _ => rfl,
          fun x hx => (hS ⟨x, hx⟩).elim⟩
      obtain ⟨v, hv, hdeg⟩ := hdegree S hS
      have hproper : S.erase v ⊂ S := erase_ssubset hv
      obtain ⟨c, hcs, hc⟩ := ih (S.erase v) hproper
      let N := (S.erase v).filter (G.Adj v)
      let e := Fintype.equivFin (↥N)
      let f (i : Fin (Fintype.card (↥N))) : Fin n := (e.symm i).val
      let L := G.comap f
      have hf (i : Fin (Fintype.card (↥N))) : G.Adj v (f i) :=
        (mem_filter.mp (e.symm i).property).2
      have hL : L.CliqueFree 3 := by
        intro t ht
        obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
        have hcl : G.IsNClique 3 {f x, f y, f z} :=
          is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩
        apply hG _ (hcl.insert (a := v) ?_)
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        all_goals exact hf _
      have hNc : Fintype.card (↥N) ≤ 7 := by
        rw [Fintype.card_coe]
        exact (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans hdeg
      obtain ⟨d, hd⟩ := h2 _ L hNc hL (fun x y => c (f x) (f y)) (fun _ _ => hcs _ _)
      let p (x : Fin n) : Bool := if hx : x ∈ N then d (e ⟨x, hx⟩) else false
      let c' (x y : Fin n) : Bool := if x = v then p y else if y = v then p x else c x y
      have hcs' (x y : Fin n) : c' x y = c' y x := by
        by_cases hx : x = v <;> by_cases hy : y = v
        · simp [hx, hy]
        · simp [c', hx, hy]
        · simp [c', hx, hy]
        · simp [c', hx, hy, hcs]
      have hAt {y z : Fin n} (hy : y ∈ S) (hz : z ∈ S)
          (hvy : G.Adj v y) (hvz : G.Adj v z) (hyz : G.Adj y z) (b : Bool) :
          ¬ (c' v y = b ∧ c' v z = b ∧ c' y z = b) := by
        have hyv := hvy.ne.symm
        have hzv := hvz.ne.symm
        have hyN : y ∈ N := mem_filter.mpr ⟨mem_erase.mpr ⟨hyv, hy⟩, hvy⟩
        have hzN : z ∈ N := mem_filter.mpr ⟨mem_erase.mpr ⟨hzv, hz⟩, hvz⟩
        have hfId (x : ↥N) : f (e x) = (x : Fin n) := by simp [f]
        have hAdj : L.Adj (e ⟨y, hyN⟩) (e ⟨z, hzN⟩) := by
          change G.Adj (f (e ⟨y, hyN⟩)) (f (e ⟨z, hzN⟩))
          simpa only [hfId] using hyz
        have hD := hd _ _ hAdj
        simp only [hfId] at hD
        rintro ⟨h₁, h₂, h₃⟩
        simp only [c', if_pos rfl, p, dif_pos hyN, dif_pos hzN, if_neg hyv, if_neg hzv] at h₁ h₂ h₃
        exact hD ⟨h₁.trans h₃.symm, h₂.trans h₃.symm⟩
      refine ⟨c', hcs', ?_⟩
      intro x hx y hy z hz hxy hxz hyz b h
      by_cases hxv : x = v
      · subst x
        exact hAt hy hz hxy hxz hyz b h
      by_cases hyv : y = v
      · subst y
        exact hAt hx hz hxy.symm hyz hxz b
          ⟨(hcs' _ _).trans h.1, h.2.2, h.2.1⟩
      by_cases hzv : z = v
      · subst z
        exact hAt hx hy hxz.symm hyz.symm hxy b
          ⟨(hcs' _ _).trans h.2.1, (hcs' _ _).trans h.2.2, h.1⟩
      simp only [c', if_neg hxv, if_neg hyv, if_neg hzv] at h
      exact hc x (mem_erase.mpr ⟨hxv, hx⟩) y (mem_erase.mpr ⟨hyv, hy⟩)
        z (mem_erase.mpr ⟨hzv, hz⟩) hxy hxz hyz b h
  obtain ⟨c, hs, hc⟩ := aux univ
  exact ⟨c, hs, fun x y z => hc x (mem_univ _) y (mem_univ _) z (mem_univ _)⟩

private theorem transversal_of_edge_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Bool) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ∀ b, ¬ (c x y = b ∧ c x z = b ∧ c y z = b)) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  let F : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ (c x y = true ∨ ¬ ∃ w, G.Adj x w ∧ G.Adj y w)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl ((hs _ _).trans h))
      (fun h => Or.inr (fun ⟨w, hw, hw'⟩ => h ⟨w, hw', hw⟩))⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hF : F.CliqueFree 3 := by
    intro t h
    obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.mp h
    exact hc x y z hxy.1 hxz.1 hyz.1 true
      ⟨hxy.2.resolve_right (fun h => h ⟨z, hxz.1, hyz.1⟩),
        hxz.2.resolve_right (fun h => h ⟨y, hxy.1, hyz.1.symm⟩),
        hyz.2.resolve_right (fun h => h ⟨x, hxy.1.symm, hxz.1.symm⟩)⟩
  obtain ⟨I, hI⟩ := H_attained F hF
  have hhit : G.IsCliqueTransversal Iᶜ := by
    intro t ht
    by_contra! h
    have hIn {x : Fin n} (hx : x ∈ t) : x ∈ I := by simpa using h x hx
    have hNo {x y : Fin n} (hx : x ∈ t) (hy : y ∈ t) (hxy : G.Adj x y) :
        c x y = false := by
      cases hb : c x y
      · rfl
      · exact (hI.isIndepSet (hIn hx) (hIn hy) hxy.ne ⟨hxy, Or.inl hb⟩).elim
    have hNotThree : t.card < 3 := by
      by_contra! hLarge
      obtain ⟨u, hu, huC⟩ := exists_subset_card_eq hLarge
      have hClique : G.IsNClique 3 u :=
        ⟨fun _ hx _ hy hxy => ht.1.1 (hu hx) (hu hy) hxy, huC⟩
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hClique
      have hx : x ∈ t := hu (by simp)
      have hy : y ∈ t := hu (by simp)
      have hz : z ∈ t := hu (by simp)
      exact hc x y z hxy hxz hyz false ⟨hNo hx hy hxy, hNo hx hz hxz, hNo hy hz hyz⟩
    have hTwo : t.card = 2 := by have := ht.2; omega
    obtain ⟨x, y, hxy, htxy⟩ := card_eq_two.mp hTwo
    have hx : x ∈ t := by simp [htxy]
    have hy : y ∈ t := by simp [htxy]
    have hAdj := ht.1.1 hx hy hxy
    have hN : ¬ ∃ w, G.Adj x w ∧ G.Adj y w := by
      rintro ⟨w, hwx, hwy⟩
      have hSub : G.IsClique (↑(insert w t) : Set (Fin n)) := by
        rw [coe_insert]
        apply ht.1.1.insert
        intro u hu _
        have : u = x ∨ u = y := by simpa [htxy] using hu
        exact this.elim (fun h => h ▸ hwx.symm) (fun h => h ▸ hwy.symm)
      have hwMem : w ∈ t := ht.1.2 hSub (subset_insert _ _) (mem_insert_self _ _)
      have : w = x ∨ w = y := by simpa [htxy] using hwMem
      exact this.elim hwx.ne.symm hwy.ne.symm
    exact hI.isIndepSet (hIn hx) (hIn hy) hxy ⟨hAdj, Or.inr hN⟩
  apply csInf_le'
  exact ⟨Iᶜ, hhit, by rw [card_compl, Fintype.card_fin, hI.card_eq]⟩

theorem main : H1 → H2 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1.H1 := by
  intro h1 h2 n G hG hMax _
  by_cases hCore : ∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v ∈ S, 8 ≤ (S.filter (G.Adj v)).card
  · exact h1 n G hG hMax hCore
  have hDeg (S : Finset (Fin n)) (hS : S.Nonempty) :
      ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 7 := by
    by_contra! h
    exact hCore ⟨S, hS, fun v hv => by have := h v hv; omega⟩
  obtain ⟨c, hs, hc⟩ := edge_coloring_7 h2 hG hDeg
  exact transversal_of_edge_coloring G c hs hc

end Proof

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1
