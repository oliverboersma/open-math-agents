import OMAReductions.R_Erdos827_erdos_827_variants_n_five_le_R1
import Mathlib

-- Step Erdos827.erdos_827.variants.n_five_le.R1.H1: hypothesis H1 of reduction
-- Erdos827.erdos_827.variants.n_five_le.R1
-- Credit: @ivillar
--
-- REUSE. The lemmas two_distances, radius_unique_at_insert, three_insert_impossible and
-- radius_unique below are taken unchanged from the merged proof
-- proofs/Erdos827.erdos_827.variants.martinez_roldan_pensado.lean by @Genbox (PR #1550).

/-!
Three non-collinear points are affinely independent, so they lie on a circle
(`AffineIndependent.existsUnique_dist_eq`); its radius is unique (`radius_unique`), so the chosen
radius `c T` satisfies `c T = r ↔ OnCircleOfRadius T r`. With no four points concyclic, at most two
third points complete a fixed chord to a triangle of a given radius (`three_insert_impossible`).
-/

open Erdos827 EuclideanGeometry Finset

namespace OMA.Erdos827FiveH1

private theorem two_distances {a b c d e : ℝ²} {r s : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : dist c a = r) (hb : dist d a = r) (he : dist e a = r)
    (ha' : dist c b = s) (hb' : dist d b = s) (he' : dist e b = s) :
    e = c ∨ e = d :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hab hcd ha hb he ha' hb' he'

private theorem radius_unique_at_insert {E : Finset ℝ²} (hE : E.card = 2)
    {x : ℝ²} (hx : x ∉ E) {r s : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert x E) s) :
    r = s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have hax : a ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hbx : b ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hxx : x ∈ (insert x {a, b} : Finset ℝ²) := by simp
  by_cases he : c = d
  · exact (hc x hxx).symm.trans (he ▸ hd x hxx)
  · exact False.elim (hx (by
      rcases two_distances he hab (hc a hax) (hc b hbx) (hc x hxx)
        (hd a hax) (hd b hbx) (hd x hxx) with h | h <;> simp [h]))

private theorem three_insert_impossible {X E : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hEX : E ⊆ X) (hE : E.card = 2)
    {x y z : ℝ²} (hxX : x ∈ X) (hyX : y ∈ X) (hzX : z ∈ X)
    (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert y E) r)
    (h₃ : OnCircleOfRadius (insert z E) r) : False := by
  classical
  have centers_ne {u v c : ℝ²} (huX : u ∈ X) (hvX : v ∈ X)
      (hu : u ∉ E) (hv : v ∉ E) (huv : u ≠ v)
      (huc : ∀ w ∈ insert u E, dist w c = r)
      (hvc : ∀ w ∈ insert v E, dist w c = r) : False := by
    apply hX (↑(insert u (insert v E)) : Set ℝ²)
    · intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huX
      · obtain rfl | hw := Finset.mem_insert.mp hw
        · exact hvX
        · exact hEX hw
    · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [huv, hu]),
        Finset.card_insert_of_notMem hv, hE]
    · refine ⟨c, r, ?_⟩
      intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huc _ (Finset.mem_insert_self ..)
      · exact hvc w hw
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨e, he⟩ := h₃
  have hcd : c ≠ d := fun hh => centers_ne hxX hyX hx hy hxy hc (hh ▸ hd)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  have ha (w : ℝ²) : a ∈ (insert w {a, b} : Finset ℝ²) := by simp
  have hb (w : ℝ²) : b ∈ (insert w {a, b} : Finset ℝ²) := by simp
  obtain h | h := two_distances hab hcd
    ((dist_comm _ _).trans (hc a (ha x))) ((dist_comm _ _).trans (hd a (ha y)))
    ((dist_comm _ _).trans (he a (ha z))) ((dist_comm _ _).trans (hc b (hb x)))
    ((dist_comm _ _).trans (hd b (hb y))) ((dist_comm _ _).trans (he b (hb z)))
  · exact centers_ne hxX hzX hx hz hxz hc (h ▸ he)
  · exact centers_ne hyX hzX hy hz hyz hd (h ▸ he)

private theorem radius_unique {T : Finset ℝ²} (hT : T.card = 3) {r s : ℝ}
    (hr : OnCircleOfRadius T r) (hs : OnCircleOfRadius T s) : r = s := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hE : (T.erase p).card = 2 := by
    have := Finset.card_erase_add_one hp
    omega
  exact radius_unique_at_insert hE (notMem_erase p T)
    (by simpa [insert_erase hp] using hr) (by simpa [insert_erase hp] using hs)

private theorem exists_radius {X : Finset ℝ²} (hX : NonTrilinear (X : Set ℝ²)) {T : Finset ℝ²}
    (hT : T ⊆ X) (h3 : T.card = 3) : ∃ r, OnCircleOfRadius T r := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  have hcol : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
    hX (hT (by simp)) (hT (by simp)) (hT (by simp)) hab hbc hac
  have hind : AffineIndependent ℝ ![a, b, c] := affineIndependent_iff_not_collinear_set.mpr hcol
  obtain ⟨cs, ⟨_, hcs⟩, _⟩ := hind.existsUnique_dist_eq
  refine ⟨cs.radius, cs.center, fun p hp => ?_⟩
  have hp' : p ∈ Set.range ![a, b, c] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  exact EuclideanGeometry.mem_sphere.mp (hcs hp')

end OMA.Erdos827FiveH1

open Erdos827 EuclideanGeometry Finset OMA.Erdos827FiveH1 in
theorem OMA.solution : OMA.R_Erdos827_erdos_827_variants_n_five_le_R1.H1 := by
  unfold OMA.R_Erdos827_erdos_827_variants_n_five_le_R1.H1
  intro X hX
  obtain ⟨hNT, hNF⟩ := hX
  classical
  let c : Finset ℝ² → ℝ := fun T => if h : ∃ r, OnCircleOfRadius T r then h.choose else 0
  have hc : ∀ T ⊆ X, T.card = 3 → OnCircleOfRadius T (c T) := by
    intro T hT h3
    have h := exists_radius hNT hT h3
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨c, ?_, ?_⟩
  · intro T hT h3 r
    constructor
    · rintro rfl
      exact hc T hT h3
    · intro hr
      exact radius_unique h3 (hc T hT h3) hr
  · intro B hB h2 r
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hlt
    rw [Finset.mem_filter, Finset.mem_sdiff] at hx hy hz
    have hins (w : ℝ²) (hw : w ∈ X) (hwB : w ∉ B) :
        OnCircleOfRadius (insert w B) (c (insert w B)) :=
      hc _ (Finset.insert_subset hw hB) (by rw [Finset.card_insert_of_notMem hwB, h2])
    have ox := hins x hx.1.1 hx.1.2
    have oy := hins y hy.1.1 hy.1.2
    have oz := hins z hz.1.1 hz.1.2
    rw [hx.2] at ox
    rw [hy.2] at oy
    rw [hz.2] at oz
    exact three_insert_impossible hNF hB h2 hx.1.1 hy.1.1 hz.1.1 hx.1.2 hy.1.2 hz.1.2
      hxy hxz hyz ox oy oz
