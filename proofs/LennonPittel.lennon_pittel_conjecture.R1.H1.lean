import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1
import Mathlib.Order.FixedPoints
import Mathlib.Data.Finset.Max

namespace OMA.StableExistence
open StableMarriage

def manAccept {n : ℕ} (p : Profile n) (Y : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  {e | ∀ w, (e.1, w) ∈ Y → p.manRank e.1 e.2 ≤ p.manRank e.1 w}

def womanAccept {n : ℕ} (p : Profile n) (X : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  {e | ∀ m, (m, e.2) ∈ X → p.womanRank e.2 e.1 ≤ p.womanRank e.2 m}

lemma manAccept_antitone {n : ℕ} (p : Profile n) : Antitone (manAccept p) := by
  intro A B h e he w hw
  exact he w (h hw)

lemma womanAccept_antitone {n : ℕ} (p : Profile n) : Antitone (womanAccept p) := by
  intro A B h e he m hm
  exact he m (h hm)

def acceptanceMap {n : ℕ} (p : Profile n) : Set (Fin n × Fin n) →o Set (Fin n × Fin n) where
  toFun := fun Y => womanAccept p (manAccept p Y)
  monotone' := by
    intro A B h
    exact womanAccept_antitone p (manAccept_antitone p h)

lemma men_unique {n : ℕ} (p : Profile n) (Y : Set (Fin n × Fin n))
    {m w v : Fin n} (hw : (m, w) ∈ manAccept p Y ∩ Y)
    (hv : (m, v) ∈ manAccept p Y ∩ Y) : w = v := by
  exact (p.manRank m).injective (le_antisymm (hw.1 v hv.2) (hv.1 w hw.2))

lemma women_unique {n : ℕ} (p : Profile n) (Y : Set (Fin n × Fin n))
    (hY : Y = womanAccept p (manAccept p Y))
    {m u w : Fin n} (hm : (m, w) ∈ manAccept p Y ∩ Y)
    (hu : (u, w) ∈ manAccept p Y ∩ Y) : m = u := by
  have hmY := hm.2
  have huY := hu.2
  rw [hY] at hmY huY
  exact (p.womanRank w).injective (le_antisymm (hmY u hu.1) (huY m hm.1))

lemma row_nonempty {n : ℕ} (p : Profile n) (Y : Set (Fin n × Fin n)) (m : Fin n)
    (h : ∃ w, (m, w) ∈ Y) : ∃ w, (m, w) ∈ manAccept p Y ∩ Y := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun w => (m, w) ∈ Y
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := h
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨w, hw, hmin⟩ := s.exists_min_image (p.manRank m) hs
  refine ⟨w, ?_, (Finset.mem_filter.mp hw).2⟩
  intro v hv
  exact hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

lemma column_nonempty {n : ℕ} (p : Profile n) (Y : Set (Fin n × Fin n))
    (hY : Y = womanAccept p (manAccept p Y)) (w : Fin n)
    (h : ∃ m, (m, w) ∈ manAccept p Y) : ∃ m, (m, w) ∈ manAccept p Y ∩ Y := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun m => (m, w) ∈ manAccept p Y
  have hs : s.Nonempty := by
    obtain ⟨v, hv⟩ := h
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  obtain ⟨m, hm, hmin⟩ := s.exists_min_image (p.womanRank w) hs
  refine ⟨m, (Finset.mem_filter.mp hm).2, ?_⟩
  rw [hY]
  intro u hu
  exact hmin u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)

lemma exists_stable {n : ℕ} (p : Profile n) : ∃ μ : Matching n, IsStable p μ := by
  classical
  let Y := (acceptanceMap p).lfp
  have hY : Y = womanAccept p (manAccept p Y) := (acceptanceMap p).map_lfp.symm
  let M := manAccept p Y ∩ Y
  have hmatch : ∀ m, ∃ w, (m, w) ∈ M := by
    intro m
    by_contra hm
    have hno : ∀ w, (m, w) ∉ Y := by
      intro w hw
      exact hm (row_nonempty p Y m ⟨w, hw⟩)
    have hx : ∀ w, (m, w) ∈ manAccept p Y := by
      intro w v hv
      exact False.elim (hno v hv)
    have hw : ∀ w, ∃ u, (u, w) ∈ M := fun w => column_nonempty p Y hY w ⟨m, hx w⟩
    choose husband hHusband using hw
    have hinj : Function.Injective husband := by
      intro w v heq
      apply men_unique p Y (hHusband w)
      simpa only [heq] using hHusband v
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
    apply hm
    refine ⟨w, ?_⟩
    simpa only [hw] using hHusband w
  choose wife hWife using hmatch
  have hinj : Function.Injective wife := by
    intro m u heq
    apply women_unique p Y hY (hWife m)
    simpa only [heq] using hWife u
  let μ : Matching n := Equiv.ofBijective wife hinj.bijective_of_finite
  have hμ : ∀ m, (m, μ m) ∈ manAccept p Y ∩ Y := hWife
  refine ⟨μ, ?_⟩
  intro m w ⟨_, hm, hw⟩
  have hx : (m, w) ∈ manAccept p Y := by
    intro v hv
    exact hm.le.trans ((hμ m).1 v hv)
  have hg : (μ.symm w, w) ∈ womanAccept p (manAccept p Y) := by
    have hh := (hμ (μ.symm w)).2
    rw [μ.apply_symm_apply, hY] at hh
    exact hh
  exact (not_lt_of_ge (hg m hx)) hw

theorem count_pos {n : ℕ} (p : Profile n) : 0 < numStableMatchings p := by
  classical
  change 0 < Fintype.card {μ : Matching n // IsStable p μ}
  obtain ⟨μ, hμ⟩ := exists_stable p
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩

end OMA.StableExistence

-- Known stable-marriage existence theorem, completing only H1.
-- Credit: @harshshah1618
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  intro n p
  exact OMA.StableExistence.count_pos p
