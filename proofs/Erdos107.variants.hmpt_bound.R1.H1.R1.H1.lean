import OMAReductions.R_Erdos107_variants_hmpt_bound_R1_H1_R1

/-! # Counterclockwise sequences are injective and in convex position

Repeating a point kills an orientation determinant, which gives injectivity (`k ≥ 3`).
For a vertex `g i` with cyclic neighbours `g p` and `g n`, the affine function
`x ↦ O(x, g p, g i) + O(x, g i, g n)` vanishes at `g i` and is positive at every other
vertex, so `g i` is not in the convex hull of the others. -/

namespace OMA.Erdos107HmptH1

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def O (u v w : E2) : ℝ := (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

lemma O_rot (u v w : E2) : O u v w = O v w u := by unfold O; ring
lemma O_self12 (u w : E2) : O u u w = 0 := by unfold O; ring
lemma O_self13 (u v : E2) : O u v u = 0 := by unfold O; ring
lemma O_self23 (u v : E2) : O u v v = 0 := by unfold O; ring

lemma cyc {k : ℕ} (g : Fin k → E2)
    (hp : ∀ i j l : Fin k, i < j → j < l → 0 < O (g i) (g j) (g l)) (x y z : Fin k)
    (h : (x.val < y.val ∧ y.val < z.val) ∨ (y.val < z.val ∧ z.val < x.val) ∨
      (z.val < x.val ∧ x.val < y.val)) :
    0 < O (g x) (g y) (g z) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hp x y z h1 h2
  · rw [O_rot]; exact hp y z x h1 h2
  · rw [← O_rot]; exact hp z x y h1 h2

lemma inj_aux {k : ℕ} (hk : 3 ≤ k) (g : Fin k → E2)
    (hp : ∀ i j l : Fin k, i < j → j < l → 0 < O (g i) (g j) (g l))
    (i j : Fin k) (h : i < j) (he : g i = g j) : False := by
  have hi : i.val < j.val := h
  by_cases h0 : 0 < i.val
  · have := cyc g hp ⟨0, by omega⟩ i j (Or.inl ⟨h0, hi⟩)
    rw [he, O_self23] at this
    exact lt_irrefl _ this
  · by_cases h1 : 1 < j.val
    · have := cyc g hp i ⟨1, by omega⟩ j (Or.inl ⟨by simp only; omega, by simp only; omega⟩)
      rw [he, O_self13] at this
      exact lt_irrefl _ this
    · have := cyc g hp i j ⟨2, by omega⟩ (Or.inl ⟨hi, by simp only; omega⟩)
      rw [he, O_self12] at this
      exact lt_irrefl _ this

end OMA.Erdos107HmptH1

open OMA.Erdos107HmptH1 in
theorem OMA.solution : OMA.R_Erdos107_variants_hmpt_bound_R1_H1_R1.H1 := by
  intro k hk g hpos
  have hp : ∀ i j l : Fin k, i < j → j < l → 0 < O (g i) (g j) (g l) := hpos
  constructor
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact inj_aux hk g hp i j h hij
    · exact inj_aux hk g hp j i h hij.symm
  · rintro a ⟨i, rfl⟩ hmem
    obtain ⟨pa, hpa⟩ : ∃ pa : Fin k, (0 < i.val ∧ pa.val = i.val - 1) ∨
        (i.val = 0 ∧ pa.val = k - 1) := by
      by_cases h : 0 < i.val
      · exact ⟨⟨i.val - 1, by omega⟩, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨⟨k - 1, by omega⟩, Or.inr ⟨by omega, rfl⟩⟩
    obtain ⟨nx, hnx⟩ : ∃ nx : Fin k, (i.val + 1 < k ∧ nx.val = i.val + 1) ∨
        (i.val + 1 = k ∧ nx.val = 0) := by
      by_cases h : i.val + 1 < k
      · exact ⟨⟨i.val + 1, h⟩, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨⟨0, by omega⟩, Or.inr ⟨by omega, rfl⟩⟩
    have hik := i.isLt
    let φ : E2 → ℝ := fun x => O x (g pa) (g i) + O x (g i) (g nx)
    have hφi : φ (g i) = 0 := by
      simp only [φ, O_self13, O_self12]; ring
    have hother : ∀ j : Fin k, j ≠ i → 0 < φ (g j) := by
      intro j hji
      have hjv : j.val ≠ i.val := fun e => hji (Fin.ext e)
      have hjk := j.isLt
      simp only [φ]
      by_cases hjp : j = pa
      · rw [hjp, O_self12, zero_add]
        exact cyc g hp pa i nx (by omega)
      by_cases hjn : j = nx
      · rw [hjn, O_self13, add_zero]
        have hpv : pa.val ≠ nx.val := by omega
        have : 0 < O (g pa) (g i) (g nx) := cyc g hp pa i nx (by omega)
        rw [O_rot, O_rot] at this
        exact this
      have hjpv : j.val ≠ pa.val := fun e => hjp (Fin.ext e)
      have hjnv : j.val ≠ nx.val := fun e => hjn (Fin.ext e)
      have t1 : 0 < O (g j) (g pa) (g i) := cyc g hp j pa i (by omega)
      have t2 : 0 < O (g j) (g i) (g nx) := cyc g hp j i nx (by omega)
      linarith
    have hconv : Convex ℝ {x : E2 | 0 < φ x} := by
      intro x hx y hy s t hs ht hst
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      have e : φ (s • x + t • y) = s * φ x + t * φ y := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        simp only [φ, O, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [e]
      rcases hs.lt_or_eq with hs' | hs'
      · have := mul_pos hs' hx
        have := mul_nonneg ht hy.le
        linarith
      · have ht1 : t = 1 := by linarith
        rw [← hs', ht1]
        linarith
    have hsub : Set.range g \ {g i} ⊆ {x : E2 | 0 < φ x} := by
      rintro x ⟨⟨j, rfl⟩, hj⟩
      have : j ≠ i := fun e => hj (by rw [e]; rfl)
      exact hother j this
    have := convexHull_min hsub hconv hmem
    rw [Set.mem_setOf_eq, hφi] at this
    exact lt_irrefl _ this
