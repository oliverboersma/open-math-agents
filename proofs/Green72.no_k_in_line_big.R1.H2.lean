import OMAReductions.R_Green72_no_k_in_line_big_R1
import Mathlib

open Finset Green72 OMA.R_Green72_no_k_in_line_big_R1

theorem OMA.solution : OMA.R_Green72_no_k_in_line_big_R1.H2 := by
  intro k N s hk hs hp
  have hb (i) (h : i ∈ s) : i.1 < N ∧ i.2 < N := by
    simpa using hs h
  refine ⟨hb, ?_⟩
  intro t hts htc hcol
  obtain ⟨p,hp',q,hq,hne⟩ := Finset.one_lt_card.mp (show 1 < t.card by omega)
  let a : ℤ := (q.2 : ℤ) - p.2
  let b : ℤ := (p.1 : ℤ) - q.1
  let c : ℤ := a * p.1 + b * p.2
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! h
    apply hne
    apply Prod.ext <;> dsimp [a,b] at h <;> omega
  have hbp := hb p (hts hp')
  have hbq := hb q (hts hq)
  have count := hp a b c hab (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [b]; omega) (by dsimp [b]; omega)
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨o,v,hov⟩ := hcol
  have param (i : ℕ × ℕ) (h : i ∈ t) :
      ∃ r : ℝ, (i.1 : ℝ) = r * v.1 + o.1 ∧ (i.2 : ℝ) = r * v.2 + o.2 := by
    obtain ⟨r,he⟩ := hov ((i.1 : ℝ),(i.2 : ℝ)) ⟨i,h,rfl⟩
    exact ⟨r,congrArg Prod.fst he,congrArg Prod.snd he⟩
  obtain ⟨rp,px,py⟩ := param p hp'
  obtain ⟨rq,qx,qy⟩ := param q hq
  have sub : t ⊆ s.filter (fun i ↦ a * i.1 + b * i.2 = c) := by
    intro i hi
    refine mem_filter.mpr ⟨hts hi,?_⟩
    obtain ⟨r,ix,iy⟩ := param i hi
    dsimp [c,a,b]
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [ix,iy,px,py,qx,qy]
    ring
  have := card_le_card sub
  omega
