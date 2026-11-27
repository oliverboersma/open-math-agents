import OMAStatements.S_oeis_a052379
import Mathlib

-- Problem: oeis-a052379
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P052379
open OMA.S_oeis_a052379

def good (k : ℕ) : Prop := ∀ d ∈ Nat.digits 10 k, d ≠ 0 ∧ d ≠ 1

instance : DecidablePred good := fun k => by unfold good; infer_instance

def H (m : ℕ) : Finset ℕ := (Finset.range (10 ^ m)).filter good

lemma good_step (q r : ℕ) (hr : 2 ≤ r ∧ r ≤ 9) : good (r + 10 * q) ↔ good q := by
  unfold good
  rw [Nat.digits_add 10 (by norm_num) r q (by omega) (Or.inl (by omega))]
  simp only [List.mem_cons, forall_eq_or_imp]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨by omega, by omega⟩, h⟩

lemma H_succ (m : ℕ) : H (m + 1) = insert 0 ((H m ×ˢ Finset.Icc 2 9).image (fun p => p.2 + 10 * p.1)) := by
  ext k
  simp only [H, Finset.mem_insert, Finset.mem_filter, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_Icc, Prod.exists]
  constructor
  · rintro ⟨hk, hg⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact Or.inl rfl
    right
    have hd : Nat.digits 10 k = k % 10 :: Nat.digits 10 (k / 10) := Nat.digits_def' (by norm_num) hpos
    have h1 := hg (k % 10) (by rw [hd]; exact List.mem_cons_self ..)
    refine ⟨k / 10, k % 10, ⟨⟨?_, ?_⟩, by omega, by omega⟩, by omega⟩
    · rw [pow_succ] at hk; omega
    · intro d hd'
      exact hg d (by rw [hd]; exact List.mem_cons_of_mem _ hd')
  · rintro (rfl | ⟨q, r, ⟨⟨hq, hg⟩, h2, h9⟩, rfl⟩)
    · exact ⟨by positivity, by simp [good]⟩
    · refine ⟨by rw [pow_succ]; omega, (good_step q r ⟨h2, h9⟩).mpr hg⟩

lemma H_card (m : ℕ) : 7 * (H m).card + 1 = 8 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [H_succ, Finset.card_insert_of_notMem, Finset.card_image_of_injOn, Finset.card_product]
    · simp only [Nat.card_Icc]
      rw [pow_succ]; omega
    · rintro ⟨q1, r1⟩ h1 ⟨q2, r2⟩ h2 he
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc] at h1 h2
      simp only at he
      ext <;> simp <;> omega
    · simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Icc, not_exists, not_and]
      intro q r h; omega

theorem sol : type_of% @OMA.S_oeis_a052379.main := by
  intro n
  have e : (Finset.Icc 1 (10 ^ (n + 1) - 1)).filter (fun k => ∀ d ∈ Nat.digits 10 k, d ≠ 0 ∧ d ≠ 1)
      = (H (n + 1)).erase 0 := by
    ext k
    simp only [H, good, Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    have : 0 < 10 ^ (n + 1) := by positivity
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
  unfold a A023001
  rw [e, Finset.card_erase_of_mem (by simp [H, good])]
  have h := H_card (n + 1)
  rw [show n + 1 + 1 = n + 2 by ring] at h
  generalize 8 ^ (n + 2) = x at h ⊢
  omega

end OMA.P052379

theorem OMA.solution : type_of% @OMA.S_oeis_a052379.main := OMA.P052379.sol
