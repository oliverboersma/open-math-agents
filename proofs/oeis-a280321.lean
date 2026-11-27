import OMAStatements.S_oeis_a280321
import Mathlib

namespace OMAProofA280321

def Z (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 * p.2 = 0)

lemma Z_eq (n : ℕ) : Z n = ({0} ×ˢ Finset.range (n + 1)) ∪ (Finset.Icc 1 n ×ˢ {0}) := by
  ext ⟨x, y⟩
  simp [Z, mul_eq_zero]
  omega

lemma Z_card (n : ℕ) : (Z n).card = 2 * n + 1 := by
  rw [Z_eq, Finset.card_union_of_disjoint]
  · simp
    omega
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp at h1 h2
    omega

lemma key (n : ℕ) (hn : 1 < n) (a b c d : ℕ) :
    ((a : ℤ) * d - b * c = n * (a * d + b * c)) ↔ (a * d = 0 ∧ b * c = 0) := by
  constructor
  · intro h
    have hX : (0 : ℤ) ≤ a * d := by positivity
    have hY : (0 : ℤ) ≤ b * c := by positivity
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    have h1 : (a : ℤ) * d = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') hX, mul_nonneg (sub_nonneg.mpr hn') hY]
    have h2 : (b : ℤ) * c = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') hX, mul_nonneg (sub_nonneg.mpr hn') hY]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (a : ℤ) * d = 0 := by exact_mod_cast h1
    have h2' : (b : ℤ) * c = 0 := by exact_mod_cast h2
    rw [h1', h2']
    ring

lemma a_eq (n : ℕ) (hn : 1 < n) : OMA.S_oeis_a280321.a n = (Z n ×ˢ Z n).card := by
  unfold OMA.S_oeis_a280321.a
  apply Finset.card_nbij' (fun t => ((t.1, t.2.2.2), (t.2.1, t.2.2.1)))
    (fun p => (p.1.1, p.2.1, p.2.2, p.1.2))
  · rintro ⟨a, b, c, d⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Z,
      key n hn] at h ⊢
    tauto
  · rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Z,
      key n hn] at h ⊢
    tauto
  · rintro ⟨a, b, c, d⟩ _
    rfl
  · rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩ _
    rfl

lemma closed (n : ℕ) (hn : 1 < n) : OMA.S_oeis_a280321.a n = (1 + 2 * n) ^ 2 := by
  rw [a_eq n hn, Finset.card_product, Z_card]
  ring

end OMAProofA280321

theorem OMA.solution : type_of% @OMA.S_oeis_a280321.main := by
  refine ⟨OMAProofA280321.closed, ?_⟩
  intro n hn
  rw [OMAProofA280321.closed n (by omega), OMAProofA280321.closed (n - 1) (by omega),
    OMAProofA280321.closed (n - 2) (by omega), OMAProofA280321.closed (n - 3) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  ring
