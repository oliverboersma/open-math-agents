import OMAStatements.S_oeis_a362069

namespace OMA.S_oeis_a362069

private abbrev ds (a : ℕ) := (Nat.digits 10 a).sum

-- Multiplication by a power of ten leaves space for the three-digit low block.
private theorem split (m a b : ℕ) (ha : a < 1000) (hb : 0 < b) :
    ds (a + 10^(m+3)*b) = ds a + ds b := by
  have hlen : (Nat.digits 10 a).length ≤ 3 :=
    (Nat.digits_length_le_iff (by decide : 1 < 10) a).mpr ha
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show (Nat.digits 10 a).length ≤ m+3 by omega)
  rw [hz]
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (k := z) (n := a) (by decide) hb
  simpa [ds] using congrArg List.sum h.symm

private theorem family (m : ℕ) : ∃ k, m < k ∧ term k ∧ term (k+1) := by
  let T : ℕ := 10^(m+3)
  let k := T^2+16*T+18
  have h₁ : k^2 = 324 + T*(576 + T*(292 + T*(32 + T*1))) := by
    dsimp only [k]
    ring
  have h₂ : (k+1)^2 = 361 + T*(608 + T*(294 + T*(32 + T*1))) := by
    dsimp only [k]
    ring
  have d₁ : ds (k^2) = 46 := by
    rw [h₁]
    dsimp only [T]
    rw [split _ 324 _ (by decide) (by positivity), split _ 576 _ (by decide) (by positivity),
      split _ 292 _ (by decide) (by positivity), split _ 32 _ (by decide) (by decide)]
    decide
  have d₂ : ds ((k+1)^2) = 45 := by
    rw [h₂]
    dsimp only [T]
    rw [split _ 361 _ (by decide) (by positivity), split _ 608 _ (by decide) (by positivity),
      split _ 294 _ (by decide) (by positivity), split _ 32 _ (by decide) (by decide)]
    decide
  refine ⟨k, ?_, ⟨T+8, ?_⟩, ⟨T+8, ?_⟩⟩
  · have hm : m < (10:ℕ)^m := Nat.lt_pow_self (by decide)
    have hT : (10:ℕ)^m ≤ T := Nat.pow_le_pow_right (by decide) (by omega : m ≤ m+3)
    dsimp only [k]
    omega
  · change k + ds (k^2) = _
    rw [d₁]
    dsimp only [k]
    ring
  · change k+1 + ds ((k+1)^2) = _
    rw [d₂]
    dsimp only [k]
    ring

end OMA.S_oeis_a362069

open OMA.S_oeis_a362069 in
theorem OMA.solution : type_of% @OMA.S_oeis_a362069.main := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  obtain ⟨k,hm,hk,hk'⟩ := family m
  exact ⟨k, ⟨hk,hk'⟩, hm⟩
