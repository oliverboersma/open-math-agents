import OMAStatements.S_oeis_a204235

-- Problem: A204235, only a(1) and a(2) are odd.
-- Credit: @bnb9001

namespace OMA_A204235_Proof

open Matrix OMA.S_oeis_a204235

lemma perm_cast_eq_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    ((M.permanent : ℕ) : ZMod 2) = (M.map (Nat.cast : ℕ → ZMod 2)).det := by
  rw [Matrix.permanent, Matrix.det_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Nat.cast_prod]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; rfl
  · rw [h, Units.neg_smul, one_smul]
    have : ∀ x : ZMod 2, -x = x := fun x => by fin_cases x <;> rfl
    rw [this]; rfl

lemma even_of_three_le {n : ℕ} (hn : 3 ≤ n) : 2 ∣ a n := by
  have hdet : ((toep n).map (Nat.cast : ℕ → ZMod 2)).det = 0 := by
    apply Matrix.det_zero_of_row_eq (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff])
    funext k
    simp only [Matrix.map_apply, toep, Matrix.of_apply]
    rw [ZMod.natCast_eq_natCast_iff']
    simp only [Nat.cast_ofNat]
    omega
  have h := perm_cast_eq_det (toep n)
  rw [hdet] at h
  unfold a
  have : ((toep n).permanent : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [h]; simp
  rw [ZMod.natCast_eq_natCast_iff'] at this
  omega

end OMA_A204235_Proof

open Matrix OMA_A204235_Proof OMA.S_oeis_a204235 in
theorem OMA.solution : type_of% @OMA.S_oeis_a204235.main := by
  intro n hn
  constructor
  · intro hodd
    by_contra h
    have h3 : 3 ≤ n := by omega
    have := even_of_three_le h3
    rw [Nat.odd_iff] at hodd
    omega
  · rintro (rfl | rfl)
    · decide
    · decide
