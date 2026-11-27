import OMAReductions.R_LatinSquare_numTransversalsZn_R1

-- Step LatinSquare.numTransversalsZn.R1.H2
-- Credit: @caa1982

open LatinSquare

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H2 := by
  intro n hn hodd
  obtain ⟨k, rfl⟩ := hodd
  constructor
  · rw [z, numTransversals, Fintype.card_pos_iff]
    refine ⟨⟨id, Function.injective_id, ?_⟩⟩
    intro i j hij
    simp only [Matrix.of_apply, id_eq] at hij
    have hval := congrArg Fin.val hij
    simp only [Fin.val_add] at hval
    have hi := i.isLt
    have hj := j.isLt
    have hmi : (i.val + i.val) % (2 * k + 1) =
        if i.val + i.val < 2 * k + 1 then i.val + i.val else i.val + i.val - (2 * k + 1) := by
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hmj : (j.val + j.val) % (2 * k + 1) =
        if j.val + j.val < 2 * k + 1 then j.val + j.val else j.val + j.val - (2 * k + 1) := by
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmi, hmj] at hval
    apply Fin.ext
    split_ifs at hval <;> omega
  · rw [z, numTransversals]
    let f : {σ : Fin (2 * k + 1) → Fin (2 * k + 1) //
        IsTransversal {
          mat := Matrix.of fun i j : Fin (2 * k + 1) => i + j
          row_injective := fun i _a _b h => by
            simp only [Matrix.of_apply] at h; exact add_left_cancel h
          col_injective := fun j _a _b h => by
            simp only [Matrix.transpose_apply, Matrix.of_apply] at h; exact add_right_cancel h
        } σ} → Equiv.Perm (Fin (2 * k + 1)) :=
      fun ⟨σ, hσ, _⟩ => Equiv.ofBijective σ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hσ, rfl⟩)
    have hfinj : Function.Injective f := by
      rintro ⟨σ₁, hσ₁, _⟩ ⟨σ₂, hσ₂, _⟩ heq
      apply Subtype.ext
      funext i
      simpa [f] using congrArg (fun e : Equiv.Perm (Fin (2 * k + 1)) => e i) heq
    have hfnot : ¬ Function.Surjective f := by
      intro hsurj
      obtain ⟨⟨σ, _, himg⟩, hσ⟩ := hsurj (Equiv.neg (Fin (2 * k + 1)))
      have hval : ∀ i : Fin (2 * k + 1), σ i = -i := fun i =>
        congrArg (fun e : Equiv.Perm (Fin (2 * k + 1)) => e i) hσ
      have h01 : (⟨0, by omega⟩ : Fin (2 * k + 1)) ≠ ⟨1, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      apply h01
      apply himg
      simp only [Matrix.of_apply, hval, add_neg_cancel]
    have hlt := Fintype.card_lt_of_injective_not_surjective f hfinj hfnot
    rwa [Fintype.card_perm, Fintype.card_fin] at hlt
