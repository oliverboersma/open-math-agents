import OMAStatements.S_oeis_a356493

-- Problem: A356493, the permanent is prime only for n = 1, 2, 3.
-- Credit: @bnb9001

namespace OMA_A356493_Proof

open Matrix OMA.S_oeis_a356493

lemma perm_cast_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    ((A.permanent : ℕ) : ZMod 2) = (A.map (Nat.cast : ℕ → ZMod 2)).det := by
  rw [Matrix.permanent, Matrix.det_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Nat.cast_prod]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; rfl
  · rw [h, Units.neg_smul, one_smul]
    have : ∀ x : ZMod 2, -x = x := fun x => by fin_cases x <;> rfl
    rw [this]; rfl

lemma nth_prime_odd {k : ℕ} (hk : 1 ≤ k) : Nat.nth Nat.Prime k % 2 = 1 := by
  have hp := Nat.prime_nth_prime k
  have hgt : 2 < Nat.nth Nat.Prime k := by
    rw [← Nat.nth_prime_zero_eq_two]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  rcases hp.eq_two_or_odd with h | h
  · omega
  · exact h

lemma even_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ∣ a n := by
  have hdet : ((toep n).map (Nat.cast : ℕ → ZMod 2)).det = 0 := by
    apply Matrix.det_zero_of_row_eq (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff])
    funext k
    simp only [Matrix.map_apply, toep, Matrix.of_apply]
    rw [ZMod.natCast_eq_natCast_iff']
    have hk := k.isLt
    rw [nth_prime_odd (by simp only [Nat.cast_one]; omega), nth_prime_odd (by simp only [Nat.cast_ofNat]; omega)]
  have h := perm_cast_eq_det (toep n)
  rw [hdet] at h
  unfold a
  have : ((toep n).permanent : ZMod 2) = ((0 : ℕ) : ZMod 2) := by rw [h]; simp
  rw [ZMod.natCast_eq_natCast_iff'] at this
  omega

lemma gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < a n := by
  unfold a
  have hterm : ∏ i, toep n ((1 : Equiv.Perm (Fin n)) i) i ≤ (toep n).permanent :=
    Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin n) => ∏ i, toep n (σ i) i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 1)
  have hdiag : ∏ i, toep n ((1 : Equiv.Perm (Fin n)) i) i = Nat.nth Nat.Prime (n - 1) ^ n := by
    simp [toep, Finset.prod_const]
  have h2 : 2 ≤ Nat.nth Nat.Prime (n - 1) := (Nat.prime_nth_prime _).two_le
  have : 2 ^ 2 ≤ Nat.nth Nat.Prime (n - 1) ^ n :=
    (Nat.pow_le_pow_left h2 2).trans (Nat.pow_le_pow_right (by omega) hn)
  omega

end OMA_A356493_Proof

open Matrix OMA_A356493_Proof OMA.S_oeis_a356493 in
theorem OMA.solution : type_of% @OMA.S_oeis_a356493.main := by
  intro n
  constructor
  · intro hp
    by_contra h
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · have : n = 0 := by omega
      subst this
      simp [a, Matrix.permanent] at hp
      exact Nat.not_prime_one hp
    · have h2 := even_of_four_le h4
      have hgt := gt_two (show 2 ≤ n by omega)
      have := hp.eq_one_or_self_of_dvd 2 h2
      omega
  · have p0 := Nat.nth_prime_zero_eq_two
    have p1 := Nat.nth_prime_one_eq_three
    have p2 := Nat.nth_prime_two_eq_five
    rintro (rfl | rfl | rfl)
    · have : a 1 = 2 := by simp [a, toep, Matrix.permanent, p0]
      rw [this]; norm_num
    · have e : toep 2 = !![3, 2; 2, 3] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [toep, p0, p1]
      have : a 2 = 13 := by rw [a, e]; decide
      rw [this]; norm_num
    · have e : toep 3 = !![5, 3, 2; 3, 5, 3; 2, 3, 5] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [toep, p0, p1, p2]
      have : a 3 = 271 := by rw [a, e]; decide
      rw [this]; norm_num
