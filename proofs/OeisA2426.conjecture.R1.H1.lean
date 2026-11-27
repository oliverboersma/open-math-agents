import OMAReductions.R_OeisA2426_conjecture_R1

/-! The degree-p coefficient of (X-1)^p (1+X+X²)^p vanishes because
the product equals (X³-1)^p. All the interior convolution terms are
multiples of p² by Frobenius. -/

namespace OMA.Trinomial

open Polynomial Finset

private noncomputable abbrev T : ℤ[X] := 1 + X + X^2

private lemma central (n : ℕ) : (T^n).coeff n = (OeisA2426.a n : ℤ) := by
  have expandTwo (j : ℕ) : (1 + X^2 : ℤ[X])^j = expand ℤ 2 ((1 + X)^j) := by simp
  rw [show T = (1 + X^2) + X by ring, add_pow, finsetSum_coeff]
  simp only [coeff_mul_natCast, coeff_mul_X_pow', Nat.sub_le, if_true]
  calc
    _ = ∑ j ∈ (range (n+1)).filter (fun j => 2 ∣ j),
          (j.choose (j/2) : ℤ) * n.choose j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [Nat.sub_sub_self hjn, expandTwo, coeff_expand (by decide), coeff_one_add_X_pow]
      split_ifs <;> simp
    _ = _ := by
      unfold OeisA2426.a
      push_cast
      refine sum_bij' (fun j _ => j/2) (fun k _ => 2*k) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨h, _⟩ := mem_filter.mp hj
        simp only [mem_range] at *
        omega
      · intro k hk
        apply mem_filter.mpr
        refine ⟨mem_range.mpr ?_, dvd_mul_right _ _⟩
        simp only [mem_range] at hk
        omega
      · intro j hj
        exact Nat.mul_div_cancel' (mem_filter.mp hj).2
      · intro k _
        omega
      · intro j hj
        rw [Nat.mul_div_cancel' (mem_filter.mp hj).2, mul_comm]

private lemma interior {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hlt : k < p)
    (F : ℤ[X]) : (p : ℤ) ∣ (F^p).coeff k := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod p)) _ = _
  rw [← coeff_map, Polynomial.map_pow, ← ZMod.expand_card, coeff_expand hp.pos,
    if_neg (fun h => hlt.not_ge (Nat.le_of_dvd hk h))]

end OMA.Trinomial

open OMA.Trinomial Polynomial Finset

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 := by
  intro p hp3 hp
  let F : ℤ[X] := X - 1
  have hnd : ¬ 3 ∣ p := fun h => (hp.eq_one_or_self_of_dvd 3 h).elim (by omega) (by omega)
  have hzero : (F^p * T^p).coeff p = 0 := by
    rw [← mul_pow, show F*T = expand ℤ 3 F by simp [F, T]; ring,
      ← map_pow, coeff_expand (by decide), if_neg hnd]
  have hF : (F^p).coeff p = 1 := by
    have hm : F.Monic := by simpa [F] using (monic_X_sub_C (1 : ℤ))
    have hd : F.natDegree = 1 := by simpa [F] using natDegree_X_sub_C (1 : ℤ)
    simpa [natDegree_pow, hd] using (hm.pow p).coeff_natDegree
  have hF0 : (F^p).coeff 0 = -1 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, (hp.odd_of_ne_two (by omega)).neg_one_pow]
  have hT0 : (T^p).coeff 0 = 1 := by simp [coeff_zero_eq_eval_zero, T]
  let term (j : ℕ) : ZMod (p^2) := ((F^p).coeff j : ℤ) * ((T^p).coeff (p-j) : ℤ)
  have hsum : ∑ j ∈ range (p+1), term j = 0 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hzero
    simpa [term, map_sum] using congrArg (Int.castRingHom (ZMod (p^2))) hzero
  have hi (j : ℕ) (hj : 0 < j) (hj' : j < p) : term j = 0 := by
    have h := mul_dvd_mul (interior hp hj hj' F) (interior hp (by omega : 0 < p-j) (by omega) T)
    dsimp only [term]
    rw [← Int.cast_mul]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa [pow_two] using h
  have rest : ∑ j ∈ range p, term j = term 0 := by
    apply sum_eq_single 0
    · intro j hj hj0
      exact hi j (Nat.pos_of_ne_zero hj0) (mem_range.mp hj)
    · simp [hp.pos]
  rw [sum_range_succ, rest] at hsum
  have eq : -(OeisA2426.a p : ZMod (p^2)) + 1 = 0 := by
    simpa [term, hF, hF0, hT0, central] using hsum
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa using (neg_add_eq_zero.mp eq)
