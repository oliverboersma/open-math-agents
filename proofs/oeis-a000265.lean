import OMAStatements.S_oeis_a000265

-- Problem: A000265: Remove all factors of 2 from n; or largest odd divisor of n; or odd part of n.
-- Upstream: formal-conjectures statements/oeis-a000265.lean:0 (declaration OMA.S_oeis_a000265.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a000265

open OMA.S_oeis_a000265

private lemma a_two_mul (m : ℕ) (hm : 0 < m) : a (2 * m) = a m := by
  unfold a
  have hne : m ≠ 0 := by omega
  have hfac : (2 * m).factorization 2 = m.factorization 2 + 1 := by
    rw [Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    omega
  rw [hfac, pow_succ', Nat.mul_div_mul_left _ _ (by norm_num)]

private lemma a_two_mul_add_one (m : ℕ) : a (2 * m + 1) = 2 * m + 1 := by
  unfold a
  have hndvd : ¬ (2 ∣ 2 * m + 1) := by omega
  have hfac : (2 * m + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hndvd
  rw [hfac, pow_zero, Nat.div_one]

private lemma sum_a_Icc (i : ℕ) :
    ∑ j ∈ Finset.Icc ((i + 1) / 2) i, a (j + 1) = ((i + 2) / 2) ^ 2 := by
  induction i with
  | zero =>
    simp [a_two_mul_add_one 0]
  | succ i ih =>
    rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hi : i = 2 * r := by omega
      subst hi
      have hl1 : (2 * r + 1) / 2 = r := by omega
      have hl2 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
      have hsq : (2 * r + 1 + 2) / 2 = (2 * r + 2) / 2 := by omega
      rw [hl1] at ih
      rw [hl2, hsq, ← ih]
      have hleft :
          ∑ j ∈ Finset.Icc r (2 * r), a (j + 1) =
            a (r + 1) + ∑ j ∈ Finset.Icc (r + 1) (2 * r), a (j + 1) := by
        rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ 2 * r),
          Finset.sum_insert (by simp)]
      have hright :
          ∑ j ∈ Finset.Icc (r + 1) (2 * r + 1), a (j + 1) =
            (∑ j ∈ Finset.Icc (r + 1) (2 * r), a (j + 1)) + a (2 * r + 2) := by
        rw [Finset.sum_Icc_succ_top (by omega : r + 1 ≤ 2 * r + 1)]
      have ha2 : a (2 * r + 2) = a (r + 1) := by
        rw [show 2 * r + 2 = 2 * (r + 1) by omega]
        exact a_two_mul (r + 1) (by omega)
      rw [hleft, hright, ha2]
      ring
    · subst hr
      have hl1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
      have hl2 : (2 * r + 1 + 1 + 1) / 2 = r + 1 := by omega
      rw [hl1] at ih
      rw [hl2, Finset.sum_Icc_succ_top (by omega : r + 1 ≤ 2 * r + 2), ih]
      have haodd : a (2 * r + 2 + 1) = 2 * r + 3 := a_two_mul_add_one (r + 1)
      have hc1 : (2 * r + 1 + 2) / 2 = r + 1 := by omega
      have hc2 : (2 * r + 1 + 1 + 2) / 2 = r + 2 := by omega
      rw [haodd, hc1, hc2]
      ring

private lemma t_det_ne_zero (N : ℕ) : (t N).det ≠ 0 := by
  have htri : (t N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    unfold t
    have hnot : ¬ ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * (j : ℕ)) := by
      have : (i : ℕ) < (j : ℕ) := hij'
      omega
    rw [if_neg hnot]
  rw [Matrix.det_of_isLowerTriangular (t N) htri]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  unfold t
  have hcond : (i : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * (i : ℕ) := by omega
  rw [if_pos hcond]
  have hne : ((((i : ℕ) + 2) / 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact one_div_ne_zero hne

private lemma t_mulVec_a (N : ℕ) :
    (t N).mulVec (fun j : Fin N => (a (j.val + 1) : ℚ)) =
      fun i : Fin N => (((i.val + 2) / 2 : ℕ) : ℚ) := by
  ext i
  rw [Matrix.mulVec, dotProduct]
  have hsum :
      ∑ j : Fin N, t N i j * (a (j.val + 1) : ℚ) =
        ∑ j ∈ Finset.range N,
          if j ≤ i.val ∧ i.val ≤ 2 * j then
            (1 / (((i.val + 2) / 2 : ℕ) : ℚ)) * (a (j + 1) : ℚ)
          else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j < N := Finset.mem_range.mp hj
    simp only [hjN, dif_pos, t]
    split_ifs <;> simp
  rw [hsum, ← Finset.sum_filter]
  have hfilter :
      (Finset.range N).filter (fun j => j ≤ i.val ∧ i.val ≤ 2 * j) =
        Finset.Icc ((i.val + 1) / 2) i.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have hiN : i.val < N := i.isLt
    omega
  rw [hfilter, ← Finset.mul_sum]
  have hcast :
      (∑ j ∈ Finset.Icc ((i.val + 1) / 2) i.val, (a (j + 1) : ℚ)) =
        ((((i.val + 2) / 2 : ℕ) : ℚ)) ^ 2 := by
    exact_mod_cast sum_a_Icc i.val
  rw [hcast]
  have hne : ((((i.val + 2) / 2 : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hne]

private lemma main_proof : ∀ n : ℕ,
    (a (n + 1) : ℚ) = ∑ k ∈ Finset.range (n + 1), A127793 n k * (((k + 2) / 2 : ℕ) : ℚ) := by
  intro n
  let w : Fin (n + 1) → ℚ := fun j => (a (j.val + 1) : ℚ)
  let v : Fin (n + 1) → ℚ := fun i => (((i.val + 2) / 2 : ℕ) : ℚ)
  have hunit : IsUnit (t (n + 1)).det := isUnit_iff_ne_zero.mpr (t_det_ne_zero (n + 1))
  have hmul : (t (n + 1))⁻¹ * t (n + 1) = 1 := Matrix.nonsing_inv_mul (t (n + 1)) hunit
  have hvec : (t (n + 1))⁻¹.mulVec v = w := by
    have hv : (t (n + 1)).mulVec w = v := t_mulVec_a (n + 1)
    rw [← hv, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hentry := congrFun hvec ⟨n, Nat.lt_succ_self n⟩
  have hEq : (a (n + 1) : ℚ) = ((t (n + 1))⁻¹.mulVec v) ⟨n, Nat.lt_succ_self n⟩ := hentry.symm
  rw [hEq, Matrix.mulVec, dotProduct, Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < n + 1 := Finset.mem_range.mp hk
  have hle : k ≤ n := Nat.lt_succ_iff.mp hkn
  simp [hkn, A127793, hle, v]

end OMA.Proof_oeis_a000265

theorem OMA.solution : type_of% @OMA.S_oeis_a000265.main :=
  OMA.Proof_oeis_a000265.main_proof
