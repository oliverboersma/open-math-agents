import OMAStatements.S_oeis_a122251

/-!
# The numerator of the reciprocal-progression Hankel determinant

Eliminating the last column gives the ratio of consecutive determinants.
In each ratio, the part of the factorial coprime to the common difference
divides the corresponding product of entries in arithmetic progression.
-/

namespace BarryHankel

open Finset Matrix

def entryDen (p i j : ℕ) : ℕ := 1 + p * (i + j)

def kernel (p m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  fun i j => 1 / (entryDen p i j : ℚ)

def blockProd (p t : ℕ) : ℕ := ∏ i ∈ range t, entryDen p i t

lemma entryDen_pos (p i j : ℕ) : 0 < entryDen p i j := by
  unfold entryDen
  omega

lemma blockProd_pos (p t : ℕ) : 0 < blockProd p t :=
  Finset.prod_pos fun i _ => entryDen_pos p i t

lemma det_last_pivot {t : ℕ} (A : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ)
    (ha : A (Fin.last t) (Fin.last t) ≠ 0) :
    A.det = A (Fin.last t) (Fin.last t) *
      (of fun i j : Fin t => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last t) * A (Fin.last t) j.castSucc /
          A (Fin.last t) (Fin.last t)).det := by
  let l := Fin.last t
  let c : Fin (t + 1) → ℚ := Fin.lastCases 0 (fun i => -A i.castSucc l / A l l)
  let B : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ :=
    fun i j => A i j + c i * A l j
  have hd : B.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c l (by simp [c, l]) (fun _ _ => rfl)
  have hz (i : Fin t) : B i.castSucc l = 0 := by
    simp [B, c, l, ha]
  have hl : B l l = A l l := by simp [B, c, l]
  have hm : B.submatrix l.succAbove l.succAbove =
      of (fun i j : Fin t => A i.castSucc j.castSucc -
        A i.castSucc l * A l j.castSucc / A l l) := by
    ext i j
    simp [B, c, l, Matrix.submatrix, div_eq_mul_inv]
    ring
  rw [← hd, Matrix.det_succ_column B l, Fin.sum_univ_castSucc]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hs : (-1 : ℚ) ^ ((l : ℕ) + (l : ℕ)) = 1 := by rw [← two_mul, pow_mul]; norm_num
  rw [hs, one_mul]
  change B l l * (B.submatrix l.succAbove l.succAbove).det = _
  rw [hl, hm]

def weight (p t : ℕ) (i : Fin t) : ℚ :=
  (p * (t - i.val) : ℕ) / (entryDen p i t : ℚ)

lemma weight_prod (p t : ℕ) :
    (∏ i : Fin t, weight p t i) =
      ((p ^ t * t.factorial : ℕ) : ℚ) / (blockProd p t : ℚ) := by
  have hfac : (∏ i ∈ range t, (t - i)) = t.factorial := by
    calc
      _ = ∏ i ∈ range t, ((t - 1 - i) + 1) := by
        apply prod_congr rfl
        intro i hi
        have := mem_range.mp hi
        omega
      _ = _ := (prod_range_reflect (fun i => i + 1) t).trans (prod_range_add_one_eq_factorial t)
  unfold weight
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => p * (t - i)),
      prod_mul_distrib, hfac]
    simp
  · rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => entryDen p i t)]
    rfl

lemma det_step (p t : ℕ) :
    (kernel p (t + 1)).det = (kernel p t).det *
      (((p ^ t * t.factorial : ℕ) : ℚ) / (blockProd p t : ℚ)) ^ 2 /
      (entryDen p t t : ℚ) := by
  let A := kernel p (t + 1)
  let l := Fin.last t
  have hentry (i j : ℕ) : (entryDen p i j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (entryDen_pos p i j).ne'
  have ha : A l l ≠ 0 := one_div_ne_zero (hentry t t)
  let S := of fun i j : Fin t => A i.castSucc j.castSucc - A i.castSucc l * A l j.castSucc / A l l
  have hS : S = diagonal (weight p t) * kernel p t * diagonal (weight p t) := by
    ext i j
    simp only [S, of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change 1 / (entryDen p i j : ℚ) -
        (1 / (entryDen p i t : ℚ)) * (1 / (entryDen p t j : ℚ)) / (1 / (entryDen p t t : ℚ)) =
      weight p t i * (1 / (entryDen p i j : ℚ)) * weight p t j
    rw [show entryDen p t j = entryDen p j t by simp [entryDen, add_comm]]
    unfold weight
    push_cast [Nat.cast_sub i.isLt.le, Nat.cast_sub j.isLt.le]
    field_simp [hentry]
    push_cast [entryDen]
    ring
  change A.det = _
  rw [det_last_pivot A ha]
  change A l l * S.det = _
  rw [hS, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, weight_prod]
  change 1 / (entryDen p t t : ℚ) * _ = _
  ring

lemma coprime_entry (p i j : ℕ) : p.Coprime (entryDen p i j) :=
  (Nat.coprime_add_mul_left_right p 1 (i + j)).mpr (Nat.coprime_one_right p)

/-- Modulo a divisor of the factorial that is coprime to the step, the
progression is a unit multiple of a block of consecutive integers. -/
lemma factorial_part_dvd {d p t : ℕ} (hd : d ∣ t.factorial) (hc : p.Coprime d) :
    d ∣ blockProd p t := by
  have : NeZero d := ⟨by
    rintro rfl
    exact t.factorial_ne_zero (by simpa using hd)⟩
  let u := ((p : ZMod d)⁻¹).val
  have hu : (p : ZMod d) * (u : ZMod d) = 1 := by
    rw [show (u : ZMod d) = (p : ZMod d)⁻¹ from ZMod.natCast_zmod_val _]
    exact ZMod.coe_mul_inv_eq_one p hc
  have he (i : ℕ) : (entryDen p i t : ZMod d) = (p : ZMod d) * ((u + t + i : ℕ) : ZMod d) := by
    push_cast [entryDen]
    linear_combination -hu
  have hz := (ZMod.natCast_eq_zero_iff _ d).mpr
    (hd.trans (Nat.factorial_dvd_ascFactorial (u + t) t))
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hz
  apply (ZMod.natCast_eq_zero_iff _ d).mp
  unfold blockProd
  rw [Nat.cast_prod]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, hz, mul_zero]

lemma reduced_block {p : ℕ} (hp : p.Prime) (t : ℕ) :
    ∃ d : ℕ, 0 < d ∧ p.Coprime d ∧
      ((p ^ t * t.factorial : ℕ) : ℚ) / (blockProd p t : ℚ) =
        (p : ℚ) ^ (t + t.factorial.factorization p) / (d : ℚ) := by
  let s := ordCompl[p] (t.factorial)
  have hs : 0 < s := Nat.ordCompl_pos p t.factorial_ne_zero
  have hsplit : p ^ t.factorial.factorization p * s = t.factorial :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  obtain ⟨d, hd⟩ := factorial_part_dvd (Nat.ordCompl_dvd t.factorial p)
    (Nat.coprime_ordCompl hp t.factorial_ne_zero)
  change blockProd p t = s * d at hd
  have hbd := blockProd_pos p t
  have hdpos : 0 < d := by
    by_contra! hz
    have : d = 0 := by omega
    simp [hd, this] at hbd
  have hc : p.Coprime (blockProd p t) :=
    Nat.coprime_prod_right_iff.mpr fun i _ => coprime_entry p i t
  rw [hd] at hc
  refine ⟨d, hdpos, (Nat.coprime_mul_iff_right.mp hc).2, ?_⟩
  have hsq : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  have hf : (t.factorial : ℚ) = (p : ℚ) ^ t.factorial.factorization p * (s : ℚ) := by
    exact_mod_cast hsplit.symm
  rw [hd]
  push_cast
  rw [hf, pow_add]
  field_simp

def valuationSum (p n : ℕ) : ℕ :=
  ∑ k ∈ range n, (k + 1 + (k + 1).factorial.factorization p)

lemma exponent_eq {p : ℕ} (hp : p.Prime) (n : ℕ) :
    OMA.S_oeis_a122251.exponent p n = valuationSum p n := by
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  have hlog := Nat.log_le_self p (k + 1)
  rw [Nat.factorization_factorial hp (b := n + 1) (by omega),
    ← sum_range_add_sum_Ico (fun j => (k + 1) / p ^ j) (show 1 ≤ n + 1 by omega)]
  simp

lemma reduced_det {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∃ d : ℕ, 0 < d ∧ p.Coprime d ∧
      (kernel p (n + 1)).det = ((p : ℚ) ^ 2) ^ (valuationSum p n) / (d : ℚ) := by
  induction n with
  | zero =>
    refine ⟨1, by decide, Nat.coprime_one_right p, ?_⟩
    simp [kernel, entryDen, valuationSum]
  | succ n ih =>
    obtain ⟨d, hd, hc, hdet⟩ := ih
    obtain ⟨b, hb, hcb, hblock⟩ := reduced_block hp (n + 1)
    let z := entryDen p (n + 1) (n + 1)
    have hz : 0 < z := entryDen_pos _ _ _
    refine ⟨d * b ^ 2 * z, by positivity, (hc.mul_right (hcb.pow_right 2)).mul_right
      (coprime_entry _ _ _), ?_⟩
    have hv : valuationSum p (n + 1) = valuationSum p n +
        (n + 1 + (n + 1).factorial.factorization p) := sum_range_succ _ _
    have hs (k : ℕ) : ((p : ℚ) ^ 2) ^ k = ((p : ℚ) ^ k) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [det_step, hdet, hblock, hv, pow_add ((p : ℚ) ^ 2), hs (n + 1 + _)]
    change _ / (z : ℚ) = _
    push_cast
    ring

end BarryHankel

theorem OMA.solution : type_of% @OMA.S_oeis_a122251.main := by
  intro p hp n
  obtain ⟨d, hd, hc, heq⟩ := BarryHankel.reduced_det hp n
  have hm : OMA.S_oeis_a122251.hankel p n = BarryHankel.kernel p (n + 1) := by
    ext i j
    simp [OMA.S_oeis_a122251.hankel, BarryHankel.kernel, BarryHankel.entryDen]
  rw [hm]
  rw [heq, BarryHankel.exponent_eq hp n]
  let v := BarryHankel.valuationSum p n
  have hcop : ((p ^ 2) ^ v).Coprime d := (hc.pow_left 2).pow_left v
  have hnum := Rat.num_div_eq_of_coprime (a := (((p ^ 2) ^ v : ℕ) : ℤ)) (b := (d : ℤ))
    (by exact_mod_cast hd) (by simpa using hcop)
  simpa [v] using hnum
