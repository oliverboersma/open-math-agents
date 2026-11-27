import FormalConjectures.OEIS.«69191»

/-! A reduction of Zhi-Wei Sun's conjecture on the eigenvalues of the prime sum matrix.
Changing the signs on odd coordinates identifies the reflected spectrum with that of a
single diagonal perturbation. Interlacing then orders the magnitudes once opposite roots
are excluded. -/
-- Credit: @marcusbuffett
namespace OMA.R_OeisA69191_conjecture_2_R1

open Matrix Polynomial OeisA69191
open scoped BigOperators

private def signAt {n : ℕ} (i : Fin n) : ℝ := if i.val % 2 = 0 then 1 else -1

private theorem sign_sq {n : ℕ} (i : Fin n) : signAt i * signAt i = 1 := by
  unfold signAt
  split <;> norm_num

private theorem conjugation {n : ℕ} (k : Fin n) (hk : k.val = 0) :
    primeMatrix ℝ n - Matrix.single k k 2 =
      diagonal signAt * (-primeMatrix ℝ n) * diagonal signAt := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.single_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.neg_apply, primeMatrix]
  by_cases h : k = i ∧ k = j
  · obtain ⟨rfl, rfl⟩ := h
    norm_num [hk, signAt]
  · have hij : i.val ≠ 0 ∨ j.val ≠ 0 := by
      by_contra! hh
      exact h ⟨Fin.ext (hk.trans hh.1.symm), Fin.ext (hk.trans hh.2.symm)⟩
    rw [if_neg h]
    by_cases hp : (i.val + j.val + 2).Prime
    · have hp' := hp.eq_two_or_odd
      simp only [if_pos hp, sub_zero, signAt]
      split <;> split <;> norm_num <;> omega
    · simp [hp]

private theorem conjugate_charpoly {n : ℕ} (k : Fin n) (hk : k.val = 0) :
    (primeMatrix ℝ n - Matrix.single k k 2).charpoly = (-primeMatrix ℝ n).charpoly := by
  rw [conjugation k hk, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin n => signAt i * signAt i) = fun _ => 1 := funext sign_sq
  simp [h]

private def half {n : ℕ} (i : Fin n) : Fin n := ⟨i.val / 2, by omega⟩

private def zig {n : ℕ} (i : Fin n) : Fin n :=
  if i.val % 2 = 0 then half i else (half i).rev

private theorem zig_injective {n : ℕ} : Function.Injective (@zig n) := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  unfold zig at h'
  split at h' <;> split at h' <;> simp only [half, Fin.val_rev] at h' <;> omega

private theorem alternating {n : ℕ} (f : Fin n → ℝ) (hmono : Antitone f)
    (upper : ∀ i, -f (Fin.rev i) < f i)
    (lower : ∀ i j, i < j → f j < -f (Fin.rev i)) :
    StrictAnti (fun i : Fin n => (-1 : ℝ) ^ i.val * f (zig i)) ∧
    ∀ i : Fin n, 0 < (-1 : ℝ) ^ i.val * f (zig i) := by
  have valform (i : Fin n) : (-1 : ℝ) ^ i.val * f (zig i) =
      if i.val % 2 = 0 then f (half i) else -f (half i).rev := by
    rw [neg_one_pow_eq_pow_mod_two]
    by_cases h : i.val % 2 = 0
    · simp [zig, h]
    · have h' : i.val % 2 = 1 := by omega
      simp [zig, h']
  constructor
  · cases n with
    | zero => exact fun i => Fin.elim0 i
    | succ m =>
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      rw [valform, valform]
      by_cases h : i.val % 2 = 0
      · have hs : (i.val + 1) % 2 ≠ 0 := by omega
        have hh : half i.succ = half i.castSucc := by apply Fin.ext; simp only [half, Fin.val_succ, Fin.val_castSucc]; omega
        simpa [hs, h, hh] using upper (half i.castSucc)
      · have hs : (i.val + 1) % 2 = 0 := by omega
        have hh : half i.castSucc < half i.succ := by change i.val / 2 < (i.val + 1) / 2; omega
        simpa [hs, h] using lower _ _ hh
  · intro i
    rw [valform]
    split
    · have hh : half i ≤ (half i).rev := by
        change i.val / 2 ≤ n - (i.val / 2 + 1)
        omega
      have := hmono hh
      have := upper (half i)
      linarith
    · have hh : half i < (half i).rev := by
        change i.val / 2 < n - (i.val / 2 + 1)
        omega
      have := lower _ _ hh
      linarith

private theorem ordered {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ f : Fin n → ℝ, Antitone f ∧ A.charpoly = ∏ i, (X - C (f i)) ∧
      (-A).charpoly = ∏ i, (X - C (-f i)) := by
  let t : Fin n ≃ Fin (Fintype.card (Fin n)) := finCongr (Fintype.card_fin n).symm
  let e : Fin n ≃ Fin n := t.trans (Fintype.equivOfCardEq (Fintype.card_fin _))
  let f : Fin n → ℝ := fun i => hA.eigenvalues₀ (t i)
  have he (i : Fin n) : hA.eigenvalues (e i) = f i := by simp [e, Matrix.IsHermitian.eigenvalues, f]
  refine ⟨f, fun _ _ h => hA.eigenvalues₀_antitone h, ?_, ?_⟩
  · rw [hA.charpoly_eq]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [← Equiv.prod_comp e (fun i => X - C (hA.eigenvalues i))]
    simp [he]
  · have diag := hA.spectral_theorem
    have hn := congrArg Neg.neg diag
    rw [hn, ← map_neg, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
    simp only [SetLike.coe_mem, Unitary.star_mul_self_of_mem, one_mul, RCLike.ofReal_real_eq_id, Function.id_comp]
    rw [Matrix.diagonal_neg, Matrix.charpoly_diagonal]
    rw [← Equiv.prod_comp e (fun i => X - C (-hA.eigenvalues i))]
    simp [he]

/-- The characteristic polynomial has no pair of opposite real roots, including zero. -/
def H1 : Prop := ∀ n : ℕ, 24 ≤ n → ∀ x : ℝ,
    (primeMatrix ℝ n).charpoly.IsRoot x → ¬ (primeMatrix ℝ n).charpoly.IsRoot (-x)

/-- Weak interlacing under a positive perturbation of a single diagonal entry. -/
def H2 : Prop := ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsHermitian →
    ∀ (k : Fin n) (c : ℝ), 0 ≤ c → ∀ (f g : Fin n → ℝ), Antitone f → Antitone g →
    A.charpoly = ∏ i, (X - C (f i)) →
    (A - Matrix.single k k c).charpoly = ∏ i, (X - C (g i)) →
    (∀ i, g i ≤ f i) ∧ (∀ i j, i < j → f j ≤ g i)

theorem main : H1 → H2 → type_of% @OeisA69191.conjecture_2 := by
  intro noOpposite interlace n hn
  let A := primeMatrix ℝ n
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    simp [A, primeMatrix, Nat.add_comm]
  obtain ⟨f, hm, hf, hneg⟩ := ordered hA
  let k : Fin n := ⟨0, by omega⟩
  have hg : (A - Matrix.single k k 2).charpoly = ∏ i : Fin n, (X - C (-f i.rev)) := by
    rw [conjugate_charpoly k rfl, hneg]
    exact (Equiv.prod_comp Fin.revPerm (fun i => X - C (-f i))).symm
  have hanti : Antitone (fun i : Fin n => -f i.rev) :=
    fun _ _ h => neg_le_neg (hm (Fin.rev_le_rev.mpr h))
  obtain ⟨up, lo⟩ := interlace n A hA k 2 (by norm_num) f _ hm hanti hf hg
  have root (i : Fin n) : A.charpoly.IsRoot (f i) := by
    rw [Polynomial.IsRoot, hf, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have diff (i j : Fin n) : f i ≠ -f j := by
    intro h
    exact noOpposite n hn _ (root j) (h ▸ root i)
  obtain ⟨ha, hp⟩ := alternating f hm (fun i => lt_of_le_of_ne (up i) (diff i _).symm)
    (fun i j h => lt_of_le_of_ne (lo i j h) (diff _ _))
  exact ⟨fun i => f (zig i), hf.trans (zig_injective.bijective_of_finite.prod_comp
    (fun i => X - C (f i))).symm, ha, hp⟩

end OMA.R_OeisA69191_conjecture_2_R1
