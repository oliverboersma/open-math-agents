import FormalConjectures.Wikipedia.Hadamard
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Exact Hamming distances and sign matrices using a base-1024 digit encoding. -/
namespace PaleyHadamard

open Matrix
open scoped BigOperators Matrix

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Off the diagonal, two translates of the quadratic character have correlation `-1`. -/
theorem quadraticChar_correlation (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - b)) = -1 := by
  classical
  let f (x : F) := if x = b then 1 else (x - a) / (x - b)
  have fneq {x : F} (hx : x ≠ b) : f x ≠ 1 := by
    simp only [f, hx, if_false]
    intro h
    have h' := (div_eq_iff (sub_ne_zero.mpr hx)).mp h
    apply hab
    linear_combination -h'
  have hf : Function.Injective f := by
    intro x y h
    by_cases hx : x = b
    · by_contra hne
      have hy : y ≠ b := fun eq => hne (hx.trans eq.symm)
      exact fneq hy (h.symm.trans (by simp [f, hx]))
    by_cases hy : y = b
    · exact (fneq hx (h.trans (by simp [f, hy]))).elim
    have h' : (x - a) * (y - b) = (y - a) * (x - b) :=
      (div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)).mp (by simpa [f, hx, hy] using h)
    have hxy : (a - b) * (x - y) = 0 := by linear_combination h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hxy).resolve_left (sub_ne_zero.mpr hab))
  let e : F ≃ F := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hx (x : F) : quadraticChar F (e x) =
      quadraticChar F (x - a) * quadraticChar F (x - b) + if x = b then 1 else 0 := by
    change quadraticChar F (f x) = _
    by_cases h : x = b
    · simp [f, h]
    simp only [f, h, if_false, add_zero]
    rw [← map_mul]
    have he : (x - a) * (x - b) = ((x - a) / (x - b)) * (x - b) ^ 2 := by
      field_simp [sub_ne_zero.mpr h]
    rw [he, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr h), mul_one]
  have hs := e.sum_comp (fun x => quadraticChar F x)
  simp only [hx, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    quadraticChar_sum_zero hF] at hs
  linarith

private theorem sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    (∑ x : F, quadraticChar F (x - a)) = 0 := by
  calc
    _ = ∑ x : F, quadraticChar F x := by
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-a) : F ≃ F) (fun x => quadraticChar F x))
    _ = 0 := quadraticChar_sum_zero hF

private theorem sum_quadraticChar_sub_sq (a : F) :
    (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - a)) + 1 =
      (Fintype.card F : ℤ) := by
  classical
  have h (x : F) : quadraticChar F (x - a) * quadraticChar F (x - a) +
      (if x = a then 1 else 0 : ℤ) = 1 := by
    by_cases hx : x = a
    · simp [hx]
    · rw [if_neg hx, add_zero, ← pow_two, quadraticChar_sq_one (sub_ne_zero.mpr hx)]
  have hh : (∑ x : F, (quadraticChar F (x - a) * quadraticChar F (x - a) +
      (if x = a then (1 : ℤ) else 0))) = ∑ _ : F, (1 : ℤ) :=
    Finset.sum_congr rfl (fun x _ => h x)
  simpa [Finset.sum_add_distrib] using hh

/-- The Paley conference matrix with one extra row and column indexed by `none`. -/
def conference (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Matrix (Option F) (Option F) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => quadraticChar F (-1)
  | some a, some b => quadraticChar F (b - a)

theorem conference_transpose :
    (conference F)ᵀ = quadraticChar F (-1) • conference F := by
  ext i j
  rcases i with _ | i <;> rcases j with _ | j
  · simp [conference, transpose_apply]
  · simp [conference, transpose_apply]
  · simpa [conference, transpose_apply, smul_eq_mul, pow_two] using
      (quadraticChar_sq_one (F := F) (a := -1) (neg_ne_zero.mpr one_ne_zero)).symm
  · simp only [conference, transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show i - j = (-1 : F) * (j - i) by ring, map_mul]

theorem conference_mul_transpose (hF : ringChar F ≠ 2) :
    conference F * (conference F)ᵀ =
      (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
  classical
  have square : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
    rw [← pow_two, quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)]
  ext i j
  rcases i with _ | i <;> rcases j with _ | j
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
    exact sum_quadraticChar_sub hF j
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
    exact sum_quadraticChar_sub hF i
  · simp only [mul_apply, Fintype.sum_option, transpose_apply, conference, square,
      Matrix.smul_apply, smul_eq_mul, one_apply, Option.some.injEq]
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, mul_one, add_comm]
      exact sum_quadraticChar_sub_sq i
    · rw [if_neg h, mul_zero, quadraticChar_correlation hF h]
      norm_num

omit [DecidableEq F] in
private theorem char_ne_two_of_mod_four {r : ℕ} (hr : r % 2 = 1)
    (hcard : Fintype.card F % 4 = r) : ringChar F ≠ 2 := by
  intro h
  have := FiniteField.even_card_of_char_two h
  omega

private theorem conference_offdiag {i j : Option F} (h : i ≠ j) :
    conference F i j = 1 ∨ conference F i j = -1 := by
  rcases i with _ | i <;> rcases j with _ | j
  · exact (h rfl).elim
  · exact Or.inl rfl
  · exact quadraticChar_dichotomy (a := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)
  · exact quadraticChar_dichotomy (sub_ne_zero.mpr (fun e => h (congrArg some e.symm)))

private theorem conference_diag (i : Option F) : conference F i i = 0 := by
  cases i <;> simp [conference]

/-- Type I as a sign matrix over the integers, with both Gram identities. -/
theorem typeI_int (hq : Fintype.card F % 4 = 3) :
    ∃ H : Matrix (Option F) (Option F) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      H * Hᵀ = ((Fintype.card F : ℤ) + 1) • (1 : Matrix (Option F) (Option F) ℤ) ∧
      Hᵀ * H = ((Fintype.card F : ℤ) + 1) • (1 : Matrix (Option F) (Option F) ℤ) := by
  have hF : ringChar F ≠ 2 := char_ne_two_of_mod_four (by decide) hq
  have hχ : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by simp [FiniteField.isSquare_neg_one_iff, hq])
  let C := conference F
  have ht : Cᵀ = -C := by
    change (conference F)ᵀ = _
    rw [conference_transpose, hχ, neg_one_smul]
  have hm : C * Cᵀ = (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) :=
    conference_mul_transpose hF
  have hc : Cᵀ * C = C * Cᵀ := by rw [ht, neg_mul, mul_neg]
  refine ⟨C + 1, fun i j => ?_, ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      left
      simp [C, conference_diag, one_apply]
    · simpa [C, one_apply, h] using (conference_offdiag (F := F) h)
  · simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one]
    rw [hm, ht, add_smul, one_smul]
    abel
  · simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one]
    rw [hc, hm, ht, add_smul, one_smul]
    abel


/-- Type II as an integer sign matrix on two copies of the bordered field. -/
theorem typeII_int (hq : Fintype.card F % 4 = 1) :
    ∃ H : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      Hᵀ * H = (2 * ((Fintype.card F : ℤ) + 1)) •
        (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := by
  have hF : ringChar F ≠ 2 := char_ne_two_of_mod_four (by decide) hq
  have hχ : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (a := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)).2
      (by simp [FiniteField.isSquare_neg_one_iff, hq])
  let C := conference F
  let A := C + 1
  let B := C - 1
  let H := fromBlocks A B B (-A)
  have ht : Cᵀ = C := by
    change (conference F)ᵀ = _
    rw [conference_transpose, hχ, one_smul]
  have hC : C * C = (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
    have h := conference_mul_transpose hF
    change C * Cᵀ = _ at h
    rwa [ht] at h
  have hA (i j : Option F) : A i j = 1 ∨ A i j = -1 := by
    by_cases h : i = j
    · subst j
      left
      simp [A, C, conference_diag, one_apply]
    · simpa [A, C, one_apply, h] using (conference_offdiag (F := F) h)
  have hB (i j : Option F) : B i j = 1 ∨ B i j = -1 := by
    by_cases h : i = j
    · subst j
      right
      simp [B, C, conference_diag, one_apply]
    · simpa [B, C, one_apply, h] using (conference_offdiag (F := F) h)
  have hS : Hᵀ = H := by
    simp only [H, A, B, fromBlocks_transpose, transpose_add, transpose_sub, transpose_neg,
      transpose_one, ht]
  let d : ℤ := 2 * ((Fintype.card F : ℤ) + 1)
  have hD : A * A + B * B = d • (1 : Matrix (Option F) (Option F) ℤ) := by
    calc
      _ = (C * C + C * C) + (1 + 1) := by
        simp only [A, B, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one]
        abel
      _ = _ := by
        rw [hC]
        have h : d = ((Fintype.card F : ℤ) + (Fintype.card F : ℤ)) + (1 + 1) := by dsimp [d]; ring
        rw [h]
        simp only [add_smul, one_smul]
  have hcomm : A * B = B * A := by
    simp only [A, B, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one]
    abel
  refine ⟨H, ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hA i j
    · exact hB i j
    · exact hB i j
    · rcases hA i j with h | h
      · right
        change -A i j = -1
        rw [h]
      · left
        change -A i j = 1
        rw [h]
        norm_num
  · have hoff₁ : A * B + B * (-A) = 0 := by rw [mul_neg, hcomm, add_neg_cancel]
    have hoff₂ : B * A + (-A) * B = 0 := by rw [neg_mul, ← hcomm, add_neg_cancel]
    have hD₂ : B * B + (-A) * (-A) = d • (1 : Matrix (Option F) (Option F) ℤ) := by
      simpa [add_comm (B * B)] using hD
    calc
      Hᵀ * H = fromBlocks (d • (1 : Matrix (Option F) (Option F) ℤ)) 0 0
          (d • (1 : Matrix (Option F) (Option F) ℤ)) := by
        rw [hS]
        change fromBlocks A B B (-A) * fromBlocks A B B (-A) = _
        rw [fromBlocks_multiply, hD, hoff₁, hoff₂, hD₂]
      _ = d • (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := by
        have hone : fromBlocks (1 : Matrix (Option F) (Option F) ℤ) 0 0
            (1 : Matrix (Option F) (Option F) ℤ) =
            (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := fromBlocks_one
        rw [← hone, fromBlocks_smul]
        simp only [smul_zero]

private theorem real_witness_of_integer_gram {W : Type*} [Fintype W] [DecidableEq W]
    {n : ℕ} (hn : Fintype.card W = n) (H : Matrix W W ℤ)
    (hentry : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hgram : Hᵀ * H = (n : ℤ) • (1 : Matrix W W ℤ)) :
    ∃ M, Hadamard.IsHadamard' (n := n) M := by
  let e := (Fintype.equivFinOfCardEq hn).symm
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => (H (e i) (e j) : ℝ)
  refine ⟨M, ?_, ?_⟩
  · intro i j
    rcases hentry (e i) (e j) with h | h <;> simp [M, h]
  · ext i j
    calc
      _ = ∑ k : Fin n, ((H (e k) (e i) * H (e k) (e j) : ℤ) : ℝ) := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin n, (H (e k) (e i) : ℝ) * (H (e k) (e j) : ℝ)) = _
        simp only [Int.cast_mul]
      _ = ((Hᵀ * H) (e i) (e j) : ℝ) := by
        simp only [mul_apply, transpose_apply]
        exact e.sum_comp (fun k : W => ((H k (e i) * H k (e j) : ℤ) : ℝ)) |>.trans
          (by push_cast; rfl)
      _ = _ := by
        rw [hgram]
        by_cases h : i = j
        · simp [h, Matrix.smul_apply, one_apply, Matrix.natCast_apply]
        · have h' : e i ≠ e j := fun eq => h (e.injective eq)
          simp [h, h', Matrix.smul_apply, one_apply, Matrix.natCast_apply]

/-- The Paley type I witness for every prime-power order parameter congruent to 3 mod 4. -/
theorem typeI (q : ℕ) (hpow : IsPrimePow q) (hq : q % 4 = 3) :
    ∃ M, Hadamard.IsHadamard' (n := q + 1) M := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpow
  let _ : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  let _ : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ k := (Nat.card_eq_fintype_card).symm.trans
    (GaloisField.card p k hk.ne')
  obtain ⟨M, he, _, hg⟩ := typeI_int (F := F) (hc ▸ hq)
  exact real_witness_of_integer_gram (by simp [hc]) M he (by simpa [hc] using hg)

/-- The Paley type II witness for every prime-power order parameter congruent to 1 mod 4. -/
theorem typeII (q : ℕ) (hpow : IsPrimePow q) (hq : q % 4 = 1) :
    ∃ M, Hadamard.IsHadamard' (n := 2 * (q + 1)) M := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpow
  let _ : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  let _ : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ k := (Nat.card_eq_fintype_card).symm.trans
    (GaloisField.card p k hk.ne')
  obtain ⟨M, he, hg⟩ := typeII_int (F := F) (hc ▸ hq)
  have ho : Fintype.card (Option F ⊕ Option F) = 2 * (p ^ k + 1) := by
    simp [hc, two_mul]
  exact real_witness_of_integer_gram ho M he (by simpa [hc] using hg)

end

end PaleyHadamard


/-!
The sign matrices implement constructions in Cati and Pasechnik, A database of constructions of Hadamard matrices (arXiv:2411.18897), using SageMath reference seeds and Paley and Kronecker constructions. All finite orthogonality computations are proved in the Lean kernel.
-/
namespace HadamardBits
open scoped BigOperators Matrix
-- Each binary digit is stored as a base-1024 digit. Reduction modulo 1023
-- therefore counts the set bits when there are at most 1022 of them.
def spread : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, a => 1024 * spread n (a / 2) + a % 2

def distBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => distBits n (a / 2) (b / 2) + (if a % 2 = b % 2 then 0 else 1)

theorem dist_le (n a b : ℕ) : distBits n a b ≤ n := by
  induction n generalizing a b with
  | zero => simp [distBits]
  | succ n ih =>
    have := ih (a / 2) (b / 2)
    simp only [distBits]
    split <;> omega

theorem certificate (n a b : ℕ) (hn : n < 1023) :
    (spread n a ^^^ spread n b) % 1023 = distBits n a b := by
  induction n generalizing a b with
  | zero => simp [spread, distBits]
  | succ n ih =>
    let x := spread (n+1) a ^^^ spread (n+1) b
    let d := if a % 2 = b % 2 then 0 else 1
    have hq : x / 1024 = spread n (a/2) ^^^ spread n (b/2) := by
      change (_ ^^^ _) / 2^10 = _
      rw [Nat.xor_div_two_pow]
      change (1024 * _ + a % 2) / 1024 ^^^ (1024 * _ + b % 2) / 1024 = _
      rw [show (1024 * spread n (a/2) + a%2) / 1024 = spread n (a/2) by omega,
          show (1024 * spread n (b/2) + b%2) / 1024 = spread n (b/2) by omega]
    have hr : x % 1024 = d := by
      change (_ ^^^ _) % 2^10 = _
      rw [Nat.xor_mod_two_pow]
      change (1024 * _ + a % 2) % 1024 ^^^ (1024 * _ + b % 2) % 1024 = _
      rw [show (1024 * spread n (a/2) + a%2) % 1024 = a%2 by omega,
          show (1024 * spread n (b/2) + b%2) % 1024 = b%2 by omega]
      dsimp [d]
      rcases Nat.mod_two_eq_zero_or_one a with ha|ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb|hb <;> rw [ha,hb] <;> decide
    have hp := ih (a/2) (b/2) (by omega)
    have hle := dist_le n (a/2) (b/2)
    have hd : d ≤ 1 := by dsimp [d]; split <;> decide
    change x % 1023 = distBits n (a/2) (b/2) + d
    rw [← hq] at hp
    omega

def signAt (a : ℕ) (i : ℕ) : ℝ := if a.testBit i then -1 else 1

theorem dotBits (n a b : ℕ) :
    ∑ i : Fin n, signAt a i * signAt b i = (n : ℝ) - 2 * distBits n a b := by
  induction n generalizing a b with
  | zero => simp [distBits]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hstep (x i : ℕ) : signAt x (i+1) = signAt (x/2) i := by
      simp only [signAt, Nat.testBit_succ]
    simp only [Fin.val_succ, hstep, ih]
    simp only [distBits, Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_succ]
    simp only [signAt, Fin.val_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with ha|ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb|hb <;> simp [ha,hb] <;> ring
private theorem determinant_of_gram {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hs : ∀ i j, M i j ∈ ({1, -1} : Finset ℝ))
    (hg : M * M.transpose = (n : ℝ) • 1) : Hadamard.IsHadamard M := by
  refine ⟨hs, ?_⟩
  have hd : M.det ^ 2 = (n : ℝ) ^ n := by
    simpa [Matrix.det_smul, ← sq] using congrArg Matrix.det hg
  rw [← Real.sqrt_sq_eq_abs, hd, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1 <;> ring

private def gramWitness (n : ℕ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, M i j ∈ ({1,-1} : Finset ℝ)) ∧ M*M.transpose = (n:ℝ) • 1

private theorem gram_to_det {n : ℕ} (H : gramWitness n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Hadamard.IsHadamard M := by
  obtain ⟨M,hm,hg⟩ := H
  exact ⟨M,determinant_of_gram hm hg⟩

private theorem unitary_of_gram {n : ℕ} (hn : 0 < n) (h : gramWitness n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Matrix.IsHadamard M := by
  obtain ⟨M,hm,hg⟩ := h
  refine ⟨M, Matrix.IsHadamard.of_mul_conjTranspose (fun i j => ?_) ?_ ?_⟩
  · apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    simpa using hm i j
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hg
  · rw [isRegular_iff_ne_zero]
    simpa using (Nat.ne_of_gt hn)

private theorem gram_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : gramWitness a) (B : gramWitness b) : gramWitness (a*b) := by
  obtain ⟨M,hM⟩ := unitary_of_gram ha A
  obtain ⟨N,hN⟩ := unitary_of_gram hb B
  let e : Fin a × Fin b ≃ Fin (a*b) := finProdFinEquiv
  have h := (hM.kronecker hN).reindex e e
  refine ⟨(Matrix.reindex e e) (Matrix.kroneckerMap (· * ·) M N), fun i j => ?_, ?_⟩
  · simpa using Unitary.mem_iff_eq_one_or_eq_neg_one.mp (h.apply_mem i j)
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.mul_conjTranspose

private theorem matrix_of_distances (n : ℕ) (row : Fin n → ℕ) (hn : n < 1023)
    (hg : ∀ i j : Fin n, i ≠ j → 2 * ((spread n (row i) ^^^ spread n (row j)) % 1023) = n) :
    gramWitness n := by
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => signAt (row i) j
  refine ⟨M, (by
    intro i j
    dsimp [M, signAt]
    split <;> simp), ?_⟩
  ext i j
  change (∑ k : Fin n, signAt (row i) k * signAt (row j) k) = _
  rw [dotBits, ← certificate n _ _ hn]
  by_cases h : i = j
  · subst j
    simp
  · have h1 := hg i j h
    have h2 : (2 : ℝ) * ↑((spread n (row i) ^^^ spread n (row j)) % 1023) = (n : ℝ) :=
      by exact_mod_cast h1
    simp [h, h2]

private theorem constant_of_orders (K : ℕ)
    (h : ∀ k : ℕ, k ≤ K → ∃ M : Matrix (Fin (4*k)) (Fin (4*k)) ℝ, Hadamard.IsHadamard M) :
    (4 * (K+1) : ℕ∞) ≤ Hadamard.hadamardConstant := by
  unfold Hadamard.hadamardConstant
  refine le_iInf fun k => le_iInf fun hk => ?_
  have hlt : K < k := by
    by_contra! hle
    exact hk (h k hle)
  exact_mod_cast (by omega : 4*(K+1) ≤ 4*k)

private def digitMask : ℕ → ℕ
  | 0 => 0
  | n+1 => 1024*digitMask n + 1

private theorem digitMask_formula (n : ℕ) : digitMask n = (1024^n - 1) / 1023 := by
  suffices h : 1023*digitMask n + 1 = 1024^n by omega
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih, digitMask]; ring

private theorem binary_witness (n a : ℕ) (h : a &&& digitMask n = a) :
    ∃ b, spread n b = a := by
  induction n generalizing a with
  | zero =>
    simp only [digitMask, Nat.and_zero] at h
    exact ⟨0, h⟩
  | succ n ih =>
    have hq := congrArg (fun x : ℕ => x / 1024) h
    change (a &&& digitMask (n+1)) / 2^10 = a / 1024 at hq
    rw [Nat.and_div_two_pow] at hq
    have hm : digitMask (n+1) / 2^10 = digitMask n := by
      change (1024*digitMask n+1)/1024 = digitMask n
      omega
    rw [hm] at hq
    obtain ⟨b,hb⟩ := ih (a/1024) hq
    have hr := congrArg (fun x : ℕ => x % 1024) h
    change (a &&& digitMask (n+1)) % 2^10 = a % 1024 at hr
    rw [Nat.and_mod_two_pow] at hr
    have hrm : digitMask (n+1) % 2^10 = 1 := by
      change (1024*digitMask n+1)%1024 = 1
      omega
    rw [hrm, Nat.and_one_is_mod] at hr
    change (a%1024)%2 = a%1024 at hr
    refine ⟨2*b + a%1024, ?_⟩
    simp only [spread]
    rw [show (2*b+a%1024)/2=b by omega, hb]
    omega

private theorem matrix_of_packed (n : ℕ) (row : Fin n → ℕ) (hn : n < 1023)
    (hm : ∀ i, row i &&& ((1024^n-1)/1023) = row i)
    (hp : ∀ i j, i ≠ j → 2*((row i ^^^ row j)%1023)=n) :
    gramWitness n := by
  classical
  have hw (i : Fin n) : ∃ b, spread n b = row i :=
    binary_witness _ _ (by rw [digitMask_formula]; apply hm)
  choose dense hd using hw
  apply matrix_of_distances n dense hn
  simpa only [hd] using hp



private def fastSpread (v : ℕ) : ℕ :=
  let x := v
  let x := (x ||| (x <<< 4608)) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  let x := (x ||| (x <<< 2304)) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  let x := (x ||| (x <<< 1152)) &&& 0xffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff
  let x := (x ||| (x <<< 576)) &&& 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff
  let x := (x ||| (x <<< 288)) &&& 0xffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff
  let x := (x ||| (x <<< 144)) &&& 0xffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff
  let x := (x ||| (x <<< 72)) &&& 0xff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff000000000000000000ff
  let x := (x ||| (x <<< 36)) &&& 0xf000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f000000000f
  let x := (x ||| (x <<< 18)) &&& 0x3000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003000030000300003
  let x := (x ||| (x <<< 9)) &&& 0x401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401004010040100401
  x


-- Generated by lean_rows.py using the verified Hadamard recipes.
-- Bit j of hadRowN i represents the negative sign in column j of row i.

private def hadMask (w : Nat) : Nat := (1 <<< w) - 1

private def hadRot (w x shift : Nat) : Nat :=
  let s := shift % w
  ((x <<< s) &&& hadMask w) ||| (x >>> (w - s))

private def hadJoin4 (w a b c d : Nat) : Nat :=
  a ||| (b <<< w) ||| (c <<< (2 * w)) ||| (d <<< (3 * w))

private def hadDouble (w : Nat) (row : Nat → Nat) (i : Nat) : Nat :=
  let x := row (i % w)
  let y := if i < w then x else x ^^^ hadMask w
  x ||| (y <<< w)

private def hadPaley1 (core : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then 0 else (core (i - 1) <<< 1) ||| (1 <<< i)

private def hadPaley2 (w : Nat) (core : Nat → Nat) (i : Nat) : Nat :=
  let j := i % w
  let x := if j = 0 then 0 else core (j - 1) <<< 1
  let d := x ||| (1 <<< j)
  if i < w then x ||| (d <<< w) else d ||| ((x ^^^ hadMask w) <<< w)

private def hadCyclicCell (w r seed initial slope flips : Nat) : Nat :=
  let x := hadRot w seed (initial + r * slope)
  if flips.testBit r then x ^^^ hadMask w else x

private def hadCwTiles (w p0 p1 p2 p3 : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, route =>
    let s := route &&& 3
    let x := if s < 2 then (if s = 0 then p0 else p1) else (if s = 2 then p2 else p3)
    let y := if route.testBit 2 then x ^^^ hadMask w else x
    y ||| ((hadCwTiles w p0 p1 p2 p3 k (route >>> 3)) <<< w)

private def hadCwRow (t w s0 s1 s2 s3 : Nat) (routes : Nat → Nat) (i : Nat) : Nat :=
  let a := i % w
  hadCwTiles w (hadRot w s0 a) (hadRot w s1 a) (hadRot w s2 a) (hadRot w s3 a)
    (4 * t) (routes (i / w))

private def hadMyTile (m g a phase h inner left : Nat) (u k kt : Nat → Nat) : Nat :=
  let column := (h % 2) * m
  let piece :=
    if g / 2 = h / 2 then
      let x := (u ((g % 2) * m + a) >>> column) &&& hadMask m
      let y := if g = h then x ||| (1 <<< a) else x
      if phase = 0 then x ||| (y <<< m) else y ||| (x <<< m)
    else
      let base := if g < h then k (g * m + a) else kt ((g % 2) * m + a)
      let x := (base >>> column) &&& hadMask m
      let y := if (g = 1 ∧ h = 2) ∨ (g = 2 ∧ h = 1) then x ^^^ hadMask m else x
      let z := y ^^^ hadMask m
      if phase = 0 then y ||| (z <<< m) else z ||| (y <<< m)
  let idx := 4 * g + h
  let payload := if inner.testBit idx then piece ^^^ hadMask (2 * m) else piece
  (payload <<< 1) ||| (if left.testBit idx then 1 else 0)

private def hadMiyamotoRow (q inner left : Nat) (top u k kt : Nat → Nat) (i : Nat) : Nat :=
  let g := i / q
  let x := i % q
  if x = 0 then top g else
    let m := (q - 1) / 2
    let a := (x - 1) % m
    let phase := (x - 1) / m
    hadJoin4 q (hadMyTile m g a phase 0 inner left u k kt)
      (hadMyTile m g a phase 1 inner left u k kt)
      (hadMyTile m g a phase 2 inner left u k kt)
      (hadMyTile m g a phase 3 inner left u k kt)

private def hadRow1 (_ : Nat) : Nat := 0

private def hadRow2 (i : Nat) : Nat :=
  if i = 0 then 0 else 2

private def hadRow4 (i : Nat) : Nat :=
  hadDouble 2 hadRow2 i

private def hadRow8 (i : Nat) : Nat :=
  hadDouble 4 hadRow4 i

private def hadCore12 (i : Nat) : Nat := hadRot 11 0x23a i

private def hadRow12 (i : Nat) : Nat :=
  hadPaley1 hadCore12 i

private def hadRow16 (i : Nat) : Nat :=
  hadDouble 8 hadRow8 i

private def hadCore20 (i : Nat) : Nat := hadRot 19 0x30af2 i

private def hadRow20 (i : Nat) : Nat :=
  hadPaley1 hadCore20 i

private def hadRow24 (i : Nat) : Nat :=
  hadDouble 12 hadRow12 i

private def hadCore28 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0xa82f669883f26838e7268aaaf2618e3d2703ee5250bead211be2d2
      else
        0x3f26b10e726872af261563d2631ee52607ead2217e2d2233827669
    else
      if slot < 3 then
        0x26871cf261555d2631c7d2607dcd2217d4d2237c67669702f66950
      else
        0x69704ee69505ea6b107e
  (x >>> ((i % 8) * 27)) &&& hadMask 27

private def hadRow28 (i : Nat) : Nat :=
  hadPaley1 hadCore28 i

private def hadRow32 (i : Nat) : Nat :=
  hadDouble 16 hadRow16 i

private def hadCore36 (i : Nat) : Nat := hadRot 17 0x5ce8 i

private def hadRow36 (i : Nat) : Nat :=
  hadPaley2 18 hadCore36 i

private def hadRow40 (i : Nat) : Nat :=
  hadDouble 20 hadRow20 i

private def hadCore44 (i : Nat) : Nat := hadRot 43 0x35883a3ee52 i

private def hadRow44 (i : Nat) : Nat :=
  hadPaley1 hadCore44 i

private def hadRow48 (i : Nat) : Nat :=
  hadDouble 24 hadRow24 i

private def hadCore52 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0xd2e60cb6b9072dae01c75b5c09d6c70674b9838dae40eb6b80
      else
        0xe01d6d35c03aec704eab9833aae41c6eb807596d700f5b1c13
    else
      if slot < 3 then
        0x4eb63833a5cc1c6d72075b5c700eb69c13ada60ce979071b5
      else
        0x3adae
  (x >>> ((i % 8) * 25)) &&& hadMask 25

private def hadRow52 (i : Nat) : Nat :=
  hadPaley2 26 hadCore52 i

private def hadRow56 (i : Nat) : Nat :=
  hadDouble 28 hadRow28 i

private def hadCore60 (i : Nat) : Nat := hadRot 59 0x22b62183e7b92ba i

private def hadRow60 (i : Nat) : Nat :=
  hadPaley1 hadCore60 i

private def hadRow64 (i : Nat) : Nat :=
  hadDouble 32 hadRow32 i

private def hadCore68 (i : Nat) : Nat := hadRot 67 0x359c281ba27ebc652 i

private def hadRow68 (i : Nat) : Nat :=
  hadPaley1 hadCore68 i

private def hadRow72 (i : Nat) : Nat :=
  hadDouble 36 hadRow36 i

private def hadCore76 (i : Nat) : Nat := hadRot 37 0x9a1dee164 i

private def hadRow76 (i : Nat) : Nat :=
  hadPaley2 38 hadCore76 i

private def hadRow80 (i : Nat) : Nat :=
  hadDouble 40 hadRow40 i

private def hadCore84 (i : Nat) : Nat := hadRot 83 0x26873a80b1372fea31e9a i

private def hadRow84 (i : Nat) : Nat :=
  hadPaley1 hadCore84 i

private def hadRow88 (i : Nat) : Nat :=
  hadDouble 44 hadRow44 i

private def hadRow92 (i : Nat) : Nat :=
  let r := i % 23
  if i < 23 then
    hadJoin4 23
      (hadCyclicCell 23 r 0x8b447 22 1 0x7fffff)
      (hadCyclicCell 23 r 0x19293 15 1 0x0)
      (hadCyclicCell 23 r 0x394a7 3 1 0x0)
      (hadCyclicCell 23 r 0x177dd 15 1 0x7fffff)
  else
  if i < 46 then
    hadJoin4 23
      (hadCyclicCell 23 r 0x19293 15 1 0x7fffff)
      (hadCyclicCell 23 r 0x8b447 22 1 0x7fffff)
      (hadCyclicCell 23 r 0x177dd 15 1 0x0)
      (hadCyclicCell 23 r 0x394a7 3 1 0x0)
  else
  if i < 69 then
    hadJoin4 23
      (hadCyclicCell 23 r 0x394a7 3 1 0x7fffff)
      (hadCyclicCell 23 r 0x177dd 15 1 0x7fffff)
      (hadCyclicCell 23 r 0x8b447 22 1 0x7fffff)
      (hadCyclicCell 23 r 0x19293 15 1 0x7fffff)
  else
    hadJoin4 23
      (hadCyclicCell 23 r 0x177dd 15 1 0x0)
      (hadCyclicCell 23 r 0x394a7 3 1 0x7fffff)
      (hadCyclicCell 23 r 0x19293 15 1 0x0)
      (hadCyclicCell 23 r 0x8b447 22 1 0x7fffff)

private def hadRow96 (i : Nat) : Nat :=
  hadDouble 48 hadRow48 i

private def hadCore100 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 3 then
      if slot < 1 then
        0xb59b35a7801e1e5acd9ad3c007d6b366b0f011d5ecd8ae380c755b36ab8c071d46cdeae203c359b35af800f2d66cd69e00
      else
        if slot < 2 then
          0x9b35af801e1ae6cd69e0079696b366b4f003d5acd9ac3c00f57b362b8e023d56cdaae3018f51b37ab880e2d66cd6be0078
        else
          0x37ab880e3a8dcd6be00786b3735a7801e5acccd9ad3c00f2db366b0f003eb6cd8ae3808eadb36ab8c063aa6cdeae2038ea
    else
      if slot < 5 then
        if slot < 4 then
          0xab8c063aad9b6ae2038ea366daf801e1acd9b69e00796b36666b4f003cb59d9ac3c00fad6762b8e023abd8daae3018eab6
        else
          0x8e023abd9b15e3018eab66d57880e3a8d9bd5e00786b366b57801e5acd9ad2d3c00f2d66ceb0f003eb59b2ae3808eaf66c
      else
        if slot < 6 then
          0x3eb59b3587808eaf66c571c063aad9b55c6038ea366f57101e1acd9ad7c00796b366b4f0f003cb59b35a3c00fad66cd6
        else
          0xf2d66cd69e
  (x >>> ((i % 8) * 49)) &&& hadMask 49

private def hadRow100 (i : Nat) : Nat :=
  hadPaley2 50 hadCore100 i

private def hadRow104 (i : Nat) : Nat :=
  hadDouble 52 hadRow52 i

private def hadCore108 (i : Nat) : Nat := hadRot 107 0x27816ea9821633397be6a897e1a i

private def hadRow108 (i : Nat) : Nat :=
  hadPaley1 hadCore108 i

private def hadRow112 (i : Nat) : Nat :=
  hadDouble 56 hadRow56 i

private def hadMyU116 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0xd915730a26c33af4c12c67e205c9ad1a255561f02b3b869649ac9c1c
      else
        0x2f40b4d35a25c64d64e0e87709a5e1ab50362d6a9111fa4e80cbd8d2
    else
      if slot < 3 then
        0x623a19b930f13ccc8945744cfa8ac324f23711b661a897b50d86178c
      else
        0x16b18e90bd2cb4186cc7aa4542b7
  (x >>> ((i % 8) * 28)) &&& hadMask 28

private def hadMyK116 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0x3be06caf1c6364eaaa1b2e71c2d87e08d6cbd054b6dc83a5a0000000
      else
        0x8c6cbc654367aa385b39c11ad9f80a96ef4074b7728fb132c57d0996
    else
      if slot < 3 then
        0x6cf5550b6738e05b3f0462dde82a96ee41c6265a3ea132d5ec0d94ee
      else
        0xcb47d8865abe84b29df02d978e30
  (x >>> ((i % 8) * 28)) &&& hadMask 28

private def hadMyTop116 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xfffffff80000003ffffffdfffffff0000000000000000000001ffffffe
    else
      0xfffffff7ffffffc0000001fffffff00000007ffffffbffffffffffffff
  (x >>> ((i % 2) * 116)) &&& hadMask 116

private def hadRow116 (i : Nat) : Nat :=
  hadMiyamotoRow 29 21392 55217 hadMyTop116 hadMyU116
    hadRow28 hadMyK116 i

private def hadRow120 (i : Nat) : Nat :=
  hadDouble 60 hadRow60 i

private def hadCore124 (i : Nat) : Nat := hadRot 61 0x8ec196bf5a60dc4 i

private def hadRow124 (i : Nat) : Nat :=
  hadPaley2 62 hadCore124 i

private def hadRow128 (i : Nat) : Nat :=
  hadDouble 64 hadRow64 i

private def hadCore132 (i : Nat) : Nat := hadRot 131 0x22a273a784a132c03fcb37ade1a31baba i

private def hadRow132 (i : Nat) : Nat :=
  hadPaley1 hadCore132 i

private def hadRow136 (i : Nat) : Nat :=
  hadDouble 68 hadRow68 i

private def hadCore140 (i : Nat) : Nat := hadRot 139 0x30ab7730c190a4be0af82daf67cf3112af2 i

private def hadRow140 (i : Nat) : Nat :=
  hadPaley1 hadCore140 i

private def hadRow144 (i : Nat) : Nat :=
  hadDouble 72 hadRow72 i

private def hadCore148 (i : Nat) : Nat := hadRot 73 0x14dd38bd86f472eca0 i

private def hadRow148 (i : Nat) : Nat :=
  hadPaley2 74 hadCore148 i

private def hadRow152 (i : Nat) : Nat :=
  hadDouble 76 hadRow76 i

private def hadRow156 (i : Nat) : Nat :=
  let r := i % 39
  if i < 39 then
    hadJoin4 39
      (hadCyclicCell 39 r 0x2619053e5 32 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x32eb7b5d3 3 1 0x0)
      (hadCyclicCell 39 r 0xecf5af37 4 1 0x0)
      (hadCyclicCell 39 r 0x2b11a83b7 15 1 0x7fffffffff)
  else
  if i < 78 then
    hadJoin4 39
      (hadCyclicCell 39 r 0x32eb7b5d3 3 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x2619053e5 32 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x2b11a83b7 15 1 0x0)
      (hadCyclicCell 39 r 0xecf5af37 4 1 0x0)
  else
  if i < 117 then
    hadJoin4 39
      (hadCyclicCell 39 r 0xecf5af37 4 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x2b11a83b7 15 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x2619053e5 32 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x32eb7b5d3 3 1 0x7fffffffff)
  else
    hadJoin4 39
      (hadCyclicCell 39 r 0x2b11a83b7 15 1 0x0)
      (hadCyclicCell 39 r 0xecf5af37 4 1 0x7fffffffff)
      (hadCyclicCell 39 r 0x32eb7b5d3 3 1 0x0)
      (hadCyclicCell 39 r 0x2619053e5 32 1 0x7fffffffff)

private def hadRow160 (i : Nat) : Nat :=
  hadDouble 80 hadRow80 i

private def hadCore164 (i : Nat) : Nat := hadRot 163 0x359c791f842ca8113adba24a377eacbde0761c652 i

private def hadRow164 (i : Nat) : Nat :=
  hadPaley1 hadCore164 i

private def hadRow168 (i : Nat) : Nat :=
  hadDouble 84 hadRow84 i

private def hadRow172 (i : Nat) : Nat :=
  let r := i % 43
  if i < 43 then
    hadJoin4 43
      (hadCyclicCell 43 r 0x64bc71e93 26 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x29a85e8565 3 1 0x0)
      (hadCyclicCell 43 r 0x1103d649af 9 1 0x0)
      (hadCyclicCell 43 r 0x5132286773 36 1 0x0)
  else
  if i < 86 then
    hadJoin4 43
      (hadCyclicCell 43 r 0x29a85e8565 3 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x64bc71e93 26 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x5132286773 36 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x1103d649af 9 1 0x0)
  else
  if i < 129 then
    hadJoin4 43
      (hadCyclicCell 43 r 0x1103d649af 9 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x5132286773 36 1 0x0)
      (hadCyclicCell 43 r 0x64bc71e93 26 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x29a85e8565 3 1 0x7ffffffffff)
  else
    hadJoin4 43
      (hadCyclicCell 43 r 0x5132286773 36 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x1103d649af 9 1 0x7ffffffffff)
      (hadCyclicCell 43 r 0x29a85e8565 3 1 0x0)
      (hadCyclicCell 43 r 0x64bc71e93 26 1 0x7ffffffffff)

private def hadRow176 (i : Nat) : Nat :=
  hadDouble 88 hadRow88 i

private def hadCore180 (i : Nat) : Nat := hadRot 179 0x23b025aaf6c8272305c30a3af3c5f3b1bec90aa5bf23a i

private def hadRow180 (i : Nat) : Nat :=
  hadPaley1 hadCore180 i

private def hadRow184 (i : Nat) : Nat :=
  hadDouble 92 hadRow92 i

private def hadRow188 (i : Nat) : Nat :=
  let r := i % 47
  if i < 47 then
    hadJoin4 47
      (hadCyclicCell 47 r 0x1eb9da2963b 17 1 0x0)
      (hadCyclicCell 47 r 0x2238c842c97 36 46 0x0)
      (hadCyclicCell 47 r 0x1bb2d748baf 36 46 0x7fffffffffff)
      (hadCyclicCell 47 r 0x1cdef525c11 26 46 0x0)
  else
  if i < 94 then
    hadJoin4 47
      (hadCyclicCell 47 r 0x2238c842c97 36 46 0x7fffffffffff)
      (hadCyclicCell 47 r 0x1eb9da2963b 17 1 0x0)
      (hadCyclicCell 47 r 0x1107495ef67 26 46 0x7fffffffffff)
      (hadCyclicCell 47 r 0x1eba25d69bb 16 46 0x7fffffffffff)
  else
  if i < 141 then
    hadJoin4 47
      (hadCyclicCell 47 r 0x1bb2d748baf 36 46 0x0)
      (hadCyclicCell 47 r 0x1107495ef67 26 46 0x0)
      (hadCyclicCell 47 r 0x1eb9da2963b 17 1 0x0)
      (hadCyclicCell 47 r 0x3a4d084c711 15 46 0x7fffffffffff)
  else
    hadJoin4 47
      (hadCyclicCell 47 r 0x1cdef525c11 26 46 0x7fffffffffff)
      (hadCyclicCell 47 r 0x1eba25d69bb 16 46 0x0)
      (hadCyclicCell 47 r 0x3a4d084c711 15 46 0x0)
      (hadCyclicCell 47 r 0x1eb9da2963b 17 1 0x0)

private def hadRow192 (i : Nat) : Nat :=
  hadDouble 96 hadRow96 i

private def hadCore196 (i : Nat) : Nat := hadRot 97 0x149d74b89f9867e474bae4a0 i

private def hadRow196 (i : Nat) : Nat :=
  hadPaley2 98 hadCore196 i

private def hadRow200 (i : Nat) : Nat :=
  hadDouble 100 hadRow100 i

private def hadCore204 (i : Nat) : Nat := hadRot 101 0xc6e480f2cfaad57cd3c049d8c i

private def hadRow204 (i : Nat) : Nat :=
  hadPaley2 102 hadCore204 i

private def hadRow208 (i : Nat) : Nat :=
  hadDouble 104 hadRow104 i

private def hadCore212 (i : Nat) : Nat := hadRot 211 0x31a9633dd3e0a04d18b406fa62ab9a09fd2e74dfaf83443396a72 i

private def hadRow212 (i : Nat) : Nat :=
  hadPaley1 hadCore212 i

private def hadRow216 (i : Nat) : Nat :=
  hadDouble 108 hadRow108 i

private def hadCore220 (i : Nat) : Nat := hadRot 109 0x8ad9c60b17a4ffc97a3418e6d44 i

private def hadRow220 (i : Nat) : Nat :=
  hadPaley2 110 hadCore220 i

private def hadRow224 (i : Nat) : Nat :=
  hadDouble 112 hadRow112 i

private def hadCore228 (i : Nat) : Nat := hadRot 227 0x26876a8197663bac38809297a071371fa16b6fee3ca2399167ea91e9a i

private def hadRow228 (i : Nat) : Nat :=
  hadPaley1 hadCore228 i

private def hadRow232 (i : Nat) : Nat :=
  hadDouble 116 hadRow116 i

private def hadRow236 (i : Nat) : Nat :=
  let r := i % 59
  if i < 59 then
    hadJoin4 59
      (hadCyclicCell 59 r 0x3086e5d0ba19a1 5 1 0x0)
      (hadCyclicCell 59 r 0x42cc2e9086e5d3 58 58 0x0)
      (hadCyclicCell 59 r 0x85985d74589ef 2 58 0x7ffffffffffffff)
      (hadCyclicCell 59 r 0x42cc2eaf791a2d 58 58 0x0)
  else
  if i < 118 then
    hadJoin4 59
      (hadCyclicCell 59 r 0x42cc2e9086e5d3 58 58 0x7ffffffffffffff)
      (hadCyclicCell 59 r 0x3086e5d0ba19a1 5 1 0x0)
      (hadCyclicCell 59 r 0x42a2f32f7a5d3b 40 58 0x0)
      (hadCyclicCell 59 r 0xf791a2eba19a1 4 58 0x7ffffffffffffff)
  else
  if i < 177 then
    hadJoin4 59
      (hadCyclicCell 59 r 0x85985d74589ef 2 58 0x0)
      (hadCyclicCell 59 r 0x42a2f32f7a5d3b 40 58 0x7ffffffffffffff)
      (hadCyclicCell 59 r 0x3086e5d0ba19a1 5 1 0x0)
      (hadCyclicCell 59 r 0x425d0cd0865d3b 40 58 0x7ffffffffffffff)
  else
    hadJoin4 59
      (hadCyclicCell 59 r 0x42cc2eaf791a2d 58 58 0x7ffffffffffffff)
      (hadCyclicCell 59 r 0xf791a2eba19a1 4 58 0x0)
      (hadCyclicCell 59 r 0x425d0cd0865d3b 40 58 0x0)
      (hadCyclicCell 59 r 0x3086e5d0ba19a1 5 1 0x0)

private def hadRow240 (i : Nat) : Nat :=
  hadDouble 120 hadRow120 i

private def hadCore244 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 15 then
      if slot < 7 then
        if slot < 3 then
          if slot < 1 then
            0xb343cb4c390803f8eacbb167fe3ef942d23e0a66a9fac88a16b1d986f2680ba475b4519080bdc7acb9177f73eeb02d2bc43662bf2cc181795c987d26a88347c96a2a01e35a93c73d2dfdaef9a262570a62e4fd580372b381a6f26e08357c94a3809c3d89ae3ad6dfd3ef982721e0a72a5f9c80b56b189a6f26608a774b43180b8adc9aaba96ffd3ee983529c435627f8c81b179509a7d27288317d1762206e15b93675d3dfda2fca0e217ca42fcf15605733341e6d2560839799723007c1d99b63cd7dfd32f584701eca52f5d1d40d53b309e6d21608ab78b33101788dd9b2ae9effd16e585509ec256e798f00f1b930ba6d2
          else
            if slot < 2 then
              0xa4758171908689c7ac17977f772eb02e7dc436257f2ccc51795c307d26930347cd122a012d5a93dc6d2dfce6f9a235d70a6c4cfd585c72b38066f26834357cc12380929d89af86d6dfc76f982a79e0a6e45f9ca5556b18166f26130a774c13180968dc9af1696ff576e983a79c436a47f8cac717950327d26138317e51622022d5b93dc5d3dece2fca3b417ca1c7cf1585d7332c0e6d26828397ac32300329d99af8cd7dec72f587a41eca8e75d1ca5d53b281e6d26108ab72c33101168dd9af0e9efe556e58fa09ec2aae798cacf1b9603a6d26109741cb68ab01037aabcb332efeaef96252770a64e1fe588312b399a2f269
            else
              0x7cd1068012d4553dc6b55fce7a5a235df2a6c4ae1585c9fb3806e526834df7cc10680929471af87b1dfc75ad82a7df0a6e43c1ca54bfb1816ad26134df74c11480968639af15b8ff5752d83a7dd436a5388cac4ff950362d26134f97e51062022ec593dc2b7deceba4a3b45fca1c42f1585f9f32c0ae52683cd97ac1070032e459af83b7dec79a587a65eca8e03d1ca5ebbb281aad2613ccb72c11501166659af11befe55d258fa2dec2aa1398cadcfb9601e2d26174f41cb12ab010d1aabc86f2efee6796255df0a644efe589c32b39862f26934343ca1639082998eac87d67fe767942c7de0a6647fac8d516b1d146f26930
        else
          if slot < 5 then
            if slot < 4 then
              0x94a3809c3d89af041abe53ef982721e0a71d6b6fc0b56b189a6f26952fce4b43180b8adc9ab0453bad3ee983529c4355d4b7f81b179509a7d26b13fc651762206e15b9394418bfda2fca0e217ca33ae9ef605733341e6d2617e78a99723007c1d99ab041cbfd32f584701ecab1e6bef40d53b309e6d2297ae8e8b33101788dd98b0455bfd16e585509ec39574f7f00f1b930ba6d22b73cc7cb12e8010d1563c86f55fee665c255df2e644ee1589c3fc398625669345e7ca16680829872ac87f1dfe762cc2c7df2a6647c1c8d53f51d142d66930de75817480868a33ac17b8ff7722e82e7dd63625788ccc57e55c302f26930fa
            else
              0x3180968dc9af1453ba60ee983a79c436a54b7fabb17950327d26133fc6563622022d5b93dc418bf282fca3b417ca1c6e9ef6757332c0e6d2683e78ac2f2300329d99af841cbd612f587a41eca8e66bef63d53b281e6d2613ae8e52b3101168dd9af0455b9616e58fa09ec2aa74f7f2af1b9603a6d26173cc65668ab01037aabc84ba0e5aef96252770a6599977f4312b399a2f26970ff2c54c390803f8eac859a1e53ef942d23e0a65d8b3ff0a16b1d986f26954fd6474519080bdc7ac05d23ad3eeb02d2bc4365c8bbfb181795c987d26b15f96616a2a01e35a93d441a3e5aef9a262570a639e96fe0372b381a6f269727eac
          else
            if slot < 6 then
              0x2022ec593dc2b4bf28834a3b45fca1c42fef675d332c0ae52683cd8ac2fcf0032e459af83b4bd6083587a65eca8e03fef63cd3b281aad2613cc8e52f5d01166659af11b5b9608a58fa2dec2aa13f7f2ae9b9601e2d26174cc656e7ab010d1aabc86fa0e589796255df0a644e977f7332b39862f269347f2c4e139082998eac87da1e50b7942c7de0a6646b3ff3b16b1d146f26930fd646a91908689c7ac17d23ac0beb02e7dc436254bbfbb91795c307d26931f96662a2a012d5a93dc61a3e688f9a235d70a6c4e96fe7372b38066f268367eac2e2380929d89af861abe60af982a79e0a6e46b6fe3b56b18166f26132fce52a
            else
              0x7c1d99ab041cbccb91804701ecab1e6befe997ac309e6d2297ae8ea06a9d9788dd98b0455bc5998805509ec39574f7fe8b72c30ba6d22b73cc78078dc810d1563c86f55e589740255df2e644ee17f7332e398625669345e6c4e1fe0829872ac87f1de50b3402c7df2a6647c1ff3b1671d142d66930de646a9fa0868a33ac17b8fac0ba402e7dd63625789fbb91755c302f26930fa6662bf2012d4553dc6b53e68834a235df2a6c4ae2fe73d2b3806e526834deac2e4fc0929471af87b1be6083582a7df0a6e43c6fe3ad6b1816ad26134dce52a5f80968639af15b9ba608a583a7dd436a5387faba97950362d26134fc65627f
      else
        if slot < 11 then
          if slot < 9 then
            if slot < 8 then
              0x8dd9af0455b96198808b09ec2aa74f7f2ab72c7d3a6d26173cc65678dcb0037aabc84ba0e5b4558082770a6599977f577cb129a2f26970ff2c418959cc3f8eac859a1e5a61c84123e0a65d8b3ff1f7ca16986f26954fd64450b58e8bdc7ac05d23ada28c8412bc4365c8bbfb9f75816987d26b15f9660c0bcaee35a93d441a3e4b51500e2570a639e96fed77cd101a6f269727eac01b959dc3d89af041abe4a51c04721e0a71d6b6fe9f7cc109a6f26952fce405ab58f8adc9ab0453ba5a18c05529c4355d4b7fe9f74c109a7d26b13fc640d8bcaee15b9394418be8bb1100e217ca33ae9efed17e5141e6d2617e78ab02b999
            else
              0xaabc86fa0e5895580868f0a644e977f733cb12aeef269347f2c4e1959cc318eac87da1e50b1c8414ce0a6646b3ff3b3ca163eef26930fd646a8b58e8a1c7ac17d23ac0b8c84345c436254bbfbb9758173e7d26931f966628bcae185a93dc61a3e689150096970a6c4e96fe737cd11ae6f268367eac2e3959c03d89af861abe6091c04949e0a6e46b6fe3b7cc153e6f26132fce52aab58c0adc9af1453ba6098c04b49c436a54b7fabb74c1d3a7d26133fc65638bca8195b93dc418bf28b11011617ca1c6e9ef6717e51dae6d2683e78ac2eb999601d99af841cbd6191801941eca8e66bef6397ac3d3e6d2613ae8e52ea9d940
          else
            if slot < 10 then
              0xac87f1de50b340414c3926647c1ff3b166163ef966930de646a9fa8e8a16bac17b8fac0ba404345193625789fbb9174173eeb26930fa6662bf2ae181793dc6b53e688340096a2aa6c4ae2fe73d2d11aef926834deac2e4fd9c03729af87b1be608340494a38a6e43c6fe3ad6c153ef926134dce52a5fd8c0b569af15b9ba608a404b431c36a5387faba96c1d3ee926134fc65627fca81b1793dc2b4bf28831011762ca1c42fef675d251da2fd2683cd8ac2fcf99605719af83b4bd60838019722ca8e03fef63cd2c3d32fd2613cc8e52f5dd940d559af11b5b9608a808b332c2aa13f7f2ae92c7d16ed26174cc656e7dcb00f1
            else
              0xb9177f73eeb02d2bc43662bf2cc181795c987d2681748eb68a321017b8f5873d2dfdaef9a262570a62e4fd580372b381a6f26d1068f92d45403c6b527a3ad6dfd3ef982721e0a72a5f9c80b56b189a6f26c106af9294701387b135aba96ffd3ee983529c435627f8c81b179509a7d26c114ee9686301715b935675d3dfda2fca0e217ca42fcf15605733341e6d2651062fa2ec440dc2b72763cd7dfd32f584701eca52f5d1d40d53b309e6d22c1072f32e4600f83b3372ae9effd16e585509ec256e798f00f1b930ba6d22c1156f1666202f11bb33c86f55e5897400868ab2644ee17f7332e12aef9669345e6c4e1fe1cc312b
        else
          if slot < 13 then
            if slot < 12 then
              0xd2dfce6f9a235d70a6c4cfd585c72b38066f2683468f9a2454025ab527b8cd6dfc76f982a79e0a6e45f9ca5556b18166f261306af9824701253b135f0e96ff576e983a79c436a47f8cac717950327d261314ee98263012d1b935e2dd3dece2fca3b417ca1c7cf1585d7332c0e6d2683062fca2c44045ab727b8cd7dec72f587a41eca8e75d1ca5d53b281e6d2611072f5864600653b335f0e9efe556e58fa09ec2aae798cacf1b9603a6d2611156e58662022d1bb35e3332efeaef96252770a64e1fe588312b399a2f26912e8396d1560206f55793b167fe3ef942d23e0a66a9fac88a16b1d986f268166879698721007f1d59
            else
              0xdfc75ad82a7df0a6e43c1ca54bfb1816ad26134def9820d012528e35f0f62ff5752d83a7dd436a5388cac4ff950362d26134fee98229012d0c735e2b73deceba4a3b45fca1c42f1585f9f32c0ae52683cd2fca20c4045d8b27b856fdec79a587a65eca8e03d1ca5ebbb281aad2613cd2f5820e0065c8b35f076efe55d258fa2dec2aa1398cadcfb9601e2d26174d6e5822a022cccb35e2372efee6796255df0a644efe589c32b39862f26934683962556021a355790dd67fe767942c7de0a6647fac8d516b1d146f26930687942c72105331d590f977f772eb02e7dc436257f2ccc51795c307d2693148eb02e3210d138f582f
          else
            if slot < 14 then
              0xd3ee983529c4355d4b7f81b179509a7d26b13fc65686301715b935608a775da2fca0e217ca33ae9ef605733341e6d2617e78aa2ec440dc2b727288317fd32f584701ecab1e6bef40d53b309e6d2297ae8e32e4600f83b335608397fd16e585509ec39574f7f00f1b930ba6d22b73cc71666202f11bb31608ab7fee665c255df2e644ee1589c3fc398625669345e79625d0021a2ac790deabfe762cc2c7df2a6647c1c8d53f51d142d66930de7942cd010530e5590fe3bf7722e82e7dd63625788ccc57e55c302f26930faeb02e9010d1467582f71dfce7a5a235df2a6c4ae1585c9fb3806e526834def9a20d0025a8aa7b8d6a
            else
              0x2fca3b417ca1c6e9ef6757332c0e6d2683e78ac2ec44045ab727b88317e512f587a41eca8e66bef63d53b281e6d2613ae8e52e4600653b335f08397ac16e58fa09ec2aa74f7f2af1b9603a6d26173cc656662022d1bb35e08ab72c2ef96252770a6599977f4312b399a2f26970ff2c4d1560206f557909741cb3ef942d23e0a65d8b3ff0a16b1d986f26954fd64698721007f1d590b343cb3eeb02d2bc4365c8bbfb181795c987d26b15f96668a321017b8f580ba4759aef9a262570a639e96fe0372b381a6f269727eac2d45403c6b527a88347cd3ef982721e0a71d6b6fc0b56b189a6f26952fce5294701387b135e08357c
    else
      if slot < 23 then
        if slot < 19 then
          if slot < 17 then
            if slot < 16 then
              0x587a65eca8e03fef63cd3b281aad2613cc8e52f5e0065c8b35f07697ac10658fa2dec2aa13f7f2ae9b9601e2d26174cc656e7a022cccb35e236b72c11796255df0a644e977f7332b39862f269347f2c4e156021a355790df41cb12f942c7de0a6646b3ff3b16b1d146f26930fd646a872105331d590fb43ca16eb02e7dc436254bbfbb91795c307d26931f96662a3210d138f582fa475816f9a235d70a6c4e96fe7372b38066f268367eac2e454025ab527b8c347cd12f982a79e0a6e46b6fe3b56b18166f26132fce52a4701253b135f0c357cc16e983a79c436a54b7fabb17950327d26133fc656263012d1b935e28a774c1
            else
              0x5509ec39574f7fe8b72c30ba6d22b73cc78078dcaf11bb31608ab78b33100255df2e644ee17f7332e398625669345e6c4e1fe021a2ac790deabcb12e802c7df2a6647c1ff3b1671d142d66930de646a9fa10530e5590fe3bca166802e7dd63625789fbb91755c302f26930fa6662bf210d1467582f71f581748a235df2a6c4ae2fe73d2b3806e526834deac2e4fc025a8aa7b8d6a7cd106982a7df0a6e43c6fe3ad6b1816ad26134dce52a5f812528e35f0f637cc106983a7dd436a5387faba97950362d26134fc65627f012d0c735e2b7374c114ca3b45fca1c42fef675d332c0ae52683cd8ac2fce4045d8b27b85697e5106
          else
            if slot < 18 then
              0x2770a6599977f577cb129a2f26970ff2c418959cc6f557909741cb68ab01123e0a65d8b3ff1f7ca16986f26954fd64450b58e87f1d590b343cb4c390812bc4365c8bbfb9f75816987d26b15f9660c0bcae17b8f580ba475b45190862570a639e96fed77cd101a6f269727eac01b959dc6b527a88347c96a2a01721e0a71d6b6fe9f7cc109a6f26952fce405ab58f87b135e08357c94a3809529c4355d4b7fe9f74c109a7d26b13fc640d8bcaf15b935608a774b431808e217ca33ae9efed17e5141e6d2617e78ab02b999dc2b727288317d1762204701ecab1e6befe997ac309e6d2297ae8ea06a9d8f83b3356083979972300
            else
              0xe0a6646b3ff3b3ca163eef26930fd646a8b58e8a31d590fb43ca163908299c436254bbfbb9758173e7d26931f966628bcae1838f582fa475817190868970a6c4e96fe737cd11ae6f268367eac2e3959c03b527b8c347cd122a012d1e0a6e46b6fe3b7cc153e6f26132fce52aab58c0bb135f0c357cc123809299c436a54b7fabb74c1d3a7d26133fc65638bca819b935e28a774c1318096817ca1c6e9ef6717e51dae6d2683e78ac2eb999602b727b88317e51622022c1eca8e66bef6397ac3d3e6d2613ae8e52ea9d9403b335f08397ac323003289ec2aa74f7f2ab72c7d3a6d26173cc65678dcb011bb35e08ab72c3310116
        else
          if slot < 21 then
            if slot < 20 then
              0x3625789fbb9174173eeb26930fa6662bf2ae1817b582f71f5817480868a32a6c4ae2fe73d2d11aef926834deac2e4fd9c0372a7b8d6a7cd1068012d454a6e43c6fe3ad6c153ef926134dce52a5fd8c0b5635f0f637cc1068092947436a5387faba96c1d3ee926134fc65627fca81b1735e2b7374c1148096863ca1c42fef675d251da2fd2683cd8ac2fcf996057327b85697e51062022ec4ca8e03fef63cd2c3d32fd2613cc8e52f5dd940d5335f07697ac1070032e46c2aa13f7f2ae92c7d16ed26174cc656e7dcb00f1b35e236b72c11501166670a644e977f733cb12aeef269347f2c4e1959cc3155790df41cb12ab010d1
            else
              0x2e4fd580372b381a6f26d1068f92d45403c6b5278e7a5bfb5df344c4ae14d2a5f9c80b56b189a6f26c106af9294701387b135c75adbfa7df304e43c14d627f8c81b179509a7d26c114ee9686301715b9355752dffa7dd306a53886c2fcf15605733341e6d2651062fa2ec440dc2b726ceba7bfb45f941c42f9452f5d1d40d53b309e6d22c1072f32e4600f83b336c79afbfa65eb08e03d9456e798f00f1b930ba6d22c1156f1666202f11bb3655d3dffa2dcb0aa13d86644ee17f7332e12aef9669345e6c4e1fe1cc312b790deabcb12e8010d15626647c1ff3b166163ef966930de646a9fa8e8a16b590fe3bca16680829872
          else
            if slot < 22 then
              0x5f9ca5556b18166f261306af9824701253b135f0dadbf8edf3054f3c14dc87f8cac717950327d261314ee98263012d1b935e2d2dfeaedd3074f3886d4bcf1585d7332c0e6d2683062fca2c44045ab727b8ba7bd9c5f947682f9438f5d1ca5d53b281e6d2611072f5864600653b335f19afbd8e5eb0f483d951ce798cacf1b9603a6d2611156e58662022d1bb35e1d3dfcaadcb1f413d8554e1fe588312b399a2f26912e8396d1560206f55796665dfd5df2c4a4ee14caa9fac88a16b1d986f268166879698721007f1d59762cffc7df285a47c14ce2bf2cc181795c987d2681748eb68a321017b8f59722efee7dd605a57886c
            else
              0x8cac4ff950362d26134fee98229012d0c735e2b71feaea5b074fba86d4a711585f9f32c0ae52683cd2fca20c4045d8b27b856fbd9d7494768bf943885d1ca5ebbb281aad2613cd2f5820e0065c8b35f076fbd8f34b0f4cbd951c0798cadcfb9601e2d26174d6e5822a022cccb35e237dfcaba4b1f45bd855427fe589c32b39862f26934683962556021a355790de5dfdccf2c4abbe14c89dfac8d516b1d146f26930687942c72105331d590facffcecf2858fbc14cc8ff2ccc51795c307d2693148eb02e3210d138f582f2efeee5d605cfb886c4acfd585c72b38066f2683468f9a2454025ab527b8da5bf9cdf3446bae14d89
      else
        if slot < 27 then
          if slot < 25 then
            if slot < 24 then
              0x605733341e6d2617e78aa2ec440dc2b727288317fb45f941c42f94675d3df40d53b309e6d2297ae8e32e4600f83b335608397fa65eb08e03d9563cd7df00f1b930ba6d22b73cc71666202f11bb31608ab7fa2dcb0aa13d872ae9efd89c3fc398625669345e79625d0021a2ac790deabfdcccb84abbe5cc89dc2c8d53f51d142d66930de7942cd010530e5590fe3bfcec59858fbe54cc8f82ccc57e55c302f26930faeb02e9010d1467582f71feee45d05cfbac6c4af11585c9fb3806e526834def9a20d0025a8aa7b8d6abf9cf4b446bbe54d895c1ca54bfb1816ad26134def9820d012528e35f0f63bf8eb5b054fbe14dc878
            else
              0xd53b281e6d2613ae8e52e4600653b335f08397ac25eb0f483d951ccd7dec6f1b9603a6d26173cc656662022d1bb35e08ab72c2dcb1f413d8554e9efe54312b399a2f26970ff2c4d1560206f557909741cb5df2c4a4ee14cb332efe8a16b1d986f26954fd64698721007f1d590b343ca7df285a47c14cbb167fe181795c987d26b15f96668a321017b8f580ba475a7dd605a57886cb9177f60372b381a6f269727eac2d45403c6b527a88347cb5df344c4ae14c73d2dfc0b56b189a6f26952fce5294701387b135e08357ca7df304e43c14e3ad6df81b179509a7d26b13fc65686301715b935608a775a7dd306a53886aba96ff
          else
            if slot < 26 then
              0xb9601e2d26174cc656e7a022cccb35e236b72c114b1f45bd855427efe55d32b39862f269347f2c4e156021a355790df41cb12f2c4abbe14c89d2efee656b1d146f26930fd646a872105331d590fb43ca16f2858fbc14cc8d67fe761795c307d26931f96662a3210d138f582fa475817d605cfb886c4a977f77272b38066f268367eac2e454025ab527b8c347cd11f3446bae14d89d2dfce756b18166f26132fce52a4701253b135f0c357cc15f3054f3c14dc8d6dfc7717950327d26133fc656263012d1b935e28a774c1dd3074f3886d4a96ff5757332c0e6d2683e78ac2ec44045ab727b88317e505f947682f9438dd3dece
            else
              0x398625669345e6c4e1fe021a2ac790deabcb12e804abbe5cc89dc2fee665d1d142d66930de646a9fa10530e5590fe3bca1668058fbe54cc8f83fe762cd5c302f26930fa6662bf210d1467582f71f58174805cfbac6c4af13f7722eb3806e526834deac2e4fc025a8aa7b8d6a7cd1069446bbe54d895c5fce7a5b1816ad26134dce52a5f812528e35f0f637cc106b054fbe14dc878dfc75ad950362d26134fc65627f012d0c735e2b7374c114b074fba86d4a70ff5752f32c0ae52683cd8ac2fce4045d8b27b85697e510694768bf943885fdeceba3b281aad2613cc8e52f5e0065c8b35f07697ac106b0f4cbd951c07fdec79a
        else
          if slot < 29 then
            if slot < 28 then
              0x986f26954fd64450b58e87f1d590b343cb4c3908247c14cbb167fe3ef942c987d26b15f9660c0bcae17b8f580ba475b451908257886cb9177f73eeb02c1a6f269727eac01b959dc6b527a88347c96a2a01c4ae14c73d2dfdaef9a209a6f26952fce405ab58f87b135e08357c94a3808e43c14e3ad6dfd3ef98209a7d26b13fc640d8bcaf15b935608a774b43180aa53886aba96ffd3ee98341e6d2617e78ab02b999dc2b727288317d1762201c42f94675d3dfda2fca309e6d2297ae8ea06a9d8f83b33560839799723008e03d9563cd7dfd32f5830ba6d22b73cc78078dcaf11bb31608ab78b33100aa13d872ae9effd16e58
            else
              0x7d26931f966628bcae1838f582fa475817190868b886c4a977f772eb02e7c6f268367eac2e3959c03b527b8c347cd122a012d2e14d89d2dfce6f9a235e6f26132fce52aab58c0bb135f0c357cc123809293c14dc8d6dfc76f982a7a7d26133fc65638bca819b935e28a774c131809693886d4a96ff576e983a7e6d2683e78ac2eb999602b727b88317e51622022c2f9438dd3dece2fca3b5e6d2613ae8e52ea9d9403b335f08397ac323003283d951ccd7dec72f587a7a6d26173cc65678dcb011bb35e08ab72c331011613d8554e9efe556e58fa1a2f26970ff2c418959cc6f557909741cb68ab0104ee14cb332efeaef9625
          else
            if slot < 30 then
              0x26834deac2e4fd9c0372a7b8d6a7cd1068012d4554d895c5fce7a5a235df326134dce52a5fd8c0b5635f0f637cc106809294714dc878dfc75ad82a7df126134fc65627fca81b1735e2b7374c114809686386d4a70ff5752d83a7dd52683cd8ac2fcf996057327b85697e51062022ec5943885fdeceba4a3b45fd2613cc8e52f5dd940d5335f07697ac1070032e45951c07fdec79a587a65ed26174cc656e7dcb00f1b35e236b72c1150116665855427efe55d258fa2def269347f2c4e1959cc3155790df41cb12ab010d1e14c89d2efee6796255def26930fd646a8b58e8a31d590fb43ca163908299c14cc8d67fe767942c7d
            else
              0x69345e6c4e1fe1cc312b790deabcb12e8010d1564c89dc2fee665c255df2e6930de646a9fa8e8a16b590fe3bca166808298724cc8f83fe762cc2c7df2a6930fa6662bf2ae1817b582f71f5817480868a326c4af13f7722e82e7dd6
  (x >>> ((i % 8) * 243)) &&& hadMask 243

private def hadRow244 (i : Nat) : Nat :=
  hadPaley1 hadCore244 i

private def hadRow248 (i : Nat) : Nat :=
  hadDouble 124 hadRow124 i

private def hadCore252 (i : Nat) : Nat := hadRot 251 0x22b230a6e4bb27d6038e2121f2950883eef56b07b7b8e3f941b22d89af3b2ba i

private def hadRow252 (i : Nat) : Nat :=
  hadPaley1 hadCore252 i

private def hadRow256 (i : Nat) : Nat :=
  hadDouble 128 hadRow128 i

private def hadRoute260 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 1 then
      0xfb419ba4819764cda0edd391033267d07ce9cf220133bea9fb89a87e8c8854ffc4d83f68191a7f426ddfb410323fab36e3da1a206fd53b712d0fe440
    else
      if slot < 2 then
        0xc8817b1508d378d7e123220d5fa702f0960646afcb81284be40c97e6c09325f8881bf35049c2fc391039aba4e083ed4e6c64419d91f6873740c8cec9
      else
        0x1911d8b44693c6b0322c5be348635b20642deda421ade440d6f61211d6f1
  (x >>> ((i % 8) * 60)) &&& hadMask 60

private def hadRow260 (i : Nat) : Nat :=
  hadCwRow 5 13 0x2d0 0x1d2e 0xedc 0xedc hadRoute260 i

private def hadRow264 (i : Nat) : Nat :=
  hadDouble 132 hadRow132 i

private def hadRow268 (i : Nat) : Nat :=
  let r := i % 67
  if i < 67 then
    hadJoin4 67
      (hadCyclicCell 67 r 0xbb6dd2567c49e6f 2 1 0x0)
      (hadCyclicCell 67 r 0x62b2d87d4b19855 55 66 0x0)
      (hadCyclicCell 67 r 0x314a555812ce9fd 61 66 0x0)
      (hadCyclicCell 67 r 0x1538f0dce1b33031 43 66 0x0)
  else
  if i < 134 then
    hadJoin4 67
      (hadCyclicCell 67 r 0x62b2d87d4b19855 55 66 0x7ffffffffffffffff)
      (hadCyclicCell 67 r 0xbb6dd2567c49e6f 2 1 0x0)
      (hadCyclicCell 67 r 0x118199b0e761e395 29 66 0x7ffffffffffffffff)
      (hadCyclicCell 67 r 0x2fe5cd206aa94a3 14 66 0x0)
  else
  if i < 201 then
    hadJoin4 67
      (hadCyclicCell 67 r 0x314a555812ce9fd 61 66 0x7ffffffffffffffff)
      (hadCyclicCell 67 r 0x118199b0e761e395 29 66 0x0)
      (hadCyclicCell 67 r 0xbb6dd2567c49e6f 2 1 0x0)
      (hadCyclicCell 67 r 0x550cc695f0da6a3 19 66 0x7ffffffffffffffff)
  else
    hadJoin4 67
      (hadCyclicCell 67 r 0x1538f0dce1b33031 43 66 0x7ffffffffffffffff)
      (hadCyclicCell 67 r 0x2fe5cd206aa94a3 14 66 0x7ffffffffffffffff)
      (hadCyclicCell 67 r 0x550cc695f0da6a3 19 66 0x0)
      (hadCyclicCell 67 r 0xbb6dd2567c49e6f 2 1 0x0)

private def hadRow272 (i : Nat) : Nat :=
  hadDouble 136 hadRow136 i

private def hadCore276 (i : Nat) : Nat := hadRot 137 0x58b036d543de7d88cc46f9ef0aadb03468 i

private def hadRow276 (i : Nat) : Nat :=
  hadPaley2 138 hadCore276 i

private def hadRow280 (i : Nat) : Nat :=
  hadDouble 140 hadRow140 i

private def hadCore284 (i : Nat) : Nat := hadRot 283 0x348a7e33d517a5a05c99a980229c33be9c1a7c68233c6bbfe6a66c5fa5a17543381aed2 i

private def hadRow284 (i : Nat) : Nat :=
  hadPaley1 hadCore284 i

private def hadRow288 (i : Nat) : Nat :=
  hadDouble 144 hadRow144 i

private def hadMyU292 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 4 then
      if slot < 2 then
        if slot < 1 then
          0xa56bb2c83191c7137c99e3ced2022d32e2b5ccf16765094aa1d1dad6a8e1b986961832ee793634ae85531249b7751b3a1b4aa89944db9a9d1d4d2d894c623d2cceae668e458e344e
        else
          0x7adb406cc3ad5b19604b95a05b7063233e6e87b9c416d419d45d53e2cc6a0bea50c2ebb1f1eeb5014d3571f40876d8f68211ce2d6b053a74db01b8a71655d2af1d1ea0966a51b6a8
      else
        if slot < 3 then
          0x7d05633478dd7430a5b68239de1caba2b982eda05a9d2767cc4c6033602db5e0698dab5cceea1928725b378417e67504dca934bb268353b20ae67c164dd2c9e14985773e821ecda4
        else
          0x19d87156b774c186960a6e68f335b8b8552904b73c799ad474cb44c134dd6a53ec8e389890578b8f5156d8a566d80db2e5c4baa68e518416f1b6ea0d6b4738280ad778f102f8eacb
    else
      if slot < 6 then
        if slot < 5 then
          0x33add9e007a714b319f0c6cc3c1b1f9af8046e70937a03c3bf5282a35c78d444f9cb6780166757334722c71a274b2b8b959bc463291b2d85cd8aedb22991551752c6c9eed9248caa
        else
          0xcd52d825974e7605d851e7520cb1f547c0e3e8732982e8779b81393ca1bc057ce3f560549d3a6d4063396cd09ede0e07d0548ef7a02b479fab202ada43744d4bd775900d6c315a36
      else
        if slot < 7 then
          0xd8b81692e71f016ed18dc423c9dbd3a0b670b93c423b10e6d05cbd749681d1b8b7680f8e1ced00bad6787a13472f7e801d4b31152d6bbe27e0462d0da217e5970b502fae9bd90a32
        else
          if slot < 8 then
            0xea03d853c2a06afc7374194ce179c81d9ee1d304ae78ac703e2af89a41b4ab31ba06e72e5f40ad0e94c509bd9746207e47da7e845b0b2b8017ef4d6b4a88cdb5d00b738e2c85e1e6
          else
            0x22b1e3ac501e6d39f205ec90e76414afdc3c83c33630f201f59f8d0079bb5cc98cd28e5e009aeebd26c5a8c36b404d5f9e2b22ec25b5a0be0707bd405ef712602b65cb9790b369cc
  (x >>> ((i % 8) * 72)) &&& hadMask 72

private def hadMyK292 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 4 then
      if slot < 2 then
        if slot < 1 then
          0x9d25a74169d25a7416ce92b3a0ace92b3a0ae74939d04e74939d0473a49ce8273a49ce82b9d22e740b9d22e7405ce9173a05ce9173a02e748b9d02e748b9d0000040000000040000
        else
          0x25ce8173a25ce8173a92e720b9c92e720b9c4973905ce4973905cea4b9a82e6a4b9a82e6d25cb4172d25cb4172e92e3a0b8e92e3a0b874971d05c74971d05c3a4b8e82e3a4b8e82e
      else
        if slot < 3 then
          0x18bef9d2418bef9d248c5f5ce928c5f5ce92462fee748462fee748a317d73a4a317d73a4d18bcb9d2d18bcb9d2ffffc0001ffffc0001973a05ce8973a05ce84b9d02e744b9d02e74
        else
          0xbe8c525cebe8c525ce5f46692e65f46692e62fa3749722fa37497217d1fa4b817d1fa4b88be8dd25c8be8dd25cc5f44e92ec5f44e92e62fa6749662fa67496317d73a4a317d73a4a
    else
      if slot < 6 then
        if slot < 5 then
          0x462dd18bfb9d22e740a316e8c5f5ce9173a0d18b7462f2e748b9d0ffffbffff000040000e8c5e5ce8e8c5e5ce8f462d2e74f462d2e74fa314973afa314973a7d18e4b9c7d18e4b9c
        else
          0x2da34be8dd25cb417216d1c5f47e92e3a0b88b68e2fa374971d05cc5b4717d13a4b8e82e62da58be99d25a7416316d4c5f5ce92b3a0a18b6c62fbe74939d048c5b6317d73a49ce82
      else
        if slot < 7 then
          0x2e743462dd18bcb9d200003fffeffffc000168c5fa317973a05ce8b462fd18b4b9d02e74da317e8c525ce8173a6d18df46392e720b9cb68c6fa314973905ce5b4657d19a4b9a82e6
        else
          if slot < 8 then
            0x741722da38be8dd25c3a0bb16d1c5f44e92e9d0598b6962fa67496ce828c5b5317d73a4ae741062db18bef9d2473a0a316d8c5f5ce92b9d0118b7462fee7485ce828c5ba317d73a4
          else
            0x173a1a317e8c5e5ce80b9d2d18bf462d2e7405ceb68c5fa314973a82e71b4637d18e4b9c4173ada31be8c525cea0b996d195f46692e6d05c8b68d2fa374972e82e05b4717d1fa4b8
  (x >>> ((i % 8) * 72)) &&& hadMask 72

private def hadMyTop292 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xffffffffffffffffff8000000000000000003fffffffffffffffffdffffffffffffffffff0000000000000000000000000000000000000000000000000000001fffffffffffffffffe
    else
      0xffffffffffffffffff7fffffffffffffffffc000000000000000001ffffffffffffffffff0000000000000000007fffffffffffffffffbffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 292)) &&& hadMask 292

private def hadRow292 (i : Nat) : Nat :=
  hadMiyamotoRow 73 21392 55217 hadMyTop292 hadMyU292
    hadRow72 hadMyK292 i

private def hadRow296 (i : Nat) : Nat :=
  hadDouble 148 hadRow148 i

private def hadCore300 (i : Nat) : Nat := hadRot 149 0xc2fc94428b62e7e98edc65f9d1b4508a4fd0c i

private def hadRow300 (i : Nat) : Nat :=
  hadPaley2 150 hadCore300 i

private def hadRow304 (i : Nat) : Nat :=
  hadDouble 152 hadRow152 i

private def hadCore308 (i : Nat) : Nat := hadRot 307 0x348e2f17f215b9d410f2ac9920290c9eb8fb11a7720e286cf6bfb66cab0f7d46257b0170b8ed2 i

private def hadRow308 (i : Nat) : Nat :=
  hadPaley1 hadCore308 i

private def hadRow312 (i : Nat) : Nat :=
  hadDouble 156 hadRow156 i

private def hadCore316 (i : Nat) : Nat := hadRot 157 0x9e04beb289509c7d9b9e766f8e42a4535f481e4 i

private def hadRow316 (i : Nat) : Nat :=
  hadPaley2 158 hadCore316 i

private def hadRow320 (i : Nat) : Nat :=
  hadDouble 160 hadRow160 i

private def hadRoute324 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 1 then
      0x7d0b7b173c2a3dcbc0f14c2a397826685c8c1b295047d7b1a3a15bf0cdd942fae62c6a8
    else
      0xab96748ba14afa85a545714ed1e0856efe2
  (x >>> ((i % 8) * 36)) &&& hadMask 36

private def hadRow324 (i : Nat) : Nat :=
  hadCwRow 3 27 0x6d198b6 0x12e6748 0x7050a0e 0x7050a0e hadRoute324 i

private def hadRow328 (i : Nat) : Nat :=
  hadDouble 164 hadRow164 i

private def hadCore332 (i : Nat) : Nat := hadRot 331 0x31bd211cb6e9b95f60d2022c74389d00c7ea59a3aaa3a65a81cff46e3d1cbbfb4f905626892c77b4272 i

private def hadRow332 (i : Nat) : Nat :=
  hadPaley1 hadCore332 i

private def hadRow336 (i : Nat) : Nat :=
  hadDouble 168 hadRow168 i

private def hadCore340 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 11 then
      if slot < 5 then
        if slot < 2 then
          if slot < 1 then
            0xb877c44e5aa579acf92527cd66a95e9c88fd8750002e1ff11396a95e6b3e4849f359ea55a7223fe1d0002b86fc44e5ea559acf92927cd67a9569c88fb874001ae13f15397a9466b3e4e49f358ea55a7623ee1c000eb80fc74e4ea599acf93926cd6ba9169f88eb870003ae23f0d39ba966693e5e49335aea65a7e23ae18000eb88fcb4e2ea599a4f9f924cd6ba9969f88eb840003ae23f2d3aba966693e3e4b334aeae5a7e23ae0000
          else
            0x8fc34e6ea599a4f97924cd6ba9969f88eb8600075c23f2d38ba966693e7e49335aea65a7e23ae10001d708fcb4eaea599a4f8f92ccd2bab969f88eb8000075c1d711f969d5d4b3349f1f2599a57572d3f11d70000875c47e5a6575acc927e7c966695d1cb4fc475c00061d711f96995d6b3249e9f2599a57672c3f11d70003875c47e5a2575acd92727cd66695c9cb8fc075c000e1df11b96a95c6b3e49c9f3598a57a72a3f21d6000
        else
          if slot < 3 then
            0xc47e5a6575acc927a7c966695d9cb0fc475c000c3af11f96895d6b3649c9f3599a57272e3f01d700070ebc46e5aa571acf92727cd66295e9ca8fc8758001c3bf11396a95e6b3e4949f359aa57a7223f61d400170efc44e5aa579acf92127cd67a9569c88ff8740005c3bf11397a9566b3e4a49f359ea55a7223ee1d000570cfc54e5ea519acf93927cd63a9569d88fb8700035c23f1d393a9666b3e4e49b35aea45a7e23ae1c001d70
          else
            if slot < 4 then
              0x4e5ea559acf92927cd67a9569c88fb8740015c37e25397a9466b3e4e49f358ea55a7623ee1c000d709f8b4e4ea599acf93926cd6ba9169f88eb8700075c07e2d39ba966693e5e49335aea65a7e23ae18001d711f8b4e2ea599a4f9f924cd6ba9969f88eb8400075c47e2d3aba966693e3e4b334aeae5a7e23ae00001d711f847e5a75752ccd27c7c966695d5cb4fc475c00003af11f96995d6b3249f9f2599a57472d3f11d700010eb
            else
              0xaea599a4f8f92ccd2bab969f88eb8000075c47e5a7169d5d4b3349f1f2599a57572d3f11d700000eb88fe5a6575acc927e7c966695d1cb4fc475c00043ae23f96995d6b3249e9f2599a57672c3f11d700030eb88fe5a2575acd92727cd66695c9cb8fc075c001c3ae23b96a95c6b3e49c9f3598a57a72a3f21d600070ef88ce5aa579acf92527cd66a95e9c88fd8750005c3be23396a95e6b3e4849f359ea55a7223fe1d000170ff88
      else
        if slot < 8 then
          if slot < 6 then
            0xa571acf92727cd66295e9ca8fc8758001c3be2372d295e6b3e4949f359aa57a7223f61d400170ef889cb6a579acf92127cd67a9569c88ff8740005c3fe2272da9566b3e4a49f359ea55a7223ee1d000570df889cbea519acf93927cd63a9569d88fb8700035c27e2a72ba9666b3e4e49b35aea45a7e23ae1c001d701f8e9caea599a4f97924cd6ba9969f88eb8600075c47e1a72ba966693e7e49335aea65a7e23ae10001d711f969c
          else
            if slot < 7 then
              0x99acf93926cd6ba9169f88eb8700075c07e3a72752e6693e5e49335aea65a7e23ae18001d711f869cdd4999a4f9f924cd6ba9969f88eb8400075c47e5a7175366693e3e4b334aeae5a7e23ae00001d711f969d5d45752ccd27c7c966695d5cb4fc475c00003ae23f2d395d6b3249f9f2599a57472d3f11d700010eb88fcb4e575acc927a7c966695d9cb0fc475c000c3ae23f2d295d6b3649c9f3599a57272e3f01d700070eb88fcb4
            else
              0xacc927e7c966695d1cb4fc475c00043ae23f2d32baeb3249e9f2599a57672c3f11d700030eb88fcb4cae9acd92727cd66695c9cb8fc075c001c3ae23f2d12ba6b3e49c9f3598a57a72a3f21d600070ef88dcb54ae9acf92527cd66a95e9c88fd8750005c3be2272d52be6b3e4849f359ea55a7223fe1d000170ff889cb54ad9acf92927cd67a9569c88fb8740015c37e2272f52a66b3e4e49f358ea55a7623ee1c000d709f8a9cbd4a
        else
          if slot < 9 then
            0xf92127cd67a9569c88ff8740005c3fe2272d52bcd63e4a49f359ea55a7223ee1d000570df889cbd4ab358f93927cd63a9569d88fb8700035c27e2a72f528cd73e4e49b35aea45a7e23ae1c001d701f8e9c9d4b3354f97924cd6ba9969f88eb8600075c47e1a73752ccd13e7e49335aea65a7e23ae10001d711f969c5d4b3364f8f92ccd2bab969f88eb8000075c47e5a75752cccb3349f1f2599a57572d3f11d700000eb88fcb4eaea
          else
            if slot < 10 then
              0xf924cd6ba9969f88eb8400075c47e5a71752ccd27cbe4b334aeae5a7e23ae00001d711f969d5d4b3349f127c7c966695d5cb4fc475c00003ae23f2d3aba966649f9f2599a57472d3f11d700010eb88fcb4caeb599927a7c966695d9cb0fc475c000c3ae23f2d32bad66649c9f3599a57272e3f01d700070eb88fcb44aeb59b92727cd66295e9ca8fc8758001c3be2372d52b8d67e4949f359aa57a7223f61d400170ef889cb54af359
            else
              0x27cd66695c9cb8fc075c001c3ae23f2d12bad66c93c9f3598a57a72a3f21d600070ef88dcb54ae359f24d27cd66a95e9c88fd8750005c3be2272d52bcd67c9249f359ea55a7223fe1d000170ff889cb54af359f24927cd67a9569c88fb8740015c37e2272f52acd67c9649f358ea55a7623ee1c000d709f8a9cbd4a3359f27926cd6ba9169f88eb8700075c07e3a72752ccd67c9e49335aea65a7e23ae18001d711f869cdd4b3349f2
    else
      if slot < 16 then
        if slot < 13 then
          if slot < 12 then
            0xcd63a9569d88fb8700035c27e2a72f528cd67c9c93b35aea45a7e23ae1c001d701f8e9c9d4b3359f2724ccd6ba9969f88eb8600075c47e1a73752ccd27cbc93335aea65a7e23ae10001d711f969c5d4b3349f3f24ccd2bab969f88eb8000075c47e5a75752ccd27c7c91f2599a57572d3f11d700000eb88fcb4eaea599a4fa7c966695d1cb4fc475c00043ae23f2d32bad66493e9f2599a57672c3f11d700030eb88fcb4caeb59924f
          else
            0x66695d5cb4fc475c00003ae23f2d3aba966693e3e4d99a57472d3f11d700010eb88fcb4caeb59924fcf9166695d9cb0fc475c000c3ae23f2d32bad66493d3e5599a57272e3f01d700070eb88fcb44aeb59b24e4f9d66295e9ca8fc8758001c3be2372d52b8d67c9393e359aa57a7223f61d400170ef889cb54af359f24a4f8d67a9569c88ff8740005c3fe2272d52bcd67c9093f359ea55a7223ee1d000570df889cbd4ab359f2524f
        else
          if slot < 14 then
            0xa95e9c88fd8750005c3be2272d52bcd67c9293e6b36a55a7223fe1d000170ff889cb54af359f2424f9acfa9569c88fb8740015c37e2272f52acd67c9493e6b2ea55a7623ee1c000d709f8a9cbd4a3359f2724f9acba9169f88eb8700075c07e3a72752ccd67c9c9366b2ea65a7e23ae18001d711f869cdd4b3349f2f2499aeba9969f88eb8400075c47e5a71752ccd27cfc9266aaeae5a7e23ae00001d711f969d5d4b3349f1f2599a
          else
            if slot < 15 then
              0x969f88eb8600075c47e1a73752ccd27cbc9266b5d4e5a7e23ae10001d711f969c5d4b3349f3f2499ad753969f88eb8000075c47e5a75752ccd27c7c966695d457572d3f11d700000eb88fcb4eaea599a4f8f92ccd95d1cb4fc475c00043ae23f2d32bad66493f3e4b33257672c3f11d700030eb88fcb4caeb59924f4f92cce95c9cb8fc075c001c3ae23f2d12bad66c9393e6b32a57a72a3f21d600070ef88dcb54ae359f24e4f9acc
            else
              0x9cb0fc475c000c3ae23f2d32bad66493d3e4b334aea72e3f01d700070eb88fcb44aeb59b24e4f9accd2ba9ca8fc8758001c3be2372d52b8d67c9393e6b314afa7223f61d400170ef889cb54af359f24a4f9acd52b69c88ff8740005c3fe2272d52bcd67c9093e6b3d4ada7223ee1d000570df889cbd4ab359f2524f9acf52969d88fb8700035c27e2a72f528cd67c9c93e6b1d4a5a7e23ae1c001d701f8e9c9d4b3359f2724d9ad752
      else
        if slot < 19 then
          if slot < 17 then
            0x88fb8740015c37e2272f52acd67c9493e6b3d4ab4e623ee1c000d709f8a9cbd4a3359f2724f9ac752ad3b88eb8700075c07e3a72752ccd67c9c9366b5d48b4fe23ae18001d711f869cdd4b3349f2f2499ad7532d3f88eb8400075c47e5a71752ccd27cfc9266b5d4cb4fe23ae00001d711f969d5d4b3349f1f2599a57572d1cb4fc475c00003ae23f2d3aba966693e3e4b334aea72d3f11d700010eb88fcb4caeb59924fcf92ccd2ba
          else
            if slot < 18 then
              0xeb8000075c47e5a75752ccd27c7c966695d5cb4fc43f11d700000eb88fcb4eaea599a4f8f92ccd2bab968fc475c00043ae23f2d32bad66493f3e4b334ae8e5a3f11d700030eb88fcb4caeb59924f4f92ccd2bb3968fc075c001c3ae23f2d12bad66c9393e6b334ae4e5a3f21d600070ef88dcb54ae359f24e4f9acc52bd3948fd8750005c3be2272d52bcd67c9293e6b354af4e423fe1d000170ff889cb54af359f2424f9acf52ad39
            else
              0x8758001c3be2372d52b8d67c9393e6b314af4e547e61d400170ef889cb54af359f24a4f9acd52bd3911fb8740005c3fe2272d52bcd67c9093e6b3d4ab4e447ee1d000570df889cbd4ab359f2524f9acf52ad3911fb8700035c27e2a72f528cd67c9c93e6b1d4ab4ec47ae1c001d701f8e9c9d4b3359f2724d9ad7522d3f11eb8600075c47e1a73752ccd27cbc9266b5d4cb4fc47ae10001d711f969c5d4b3349f3f2499ad7532d3f11
        else
          if slot < 20 then
            0x75c07e3a72752ccd67c9c9366b5d48b4fc475c38001d711f869cdd4b3349f2f2499ad7532d3f11d70c00075c47e5a71752ccd27cfc9266b5d4cb4fc475c20001d711f969d5d4b3349f1f2599a57572d3f11d7075c00003ae23f2d3aba966693e3e4b334aeae5a7e21d700010eb88fcb4caeb59924fcf92ccd2ba3969f8875c000c3ae23f2d32bad66493d3e4b334aece587e21d700070eb88fcb44aeb59b24e4f9accd2b93971f8
          else
            if slot < 21 then
              0x43ae23f2d32bad66493f3e4b334ae8e5a7e23ae00030eb88fcb4caeb59924f4f92ccd2bb3961f88eb8001c3ae23f2d12bad66c9393e6b334ae4e5c7e03ae00070ef88dcb54ae359f24e4f9acc52bd3951f90eb0005c3be2272d52bcd67c9293e6b354af4e447ec3a800170ff889cb54af359f2424f9acf52ad3911ff0e80015c37e2272f52acd67c9493e6b3d4ab4e447dc3a000d709f8a9cbd4a3359f2724f9ac752ad3b11f70e
            else
              0xeb88fcb4eaea599a4f8f92ccd2bab969f88eb8
  (x >>> ((i % 8) * 169)) &&& hadMask 169

private def hadRow340 (i : Nat) : Nat :=
  hadPaley2 170 hadCore340 i

private def hadRow344 (i : Nat) : Nat :=
  hadDouble 172 hadRow172 i

private def hadCore348 (i : Nat) : Nat := hadRot 347 0x27817fa88445336b6e8f8a98e5a1823483166b503e33383f529973ed3be7a58e6ae0e8929335ddeea017e1a i

private def hadRow348 (i : Nat) : Nat :=
  hadPaley1 hadCore348 i

private def hadRow352 (i : Nat) : Nat :=
  hadDouble 176 hadRow176 i

private def hadMyU356 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 5 then
      if slot < 2 then
        if slot < 1 then
          0x9b726de4720170aec2b9638d999bd23158b05b309cbbc76c24f134bcd825414edd6396d7e8960ce41eb8476425ea9ebb28831d0be4716583f5a17d984b0e952a783a187dca7f4604cb19b32cc55cbe208fa74aed824836ea
        else
          0xc57f94a24936a6b71b31c0d8b5f8c909a05572d31b3c6b663d630c502760bc9e8ff413f831a66a129c14ebcdeaa91e30d36d09605a75e65b8a9d5c24b60ad20f2b737c656f0e321b8475157531bf12562f191f4b0a03de98
      else
        if slot < 3 then
          0x3f9e41313aa4a5f956609aee07389c4ec7a04fab48a9372391ce0779512d5f205e55c8c8279fc59066a9fa52d5a26651c3d7641376ac153bf17410e5a9ba3ba9360832f61a1631f2d494e9cd86b47d0d498c75b88a76c722
        else
          if slot < 4 then
            0x6658c1fc82fb3d72839485a30c6bc66d6f1793d06e40590931fad1b3cd8cb4eaa0c924529fea3038cd8ed656e3192b0be2d44e36e511daf8c68586f4c61b397292b45a7082e8fdc106c95dc5d9bc38a6645aba8356ec826e
          else
            0x6917eb69c626e21d78273d2c8f2436e3bb7282a41b3a8c4bd999b1dd390cda0d104e27b64ed9c69d43750e8898f46a48fd197bc050d2f84c70f6a63e8caea8ae21dd243ab951daced4f04b5066cb0c78955767ae5a0690b
    else
      if slot < 8 then
        if slot < 6 then
          0xb7a503a8ec2c1eafde442871eb08fc4b018dce7b384568d563760998c7f1a7dc2090fa559ec42279b92ba7602e5f1047d3a576c1241b75062fe53be18a334cd98d32219be85afc15c1e54a970d114dd7957a4a68e27d0b8c
        else
          if slot < 7 then
            0xc555d514279eb8be1d1815b22ae1921bdf557f4c8882ed5a7acc8087545e8616e9f68df4e6400ba327920bf43554ee9841e3fa53d1e10c1ea9af878092db467534331fd433d3c0496c99f81a934e4adf41c86c3f623ec941
          else
            0x8cd831287ed1abf660c0f947ecb20c336a54e32964f6c9fb498310e49ca390b9be0bbeac04ca77a2b0ce1c6e729f46c128d625ba61471fa86fc250b4799ad57207875597ab20563ec47c32a34baaebf328070d631899712f
      else
        if slot < 9 then
          0xe5320357dd07638730d45e708c192df937d9d09c53926cc304d37e26f2694c72a5b7e148c1b319f03066fd58de3c51322d42b648537eca5f4f22189d15ad050dafb88b91844f2fa1df5b0a0b5a2b44c8a3c7b537eca126d4
        else
          if slot < 10 then
            0x2672fb16f2fd049e4c5d101335e5ab79768617a2aebd84987544d411132feaaf9e428abaaa3a818b87d1d70e014cfd755f48e9918c6bc6a04d5e9aad2c54c3e237e2d0a43f615e1e04eab599b148362f94ef8e2865da46
          else
            0x42379aa5f0906e5d49d9e49906ec6ab16043be58fe310d23f10d78ea21cde73b1843715c0a5ed14227bf578361382fb527282937c46fc3203cbcc2bf8c9581f99369901e1f59578cc2cae62db478219772aac30878bca5fc
  (x >>> ((i % 8) * 88)) &&& hadMask 88

private def hadMyK356 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 5 then
      if slot < 2 then
        if slot < 1 then
          0x3be2e08d6ca3be2e08d6ca9df17046b649df17046b644ef8b8235b24ef8b8235b2a77c5c11ad8a77c5c11ad853be2e08d6c53be2e08d6c29df17046b629df17046b694ef8b8235a94ef8b8235a0000000000000000000000
        else
          0xe2e08d6ca76e2e08d6ca76f17046b653af17046b653af8b8235b29cf8b8235b29c7c5c11ad94e7c5c11ad94ebe2e08d6ca6be2e08d6ca6df17046b652df17046b652ef8b8235b28ef8b8235b2877c5c11ad9477c5c11ad94
      else
        if slot < 3 then
          0xe08d6ca77c4e08d6ca77c47046b653be27046b653be2b8235b29df0b8235b29df05c11ad94ef85c11ad94ef82e08d6ca77c2e08d6ca77c17046b653be17046b653be8b8235b29de8b8235b29dec5c11ad94eec5c11ad94ee
        else
          if slot < 4 then
            0x8d6ca77c5c08d6ca77c5c046b653be2e046b653be2e0235b29df170235b29df17011ad94ef8b811ad94ef8b808d6ca77c5c08d6ca77c5c046b653be2e046b653be2e8235b29df168235b29df16c11ad94ef8ac11ad94ef8a
          else
            0x6ca77c5c11a6ca77c5c11ab653be2e08cb653be2e08c5b29df170465b29df17046ad94ef8b822ad94ef8b822d6ca77c5c10d6ca77c5c106b653be2e086b653be2e0835b29df170435b29df17041ad94ef8b821ad94ef8b82
    else
      if slot < 8 then
        if slot < 6 then
          0xac41d1f729353be2e08d6cd620e8fb94929df17046b66b10747dca594ef8b8235afffffffffff00000000000ca77c5c11acca77c5c11ac653be2e08d6653be2e08d6b29df17046ab29df17046ad94ef8b8234d94ef8b8234
        else
          if slot < 7 then
            0x41d1f729359be2e08d6ca620e8fb949addf17046b65210747dca4d7ef8b8235b28883a3ee526b77c5c11ad94c41d1f729353be2e08d6ca620e8fb949b9df17046b64b10747dca4d4ef8b8235b25883a3ee527a77c5c11ad8
          else
            0xd1f729358832e08d6ca77ce8fb949ac4117046b653be747dca4d6218b8235b29de3a3ee526b11c5c11ad94ee1d1f7293589e2e08d6ca760e8fb949ac5f17046b653a0747dca4d63f8b8235b29c83a3ee526b17c5c11ad94e
      else
        if slot < 9 then
          0xf72935883a308d6ca77c5cfb949ac41d1046b653be2e7dca4d620e98235b29df163ee526b1075c11ad94ef8a1f72935883be08d6ca77c48fb949ac41d7046b653be247dca4d620fb8235b29df0a3ee526b1075c11ad94ef8
        else
          if slot < 10 then
            0x2935883a3efd6ca77c5c10949ac41d1f76b653be2e08ca4d620e8fb35b29df1704e526b10747d1ad94ef8b8272935883a3f8d6ca77c5c0b949ac41d1f46b653be2e0dca4d620e8f235b29df170ee526b1074711ad94ef8b8
          else
            0x35883a3ee53ca77c5c11ac9ac41d1f729653be2e08d64d620e8fb95b29df17046a26b10747dcbd94ef8b8234935883a3ee56ca77c5c11a49ac41d1f73b653be2e08ca4d620e8fb95b29df17046526b10747ddad94ef8b822
  (x >>> ((i % 8) * 88)) &&& hadMask 88

private def hadMyTop356 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xffffffffffffffffffffff80000000000000000000003fffffffffffffffffffffdffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffe
    else
      0xffffffffffffffffffffff7fffffffffffffffffffffc0000000000000000000001ffffffffffffffffffffff00000000000000000000007fffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 356)) &&& hadMask 356

private def hadRow356 (i : Nat) : Nat :=
  hadMiyamotoRow 89 21392 55217 hadMyTop356 hadMyU356
    hadRow88 hadMyK356 i

private def hadRow360 (i : Nat) : Nat :=
  hadDouble 180 hadRow180 i

private def hadCore364 (i : Nat) : Nat := hadRot 181 0x8e81deae4304d994b6b87bf7875b4a66c8309d5ee05c4 i

private def hadRow364 (i : Nat) : Nat :=
  hadPaley2 182 hadCore364 i

private def hadRow368 (i : Nat) : Nat :=
  hadDouble 184 hadRow184 i

private def hadRoute372 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 1 then
      0x7d0b7b173c2a3dcbc0f14c2a397826685c8c1b295047d7b1a3a15bf0cdd942fae62c6a8
    else
      0xab96748ba14afa85a545714ed1e0856efe2
  (x >>> ((i % 8) * 36)) &&& hadMask 36

private def hadRow372 (i : Nat) : Nat :=
  hadCwRow 3 31 0x2dc3b40 0x6753cae6 0x6753cae6 0x7d23c4be hadRoute372 i

private def hadRow376 (i : Nat) : Nat :=
  hadDouble 188 hadRow188 i

private def hadCore380 (i : Nat) : Nat := hadRot 379 0x31bd601d92bbad596df22460320dcc38970850f6f28b87aaa1e2eb090f5ef16e3cc4fb3f9dbb049654a22b647f94272 i

private def hadRow380 (i : Nat) : Nat :=
  hadPaley1 hadCore380 i

private def hadRow384 (i : Nat) : Nat :=
  hadDouble 192 hadRow192 i

private def hadCore388 (i : Nat) : Nat := hadRot 193 0x10d56899df3471b0adbe87c84f85f6d43638b3ee645aac20 i

private def hadRow388 (i : Nat) : Nat :=
  hadPaley2 194 hadCore388 i

private def hadRow392 (i : Nat) : Nat :=
  hadDouble 196 hadRow196 i

private def hadCore396 (i : Nat) : Nat := hadRot 197 0xd279b04e483aa380f7dead4cccad5efbc07157049c836792c i

private def hadRow396 (i : Nat) : Nat :=
  hadPaley2 198 hadCore396 i

private def hadRow400 (i : Nat) : Nat :=
  hadDouble 200 hadRow200 i

private def hadMyU404 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 6 then
      if slot < 3 then
        if slot < 1 then
          0x8ed756ec13c23eac1c39d9d0003f653370c99ce73180df26358179afa7822cf629a593d1352c0cd5fea611959c685e47b066825fac7b784281f0f313bb605e82b53999833f2f850609da5b7413ae7cc8396b7c09990ed34ac72f087a71a995fa4012fd4c
        else
          if slot < 2 then
            0xe9579d812b650c0a999c34e9fdde9c9c4b9902715605f5a60747b6e6c270ba218a98cf8535b2ad9f4e11c3d2285652ea29bd34aefb608e4cb2429b671958733d17a306b5679614487ccacb392ebdb0159b3ca0aab2ce46c0faaae982f255dd82249f38a3
          else
            0x5b704e49ac738a25baa27f1c25bb89724714d93195f50afc507acc23d32a2ad7064eb917e28e4cd8229b58ec43419c2e6debdb60c0b8d6c7634a01b5337ecb5fa78ab20e110d553f9047f07d5d9c16d600ccc54aed991599eac4c274b70e532807aac9fc
      else
        if slot < 4 then
          0x21c1354797eb43f8827f2aac2b8dac740c1b6cdfb32b6014b1dc6b65106cc9f5ed9d0e60b08d51532f10cd7851fa275c983a6ca3893a4776828fd42bea632738d649c83b690e3f915769147d02da4f10de5550ed8af1a949ec23c96d02f8a563d46dc2aa
        else
          if slot < 5 then
            0x9ab58317a2f334d4cf848a1a74c9c41b7dd4b386a639b650932f0e21cbe6d52f6515d29a851174390d9db78b6b287cc65461026748e4e5eef8196be81aa3929b5206e7aa5fe5cb0e66540cc3b4b90c8d5e4fe4d57805329c01ada0e6eafa6a266dd4a8cc
          else
            0xf3066672b505f696e418287d35087b78d7e90681b77233c3e0a62195feacc0d983789e858e6cd10797d67a052b22f269651be64c3b329bf02b193ec06339c10f20ddabadc402e6e70e0d5fa93d065d557c31473e49106ee366a036f5d270d89cd355414f
    else
      if slot < 9 then
        if slot < 7 then
          0x21b96fd1c4c2b065ba3703a73909eb0ecc253e872f5f589d20e8e6a87530ec101cbdfb8268d543757b6b064381e5b1cc9356334dd18e6c6c1a01d7df3086d1864ef7f16142f40ee23b057656397843d38d4cafd20097ea6a704cf9d720b8b2dc26640fb5
        else
          if slot < 8 then
            0xfabb384db40086d5730a1dd4e4f56a60b89c8cf36bb89a1b412eafd611e0c475cb58c2b8da1b7576b04f43029b5acc51c791d3ab330a566a27cadf61c62c01c555d5806af82efabacd8c884669af4e01d381b9dcda5b126417ed1dbc12444eb25e817657
          else
            0xa5984a961cf4d77370e9c019e95a41549b927d73cf874340e36ad609a8d4b1eade58b2720799d6f02e44e1a753f092b5906de6b304d60f1d2acfac59a4827db1b0173239cb537d694b241a65f6e1544b039f4ad20f4e5193a7df01e09837cf54835a728c
      else
        if slot < 11 then
          if slot < 10 then
            0xf92764aa096a71c0b0b87cf3acbce1a5486695e600e5c3b3bab693c52907a95cb8152f02df6b800b2d661f9d7de2e860ca749f85e92b801d96478152cf3b56e007525e87e6b73cd2a0789ae7e19ad340074b94c185d1efaa5782528f25b5bed03d2a074e
          else
            0xc4e474195abca0b6164775b3c400b6c873757dcaee1433aad8b0641e03ef970c5396b04abcf70348aa1dbe9a629cbc12d4be4e7133a03636d60934a5afb2b2e3c1ac83359f9049668d7cd5961c89d03dae6d826b5243f2be34ac5641ad5a781393469ed5
        else
          if slot < 12 then
            0xf290cdc35e42412e46bebd38550c8e2fda761339703b1769838920f6e2dfa0ba9ba05e935c872e01cbd65989923696cee7607d5806aeaa8e044c6cd757dd0159a94333572c0d18e1bed4f9030bc835babb6278e28cd6b6588c1e21afd5d216c750c6b4eb
          else
            0xa1a3fbdc9861ba83711dc0bd0d8d9c62ecb32d8433efae01609835b7abb0a9ab24ce369e070dc32b8559c5ec59077ef4e02
  (x >>> ((i % 8) * 100)) &&& hadMask 100

private def hadMyK404 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 6 then
      if slot < 3 then
        if slot < 1 then
          0x3cb59b35a7a00f2d66cd69e001f5acd9ac3d007d6b366b0f008eaf66c571c823abd9b15c700c755b36ab8c431d56cdaae300e3a8d9bd5c4238ea366f57100f0d66cd6be013c359b35af800796b366b4f009e5acd9ad3c000000000000004000000000000
        else
          if slot < 2 then
            0xcd9ad3c02f2d3366b4f003cb45acd9ad3d00f16b366b4f003cad66cd61e807ab59b3587801e57b362b8e42395ecd8ae3808eaad9b55c6231aab66d57180c6d46cdeae2138b51b37ab880e26b366b5f00bc1acd9ad7c00f0b59b35a7805e2d66cd69e0078
          else
            0x9ad7c02f0d66a6b5f003c359acd69e01796b3335a7801e5acc66cd69e8079699b35a7801e5ab366b0f403eb2cd9ac3c00facd9b15c7211d5b66c571c047566cdaae3118ea9b36ab8c063aa366f57109c750d9bd5c4071d49b35af805e1aa6cd6be00786a
      else
        if slot < 4 then
          0xd5c4271d46cdb57101c751b366be01786b3669af801e1acd9ab4f00bcb59b32d3c00f2d66cc66b4f403cb5999ad3c00f2d66b3587a01f5acacd61e007d6b2d8ae3908eaf6362b8e023abd86d57188c755b1b55c6031d56c37ab884e3a8d8deae2038ea36
        else
          if slot < 5 then
            0xc6231d56cdaab180c755b36aae2138ea366f53880e3a8d9bd4f00bc359b35abc00f0d66cd6a7805e5acd9ad1e00796b366b45a7a01e5acd9969e00796b366ac3d00fad66cab0f003eb59b2571c84757b3615c7011d5ecd8ab8c463aad9b2ae3018eab66c
          else
            0x211d5ecd8ae3804757b362b8e118eab66d5718063aad9b55c609c751b37ab88071d46cdeae205e1acd9ad7c00786b366b5f002f2d66cd69e003cb59b35a783d00f2d66cd68f003cb59b35a1e807d6b366b07801f5acd9ac8e423abd9b15a3808eaf66c56
    else
      if slot < 9 then
        if slot < 7 then
          0x7150993a8e3fe3abd9b15c72038aa4c95473ff1d56cdaae3101c572642a3bff8ea366f571080f29932941fffc359b35af8048694c994b0ffde5acd9ad3c02ffffffffffffc00000000000180796b366b4f001e5acd9ad3c403eb59b3587800fad66cd61e
        else
          if slot < 8 then
            0x5299329e1ff86b59b3587a01ea84c9d471fdc55ecd8ae3908e55264aa39fce6ab66d57188c62b932151dfc7751b37ab884e294c994a0ffc3dacd9ad7c02f04a64ca587fe1ed66cd69e0178c34a64ca587fcf2d66cd69e80e0a532653c3fc7d6b366b0f40
          else
            0x9932961ff86959b35a7a01e5a4c994f0ffc14ecd9ac3d00fac264ea38fee2a766c571c84756932551cfe7155b36ab8c463aac990a8efe38acd9bd5c4271d464ca507fe1e566cd6be01786a32652c3ff0d2f366b4f00bcb4a532652c3ff0d6b366b4f403c
      else
        if slot < 11 then
          if slot < 10 then
            0x4b0ffc34a64ced3c02f2d66cc994b0ffc34a659ad3d00f2d664ca787fe0a536cd61e807d6b22751c7f71509f62b8e423abd892a8e7f38aa4db55c6231d56cc85477f1c5724deae2138ea3665283ff0f29966b5f00bc359a32961ff8694cf35a7805e5acc
          else
            0xffc3ca64ca57c02f0d66cd6a87fe1a532652de01796b366b4a587fe1a5326569e80796b36653c3ff0529936b0f403eb59b2a8e3fb8a84c9d5c7211d5ecd85473f9c55264eae3118eab66c2a3bf8e2b932757109c751b36941ff8794c995af805e1acd9a
        else
          if slot < 12 then
            0xfe38ae4c85474271d46cdeae2fe1e53265283c1786b366b5f0ff0d29932961c0bcb59b35a78c3ff0d2993294f403cb59b35ae1ff8294c994c7a01f5acd9ac71fdc54264ea63908eaf66c5639fce2a932557188c755b36aa1dfc715c990af884e3a8d9bd4
          else
            0xff8694c994b0e01e5acd9ad3cffc14a64ca78500fad66cd61efee2a132751c484757b362b8efe7154992a8e4463aad9b55c6
  (x >>> ((i % 8) * 100)) &&& hadMask 100

private def hadMyTop404 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xfffffffffffffffffffffffff80000000000000000000000003ffffffffffffffffffffffffdfffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffe
    else
      0xfffffffffffffffffffffffff7ffffffffffffffffffffffffc0000000000000000000000001fffffffffffffffffffffffff00000000000000000000000007ffffffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 404)) &&& hadMask 404

private def hadRow404 (i : Nat) : Nat :=
  hadMiyamotoRow 101 21392 55217 hadMyTop404 hadMyU404
    hadRow100 hadMyK404 i

private def hadRow408 (i : Nat) : Nat :=
  hadDouble 204 hadRow204 i

private def hadRow412 (i : Nat) : Nat :=
  let r := i % 103
  if i < 103 then
    hadJoin4 103
      (hadCyclicCell 103 r 0x169548a3bc23aed5697e6e313 93 1 0x0)
      (hadCyclicCell 103 r 0x11f3eebe94ce540ec94298f4d 4 102 0x0)
      (hadCyclicCell 103 r 0x61a9fe16d81391d13452f1c9 58 102 0x7fffffffffffffffffffffffff)
      (hadCyclicCell 103 r 0xfb45111c43d2c1cf64624499 40 102 0x7fffffffffffffffffffffffff)
  else
  if i < 206 then
    hadJoin4 103
      (hadCyclicCell 103 r 0x11f3eebe94ce540ec94298f4d 4 102 0x7fffffffffffffffffffffffff)
      (hadCyclicCell 103 r 0x169548a3bc23aed5697e6e313 93 1 0x0)
      (hadCyclicCell 103 r 0x99224626f3834bc23888a2df 69 102 0x0)
      (hadCyclicCell 103 r 0x49c7a51645c4e40db43fcac3 52 102 0x7fffffffffffffffffffffffff)
  else
  if i < 309 then
    hadJoin4 103
      (hadCyclicCell 103 r 0x61a9fe16d81391d13452f1c9 58 102 0x0)
      (hadCyclicCell 103 r 0x99224626f3834bc23888a2df 69 102 0x7fffffffffffffffffffffffff)
      (hadCyclicCell 103 r 0x169548a3bc23aed5697e6e313 93 1 0x0)
      (hadCyclicCell 103 r 0x153994bebbe7c40b2f1942937 58 102 0x7fffffffffffffffffffffffff)
  else
    hadJoin4 103
      (hadCyclicCell 103 r 0xfb45111c43d2c1cf64624499 40 102 0x0)
      (hadCyclicCell 103 r 0x49c7a51645c4e40db43fcac3 52 102 0x0)
      (hadCyclicCell 103 r 0x153994bebbe7c40b2f1942937 58 102 0x0)
      (hadCyclicCell 103 r 0x169548a3bc23aed5697e6e313 93 1 0x0)

private def hadRow416 (i : Nat) : Nat :=
  hadDouble 208 hadRow208 i

private def hadCore420 (i : Nat) : Nat := hadRot 419 0x22b270a3c0aa37e41bae3667b584438bac212253b592978060c83ecf9fe16b65235bb7bca2e3dde5219938a27d813aafc3af1b2ba i

private def hadRow420 (i : Nat) : Nat :=
  hadPaley1 hadCore420 i

private def hadRow424 (i : Nat) : Nat :=
  hadDouble 212 hadRow212 i

private def hadRow428 (i : Nat) : Nat :=
  let r := i % 107
  if i < 107 then
    hadJoin4 107
      (hadCyclicCell 107 r 0x2b0f7ba9d305e25cdde5f50f6f 89 1 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x2c2262ddd065caef6f9499ef19 105 106 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x2c2262dc2f9a3510b86a0f6f09 105 106 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x2c2262ddd065caef506b6610e5 105 106 0x7ffffffffffffffffffffffffff)
  else
  if i < 214 then
    hadJoin4 107
      (hadCyclicCell 107 r 0x2c2262ddd065caef6f9499ef19 105 106 0x0)
      (hadCyclicCell 107 r 0x2b0f7ba9d305e25cdde5f50f6f 89 1 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x29c219b582bdd4e982eed1910d 6 106 0x0)
      (hadCyclicCell 107 r 0x243dbc1587422b167d0ed1910d 6 106 0x7ffffffffffffffffffffffffff)
  else
  if i < 321 then
    hadJoin4 107
      (hadCyclicCell 107 r 0x2c2262dc2f9a3510b86a0f6f09 105 106 0x0)
      (hadCyclicCell 107 r 0x29c219b582bdd4e982eed1910d 6 106 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x2b0f7ba9d305e25cdde5f50f6f 89 1 0x7ffffffffffffffffffffffffff)
      (hadCyclicCell 107 r 0x2422b167d112e6ef2fb384336b 77 106 0x7ffffffffffffffffffffffffff)
  else
    hadJoin4 107
      (hadCyclicCell 107 r 0x2c2262ddd065caef506b6610e5 105 106 0x0)
      (hadCyclicCell 107 r 0x243dbc1587422b167d0ed1910d 6 106 0x0)
      (hadCyclicCell 107 r 0x2422b167d112e6ef2fb384336b 77 106 0x0)
      (hadCyclicCell 107 r 0x2b0f7ba9d305e25cdde5f50f6f 89 1 0x7ffffffffffffffffffffffffff)

private def hadRow432 (i : Nat) : Nat :=
  hadDouble 216 hadRow216 i

private def hadMyU436 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 7 then
      if slot < 3 then
        if slot < 1 then
          0xa195fef48592866b8587d5a4b42c88cfe5e60552d9651a1b64c5bab23e3e4b359a412b7aa00ff154c592f4f92ce668055cf300fdc94666c597e4e23cc0a7d3182567665d64347f252172f4ae98442b333b3a09aff9e903c298754e72790d415a4e3fe392d4185bcc5519ed0c
        else
          if slot < 2 then
            0x8e79f906b4476325807e64b5553573c72835b0bb2b2c0a3656aad94e9ebb414ea4975940d5b2b5c0d234f5da0651b5f918073985af2eb9cf46341de151fa9810e67749188ef2d1a4c98f6e46c0c750bb69155f968d47452e76360a799558ca331f1e80d653cdd4a050f296f5
          else
            0xff34676a86809b869679f3113303e5214da13e8ed418556336cdf8c7dca4e648e91860746e8cf29766be66239e05e88382c572cb47b9c1ff3b1c13264700373f836a2b575f2118ee8b2669c1a03d6b587afc71a031771791ec024897ce9ae3cbae60cae1c687301c6cb4ba37
      else
        if slot < 5 then
          if slot < 4 then
            0xdc5f216ca129f07ecdb31aa860a6405855b98b3fc332233e79a587c62648ad4d78fb0db18ca7dd2826899522be22b7d49dc2cd9c71c1b14ca515b25cbf85ce872af38c0f4e936a294ca340c73d5385ce87fb511f512a645a0e38e6cd0ee4a7c7acad449918d052ef94c636c3
          else
            0x37436b0538f3aa6d55a9b140d351b88b5827e79c72aab499f8069358e1d4c19d74f3b174b4d8e033827a3ba301638fdd65cfa44900de99345dc6213eb9786b5af0160e5899320e373fe0eb515b07f3b00345e81e71199f5a778b4d3a8d070625c499c94ef8dba53cc5d8b818
        else
          if slot < 6 then
            0xd2a819e9fcc44d768c9b61629a6852684bdfea6150b496af868759f29ac05e3e3316bda53c2814aecd28b8ac5a7eaa0c6aa67941b1b9bc64c962d3dc465b742b8c0d89d2a1ee0b18bce7624bb99c20657eeb629816ebcb11d3d6867380627a495ca0b75e5cac0eb536ac0a6b
          else
            0xad922fc9847b10e819f7bf113446909d3fc7488b09ec555d4c37c40ad271ff1c96a0c2de62a8cf6860f025e7fd64170ac27939cab865d3a1293f8b09af7333508865d4b0cf11c9fa68d9a99b9a90632f940599cd27cbd2698a4efc033cea80966b349f1f134caa3fc0157b52
    else
      if slot < 10 then
        if slot < 8 then
          0xea7c34623c2dcc1e5fbc7154294277efa332a0324cd2f0a1ba35dc43bf3d198584a2768f541ed0b610ebf97ac3a019d23c3d122db475951f8bd02f846c11f9e9d2649ae44afd2f506a8128d72f24d9c2b262d7c97a93417b14b8fc45c744d8169f25988d2d5663afea27d00
        else
          if slot < 9 then
            0x9fcd839b20d232ae6e263256d13afeb45cd93000f4f1712483bfb097ced073843d81e7e541acb621c6bf588c7d41920b1f2ea14a5ba330fb4c63286d967df8745e42ca09b35d418d8aac939fe52e708b5065ae28d0b2c5e8171fdf26c291913de9c68bb02aa328fe691714ec
          else
            0xc3779222ac51cfde101f0dd0763d592cd117508f7e7289a92d8ac9ebc0ee881b8d63e2b4c54e4c475e1c071446f86fbfd5a67a12622278ac89a8177339fde21dc95809a7eb635b52141453cb443136765ebf290a6d48bc245f3cc9a17906b5f900b368576571e9f74c4ac825
      else
        if slot < 12 then
          if slot < 11 then
            0x8a0a12b6b1b5f9e9b9b2308b4f2733ba05644d4796406a4ee11efe7d87d88a380e1d1119217996aff1ac76045dc0f5eb88c9ca8cb51fbc42ba22cd26ae4d46d2564539fce28d51127bb0f1b82ec3e021ef97196888f295d7acc16b4b2198faea53c445a63a7c66134b5a0cd7
          else
            0x4d546c60aeb3642b4439d29fe72a6d85318cb7c3014d09e8b87ef91260af8c46bf5b17694a15d3e3406f087382dcfa4e11b4d60a9f9ec00326ce8b5fd437f704923a3cb312c136706cfe722da93191d9d5a9ba85b34027ea904d48cbbe5e390f44ad94253f75827a164cf3e8
        else
          if slot < 13 then
            0x5582bd2fd489f50e6c93d3ac52887d02f47e2a6964992e5e7e20d60170d7a7f5c238b6d122f0f12e4868662f3f708db42de0abc5b9130153317dfb90aeb176143d2cc9ed0f118b0f95c250aa38f7e9e0c55037458e5ef20dca3a259fc5315e8d342c51d69a6250d93efe3a0
          else
            0x3444b8ff2e42588fb0caeaa8de42378864fd126d48b223f7be605cd2c46693e5a06c02f915fd719aaa0b257a4fad1908b8e88fc74a37
  (x >>> ((i % 8) * 108)) &&& hadMask 108

private def hadMyK436 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 7 then
      if slot < 3 then
        if slot < 1 then
          0x3f48ab3ef4e663420cabb40f2d81fa4559f7a7331a10655da0796c0fd22acfbd3998d0832aed03cb687e91567de9ccc6841957681e5ac3f48ab3ef4e663420cabb40f2c61fa4559f7a7331a10655da0796b0fd22acfbd3998d0832aed03ca000000000000000000000000000
        else
          if slot < 2 then
            0x48ab3ef4e663420cabb40f2d87ea4559f7a7331a10655da0796c3ed22acfbd3998d0832aed03cb61ee91567de9ccc6841957681e5b0ef48ab3ef4e663420cabb40f2d86fa4559f7a7331a10655da0796c2fd22acfbd3998d0832aed03cb607e91567de9ccc6841957681e5b0
          else
            0xab3ef4e663420cabb40f2d87e90559f7a7331a10655da0796c3f482acfbd3998d0832aed03cb61fa41567de9ccc6841957681e5b0fd28ab3ef4e663420cabb40f2d87e84559f7a7331a10655da0796c3f422acfbd3998d0832aed03cb61fa91567de9ccc6841957681e5b0fc
      else
        if slot < 5 then
          if slot < 4 then
            0x3ef4e663420cabb40f2d87e91569f7a7331a10655da0796c3f48aacfbd3998d0832aed03cb61fa45467de9ccc6841957681e5b0fd22ab3ef4e663420cabb40f2d87e91459f7a7331a10655da0796c3f48aacfbd3998d0832aed03cb61fa44567de9ccc6841957681e5b0fd22
          else
            0xf4e663420cabb40f2d87e91567c7a7331a10655da0796c3f48ab3ebd3998d0832aed03cb61fa4559ede9ccc6841957681e5b0fd22aceef4e663420cabb40f2d87e91566f7a7331a10655da0796c3f48ab2fbd3998d0832aed03cb61fa45587de9ccc6841957681e5b0fd22ac
        else
          if slot < 6 then
            0xe663420cabb40f2d87e91567de87331a10655da0796c3f48ab3ef43998d0832aed03cb61fa4559f7a9ccc6841957681e5b0fd22acfbc4e663420cabb40f2d87e91567dea7331a10655da0796c3f48ab3eed3998d0832aed03cb61fa4559f6e9ccc6841957681e5b0fd22acfa
          else
            0x63420cabb40f2d87e91567de9cc31a10655da0796c3f48ab3ef4e698d0832aed03cb61fa4559f7a72cc6841957681e5b0fd22acfbd38663420cabb40f2d87e91567de9c331a10655da0796c3f48ab3ef4e998d0832aed03cb61fa4559f7a6ccc6841957681e5b0fd22acfbd2
    else
      if slot < 10 then
        if slot < 8 then
          0x420cabb40f2d87e91567de9ccc6a10655da0796c3f48ab3ef4e662d0832aed03cb61fa4559f7a73306841957681e5b0fd22acfbd39983420cabb40f2d87e91567de9ccc1a10655da0796c3f48ab3ef4e668d0832aed03cb61fa4559f7a732c6841957681e5b0fd22acfbd398
        else
          if slot < 9 then
            0xcabb40f2d87e91567de9ccc6840655da0796c3f48ab3ef4e66342832aed03cb61fa4559f7a7331a041957681e5b0fd22acfbd3998d020cabb40f2d87e91567de9ccc6810655da0796c3f48ab3ef4e66340832aed03cb61fa4559f7a7331a841957681e5b0fd22acfbd3998c
          else
            0xabb40f2d87e91567de9ccc6841855da0796c3f48ab3ef4e663420c2aed03cb61fa4559f7a7331a106957681e5b0fd22acfbd3998d082cabb40f2d87e91567de9ccc6840655da0796c3f48ab3ef4e66342032aed03cb61fa4559f7a7331a101957681e5b0fd22acfbd3998d08
      else
        if slot < 12 then
          if slot < 11 then
            0xb40f2d87e91567de9ccc6841956da0796c3f48ab3ef4e663420caaed03cb61fa4559f7a7331a106547681e5b0fd22acfbd3998d0832abb40f2d87e91567de9ccc6841945da0796c3f48ab3ef4e663420caaed03cb61fa4559f7a7331a106457681e5b0fd22acfbd3998d0832
          else
            0xf2d87e91567de9ccc6841957680796c3f48ab3ef4e663420cabb403cb61fa4559f7a7331a10655da81e5b0fd22acfbd3998d0832aec40f2d87e91567de9ccc68419576a0796c3f48ab3ef4e663420cabad03cb61fa4559f7a7331a10655c681e5b0fd22acfbd3998d0832ae
        else
          if slot < 13 then
            0x2d87e91567de9ccc6841957681e96c3f48ab3ef4e663420cabb40ecb61fa4559f7a7331a10655da06e5b0fd22acfbd3998d0832aed02f2d87e91567de9ccc6841957680796c3f48ab3ef4e663420cabb403cb61fa4559f7a7331a10655da01e5b0fd22acfbd3998d0832aed0
          else
            0xd87e91567de9ccc6841957681e46c3f48ab3ef4e663420cabb40f2b61fa4559f7a7331a10655da0785b0fd22acfbd3998d0832aed03c
  (x >>> ((i % 8) * 108)) &&& hadMask 108

private def hadMyTop436 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xfffffffffffffffffffffffffff8000000000000000000000000003ffffffffffffffffffffffffffdfffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffe
    else
      0xfffffffffffffffffffffffffff7ffffffffffffffffffffffffffc000000000000000000000000001fffffffffffffffffffffffffff0000000000000000000000000007ffffffffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 436)) &&& hadMask 436

private def hadRow436 (i : Nat) : Nat :=
  hadMiyamotoRow 109 21392 55217 hadMyTop436 hadMyU436
    hadRow108 hadMyK436 i

private def hadRow440 (i : Nat) : Nat :=
  hadDouble 220 hadRow220 i

private def hadCore444 (i : Nat) : Nat := hadRot 443 0x27913dade01c264946eabd1ef6828b2dcb830227201db85651873ab32a31e7595e247fb1bbf3e2c4b2ebe908742a89d6d9bc7f84a43761a i

private def hadRow444 (i : Nat) : Nat :=
  hadPaley1 hadCore444 i

private def hadRow448 (i : Nat) : Nat :=
  hadDouble 224 hadRow224 i

private def hadMyU452 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 7 then
      if slot < 3 then
        if slot < 1 then
          0x31bf0b3b996249c551579072d366387b84f6cac32672c48be2187aae992ee30fb2315575282ce4923cdb0a9bf18ff1988398991e7269562ddd1570cdd84c78fe540739043f70274f6c31b72f08369b227c0d5ad29695d7035d935257a38387058ee54346ebabaec58499c4c3d7864732
        else
          if slot < 2 then
            0x7f10ffcb4a6202692d3e2cbd43828f8c3ae9e213876056d09b31bad51dce1f76d180c69227745d9c4d684de48768f4487b2c89c906ab4bfce7b890d957871439926480ee756ec6f86c3c6da14c44e51c32372b3b6b74341e16c99b93621a0913d5dff3ee122723e4e0eab89300adbe89
          else
            0x45ea3d094a3b3bd3886b535cb92176b996aca5109dfbc133bd9a089090fb1b45064fae1d350cb70bdd90643fe6518295b50e695d1ac5e6e0ba4bfc6a94247109e71ac3e4b954f0576de81398932415e3b09bad0fac73bede214158811ee9dc651ea1dc29d76518ac8dc28ae0ea36d716
      else
        if slot < 5 then
          if slot < 4 then
            0xec32236076bee1d04617656f48e37e4d19981b4f45ca2a9db68b2075732e04ce2d2bb6e40d46cf65847c16dda1054b66f93047ca4cf6649d9f66d2a085bb68b9266f3253e20c6dd4b4732074ce3e21a6f362b027a2f2d81998b27eae04d16db95453877d6e06c44c37c712f6a6e8620b
          else
            0xb13518a6eb943b68eb6c570751431a82847b7dce358578a63b977881c919c817b6ea0ff0b5d90dc7a8248e2429563fd25d2a9d27c358e790ada9418a67fc260767a358ba967075f260a2d8df0909bbd0ed30acb8b908a535699d6e091059bdcc83dfdcdc5290bc57a2849d3acad611cb
        else
          if slot < 6 then
            0x727c4e44877cf917db500c91d57d99368782c2ed6fbabc8905846c93285b63c361f63dcd4ec4c38a72228e1ea9b091de776ae770126499cde122f16e127b23fd2d56093913463018b6ef873b816b239ba2ee449e1c847975c31f1ab5d8cd90b6a06404652d3ff08fe41c2bd347cb496
          else
            0x21a375d5d762c24ce261ebc323994ac9bac0eba969a771a0e1c1c5ea10f4ed8c36f2e44b5ab03e44d96c1e321bb30ea8bb0efc209ce02a7fc1198ff18fd950b46a964e789919aa8c4df0c77499db3c49273414ae64c3536f21de1c755e1847d1234e924699dcd0fd8c66cb4e09ea8aa3
    else
      if slot < 10 then
        if slot < 8 then
          0x875363fd2d0229b5df01b475631153f931f6be1400e8f312de0a35aabdc8c86c8b5a92703fcbbbb811484cd70dbdc4b4241e4fd033de1a2a167dc25b6578825785b61ee3168c24deb846ecba1123d17a67716c614a2fdc237e542890f9ab27a4f25285a3be12fb0e8454b2f4d1dd52b0
        else
          if slot < 9 then
            0xdb65763d4a12147b00fe8a152f53e9a6bb1c8d142aaf847d552293c97887df84660b1cf5ce28be8985a47608eb9284c67e2fb69f8ed440323b9075c785252d5b716ee9a5121cd2e30db360595307f8cfd539090d3f610ed1b8b0a5a2ec75faa0c8c6aeb6c3be5a2c0049be0768b24e67
          else
            0xbbe55d0285a75cd0da50b5870fd91cf22ca1ca51fc58fce9180fc5ac875858a8b26cf626dfba4425535ec6ec8e7450343a12775c20d3abee2177120e1c3e758d7d7728184cba31bb2b05078debc6379a9681e07559dd97a20a163fc21b8d0b4cb65f48eec953848a9ce19da78462d96
      else
        if slot < 12 then
          if slot < 11 then
            0x59718805f53fd0fd938d6846c859f2b84e2ad20aeccfc550a43ff8482f9788451e85f21ee4c68c4d75c51d83460a87d7d99d7b7346122ec49bebe15062c1b823744862cedeb94fa178a211e9f4a3aeb23163277837504b54721d4f121ffc250aa3f30bfcafa0118e9a9a136216b1c9bf
          else
            0x95121ca937712f69b4621e5b9873c685045e9bb9aaa6d32d0b1d843f7b1e0a0d4dd8c5e07816959ec63de7c387048ee847d321814eebeb1ac2c0a2e71376377d5cb043aee485f364d151a1ae13acaa4225dfb646f8a5385344f3895a3f018973f1a3ae5a140baa7dd0bf0e1ad0a5b0b3
        else
          if slot < 13 then
            0x345a7dc36d75e6724d16e07d92a50d1d8b7086fc6313055fae3745ca9a06cdb0c74bb0909cabf31fe0b4a4a1e3ae09dc3848a597768eda7e632149d7106e4c022b71f96df438d06621fbe11e25a1917d1473af5428b138dd659793c944aabe21f5284852bc6ea6dbcaf4a8517f00de
          else
            0x2170df487dc5a10d4abb8b2f4d2a142a7ec43bf4524a4f25e4d59f09885d37621d7b2486368ee65e8bc4411ea6da43be683168c7786da1ea242d23bdb0eb3254587bcc0bf278495ad1361313bd12881dddd3fc0e00287d6f8c9fca55ac507b48cf179440b4bfc6cae188c6ae2d80fbad
  (x >>> ((i % 8) * 112)) &&& hadMask 112

private def hadMyK452 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 7 then
      if slot < 3 then
        if slot < 1 then
          0x3be06ca3be06ca3be06ca3be06caf1c6364f1c6364f1c6364f1c6364eaaa1b2eaaa1b2eaaa1b2eaaa1b2e71c2d8e71c2d8e71c2d8e71c2d87e08d6c7e08d6c7e08d6c7e08d6cbd054b6bd054b6bd054b6bd054b6dc83a5adc83a5adc83a5adc83a5a0000000000000000000000000000
        else
          if slot < 2 then
            0x8c6cbc68c6cbc68c6cbc68c6cbc654367aa54367aa54367aa54367aa385b39c385b39c385b39c385b39c11ad9f811ad9f811ad9f811ad9f80a96ef40a96ef40a96ef40a96ef4074b772074b772074b772074b7728fb132c8fb132c8fb132c8fb132c57d099657d099657d099657d0996
          else
            0x6cf55506cf55506cf55506cf5550b6738e0b6738e0b6738e0b6738e05b3f0465b3f0465b3f0465b3f0462dde82a2dde82a2dde82a2dde82a96ee41c96ee41c96ee41c96ee41c6265a3e6265a3e6265a3e6265a3ea132d5ea132d5ea132d5ea132d5ec0d94eec0d94eec0d94eec0d94ee
      else
        if slot < 5 then
          if slot < 4 then
            0x81f72937e08d6c81f72937e08d6c42fab49bd054b642fab49bd054b6237c5a5dc83a5a237c5a5dc83a5afffffff0000000fffffff0000000cb47d88cb47d88cb47d88cb47d8865abe8465abe8465abe8465abe84b29df02b29df02b29df02b29df02d978e30d978e30d978e30d978e30
          else
            0xf56910b0a96ef4f56910b0a96ef4f8b488d074b772f8b488d074b772704ecd38fb132c704ecd38fb132ca82f66957d0996a82f66957d0996c41f9353be06cac41f9353be06ca0e39c9bf1c63640e39c9bf1c63641555e4deaaa1b21555e4deaaa1b218e3d27e71c2d818e3d27e71c2d8
        else
          if slot < 6 then
            0x6911be396ee41c6911be396ee41c9d9a5c16265a3e9d9a5c16265a3e5ecd2a1a132d5e5ecd2a1a132d5e3f26b11c0d94ee3f26b11c0d94ee73934398c6cbc673934398c6cbc6abc985554367aaabc985554367aac7a4c63385b39cc7a4c63385b39cee5260711ad9f8ee5260711ad9f8
          else
            0x34b8277cb47d8834b8277cb47d889a5417b65abe849a5417b65abe844d620fdb29df024d620fdb29df0226871cfd978e3026871cfd978e30930aaaf6cf5550930aaaf6cf5550498c71fb6738e0498c71fb6738e0a4c0fb95b3f046a4c0fb95b3f046d2217d52dde82ad2217d52dde82a
    else
      if slot < 10 then
        if slot < 8 then
          0xc41f935c41f9353be06ca3be06ca0e39c9b0e39c9bf1c6364f1c63641555e4d1555e4deaaa1b2eaaa1b218e3d2718e3d27e71c2d8e71c2d881f729381f72937e08d6c7e08d6c42fab4942fab49bd054b6bd054b6237c5a5237c5a5dc83a5adc83a5affffffffffffff00000000000000
        else
          if slot < 9 then
            0x739343973934398c6cbc68c6cbc6abc9855abc985554367aa54367aac7a4c63c7a4c63385b39c385b39cee52607ee5260711ad9f811ad9f8f56910bf56910b0a96ef40a96ef4f8b488df8b488d074b772074b772704ecd3704ecd38fb132c8fb132ca82f669a82f66957d099657d0996
          else
            0x930aaaf930aaaf6cf55506cf5550498c71f498c71fb6738e0b6738e0a4c0fb9a4c0fb95b3f0465b3f046d2217d5d2217d52dde82a2dde82a6911be36911be396ee41c96ee41c9d9a5c19d9a5c16265a3e6265a3e5ecd2a15ecd2a1a132d5ea132d5e3f26b113f26b11c0d94eec0d94ee
      else
        if slot < 12 then
          if slot < 11 then
            0x7e08d6c81f729381f72937e08d6cbd054b642fab4942fab49bd054b6dc83a5a237c5a5237c5a5dc83a5a0000000ffffffffffffff000000034b827734b8277cb47d88cb47d889a5417b9a5417b65abe8465abe844d620fd4d620fdb29df02b29df0226871cf26871cfd978e30d978e30
          else
            0xa96ef4f56910bf56910b0a96ef4074b772f8b488df8b488d074b7728fb132c704ecd3704ecd38fb132c57d0996a82f669a82f66957d09963be06cac41f935c41f9353be06caf1c63640e39c9b0e39c9bf1c6364eaaa1b21555e4d1555e4deaaa1b2e71c2d818e3d2718e3d27e71c2d8
        else
          if slot < 13 then
            0x96ee41c6911be36911be396ee41c6265a3e9d9a5c19d9a5c16265a3ea132d5e5ecd2a15ecd2a1a132d5ec0d94ee3f26b113f26b11c0d94ee8c6cbc6739343973934398c6cbc654367aaabc9855abc985554367aa385b39cc7a4c63c7a4c63385b39c11ad9f8ee52607ee5260711ad9f8
          else
            0xcb47d8834b827734b8277cb47d8865abe849a5417b9a5417b65abe84b29df024d620fd4d620fdb29df02d978e3026871cf26871cfd978e306cf5550930aaaf930aaaf6cf5550b6738e0498c71f498c71fb6738e05b3f046a4c0fb9a4c0fb95b3f0462dde82ad2217d5d2217d52dde82a
  (x >>> ((i % 8) * 112)) &&& hadMask 112

private def hadMyTop452 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xffffffffffffffffffffffffffff80000000000000000000000000003fffffffffffffffffffffffffffdffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffe
    else
      0xffffffffffffffffffffffffffff7fffffffffffffffffffffffffffc0000000000000000000000000001ffffffffffffffffffffffffffff00000000000000000000000000007fffffffffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 452)) &&& hadMask 452

private def hadRow452 (i : Nat) : Nat :=
  hadMiyamotoRow 113 21392 55217 hadMyTop452 hadMyU452
    hadRow112 hadMyK452 i

private def hadRow456 (i : Nat) : Nat :=
  hadDouble 228 hadRow228 i

private def hadCore460 (i : Nat) : Nat := hadRot 229 0x8e909e3ecf04a845d3942fb299dbf6e6537d0a72e885483cdf1e425c4 i

private def hadRow460 (i : Nat) : Nat :=
  hadPaley2 230 hadCore460 i

private def hadRow464 (i : Nat) : Nat :=
  hadDouble 232 hadRow232 i

private def hadCore468 (i : Nat) : Nat := hadRot 467 0x269338a5f42e22cc50cfa706b7f31a0e9dab0a002390af9334d411f0a936af077d4d3360af63bffaf2a468fa730129f1a0cf5ccbb8bd05ae3369a i

private def hadRow468 (i : Nat) : Nat :=
  hadPaley1 hadCore468 i

private def hadRow472 (i : Nat) : Nat :=
  hadDouble 236 hadRow236 i

private def hadRoute476 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0xc086b330aed356004d1d7ef517e4c11a98f3a135607a8bfa608d8c79da026acd45fdb046ca3ced3004d5a2fef02364de76996009a17f7a91b2633b4c6ac013bfbd40d9305da63cd5802fdea2ec9822d31e69ab00
      else
        0x27ae2b5600bfa2e712de53d714a6ac03d173e96f2c0435b18576c26ac068eb921ad842bb6404d59475c90d6c095db32009aa3ae4d6b6042ed986c0135d72685b021f6cc2958026b9347d810d36615dab005c9a3a
    else
      if slot < 3 then
        0x560099b5e73252cf0b7d16ac015af3852967c5be8c4d580579c354b3e4df461eb8a484d5828b9feb79625c527809ab05cffbbcb12e293d401356e7fd1e5896149ebd8026b3fe8b2c4b7a4f5c2b004dff45d625bc
      else
        0x9ab03ce1b659f24fa30b01356670daecf929d185b8026ab86d7a7c94a8c2dfb004d436bcfe4a58616fa
  (x >>> ((i % 8) * 84)) &&& hadMask 84

private def hadRow476 (i : Nat) : Nat :=
  hadCwRow 7 17 0x1c78e 0xbb74 0x1a016 0x12312 hadRoute476 i

private def hadRow480 (i : Nat) : Nat :=
  hadDouble 240 hadRow240 i

private def hadCore484 (i : Nat) : Nat := hadRot 241 0x4595ca5dce8670dbda83b345f1ed02de3e8b37056f6c3985cee94ea6880 i

private def hadRow484 (i : Nat) : Nat :=
  hadPaley2 242 hadCore484 i

private def hadRow488 (i : Nat) : Nat :=
  hadDouble 244 hadRow244 i

private def hadCore492 (i : Nat) : Nat := hadRot 491 0x23a037aeb081265334ee2bf9a3c6d9a0a0ce4707a335402d62e15ad2093823be36fb4a578b94bfd533a1f1d8cfafa649c3a602b88d3359b7ef28a13fa3a i

private def hadRow492 (i : Nat) : Nat :=
  hadPaley1 hadCore492 i

private def hadRow496 (i : Nat) : Nat :=
  hadDouble 248 hadRow248 i

private def hadCore500 (i : Nat) : Nat := hadRot 499 0x31bd711894e8ad3f699b176f7208f400c32c3c64b8959241c0f7aa7b058afaaa0ae5f21aa10fc7db656e2d9c3cb3cffd0efb109172669034ae8d6e7714272 i

private def hadRow500 (i : Nat) : Nat :=
  hadPaley1 hadCore500 i

private def hadRow504 (i : Nat) : Nat :=
  hadDouble 252 hadRow252 i

private def hadRow508 (i : Nat) : Nat :=
  let r := i % 127
  if i < 127 then
    hadJoin4 127
      (hadCyclicCell 127 r 0xb4b3ee337d58b172a099c419697f17 60 1 0x0)
      (hadCyclicCell 127 r 0x161096686d846df7846468b2bf2a847 19 126 0x7fffffffffffffffffffffffffffffff)
      (hadCyclicCell 127 r 0x1263c27d8263dd9c0acb4ad51d9c15 10 126 0x7fffffffffffffffffffffffffffffff)
      (hadCyclicCell 127 r 0x16327d66f053dc8a461565c1ab1048f 20 126 0x7fffffffffffffffffffffffffffffff)
  else
  if i < 254 then
    hadJoin4 127
      (hadCyclicCell 127 r 0x161096686d846df7846468b2bf2a847 19 126 0x0)
      (hadCyclicCell 127 r 0xb4b3ee337d58b172a099c419697f17 60 1 0x0)
      (hadCyclicCell 127 r 0x1e2411ab074d50c4a277941ecd7c98d 112 126 0x0)
      (hadCyclicCell 127 r 0x150737156a5a6a073778c837c878c9 126 126 0x7fffffffffffffffffffffffffffffff)
  else
  if i < 381 then
    hadJoin4 127
      (hadCyclicCell 127 r 0x1263c27d8263dd9c0acb4ad51d9c15 10 126 0x0)
      (hadCyclicCell 127 r 0x1e2411ab074d50c4a277941ecd7c98d 112 126 0x7fffffffffffffffffffffffffffffff)
      (hadCyclicCell 127 r 0xb4b3ee337d58b172a099c419697f17 60 1 0x0)
      (hadCyclicCell 127 r 0x15974ecef0824ef24f4cb7bcbf1deab 87 126 0x7fffffffffffffffffffffffffffffff)
  else
    hadJoin4 127
      (hadCyclicCell 127 r 0x16327d66f053dc8a461565c1ab1048f 20 126 0x0)
      (hadCyclicCell 127 r 0x150737156a5a6a073778c837c878c9 126 126 0x0)
      (hadCyclicCell 127 r 0x15974ecef0824ef24f4cb7bcbf1deab 87 126 0x0)
      (hadCyclicCell 127 r 0xb4b3ee337d58b172a099c419697f17 60 1 0x0)

private def hadRow512 (i : Nat) : Nat :=
  hadDouble 256 hadRow256 i

private def hadCore516 (i : Nat) : Nat := hadRot 257 0x5ca862611f565e0594fadcdb1dfa441ce0897ee36ced7ca681e9abe2191854e8 i

private def hadRow516 (i : Nat) : Nat :=
  hadPaley2 258 hadCore516 i

private def hadRow520 (i : Nat) : Nat :=
  hadDouble 260 hadRow260 i

private def hadCore524 (i : Nat) : Nat := hadRot 523 0x348a2e32f707b1f65491bf8565a85097c89a78b931002a8c878c373a9deb3c901a7f6c32846a313ce1eceabff7362e1a6ec16f5ea595e0276d590721f10b38baed2 i

private def hadRow524 (i : Nat) : Nat :=
  hadPaley1 hadCore524 i

private def hadRow528 (i : Nat) : Nat :=
  hadDouble 264 hadRow264 i

private def hadRoute532 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 2 then
      if slot < 1 then
        0xc086b330aed356004d1d7ef517e4c11a98f3a135607a8bfa608d8c79da026acd45fdb046ca3ced3004d5a2fef02364de76996009a17f7a91b2633b4c6ac013bfbd40d9305da63cd5802fdea2ec9822d31e69ab00
      else
        0x27ae2b5600bfa2e712de53d714a6ac03d173e96f2c0435b18576c26ac068eb921ad842bb6404d59475c90d6c095db32009aa3ae4d6b6042ed986c0135d72685b021f6cc2958026b9347d810d36615dab005c9a3a
    else
      if slot < 3 then
        0x560099b5e73252cf0b7d16ac015af3852967c5be8c4d580579c354b3e4df461eb8a484d5828b9feb79625c527809ab05cffbbcb12e293d401356e7fd1e5896149ebd8026b3fe8b2c4b7a4f5c2b004dff45d625bc
      else
        0x9ab03ce1b659f24fa30b01356670daecf929d185b8026ab86d7a7c94a8c2dfb004d436bcfe4a58616fa
  (x >>> ((i % 8) * 84)) &&& hadMask 84

private def hadRow532 (i : Nat) : Nat :=
  hadCwRow 7 19 0x3168c 0x26964 0x5c03a 0x3402c hadRoute532 i

private def hadRow536 (i : Nat) : Nat :=
  hadDouble 268 hadRow268 i

private def hadCore540 (i : Nat) : Nat := hadRot 269 0xc6a5c8f7468a806436f0dacc9affa0e3ad71c17fd64cd6c3db09805458bbc4e958c i

private def hadRow540 (i : Nat) : Nat :=
  hadPaley2 270 hadCore540 i

private def hadRow544 (i : Nat) : Nat :=
  hadDouble 272 hadRow272 i

private def hadCore548 (i : Nat) : Nat := hadRot 547 0x35886b3bc774a1754b9591db27fc808c8e2479c938ad0830a6d1101f2eba7e1f6a43a3da90781a28b07f7749af3ef4ae36c61db8ecefec01b2476562d517ad11c2329ee52 i

private def hadRow548 (i : Nat) : Nat :=
  hadPaley1 hadCore548 i

private def hadRow552 (i : Nat) : Nat :=
  hadDouble 276 hadRow276 i

private def hadCore556 (i : Nat) : Nat := hadRot 277 0x9a4da28758f8dab1231a801fd75ccc3f2ded3f0ccebafe0056312356c7c6b8516c964 i

private def hadRow556 (i : Nat) : Nat :=
  hadPaley2 278 hadCore556 i

private def hadRow560 (i : Nat) : Nat :=
  hadDouble 280 hadRow280 i

private def hadCore564 (i : Nat) : Nat := hadRot 563 0x26832aa5b676278860c395c7e2c53a3ed3ba0ba53d8c0a8013b20ad8b477a4431db02137bf2473dda11d2e4afb237feafce435a2fa23483a35cb81c563cf9ee1b91925aab3e9a i

private def hadRow564 (i : Nat) : Nat :=
  hadPaley1 hadCore564 i

private def hadRow568 (i : Nat) : Nat :=
  hadDouble 284 hadRow284 i

private def hadCore572 (i : Nat) : Nat := hadRot 571 0x31a97238d1e3a42b1dfd07f5279be220e9481148ee914598b694686406b3f3fa126c8e2ab8ec9b7a030329fd9e9d692e65d7688ed77ed68fbb8261b501f40472bda3874e3b16a72 i

private def hadRow572 (i : Nat) : Nat :=
  hadPaley1 hadCore572 i

private def hadRow576 (i : Nat) : Nat :=
  hadDouble 288 hadRow288 i

private def hadCore580 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 18 then
      if slot < 9 then
        if slot < 4 then
          if slot < 2 then
            if slot < 1 then
              0xe99906d6dd8c79e237d81ad1f2aa78bd49a4af279563e2d606ff11e58c6cdad9a66500003a6661b5b7631e788df604b47caa9eaf52292be9e548f8bd81bbc47b631a36b6e99900002e99986d6dd8c79e237d802d1f2aa7abd4aa4aea795a3e2f606cf11fd8c60dadba6640000ba6661b5b7631e788df608b47caa9caf53a92ba9e568f8bd81b3c477631c36b6e99800002e99d86d4dd8c79e237d862d1f2aa72bd4ea4aaa795a3e3f606cf11dd8c70dacba6600004ba6761b437631e788df638b47caa94af57a92aa9e568f87d81f3c477630c36b2e99800032e98d86d8dd8c79e037d9e2d1f2aa12bd5ea4aaa795a3e5f607cf10dd8cb0dacba640000cba6b61b637611e780df6f8b43caaa4af57a92aa9e168fb7d80f3c437636c36b2e980000
            else
              0x9974d6c34c6ec23cf81be9f16a7955495eaf521553e2d1e6fb01e78c6ec6d86c65d30000665d35b0c31bb88f3e06f87c5a9e555257abd4a554f8b471bec479e31bb0b61b9974800019974d6c38c6ee23cd81bf1f16a7955495caf539553e2d186fb11e78c6ecad86e65d00000665db5b0e31bb88f3606f47c5a9e5752572bd4e554f8b441bec479e31bb6b6199974000099976d6c18c6fe23cd81bd1f16a795d4954af579553e2d006fb11e78c6edad86665d00002665db5b1631b788f7606f47c4a9e5f52512bd5e554f8b481bec479e31bb6b6199970000299966d6cd8c69e23fd81ad1f1aa793d4964af479553e2d606fb11e78c6edad82665c0001a6651b5b7631a788ff606b47c2a9e6f52492bd9e550f8b581bfc479631bb6b6299960000
          else
            if slot < 3 then
              0x86d6dd8c79e237d812d1f2aa7abd48a4afa79523e2f606ef11ed8c68dadba664000074cce1b5b7631e788df600b47caa9eaf52a92ba9e568f8bd81b3c47f631836b6e99900005d33186d6dd8c79e237d822d1f2aa72bd4ea4aea795a3e2f606cf11dd8c70dadba660000174cd61b537631e788df618b47caa9caf53a92aa9e568f8fd81b3c477631c36b2e99800005d33d86d0dd8c79e237d8e2d1f2aa52bd5ea4aaa795a3e1f607cf11dd8c30dacba660000974cb61b637631e780df678b47caa84af57a92aa9e568f97d81f3c437632c36b2e99000065d32d86d8dd8479e037dbe2d0f2aa92bd5ea4aaa785a3edf603cf10dd8db0dacba600001974c65d35b0db1bb08f3c06fb7c5a1e555257abd49554f0b47dbec079e21bb1b61b5974c0000
            else
              0xd6c30c6ee23cf81be1f16a7955495eaf529553e2d1c6fb11e78c6ec2d86e65d20000ccba35b0e31bb88f3606fc7c5a9e5552572bd4e554f8b461bec479e31bb2b61b99740000332ead6c38c6ee23cd81bd1f16a795d495caf539553e2d106fb11e78c6edad86665d00000ccbbb5b0631bf88f3606f47c5a9e5752552bd5e554f8b401bec479e31bb6b61999740001332e6d6c58c6de23dd81bd1f12a797d4944af579553e2d206fb11e78c6edad86665c00004ccb9b5b3631a788ff606b47c6a9e4f52592bd1e554f8b581bec479e31bb6b60999700005332c6d6dd8c69e23fd81ad1f0aa79bd4924af679543e2d606ff11e58c6edad8a665800034cca1b5b7631e788df606b47caa9e2f52692bc9e558f8b581bfc479631b36b6699940001d332
        else
          if slot < 6 then
            if slot < 5 then
              0xdd8c79e237d802d1f2aa7abd4aa4aea795a3e2f606cf11fd8c60dadba664000174ccc36b37631e788df608b47caa9caf53a92ba9e568f8bd81b3c477631c36b6e99800005d3330dacdd8c79e237d862d1f2aa72bd4ea4aaa795a3e3f606cf11dd8c70dacba660000174cec36a37631e788df638b47caa94af57a92aa9e568f87d81f3c477630c36b2e99800025d33b0da8dd8c79e037d9e2d1f2aa12bd5ea4aaa795a3e5f607cf10dd8cb0dacba640001974c6c36e37611e780df6f8b43caaa4af57a92aa9e168fb7d80f3c437636c36b2e98000065d35b0d96c36c6ec23cf01bedf1687955495eaf525553c2d1f6fb01e7886ec6d86d65d300000cba75b0d31bb08f3e06fa7c5a9e555257abd48554f8b479bec079e31bb1b61b1974c000132e9
            else
              0x8c6ee23cd81bf1f16a7955495caf539553e2d186fb11e78c6ecad86e65d00000ccba6b61e31bb88f3606f47c5a9e5752572bd4e554f8b441bec479e31bb6b61999740000332edad858c6fe23cd81bd1f16a795d4954af579553e2d006fb11e78c6edad86665d00004ccbb6b61631b788f7606f47c4a9e5f52512bd5e554f8b481bec479e31bb6b61999700001332edad8d8c69e23fd81ad1f1aa793d4964af479553e2d606fb11e78c6edad82665c00014ccb36b67631a788ff606b47c2a9e6f52492bd9e550f8b581bfc479631bb6b6299960000d3328dad9d8c79e237d81ad1f2aa78bd49a4af279563e2d606ff11e58c6cdad9a665000074cc836b77631e788df604b47caa9eaf52292be9e548f8bd81bbc47b631a36b6e99900001d3330dad
          else
            if slot < 7 then
              0x79e237d822d1f2aa72bd4ea4aea795a3e2f606cf11dd8c70dadba660000174ccc36b6ec61e788df618b47caa9caf53a92aa9e568f8fd81b3c477631c36b2e99800005d33b0da9bb1879e237d8e2d1f2aa52bd5ea4aaa795a3e1f607cf11dd8c30dacba660000974cec3686ec71e780df678b47caa84af57a92aa9e568f97d81f3c437632c36b2e99000065d31b0db1bb1479e037dbe2d0f2aa92bd5ea4aaa785a3edf603cf10dd8db0dacba600001974d6c36c6ec31bb08f3c06fb7c5a1e555257abd49554f0b47dbec079e21bb1b61b5974c000032e9ad86cc6ec23cf81be9f16a7955495eaf521553e2d1e6fb01e78c6ec6d86c65d300004cba6b61a31bb88f3e06f87c5a9e555257abd4a554f8b471bec479e31bb0b61b99748000332e9ad86
            else
              if slot < 8 then
                0xe23cd81bd1f16a795d495caf539553e2d106fb11e78c6edad86665d00000ccbb6b61c637788f3606f47c5a9e5752552bd5e554f8b401bec479e31bb6b61999740001332edad8318dde23dd81bd1f12a797d4944af579553e2d206fb11e78c6edad86665c00004ccbb6b62c636788ff606b47c6a9e4f52592bd1e554f8b581bec479e31bb6b60999700005332cdad9b18d9e23fd81ad1f0aa79bd4924af679543e2d606ff11e58c6edad8a665800034cca36b6ec636788df606b47caa9e2f52692bc9e558f8b581bfc479631b36b6699940001d3320dadbb18f9e237d812d1f2aa7abd48a4afa79523e2f606ef11ed8c68dadba664000074ccc36b6ec63e788df600b47caa9eaf52a92ba9e568f8bd81b3c47f631836b6e99900005d3330dadbb18
              else
                0x37d862d1f2aa72bd4ea4aaa795a3e3f606cf11dd8c70dacba660000174cec36a6ec63cf10df638b47caa94af57a92aa9e568f87d81f3c477630c36b2e99800025d33b0da1bb18f3c437d9e2d1f2aa12bd5ea4aaa795a3e5f607cf10dd8cb0dacba640001974c6c36c6ec63cf00df6f8b43caaa4af57a92aa9e168fb7d80f3c437636c36b2e98000065d35b0db1bb08f3c23cf01bedf1687955495eaf525553c2d1f6fb01e7886ec6d86d65d300000cba6b61b637608f3e06fa7c5a9e555257abd48554f8b479bec079e31bb1b61b1974c000132e9ad8698dda23cf81be1f16a7955495eaf529553e2d1c6fb11e78c6ec2d86e65d20000ccba6b618637788f3606fc7c5a9e5552572bd4e554f8b461bec479e31bb2b61b99740000332e9ad8718dd
      else
        if slot < 13 then
          if slot < 11 then
            if slot < 10 then
              0xd81bd1f16a795d4954af579553e2d006fb11e78c6edad86665d00004ccbb6b60c637f11e7606f47c4a9e5f52512bd5e554f8b481bec479e31bb6b61999700001332edad8b18dbc47bd81ad1f1aa793d4964af479553e2d606fb11e78c6edad82665c00014ccb36b66c634f11ff606b47c2a9e6f52492bd9e550f8b581bfc479631bb6b6299960000d3328dadbb18d3c477d81ad1f2aa78bd49a4af279563e2d606ff11e58c6cdad9a665000074cc836b6ec63cf11df604b47caa9eaf52292be9e548f8bd81bbc47b631a36b6e99900001d3330dadbb18f3c477d802d1f2aa7abd4aa4aea795a3e2f606cf11fd8c60dadba664000174ccc36b6ec63cf10df608b47caa9caf53a92ba9e568f8bd81b3c477631c36b6e99800005d3330dadbb18f3c4
            else
              0xe2d1f2aa52bd5ea4aaa795a3e1f607cf11dd8c30dacba660000974cec3686ec63cf11bec78b47caa84af57a92aa9e568f97d81f3c437632c36b2e99000065d31b0db1bb18f3c06fb3e2d0f2aa92bd5ea4aaa785a3edf603cf10dd8db0dacba600001974d6c36c6ec23cf01bec06fb7c5a1e555257abd49554f0b47dbec079e21bb1b61b5974c000032e9ad86d8dd8479e81be9f16a7955495eaf521553e2d1e6fb01e78c6ec6d86c65d300004cba6b61a637611e7e06f87c5a9e555257abd4a554f8b471bec479e31bb0b61b99748000332e9ad8618ddc479d81bf1f16a7955495caf539553e2d186fb11e78c6ecad86e65d00000ccba6b61c637711e7606f47c5a9e5752572bd4e554f8b441bec479e31bb6b61999740000332edad8718ddc479
          else
            if slot < 12 then
              0xd1f12a797d4944af579553e2d206fb11e78c6edad86665c00004ccbb6b62c636f11eec0db47c6a9e4f52592bd1e554f8b581bec479e31bb6b60999700005332cdad9b18d3c47fb036d1f0aa79bd4924af679543e2d606ff11e58c6edad8a665800034cca36b6ec634f11fec0cb47caa9e2f52692bc9e558f8b581bfc479631b36b6699940001d3320dadbb18f3c46fb032d1f2aa7abd48a4afa79523e2f606ef11ed8c68dadba664000074ccc36b6ec63cf11bec08b47caa9eaf52a92ba9e568f8bd81b3c47f631836b6e99900005d3330dadbb18f3c46fb022d1f2aa72bd4ea4aea795a3e2f606cf11dd8c70dadba660000174ccc36b6ec63cf11bec18b47caa9caf53a92aa9e568f8fd81b3c477631c36b2e99800005d33b0da9bb18f3c46fb0
            else
              0xf2aa12bd5ea4aaa795a3e5f607cf10dd8cb0dacba640001974c6c36c6ec63cf01becf168bcaaa4af57a92aa9e168fb7d80f3c437636c36b2e98000065d35b0db1bb08f3c06fb7c5a1f1687955495eaf525553c2d1f6fb01e7886ec6d86d65d300000cba6b61b637611e780df67c5a9e555257abd48554f8b479bec079e31bb1b61b1974c000132e9ad8698dd8479f037d1f16a7955495eaf529553e2d1c6fb11e78c6ec2d86e65d20000ccba6b618637711e7c0df47c5a9e5552572bd4e554f8b461bec479e31bb2b61b99740000332e9ad8718ddc479b037d1f16a795d495caf539553e2d106fb11e78c6edad86665d00000ccbb6b61c637711e6c0df47c5a9e5752552bd5e554f8b401bec479e31bb6b61999740001332edad8318dfc479b037
        else
          if slot < 15 then
            if slot < 14 then
              0xaa793d4964af479553e2d606fb11e78c6edad82665c00014ccb36b66c634f11fec0d68f8aa9e6f52492bd9e550f8b581bfc479631bb6b6299960000d3328dadbb18d3c47fb035a3e2aa78bd49a4af279563e2d606ff11e58c6cdad9a665000074cc836b6ec63cf11bec0d68f8aa9eaf52292be9e548f8bd81bbc47b631a36b6e99900001d3330dadbb18f3c46fb025a3e2aa7abd4aa4aea795a3e2f606cf11fd8c60dadba664000174ccc36b6ec63cf11bec0168fcaa9caf53a92ba9e568f8bd81b3c477631c36b6e99800005d3330dadbb18f3c46fb045a3f2aa72bd4ea4aaa795a3e3f606cf11dd8c70dacba660000174cec36a6ec63cf11bec3168fcaa94af57a92aa9e568f87d81f3c477630c36b2e99800025d33b0da1bb18f3c46fb1c5a3
            else
              0x92bd5ea4aaa785a3edf603cf10dd8db0dacba600001974d6c36c6ec23cf01bedf16879551e555257abd49554f0b47dbec079e21bb1b61b5974c000032e9ad86d8dd8479e037dbe2d27955495eaf521553e2d1e6fb01e78c6ec6d86c65d300004cba6b61a637611e7c0df4f8b49e555257abd4a554f8b471bec479e31bb0b61b99748000332e9ad8618ddc479f037c3e2da7955495caf539553e2d186fb11e78c6ecad86e65d00000ccba6b61c637711e6c0df8f8b29e5752572bd4e554f8b441bec479e31bb6b61999740000332edad8718ddc479b037a3e2ea795d4954af579553e2d006fb11e78c6edad86665d00004ccbb6b60c637f11e6c0de8f8aa9e5f52512bd5e554f8b481bec479e31bb6b61999700001332edad8b18dbc47bb037a3e2
          else
            if slot < 16 then
              0xbd4924af679543e2d606ff11e58c6edad8a665800034cca36b6ec634f11fec0d68f8553caf52692bc9e558f8b581bfc479631b36b6699940001d3320dadbb18f3c46fb035a3e554f2bd48a4afa79523e2f606ef11ed8c68dadba664000074ccc36b6ec63cf11bec0968f9553caf52a92ba9e568f8bd81b3c47f631836b6e99900005d3330dadbb18f3c46fb005a3e554f2bd4ea4aea795a3e2f606cf11dd8c70dadba660000174ccc36b6ec63cf11bec1168f9553caf53a92aa9e568f8fd81b3c477631c36b2e99800005d33b0da9bb18f3c46fb0c5a3e554d2bd5ea4aaa795a3e1f607cf11dd8c30dacba660000974cec3686ec63cf11bec7168f95524af57a92aa9e568f97d81f3c437632c36b2e99000065d31b0db1bb18f3c06fb3c5a3e554
            else
              if slot < 17 then
                0x495eaf525553c2d1f6fb01e7886ec6d86d65d300000cba6b61b637611e780df6f8b43caad257abd48554f8b479bec079e31bb1b61b1974c000132e9ad8698dd8479f037d3e2d4f2a9495eaf529553e2d1c6fb11e78c6ec2d86e65d20000ccba6b618637711e7c0df0f8b53cab52572bd4e554f8b461bec479e31bb2b61b99740000332e9ad8718ddc479b037e3e2d4f2ad495caf539553e2d106fb11e78c6edad86665d00000ccbb6b61c637711e6c0de8f8b53caf52552bd5e554f8b401bec479e31bb6b61999740001332edad8318dfc479b037a3e2d4f2bd4944af579553e2d206fb11e78c6edad86665c00004ccbb6b62c636f11eec0de8f8953caf52592bd1e554f8b581bec479e31bb6b60999700005332cdad9b18d3c47fb035a3e354f2
              else
                0xa4af279563e2d606ff11e58c6cdad9a665000074cc836b6ec63cf11bec0d68f9553c5ea4a92be9e548f8bd81bbc47b631a36b6e99900001d3330dadbb18f3c46fb025a3e554f57a92a4aea795a3e2f606cf11fd8c60dadba664000174ccc36b6ec63cf11bec0168f9553d5ea5a92ba9e568f8bd81b3c477631c36b6e99800005d3330dadbb18f3c46fb045a3e554e57a9ea4aaa795a3e3f606cf11dd8c70dacba660000174cec36a6ec63cf11bec3168f955395ea7a92aa9e568f87d81f3c477630c36b2e99800025d33b0da1bb18f3c46fb1c5a3e554a57a9ea4aaa795a3e5f607cf10dd8cb0dacba640001974c6c36c6ec63cf01becf168f955095eb7a92aa9e168fb7d80f3c437636c36b2e98000065d35b0db1bb08f3c06fb7c5a1e555257a
    else
      if slot < 27 then
        if slot < 22 then
          if slot < 20 then
            if slot < 19 then
              0xaf521553e2d1e6fb01e78c6ec6d86c65d300004cba6b61a637611e7c0df4f8b53caaa4af2bd4a554f8b471bec479e31bb0b61b99748000332e9ad8618ddc479f037c3e2d4f2aa92bcaf539553e2d186fb11e78c6ecad86e65d00000ccba6b61c637711e6c0df8f8b53caaa4af2bd4e554f8b441bec479e31bb6b61999740000332edad8718ddc479b037a3e2d4f2ba92b4af579553e2d006fb11e78c6edad86665d00004ccbb6b60c637f11e6c0de8f8b53caea4a92bd5e554f8b481bec479e31bb6b61999700001332edad8b18dbc47bb037a3e254f2fa92a4af479553e2d606fb11e78c6edad82665c00014ccb36b66c634f11fec0d68f8d53c9ea4a92bd9e550f8b581bfc479631bb6b6299960000d3328dadbb18d3c47fb035a3e154f37a92
            else
              0xa79523e2f606ef11ed8c68dadba664000074ccc36b6ec63cf11bec0968f9553d5ea45257a9e568f8bd81b3c47f631836b6e99900005d3330dadbb18f3c46fb005a3e554f57a95495ea795a3e2f606cf11dd8c70dadba660000174ccc36b6ec63cf11bec1168f955395ea75256a9e568f8fd81b3c477631c36b2e99800005d33b0da9bb18f3c46fb0c5a3e554e57a9d495aa795a3e1f607cf11dd8c30dacba660000974cec3686ec63cf11bec7168f955295eaf5252a9e568f97d81f3c437632c36b2e99000065d31b0db1bb18f3c06fb3c5a3e554257abd496aa785a3edf603cf10dd8db0dacba600001974d6c36c6ec23cf01bedf1687955495eaf524bd49554f0b47dbec079e21bb1b61b5974c000032e9ad86d8dd8479e037dbe2d0f2aa92bd
          else
            if slot < 21 then
              0x9553e2d1c6fb11e78c6ec2d86e65d20000ccba6b618637711e7c0df0f8b53caaa4af57a96554f8b461bec479e31bb2b61b99740000332e9ad8718ddc479b037e3e2d4f2aa92b95ea79553e2d106fb11e78c6edad86665d00000ccbb6b61c637711e6c0de8f8b53caea4ae57a9e554f8b401bec479e31bb6b61999740001332edad8318dfc479b037a3e2d4f2ba92a95ea79553e2d206fb11e78c6edad86665c00004ccbb6b62c636f11eec0de8f8953cbea4a257a9e554f8b581bec479e31bb6b60999700005332cdad9b18d3c47fb035a3e354f27a92c95ea79543e2d606ff11e58c6edad8a665800034cca36b6ec634f11fec0d68f8553cdea49257a9e558f8b581bfc479631b36b6699940001d3320dadbb18f3c46fb035a3e554f17a93495e
            else
              0xa3e2f606cf11fd8c60dadba664000174ccc36b6ec63cf11bec0168f9553d5ea5525753cae8f8bd81b3c477631c36b6e99800005d3330dadbb18f3c46fb045a3e554e57a9d495d4f29a3e3f606cf11dd8c70dacba660000174cec36a6ec63cf11bec3168f955395ea7525553cb68f87d81f3c477630c36b2e99800025d33b0da1bb18f3c46fb1c5a3e554a57abd49554f25a3e5f607cf10dd8cb0dacba640001974c6c36c6ec63cf01becf168f955095eaf525553c968fb7d80f3c437636c36b2e98000065d35b0db1bb08f3c06fb7c5a1e555257abd49554f1553c2d1f6fb01e7886ec6d86d65d300000cba6b61b637611e780df6f8b43caaa4af57a92554f8b479bec079e31bb1b61b1974c000132e9ad8698dd8479f037d3e2d4f2aa92bd5ea4
        else
          if slot < 24 then
            if slot < 23 then
              0xe2d186fb11e78c6ecad86e65d00000ccba6b61c637711e6c0df8f8b53caaa4ae57a9caa9f8b441bec479e31bb6b61999740000332edad8718ddc479b037a3e2d4f2ba92b95ea72aa7e2d006fb11e78c6edad86665d00004ccbb6b60c637f11e6c0de8f8b53caea4aa57abcaa8f8b481bec479e31bb6b61999700001332edad8b18dbc47bb037a3e254f2fa92895eaf2aa3e2d606fb11e78c6edad82665c00014ccb36b66c634f11fec0d68f8d53c9ea4b257a3caa8f8b581bfc479631bb6b6299960000d3328dadbb18d3c47fb035a3e154f37a92495ecf2aa3e2d606ff11e58c6cdad9a665000074cc836b6ec63cf11bec0d68f9553c5ea4d25793caa8f8bd81bbc47b631a36b6e99900001d3330dadbb18f3c46fb025a3e554f57a91495f4f2a
            else
              0xf606cf11dd8c70dadba660000174ccc36b6ec63cf11bec1168f955395ea7525753cad1f17d81b3c477631c36b2e99800005d33b0da9bb18f3c46fb0c5a3e554e57a9d49554f2b47c5f607cf11dd8c30dacba660000974cec3686ec63cf11bec7168f955295eaf525553cad1f17d81f3c437632c36b2e99000065d31b0db1bb18f3c06fb3c5a3e554257abd49554f2b47cdf603cf10dd8db0dacba600001974d6c36c6ec23cf01bedf1687955495eaf525553c2d1f0b47dbec079e21bb1b61b5974c000032e9ad86d8dd8479e037dbe2d0f2aa92bd5ea4aaa7a2d1e6fb01e78c6ec6d86c65d300004cba6b61a637611e7c0df4f8b53caaa4af57a90aa9f8b471bec479e31bb0b61b99748000332e9ad8618ddc479f037c3e2d4f2aa92bd5ea52aa7
          else
            if slot < 25 then
              0x6fb11e78c6edad86665d00000ccbb6b61c637711e6c0de8f8b53caea4ae57a9caa9f16881bec479e31bb6b61999740001332edad8318dfc479b037a3e2d4f2ba92a95eaf2aa7c5a206fb11e78c6edad86665c00004ccbb6b62c636f11eec0de8f8953cbea4a257abcaa9f16981bec479e31bb6b60999700005332cdad9b18d3c47fb035a3e354f27a92c95e8f2aa7c5a606ff11e58c6edad8a665800034cca36b6ec634f11fec0d68f8553cdea49257b3caa1f16d81bfc479631b36b6699940001d3320dadbb18f3c46fb035a3e554f17a93495e4f2ac7c5b606ef11ed8c68dadba664000074ccc36b6ec63cf11bec0968f9553d5ea45257d3ca91f17d81b3c47f631836b6e99900005d3330dadbb18f3c46fb005a3e554f57a95495d4f2b47c5
            else
              if slot < 26 then
                0xcf11dd8c70dacba660000174cec36a6ec63cf11bec3168f955395ea7525553cad1f1fb0373c477630c36b2e99800025d33b0da1bb18f3c46fb1c5a3e554a57abd49554f2b47c3ec0fcf10dd8cb0dacba640001974c6c36c6ec63cf01becf168f955095eaf525553cad1f2fb02f3c437636c36b2e98000065d35b0db1bb08f3c06fb7c5a1e555257abd49554f0b47dbec06fb01e7886ec6d86d65d300000cba6b61b637611e780df6f8b43caaa4af57a92aa9e168f9bec079e31bb1b61b1974c000132e9ad8698dd8479f037d3e2d4f2aa92bd5ea42aa7c5a3c6fb11e78c6ec2d86e65d20000ccba6b618637711e7c0df0f8b53caaa4af57a94aa9f168e1bec479e31bb2b61b99740000332e9ad8718ddc479b037e3e2d4f2aa92b95ea72aa7c5a3
              else
                0x11e78c6edad86665d00004ccbb6b60c637f11e6c0de8f8b53caea4aa57abcaa9f168037dc479e31bb6b61999700001332edad8b18dbc47bb037a3e254f2fa92895eaf2aa7c5a40df711e78c6edad82665c00014ccb36b66c634f11fec0d68f8d53c9ea4b257a3caa9f16b037dc479631bb6b6299960000d3328dadbb18d3c47fb035a3e154f37a92495ecf2a87c5ac0dff11e58c6cdad9a665000074cc836b6ec63cf11bec0d68f9553c5ea4d25793cab1f16b037bc47b631a36b6e99900001d3330dadbb18f3c46fb025a3e554f57a91495f4f2a47c5ec0dcf11fd8c60dadba664000174ccc36b6ec63cf11bec0168f9553d5ea5525753cad1f17b0373c477631c36b6e99800005d3330dadbb18f3c46fb045a3e554e57a9d495d4f2b47c5ec0d
      else
        if slot < 32 then
          if slot < 29 then
            if slot < 28 then
              0xdd8c30dacba660000974cec3686ec63cf11bec7168f955295eaf525553cad1f0fb03e788b7632c36b2e99000065d31b0db1bb18f3c06fb3c5a3e554257abd49554f2b47cbec0f9e20dd8db0dacba600001974d6c36c6ec23cf01bedf1687955495eaf525553c2d1f6fb01e78879e21bb1b61b5974c000032e9ad86d8dd8479e037dbe2d0f2aa92bd5ea4aaa785a3edf601e78c6ec6d86c65d300004cba6b61a637611e7c0df4f8b53caaa4af57a90aa9f168f37d8479e31bb0b61b99748000332e9ad8618ddc479f037c3e2d4f2aa92bd5ea52aa7c5a38df611e78c6ecad86e65d00000ccba6b61c637711e6c0df8f8b53caaa4ae57a9caa9f168c37d8479e31bb6b61999740000332edad8718ddc479b037a3e2d4f2ba92b95ea72aa7c5a20df6
            else
              0x8c6edad86665c00004ccbb6b62c636f11eec0de8f8953cbea4a257abcaa9f169037d88f3e31bb6b60999700005332cdad9b18d3c47fb035a3e354f27a92c95e8f2aa7c5ac0df623cd8c6edad8a665800034cca36b6ec634f11fec0d68f8553cdea49257b3caa1f16b037f88f3631b36b6699940001d3320dadbb18f3c46fb035a3e554f17a93495e4f2ac7c5ac0dfe23cd8c68dadba664000074ccc36b6ec63cf11bec0968f9553d5ea45257d3ca91f17b037788f7631836b6e99900005d3330dadbb18f3c46fb005a3e554f57a95495d4f2b47c5ec0d9e23dd8c70dadba660000174ccc36b6ec63cf11bec1168f955395ea7525753cad1f17b036788f7631c36b2e99800005d33b0da9bb18f3c46fb0c5a3e554e57a9d49554f2b47c7ec0d9e23
          else
            if slot < 30 then
              0xb0dacba640001974c6c36c6ec63cf01becf168f955095eaf525553cad1f2fb03e7886ec66c36b2e98000065d35b0db1bb08f3c06fb7c5a1e555257abd49554f0b47dbec079e21bb186ec6d86d65d300000cba6b61b637611e780df6f8b43caaa4af57a92aa9e168fb7d80f3c51bb1b61b1974c000132e9ad8698dd8479f037d3e2d4f2aa92bd5ea42aa7c5a3cdf603cf1c6ec2d86e65d20000ccba6b618637711e7c0df0f8b53caaa4af57a94aa9f168e37d88f3c31bb2b61b99740000332e9ad8718ddc479b037e3e2d4f2aa92b95ea72aa7c5a30df623cf0c6edad86665d00000ccbb6b61c637711e6c0de8f8b53caea4ae57a9caa9f168837d88f3c31bb6b61999740001332edad8318dfc479b037a3e2d4f2ba92a95eaf2aa7c5a00df623cf
            else
              if slot < 31 then
                0xdad82665c00014ccb36b66c634f11fec0d68f8d53c9ea4b257a3caa9f16b037d88f3c63736b6299960000d3328dadbb18d3c47fb035a3e154f37a92495ecf2a87c5ac0dfe23cb18dcdad9a665000074cc836b6ec63cf11bec0d68f9553c5ea4d25793cab1f16b037f88f2c63636b6e99900001d3330dadbb18f3c46fb025a3e554f57a91495f4f2a47c5ec0dde23db18d0dadba664000174ccc36b6ec63cf11bec0168f9553d5ea5525753cad1f17b036788fec63436b6e99800005d3330dadbb18f3c46fb045a3e554e57a9d495d4f2b47c5ec0d9e23bb18f0dacba660000174cec36a6ec63cf11bec3168f955395ea7525553cad1f1fb036788eec62c36b2e99800025d33b0da1bb18f3c46fb1c5a3e554a57abd49554f2b47c3ec0f9e23bb18
              else
                0xcba600001974d6c36c6ec23cf01bedf1687955495eaf525553c2d1f6fb01e7886ec6d86d361b5974c000032e9ad86d8dd8479e037dbe2d0f2aa92bd5ea4aaa785a3edf603cf10dd8ed86c65d300004cba6b61a637611e7c0df4f8b53caaa4af57a90aa9f168f37d80f3c63762b61b99748000332e9ad8618ddc479f037c3e2d4f2aa92bd5ea52aa7c5a38df623cf18dd8ad86e65d00000ccba6b61c637711e6c0df8f8b53caaa4ae57a9caa9f168c37d88f3c63766b61999740000332edad8718ddc479b037a3e2d4f2ba92b95ea72aa7c5a20df623cf18dd9ad86665d00004ccbb6b60c637f11e6c0de8f8b53caea4aa57abcaa9f168037d88f3c63776b61999700001332edad8b18dbc47bb037a3e254f2fa92895eaf2aa7c5a40df623cf18dd
        else
          if slot < 34 then
            if slot < 33 then
              0xa665800034cca36b6ec634f11fec0d68f8553cdea49257b3caa1f16b037f88f2c6376d6c699940001d3320dadbb18f3c46fb035a3e554f17a93495e4f2ac7c5ac0dfe23cb18d9b5b3a664000074ccc36b6ec63cf11bec0968f9553d5ea45257d3ca91f17b037788f6c6346d6ce99900005d3330dadbb18f3c46fb005a3e554f57a95495d4f2b47c5ec0d9e23fb18c1b5bba660000174ccc36b6ec63cf11bec1168f955395ea7525753cad1f17b036788eec6386d6ae99800005d33b0da9bb18f3c46fb0c5a3e554e57a9d49554f2b47c7ec0d9e23bb18e1b58ba660000974cec3686ec63cf11bec7168f955295eaf525553cad1f0fb03e788eec6186d72e99000065d31b0db1bb18f3c06fb3c5a3e554257abd49554f2b47cbec0f9e21bb1961b5
            else
              0x65d300000cba6b61b637611e780df6f8b43caaa4af57a92aa9e168fb7d80f3c437636c369974c000132e9ad8698dd8479f037d3e2d4f2aa92bd5ea42aa7c5a3cdf603cf18dd8db0da65d20000ccba6b618637711e7c0df0f8b53caaa4af57a94aa9f168e37d88f3c637616c3799740000332e9ad8718ddc479b037e3e2d4f2aa92b95ea72aa7c5a30df623cf18dd95b0d665d00000ccbb6b61c637711e6c0de8f8b53caea4ae57a9caa9f168837d88f3c6376d6c3199740001332edad8318dfc479b037a3e2d4f2ba92a95eaf2aa7c5a00df623cf18ddb5b0e665c00004ccbb6b62c636f11eec0de8f8953cbea4a257abcaa9f169037d88f3c6376d6c2999700005332cdad9b18d3c47fb035a3e354f27a92c95e8f2aa7c5ac0df623cf18ddb5b0
          else
            if slot < 35 then
              0x74cc836b6ec63cf11bec0d68f9553c5ea4d25793cab1f16b037f88f2c6366d6cd33280001d3330dadbb18f3c46fb025a3e554f57a91495f4f2a47c5ec0dde23db18d1b5b74cc8000174ccc36b6ec63cf11bec0168f9553d5ea5525753cad1f17b036788fec6306d6dd33200005d3330dadbb18f3c46fb045a3e554e57a9d495d4f2b47c5ec0d9e23bb18e1b5b74cc0000174cec36a6ec63cf11bec3168f955395ea7525553cad1f1fb036788eec6386d65d33000025d33b0da1bb18f3c46fb1c5a3e554a57abd49554f2b47c3ec0f9e23bb1861b5974cc0001974c6c36c6ec63cf01becf168f955095eaf525553cad1f2fb03e7886ec6586d65d32000065d35b0db1bb08f3c06fb7c5a1e555257abd49554f0b47dbec079e21bb1b61b5974c
            else
              if slot < 36 then
                0x4cba6b61a637611e7c0df4f8b53caaa4af57a90aa9f168f37d80f3c637636c3632e98000332e9ad8618ddc479f037c3e2d4f2aa92bd5ea52aa7c5a38df623cf18dd85b0dccba40000ccba6b61c637711e6c0df8f8b53caaa4ae57a9caa9f168c37d88f3c637656c3732e80000332edad8718ddc479b037a3e2d4f2ba92b95ea72aa7c5a20df623cf18ddb5b0cccba00004ccbb6b60c637f11e6c0de8f8b53caea4aa57abcaa9f168037d88f3c6376d6c3332e80001332edad8b18dbc47bb037a3e254f2fa92895eaf2aa7c5a40df623cf18ddb5b0cccb800014ccb36b66c634f11fec0d68f8d53c9ea4b257a3caa9f16b037d88f3c6376d6c1332e0000d3328dadbb18d3c47fb035a3e154f37a92495ecf2a87c5ac0dfe23cb18ddb5b14ccb
              else
                0x32e9ad86d8dd8479e037dbe2d0f2aa92bd5ea4aaa785a3edf603cf10dd8db0dacba6
  (x >>> ((i % 8) * 289)) &&& hadMask 289

private def hadRow580 (i : Nat) : Nat :=
  hadPaley2 290 hadCore580 i

private def hadRow584 (i : Nat) : Nat :=
  hadDouble 292 hadRow292 i

private def hadCore588 (i : Nat) : Nat := hadRot 587 0x26973980f56c2aee058c861af3770617bf986a1e6a96a93200a18584bb93ec9131417c2b9362bc17d7376c83622de5e7affb36a96a987a9e602179f1130a79ece5f88abc950fe63169a i

private def hadRow588 (i : Nat) : Nat :=
  hadPaley1 hadCore588 i

private def hadRow592 (i : Nat) : Nat :=
  hadDouble 296 hadRow296 i

private def hadMyU596 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 9 then
      if slot < 4 then
        if slot < 2 then
          if slot < 1 then
            0x10bbe8b6de2b526c60cbbae3186c1b7f42c41884ef4da2f4d8d14b1f571792a248df9c16b0c5566e63cd6d298f0c02fdab21330a3eef046690a7f9972775c91c2016de4d98647abea849a4a7174db3738a65a1a0be7a88d1a11fb7415724927a5d9b9c50ad1f077b14469c249f9c2b39129bd2ecdce624e8689f5c646561a6dea249f00a6f96b4fb2807c9ca6e63258d2633b29c
          else
            0x4db86c975280abcde576d6048a1253b1d5e37169f36cbe35851e0f22b630ea3193f52c8d2a25c69b31b4ca02f2fd9bb08549054e38f17bb82dec51b986525667e7c5cc2c0c037d83ab6d710f4e8dce32903d3ebf0a61a4a18fa07d3961463bde376f881582f175610f962f56c2e0cc457587b87b8a21ba8b5deb480e89a1bf0b943a2a5e3dd7d9d105d052fd1a465d556d587a00
        else
          if slot < 3 then
            0xb3d44fe88429ea5d435a2b10938974e3c36fc8e7d9f9ed159388588060ee15ceafc30d07aa4bf3c5e6390a7c562289c532a4536f29742bba5b36af354851e33d06542993439b51ab83dd62b8b9fae8128d2f29b221c83a9c5e0d3e17e38dd567d95289783ca1590b60e54dd8e0e8f6562af95ecf222393931c882b6527754393c3dbb6cd82e259117ecc8afe4199002aee7ab80f
          else
            0xedab29093d687c425dbc6a098eb4f266d68e01b559c414f061d7796c63604d66c621ff7d50ec71b3a01a71b3c436c3299056370dd29f9b5c663d9d20560d9e95ae090cc4dd982e36dedafa33fd6e829d30b04518341b9bf5c31859b527edcb71a44bf4a185086d94c8657bb28355c59f057b8f200f873a29e24826c5ba495e1aef35faf1944d24fc51c9471ac97001fb6a50f3e8
      else
        if slot < 6 then
          if slot < 5 then
            0xfe4a44f5e1ca01e346fa295dd4f6153d842855f600af8b2f5044be3ec9c2aae6b1ed0e21d2ebf4459f64724229a65d35936f3ca276384309965109389be688bf5c30871b914f3db26b2ef1f4882bd347d401be92e11c2de359d550e4dd8b1e014e1ebc8949fe85086f2a1bcaeea5177c1f5c8878a5e2464f6520cf3f434c5f3560abb9a52127e50b98b3959cc1295cdc85ded581
          else
            0x428614bf48963b4edfa8eab05377a984ca6d82883432e505daff317d2b668630ebf6760b06d6a5e6c1a812e6f198d6dedb1d066ec8cc241db08f363960173638deb67e52ec3b1a826530da7bae183ca08e6ab602afbfe118d9ac81b186e908f85af2425356dc1c5ad993cb5c64158fa73467429f92129677606adee84ecea520ce6bc9891e947844ebe0f941ab3e8cb0bf3cc129
        else
          if slot < 7 then
            0x14f07a452a6f9aaec71bc5c1c6eca9c1b426a653d2c5205d7e747519fa1f2c1e8e5704e11382f31e284ab3d5b3696ef07562b670b2650a9511a8f942719e8f3f4b750ba53db2895328e404684726a2de7e6f9c55782c30fd5cea1dc18b0ae95e50845fc8af34fdb0f1cba4724235168a4e28fc92c8a63d7e85f3c295b7e003a4d63e517387c013c77a83e73dd61ea49768d90491
          else
            if slot < 8 then
              0x3d06a047dbb1ef718a0cc1d0dabd1a7c21aba5f2f02531cec5cbc239a72f817c614961943f9f99a929867628ded06db5706fb00c0d0ce8f6fd3d014cb633658e9377a3c71ca824a8437613c1e286b1f4db3e5a152c4d2bf26315c31b5a9ecf54052ba4d876cbb1eae3729214481adb44cdfa22691d06cdb77c07579dd50026609fd327271113cdea7d51aaf0f270abb929b5044e
            else
              0xe2d428e766e9792493b50e7e490e588a37b8361699473b36cba39496a0bb7e2162c4579f4110e24ebb93a67f9425a4855f5789866c9eda00c3c652dacf19d9aa8d883ddf143321356fd0e34a2c6cbd16cbdc84435a0e7ec491527a3abc18d92b51edb45f742208d0bfb60d8631d774282e822e6faef1e951401786adaaae98962fdb45761147787786ba8b0a743f61645c04b5ee
    else
      if slot < 14 then
        if slot < 11 then
          if slot < 10 then
            0xc885bc1fb798ea06626519d2bb50f924d3e23d43cda8c91d4713b31b28069bdfbee900bd21ea03cdc70afa1e0399784cb87cbee70a65e10d284bf32e4eeb443861e252e4d7578a8aa74c3cc1c9ea3c3e5381f40b14552f5dcf62928cd3e254cf4561f29527a25a222d76f7739092c64f80537cb5a7d9403e4e5373192c69319d94e85c919cecdd2f652270915ed961a9898ebe45
          else
            0xac5ba3bf8ac44b51a405b7a8f897117898fa40b353f67f9a40ce0780ac6fca870661e999ea08ee2bc4ed414ab15f5152cfcdbd3c23e32248a1b5672f334461a97847877a74f950de89384117d96dbcd6a88943899b29cb87c4157e25e6410f6ee1fe6c02698c463cf686d29c95f097024b7b7547f3648c0cf3156370e792228fccbb129313beba1905746e822b5fea1df5127845
        else
          if slot < 12 then
            0xb4aafad9113a246e8a6f9ec9cc915d4f88078fd587634095e987523134d76f6d48c33d10562feaaca32137e09b0a9689bcbfb222697a08b279eded398c3d0c804ebe8d61d481730fd664d9e32f754814f326a083e67b563953847e2317cc73739a6027d2c1170fb358f8c2f0a1f588d76ec3cc62a4bcc6440c7c8bb7da05a197a8a1175f4fd3e41660b1457cf93267044fb22f50
          else
            if slot < 13 then
              0x9ddf4aa2af932c000bcc6479b40948fe467e74ec78550179196adc5e6b6bcdc55a4f101173a726ee2843c8cf40e3f2f35e8a2bc472a2a99e3eedb152bac43123069592f4504e2fd111fdd1fb6588d5c607a0d935a89f6680f338c8c4fd897364620e323db6cbafcc7d313e95a04096735dc06948f84af0ad5e3b15ff413a8e2922329bdecb4a67405e017bf358ad9209f8754991
            else
              0xe5d2824eb239259ed291ed3a4ae13e02a1be752de6927135c9052e9f9f61501f21d4972de2ccea244b8c9f10797a4e7b4ba17496902ced9667b92a5c40f8e077c36b9a51079cd067436da3394151a21fe12cff3b7cd6a8bd60c11a7062e7ca2477402f51ae71d479ce40edb140747b174ef520f8117a2573af2fca10c76b4861cbc76ac30849eac3e81aed1caf79e2712c494d1e
      else
        if slot < 16 then
          if slot < 15 then
            0xe8ed5a627a02a878dcb3a2023c96a8ecf5b59f4000d327d5154beee79f989fc4a40b67898cdd605f0d5e48430d5b9e2ca48d2391e7bd4e273a917a207c12bdcba0f4e184b5b8c214fd3d39d62bd00bb8914f9d378b80a36dc09ce78ae3fcd21fe1162a0a7315839620c1af455acfb70fb81c7c08e9527799adb0b982ce78229675b97a7823e4c748915cce6dcd025a4ba174b79c
          else
            0x312b865ea40b1b86afda822f30c4adbdbacb2945d89172226d7d54b478047caea24ce4de7d7a01e80b994b4def652264ab87e4126d46b3fad43d487c4a580eeb3b11251c5720bfea371e4db6f131c1189b3a46da40816a5f232f8cfd726c17818eac469b7e2fc8c4c733c059be456b8312308d752a36ddf1efe222fd1c828bd26a5f1c0bcc4f0851dd939665515388f5145eb3d3
        else
          if slot < 17 then
            0x781cc0967f9bf2b3415e665e1983854fd8d40962b488d47f71768d497c647a23a47c57b688a3419a09f2fcbeba202bd137c88399327cfa0898cf49518cf0ddbad457a616816fb744f8ca20d2f9019673b38cf846be143d0c7c6b37c3415933ca04abbd31e6e311f8872a71ab799f0c804c2f0c672dede79099afc33a04ae1ac5f5543641fb21314d55fd34417a591137f4f645a
          else
            if slot < 18 then
              0x6337238ae24c56cf0ae12f4025df7ef658053919815c67b7e0f6844f11f2c927c2b752e629d8ba826175f72325236887922bee15feb5105cc0c49b3f8abb7b49034cfc511279c3b1aa33c65900d9fe1ddbc209ba43ea4e52d85bcf18870a4455acf6da6fa209e91faa08f874e536647a56188b33d39ab61447245ec2a7cb97b8788bea354a0adc8f51dc409131f10f2f6cfcd2a2
            else
              0x1792a53e1a8bcca91f18d24273bbdbad111690be0729f0f15e4e0cf2cc5251bceebd2a8a3418708b5dc9d33f4852ccb954547abac9d291ea6701e17d438ecf015c21e99439df4f874c87
  (x >>> ((i % 8) * 148)) &&& hadMask 148

private def hadMyK596 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 9 then
      if slot < 4 then
        if slot < 2 then
          if slot < 1 then
            0x9ba717b0de8e5d942126e9c5ec37a397650044dd38bd86f472eca109374e2f61bd1cbb2802a6e9c5ec37a397650829ba717b0de8e5d94005374e2f61bd1cbb28414dd38bd86f472eca0029ba717b0de8e5d9420a6e9c5ec37a397650014dd38bd86f472eca105374e2f61bd1cbb2800a6e9c5ec37a397650829ba717b0de8e5d9400000000000000000004000000000000000000
          else
            0xa717b0de8e5d94214da9c5ec37a3976500536d38bd86f472eca10a6b4e2f61bd1cbb28029ae9c5ec37a3976508533a717b0de8e5d94014c74e2f61bd1cbb284299d38bd86f472eca00a6ba717b0de8e5d94214ae9c5ec37a397650052dd38bd86f472eca10a374e2f61bd1cbb280286e9c5ec37a397650851ba717b0de8e5d94014374e2f61bd1cbb28428dd38bd86f472eca00a
        else
          if slot < 3 then
            0x17b0de8e5d94214dd385ec37a39765005374e8bd86f472eca10a6e9a2f61bd1cbb28029ba6c5ec37a39765085374b17b0de8e5d94014dd2e2f61bd1cbb28429ba38bd86f472eca00a6e8717b0de8e5d94214dd1c5ec37a3976500537438bd86f472eca10a6e8e2f61bd1cbb28029ba9c5ec37a39765085372717b0de8e5d94014dc4e2f61bd1cbb28429b938bd86f472eca00a6e
          else
            0xb0de8e5d94214dd38bac37a39765005374e2ed86f472eca10a6e9c5b61bd1cbb28029ba716ec37a39765085374e2bb0de8e5d94014dd38af61bd1cbb28429ba713d86f472eca00a6e9c47b0de8e5d94214dd389ec37a39765005374e2bd86f472eca10a6e9c2f61bd1cbb28029ba705ec37a39765085374e17b0de8e5d94014dd382f61bd1cbb28429ba70bd86f472eca00a6e9c
      else
        if slot < 6 then
          if slot < 5 then
            0xde8e5d94214dd38bd837a39765005374e2f606f472eca10a6e9c5ec1bd1cbb28029ba717b037a39765085374e2f60de8e5d94014dd38bd81bd1cbb28429ba717b06f472eca00a6e9c5ec0de8e5d94214dd38bd837a39765005374e2f686f472eca10a6e9c5ea1bd1cbb28029ba717ac37a39765085374e2f30de8e5d94014dd38bc61bd1cbb28429ba717986f472eca00a6e9c5e
          else
            0x8e5d94214dd38bd86f239765005374e2f61bc472eca10a6e9c5ec3791cbb28029ba717b0dea39765085374e2f61ba8e5d94014dd38bd86ed1cbb28429ba717b0db472eca00a6e9c5ec36e8e5d94214dd38bd86ba39765005374e2f61af472eca10a6e9c5ec33d1cbb28029ba717b0c7a39765085374e2f619e8e5d94014dd38bd86bd1cbb28429ba717b0af472eca00a6e9c5ec2
        else
          if slot < 7 then
            0x5d94214dd38bd86f471765005374e2f61bd1c2eca10a6e9c5ec37a38bb28029ba717b0de8e9765085374e2f61bd1a5d94014dd38bd86f46cbb28429ba717b0de8b2eca00a6e9c5ec37a2e5d94214dd38bd86f439765005374e2f61bd072eca10a6e9c5ec37a1cbb28029ba717b0de839765085374e2f61bd0e5d94014dd38bd86f41cbb28429ba717b0de872eca00a6e9c5ec37a
          else
            if slot < 8 then
              0x94214dd38bd86f472ea5005374e2f61bd1cbaca10a6e9c5ec37a397328029ba717b0de8e5c65085374e2f61bd1cb994014dd38bd86f472eb28429ba717b0de8e5aca00a6e9c5ec37a396d94214dd38bd86f472b65005374e2f61bd1caeca10a6e9c5ec37a393b28029ba717b0de8e4765085374e2f61bd1c9d94014dd38bd86f472bb28429ba717b0de8e2eca00a6e9c5ec37a38
            else
              0x214dd38bd86f472eca005374e2f61bd1cbb2810a6e9c5ec37a397650029ba717b0de8e5d94085374e2f61bd1cbb28014dd38bd86f472eca8429ba717b0de8e5d9200a6e9c5ec37a397644214dd38bd86f472ec9005374e2f61bd1cbb2a10a6e9c5ec37a397628029ba717b0de8e5d85085374e2f61bd1cbb14014dd38bd86f472ec28429ba717b0de8e5d8a00a6e9c5ec37a3976
    else
      if slot < 14 then
        if slot < 11 then
          if slot < 10 then
            0x59163a13c85c689affe9ba717b0de8e5d9420ac8b1d09e42e344d7fd4dd38bd86f472eca10d6458e84f2171a26bfca6e9c5ec37a3976508eb22c742790b8d135fc5374e2f61bd1cbb284f59163a13c85c689afc29ba717b0de8e5d942ffffffffffffffffffc00000000000000000185374e2f61bd1cbb28014dd38bd86f472eca0429ba717b0de8e5d9400a6e9c5ec37a397650
          else
            0x163a13c85c689affacfa717b0de8e5d94214c8b1d09e42e344d7fd65d38bd86f472eca10a6458e84f2171a26bfeb6e9c5ec37a39765085222c742790b8d135ff5f74e2f61bd1cbb284289163a13c85c689affadba717b0de8e5d94214c8b1d09e42e344d7fd4dd38bd86f472eca10a6458e84f2171a26bfee6e9c5ec37a39765084b22c742790b8d135ff5374e2f61bd1cbb2842
        else
          if slot < 12 then
            0x3a13c85c689affac8b717b0de8e5d94214dd21d09e42e344d7fd645f8bd86f472eca10a6e88e84f2171a26bfeb22dc5ec37a39765085374c742790b8d135ff5914e2f61bd1cbb28429ba63a13c85c689affac8e717b0de8e5d94214dcb1d09e42e344d7fd64538bd86f472eca10a6e58e84f2171a26bfeb269c5ec37a39765085362c742790b8d135ff5974e2f61bd1cbb28429a
          else
            if slot < 13 then
              0x13c85c689affac8b1d7b0de8e5d94214dd38a09e42e344d7fd6458efd86f472eca10a6e9c484f2171a26bfeb22c75ec37a39765085374e242790b8d135ff59163ef61bd1cbb28429ba70a13c85c689affac8b1d7b0de8e5d94214dd38d09e42e344d7fd6458cbd86f472eca10a6e9ce84f2171a26bfeb22c45ec37a39765085374e742790b8d135ff591662f61bd1cbb28429ba6
            else
              0xc85c689affac8b1d09cde8e5d94214dd38bd8e42e344d7fd6458e84c6f472eca10a6e9c5ecf2171a26bfeb22c742437a39765085374e2f6790b8d135ff59163a161bd1cbb28429ba717a3c85c689affac8b1d0f0de8e5d94214dd38bc9e42e344d7fd6458e8586f472eca10a6e9c5e4f2171a26bfeb22c746c37a39765085374e2e2790b8d135ff59163a761bd1cbb28429ba716
      else
        if slot < 16 then
          if slot < 15 then
            0x5c689affac8b1d09e468e5d94214dd38bd86e2e344d7fd6458e84f27472eca10a6e9c5ec36171a26bfeb22c742797a39765085374e2f61a0b8d135ff59163a13cfd1cbb28429ba717b0c85c689affac8b1d09e5e8e5d94214dd38bd8642e344d7fd6458e84f6f472eca10a6e9c5ec22171a26bfeb22c7427f7a39765085374e2f6090b8d135ff59163a13dbd1cbb28429ba717b0
          else
            0x689affac8b1d09e42e65d94214dd38bd86f46344d7fd6458e84f21772eca10a6e9c5ec37a21a26bfeb22c742790bf9765085374e2f61bd08d135ff59163a13c85dcbb28429ba717b0de8c689affac8b1d09e42ce5d94214dd38bd86f4e344d7fd6458e84f21472eca10a6e9c5ec37a71a26bfeb22c742790e39765085374e2f61bcb8d135ff59163a13c851cbb28429ba717b0de
        else
          if slot < 17 then
            0x9affac8b1d09e42e34594214dd38bd86f472e4d7fd6458e84f2171a6ca10a6e9c5ec37a39626bfeb22c742790b8d765085374e2f61bd1ca135ff59163a13c85c6fb28429ba717b0de8e489affac8b1d09e42e35d94214dd38bd86f47244d7fd6458e84f2171eeca10a6e9c5ec37a38a26bfeb22c742790b8d765085374e2f61bd1cd135ff59163a13c85c4bb28429ba717b0de8e
          else
            if slot < 18 then
              0xffac8b1d09e42e344d4214dd38bd86f472eca7fd6458e84f2171a26e10a6e9c5ec37a39764bfeb22c742790b8d135085374e2f61bd1cbb25ff59163a13c85c689e8429ba717b0de8e5d8affac8b1d09e42e344d4214dd38bd86f472ecd7fd6458e84f2171a24a10a6e9c5ec37a39766bfeb22c742790b8d165085374e2f61bd1cba35ff59163a13c85c68f28429ba717b0de8e5c
            else
              0xfac8b1d09e42e344d7e14dd38bd86f472eca0fd6458e84f2171a26bd0a6e9c5ec37a397650feb22c742790b8d135c85374e2f61bd1cbb28ff59163a13c85c689ac429ba717b0de8e5d94
  (x >>> ((i % 8) * 148)) &&& hadMask 148

private def hadMyTop596 (i : Nat) : Nat :=
  let slot := i / 2
  let x :=
    if slot < 1 then
      0xfffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffdfffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffe
    else
      0xfffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000007ffffffffffffffffffffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  (x >>> ((i % 2) * 596)) &&& hadMask 596

private def hadRow596 (i : Nat) : Nat :=
  hadMiyamotoRow 149 21392 55217 hadMyTop596 hadMyU596
    hadRow148 hadMyK596 i

private def hadRow600 (i : Nat) : Nat :=
  hadDouble 300 hadRow300 i

private def hadRow604 (i : Nat) : Nat :=
  let r := i % 151
  if i < 151 then
    hadJoin4 151
      (hadCyclicCell 151 r 0x286ef42b834c99a7c57a113d7d65b8cb38965 53 1 0x0)
      (hadCyclicCell 151 r 0x10ef23c36270a494ed42e7c46eaf30a045023 134 150 0x0)
      (hadCyclicCell 151 r 0x3f464d293d73230965cab6e8a298cd32fe09 150 150 0x7fffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 151 r 0x3b9fafeaf678b0f461cd2893e057706a6f6b 92 150 0x0)
  else
  if i < 302 then
    hadJoin4 151
      (hadCyclicCell 151 r 0x10ef23c36270a494ed42e7c46eaf30a045023 134 150 0x7fffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 151 r 0x286ef42b834c99a7c57a113d7d65b8cb38965 53 1 0x0)
      (hadCyclicCell 151 r 0x35bd9583ba81f2452ce18bc3479bd5fd7e77 67 150 0x7fffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 151 r 0x241fd32cc65145db54e9a43133af252c98bf 9 150 0x7fffffffffffffffffffffffffffffffffffff)
  else
  if i < 453 then
    hadJoin4 151
      (hadCyclicCell 151 r 0x3f464d293d73230965cab6e8a298cd32fe09 150 150 0x0)
      (hadCyclicCell 151 r 0x35bd9583ba81f2452ce18bc3479bd5fd7e77 67 150 0x0)
      (hadCyclicCell 151 r 0x286ef42b834c99a7c57a113d7d65b8cb38965 53 1 0x0)
      (hadCyclicCell 151 r 0x1433d5d88f9d0adca494391b0f13dc2062051 148 150 0x7fffffffffffffffffffffffffffffffffffff)
  else
    hadJoin4 151
      (hadCyclicCell 151 r 0x3b9fafeaf678b0f461cd2893e057706a6f6b 92 150 0x7fffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 151 r 0x241fd32cc65145db54e9a43133af252c98bf 9 150 0x0)
      (hadCyclicCell 151 r 0x1433d5d88f9d0adca494391b0f13dc2062051 148 150 0x0)
      (hadCyclicCell 151 r 0x286ef42b834c99a7c57a113d7d65b8cb38965 53 1 0x0)

private def hadRow608 (i : Nat) : Nat :=
  hadDouble 304 hadRow304 i

private def hadRoute612 (i : Nat) : Nat :=
  let slot := i / 8
  let x :=
    if slot < 1 then
      0x7d0b7b173c2a3dcbc0f14c2a397826685c8c1b295047d7b1a3a15bf0cdd942fae62c6a8
    else
      0xab96748ba14afa85a545714ed1e0856efe2
  (x >>> ((i % 8) * 36)) &&& hadMask 36

private def hadRow612 (i : Nat) : Nat :=
  hadCwRow 3 51 0x7128c1983148e 0x7128c1983148f 0x37a2836c145ed 0x37a2836c145ed hadRoute612 i

private def hadRow616 (i : Nat) : Nat :=
  hadDouble 308 hadRow308 i

private def hadCore620 (i : Nat) : Nat := hadRot 619 0x30bf7414809ba99a7ebe3c3573696d3285527443a01ab58dc0b08738825cf0b66f999ca2819f8ae067ebac6660992f0c5bee31ef2fc4e52a7fa3dd1b55eb349693153c38281a66a26fed7d102f2 i

private def hadRow620 (i : Nat) : Nat :=
  hadPaley1 hadCore620 i

private def hadRow624 (i : Nat) : Nat :=
  hadDouble 312 hadRow312 i

private def hadCore628 (i : Nat) : Nat := hadRot 313 0x148d342c93dc567d7192a9fc189e0afdde91b1863625eefd41e460fe55263af9a8ef24d0b2c4a0 i

private def hadRow628 (i : Nat) : Nat :=
  hadPaley2 314 hadCore628 i

private def hadRow632 (i : Nat) : Nat :=
  hadDouble 316 hadRow316 i

private def hadCore636 (i : Nat) : Nat := hadRot 317 0xd239f85b411ea60836ea2a5188f4fe9fb964c5cce8c9a77e5fcbc4629515db04195e20b687e712c i

private def hadRow636 (i : Nat) : Nat :=
  hadPaley2 318 hadCore636 i

private def hadRow640 (i : Nat) : Nat :=
  hadDouble 320 hadRow320 i

private def hadCore644 (i : Nat) : Nat := hadRot 643 0x349e7c12945fa8b63ddf8914333e7587a44859552e38b88eb5a0a00390893ec533da9a3f983d89d9a646e43e603a6a4335c836ef63ffafa528ee2e38b5565edda1e518333d76e044392ea05d6b7c186d2 i

private def hadRow644 (i : Nat) : Nat :=
  hadPaley1 hadCore644 i

private def hadRow648 (i : Nat) : Nat :=
  hadDouble 324 hadRow324 i

private def hadRow652 (i : Nat) : Nat :=
  let r := i % 163
  if i < 163 then
    hadJoin4 163
      (hadCyclicCell 163 r 0x56233b95fe95358659bf071276e3e04cb3ca6ad 105 1 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x3d6f546659239195a2bc3930960450182e69beb 121 162 0x0)
      (hadCyclicCell 163 r 0x68c21eb3317dc36aa7972716bfb8072fad9470d 98 162 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x3a5531510f536ee021706c2df9d2d90e62944cb 103 162 0x7ffffffffffffffffffffffffffffffffffffffff)
  else
  if i < 326 then
    hadJoin4 163
      (hadCyclicCell 163 r 0x3d6f546659239195a2bc3930960450182e69beb 121 162 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x56233b95fe95358659bf071276e3e04cb3ca6ad 105 1 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x34c8a519c26d2e7ed0d83a101ddb2bc22a32a97 68 162 0x0)
      (hadCyclicCell 163 r 0x58714dafa700efeb47274f2ab61df4666bc218b 72 162 0x7ffffffffffffffffffffffffffffffffffffffff)
  else
  if i < 489 then
    hadJoin4 163
      (hadCyclicCell 163 r 0x68c21eb3317dc36aa7972716bfb8072fad9470d 98 162 0x0)
      (hadCyclicCell 163 r 0x34c8a519c26d2e7ed0d83a101ddb2bc22a32a97 68 162 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x56233b95fe95358659bf071276e3e04cb3ca6ad 105 1 0x7ffffffffffffffffffffffffffffffffffffffff)
      (hadCyclicCell 163 r 0x35f659d0602881a43270f516a627126998abdaf 50 162 0x7ffffffffffffffffffffffffffffffffffffffff)
  else
    hadJoin4 163
      (hadCyclicCell 163 r 0x3a5531510f536ee021706c2df9d2d90e62944cb 103 162 0x0)
      (hadCyclicCell 163 r 0x58714dafa700efeb47274f2ab61df4666bc218b 72 162 0x0)
      (hadCyclicCell 163 r 0x35f659d0602881a43270f516a627126998abdaf 50 162 0x0)
      (hadCyclicCell 163 r 0x56233b95fe95358659bf071276e3e04cb3ca6ad 105 1 0x7ffffffffffffffffffffffffffffffffffffffff)

private def hadRow656 (i : Nat) : Nat :=
  hadDouble 328 hadRow328 i

private def hadCore660 (i : Nat) : Nat := hadRot 659 0x23a026afb2d3260131a619b4e7c2ebb8f4ec6393e829208f47c40fa31770206a55ca475a92a12cb1023bf72cb7ab6a51dac55a9fbf1173a0fdc1d0efb6be83639c8d0e228bc18d2679a737f9b34b20a9bfa3a i

private def hadRow660 (i : Nat) : Nat :=
  hadPaley1 hadCore660 i

private def hadRow664 (i : Nat) : Nat :=
  hadDouble 332 hadRow332 i

private def hadRowByOrder (n i : Nat) : Nat :=
  if n < 4 then (if n = 2 then hadRow2 i else 0) else
  if n > 664 ∨ n % 4 ≠ 0 then 0 else
    let k := n / 4
    if k < 84 then
      if k < 42 then
        if k < 21 then
          if k < 11 then
            if k < 6 then
              if k < 3 then
                if k < 2 then
                  hadRow4 i
                else
                  hadRow8 i
              else
                if k < 4 then
                  hadRow12 i
                else
                  if k < 5 then
                    hadRow16 i
                  else
                    hadRow20 i
            else
              if k < 8 then
                if k < 7 then
                  hadRow24 i
                else
                  hadRow28 i
              else
                if k < 9 then
                  hadRow32 i
                else
                  if k < 10 then
                    hadRow36 i
                  else
                    hadRow40 i
          else
            if k < 16 then
              if k < 13 then
                if k < 12 then
                  hadRow44 i
                else
                  hadRow48 i
              else
                if k < 14 then
                  hadRow52 i
                else
                  if k < 15 then
                    hadRow56 i
                  else
                    hadRow60 i
            else
              if k < 18 then
                if k < 17 then
                  hadRow64 i
                else
                  hadRow68 i
              else
                if k < 19 then
                  hadRow72 i
                else
                  if k < 20 then
                    hadRow76 i
                  else
                    hadRow80 i
        else
          if k < 31 then
            if k < 26 then
              if k < 23 then
                if k < 22 then
                  hadRow84 i
                else
                  hadRow88 i
              else
                if k < 24 then
                  hadRow92 i
                else
                  if k < 25 then
                    hadRow96 i
                  else
                    hadRow100 i
            else
              if k < 28 then
                if k < 27 then
                  hadRow104 i
                else
                  hadRow108 i
              else
                if k < 29 then
                  hadRow112 i
                else
                  if k < 30 then
                    hadRow116 i
                  else
                    hadRow120 i
          else
            if k < 36 then
              if k < 33 then
                if k < 32 then
                  hadRow124 i
                else
                  hadRow128 i
              else
                if k < 34 then
                  hadRow132 i
                else
                  if k < 35 then
                    hadRow136 i
                  else
                    hadRow140 i
            else
              if k < 39 then
                if k < 37 then
                  hadRow144 i
                else
                  if k < 38 then
                    hadRow148 i
                  else
                    hadRow152 i
              else
                if k < 40 then
                  hadRow156 i
                else
                  if k < 41 then
                    hadRow160 i
                  else
                    hadRow164 i
      else
        if k < 63 then
          if k < 52 then
            if k < 47 then
              if k < 44 then
                if k < 43 then
                  hadRow168 i
                else
                  hadRow172 i
              else
                if k < 45 then
                  hadRow176 i
                else
                  if k < 46 then
                    hadRow180 i
                  else
                    hadRow184 i
            else
              if k < 49 then
                if k < 48 then
                  hadRow188 i
                else
                  hadRow192 i
              else
                if k < 50 then
                  hadRow196 i
                else
                  if k < 51 then
                    hadRow200 i
                  else
                    hadRow204 i
          else
            if k < 57 then
              if k < 54 then
                if k < 53 then
                  hadRow208 i
                else
                  hadRow212 i
              else
                if k < 55 then
                  hadRow216 i
                else
                  if k < 56 then
                    hadRow220 i
                  else
                    hadRow224 i
            else
              if k < 60 then
                if k < 58 then
                  hadRow228 i
                else
                  if k < 59 then
                    hadRow232 i
                  else
                    hadRow236 i
              else
                if k < 61 then
                  hadRow240 i
                else
                  if k < 62 then
                    hadRow244 i
                  else
                    hadRow248 i
        else
          if k < 73 then
            if k < 68 then
              if k < 65 then
                if k < 64 then
                  hadRow252 i
                else
                  hadRow256 i
              else
                if k < 66 then
                  hadRow260 i
                else
                  if k < 67 then
                    hadRow264 i
                  else
                    hadRow268 i
            else
              if k < 70 then
                if k < 69 then
                  hadRow272 i
                else
                  hadRow276 i
              else
                if k < 71 then
                  hadRow280 i
                else
                  if k < 72 then
                    hadRow284 i
                  else
                    hadRow288 i
          else
            if k < 78 then
              if k < 75 then
                if k < 74 then
                  hadRow292 i
                else
                  hadRow296 i
              else
                if k < 76 then
                  hadRow300 i
                else
                  if k < 77 then
                    hadRow304 i
                  else
                    hadRow308 i
            else
              if k < 81 then
                if k < 79 then
                  hadRow312 i
                else
                  if k < 80 then
                    hadRow316 i
                  else
                    hadRow320 i
              else
                if k < 82 then
                  hadRow324 i
                else
                  if k < 83 then
                    hadRow328 i
                  else
                    hadRow332 i
    else
      if k < 125 then
        if k < 104 then
          if k < 94 then
            if k < 89 then
              if k < 86 then
                if k < 85 then
                  hadRow336 i
                else
                  hadRow340 i
              else
                if k < 87 then
                  hadRow344 i
                else
                  if k < 88 then
                    hadRow348 i
                  else
                    hadRow352 i
            else
              if k < 91 then
                if k < 90 then
                  hadRow356 i
                else
                  hadRow360 i
              else
                if k < 92 then
                  hadRow364 i
                else
                  if k < 93 then
                    hadRow368 i
                  else
                    hadRow372 i
          else
            if k < 99 then
              if k < 96 then
                if k < 95 then
                  hadRow376 i
                else
                  hadRow380 i
              else
                if k < 97 then
                  hadRow384 i
                else
                  if k < 98 then
                    hadRow388 i
                  else
                    hadRow392 i
            else
              if k < 101 then
                if k < 100 then
                  hadRow396 i
                else
                  hadRow400 i
              else
                if k < 102 then
                  hadRow404 i
                else
                  if k < 103 then
                    hadRow408 i
                  else
                    hadRow412 i
        else
          if k < 114 then
            if k < 109 then
              if k < 106 then
                if k < 105 then
                  hadRow416 i
                else
                  hadRow420 i
              else
                if k < 107 then
                  hadRow424 i
                else
                  if k < 108 then
                    hadRow428 i
                  else
                    hadRow432 i
            else
              if k < 111 then
                if k < 110 then
                  hadRow436 i
                else
                  hadRow440 i
              else
                if k < 112 then
                  hadRow444 i
                else
                  if k < 113 then
                    hadRow448 i
                  else
                    hadRow452 i
          else
            if k < 119 then
              if k < 116 then
                if k < 115 then
                  hadRow456 i
                else
                  hadRow460 i
              else
                if k < 117 then
                  hadRow464 i
                else
                  if k < 118 then
                    hadRow468 i
                  else
                    hadRow472 i
            else
              if k < 122 then
                if k < 120 then
                  hadRow476 i
                else
                  if k < 121 then
                    hadRow480 i
                  else
                    hadRow484 i
              else
                if k < 123 then
                  hadRow488 i
                else
                  if k < 124 then
                    hadRow492 i
                  else
                    hadRow496 i
      else
        if k < 146 then
          if k < 135 then
            if k < 130 then
              if k < 127 then
                if k < 126 then
                  hadRow500 i
                else
                  hadRow504 i
              else
                if k < 128 then
                  hadRow508 i
                else
                  if k < 129 then
                    hadRow512 i
                  else
                    hadRow516 i
            else
              if k < 132 then
                if k < 131 then
                  hadRow520 i
                else
                  hadRow524 i
              else
                if k < 133 then
                  hadRow528 i
                else
                  if k < 134 then
                    hadRow532 i
                  else
                    hadRow536 i
          else
            if k < 140 then
              if k < 137 then
                if k < 136 then
                  hadRow540 i
                else
                  hadRow544 i
              else
                if k < 138 then
                  hadRow548 i
                else
                  if k < 139 then
                    hadRow552 i
                  else
                    hadRow556 i
            else
              if k < 143 then
                if k < 141 then
                  hadRow560 i
                else
                  if k < 142 then
                    hadRow564 i
                  else
                    hadRow568 i
              else
                if k < 144 then
                  hadRow572 i
                else
                  if k < 145 then
                    hadRow576 i
                  else
                    hadRow580 i
        else
          if k < 156 then
            if k < 151 then
              if k < 148 then
                if k < 147 then
                  hadRow584 i
                else
                  hadRow588 i
              else
                if k < 149 then
                  hadRow592 i
                else
                  if k < 150 then
                    hadRow596 i
                  else
                    hadRow600 i
            else
              if k < 153 then
                if k < 152 then
                  hadRow604 i
                else
                  hadRow608 i
              else
                if k < 154 then
                  hadRow612 i
                else
                  if k < 155 then
                    hadRow616 i
                  else
                    hadRow620 i
          else
            if k < 161 then
              if k < 158 then
                if k < 157 then
                  hadRow624 i
                else
                  hadRow628 i
              else
                if k < 159 then
                  hadRow632 i
                else
                  if k < 160 then
                    hadRow636 i
                  else
                    hadRow640 i
            else
              if k < 164 then
                if k < 162 then
                  hadRow644 i
                else
                  if k < 163 then
                    hadRow648 i
                  else
                    hadRow652 i
              else
                if k < 165 then
                  hadRow656 i
                else
                  if k < 166 then
                    hadRow660 i
                  else
                    hadRow664 i



private theorem fromColumns {n : ℕ} (h : ∃ M, Hadamard.IsHadamard' (n := n) M) :
    gramWitness n := by
  obtain ⟨M,he,hg⟩ := h
  refine ⟨M.transpose, fun i j => he j i, ?_⟩
  rw [Matrix.transpose_transpose, hg]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.natCast_apply, Matrix.one_apply, hij]



private def goodRow (n : ℕ) (row : ℕ → ℕ) (i : ℕ) : Bool :=
  let a := fastSpread (row i)
  (a &&& ((1024^n-1)/1023) == a) &&
    (List.range i).all (fun j => 2*((a ^^^ fastSpread (row j)) % 1023) == n)

private def RowRange (n : ℕ) (row : ℕ → ℕ) (l r : ℕ) : Prop := ∀ i, l ≤ i → i < r → goodRow n row i = true
private theorem viaCheck {n l r : ℕ} {row : ℕ → ℕ}
    (h : ((List.range (r-l)).all fun j => goodRow n row (l+j)) = true) : RowRange n row l r := by
  intro i hl hr
  have := List.all_eq_true.mp h (i-l) (List.mem_range.mpr (by omega))
  rwa [show l + (i-l) = i by omega] at this

private theorem viaSplit {n l m r : ℕ} {row : ℕ → ℕ} (ha : RowRange n row l m) (hb : RowRange n row m r) :
    RowRange n row l r := by
  intro i hl hr
  rcases lt_or_ge i m with h|h
  · exact ha i hl h
  · exact hb i h hr

private theorem viaRows (n : ℕ) (row : ℕ → ℕ) (hlen : n < 1023) (h : RowRange n row 0 n) : gramWitness n := by
  have hr (i : Fin n) := Bool.and_eq_true_iff.mp (h i.val (Nat.zero_le _) i.isLt)
  apply matrix_of_packed n (fun i => fastSpread (row i.val)) hlen
  · intro i
    exact beq_iff_eq.mp (hr i).1
  have lower (i j : Fin n) (h : j.val < i.val) :
      2*((fastSpread (row i.val) ^^^ fastSpread (row j.val)) % 1023) = n :=
    beq_iff_eq.mp (List.all_eq_true.mp (hr i).2 j.val (List.mem_range.mpr h))
  intro i j hne
  rcases lt_or_gt_of_ne hne with h|h
  · rw [Nat.xor_comm]; exact lower j i h
  · exact lower i j h


set_option maxRecDepth 16000 in
/- Each row interval is checked as a data declaration. Projecting its proof below
keeps the kernel checks in order when elaborating a large family of intervals. -/
private def c2_0 : PLift (RowRange 2 hadRow2 0 2) := ⟨viaCheck (by decide +kernel)⟩

private theorem g2 : gramWitness 2 := viaRows _ _ (by decide) c2_0.down

private theorem g4 : gramWitness 4 := gram_product (by decide) (by decide) g2 g2

private theorem g8 : gramWitness 8 := gram_product (by decide) (by decide) g2 g4

private theorem g12 : gramWitness 12 := fromColumns (PaleyHadamard.typeI 11 ((isPrimePow_nat_iff _).mpr ⟨11, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g16 : gramWitness 16 := gram_product (by decide) (by decide) g2 g8

private theorem g20 : gramWitness 20 := fromColumns (PaleyHadamard.typeI 19 ((isPrimePow_nat_iff _).mpr ⟨19, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g24 : gramWitness 24 := gram_product (by decide) (by decide) g2 g12

private theorem g28 : gramWitness 28 := fromColumns (PaleyHadamard.typeI 27 ((isPrimePow_nat_iff _).mpr ⟨3, 3, by norm_num, by decide, by decide⟩) (by decide))

private theorem g32 : gramWitness 32 := gram_product (by decide) (by decide) g2 g16

private theorem g36 : gramWitness 36 := fromColumns (PaleyHadamard.typeII 17 ((isPrimePow_nat_iff _).mpr ⟨17, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g40 : gramWitness 40 := gram_product (by decide) (by decide) g2 g20

private theorem g44 : gramWitness 44 := fromColumns (PaleyHadamard.typeI 43 ((isPrimePow_nat_iff _).mpr ⟨43, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g48 : gramWitness 48 := gram_product (by decide) (by decide) g2 g24

private theorem g52 : gramWitness 52 := fromColumns (PaleyHadamard.typeII 25 ((isPrimePow_nat_iff _).mpr ⟨5, 2, by norm_num, by decide, by decide⟩) (by decide))

private theorem g56 : gramWitness 56 := gram_product (by decide) (by decide) g2 g28

private theorem g60 : gramWitness 60 := fromColumns (PaleyHadamard.typeI 59 ((isPrimePow_nat_iff _).mpr ⟨59, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g64 : gramWitness 64 := gram_product (by decide) (by decide) g2 g32

private theorem g68 : gramWitness 68 := fromColumns (PaleyHadamard.typeI 67 ((isPrimePow_nat_iff _).mpr ⟨67, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g72 : gramWitness 72 := gram_product (by decide) (by decide) g2 g36

private theorem g76 : gramWitness 76 := fromColumns (PaleyHadamard.typeII 37 ((isPrimePow_nat_iff _).mpr ⟨37, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g80 : gramWitness 80 := gram_product (by decide) (by decide) g2 g40

private theorem g84 : gramWitness 84 := fromColumns (PaleyHadamard.typeI 83 ((isPrimePow_nat_iff _).mpr ⟨83, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g88 : gramWitness 88 := gram_product (by decide) (by decide) g2 g44

set_option maxRecDepth 16000 in
private def c92_0 : PLift (RowRange 92 hadRow92 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_8 : PLift (RowRange 92 hadRow92 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_16 : PLift (RowRange 92 hadRow92 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_24 : PLift (RowRange 92 hadRow92 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_32 : PLift (RowRange 92 hadRow92 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_40 : PLift (RowRange 92 hadRow92 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_48 : PLift (RowRange 92 hadRow92 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_56 : PLift (RowRange 92 hadRow92 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_64 : PLift (RowRange 92 hadRow92 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_72 : PLift (RowRange 92 hadRow92 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_80 : PLift (RowRange 92 hadRow92 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c92_88 : PLift (RowRange 92 hadRow92 88 92) := ⟨viaCheck (by decide +kernel)⟩

private theorem g92 : gramWitness 92 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit c92_0.down c92_8.down) (viaSplit c92_16.down c92_24.down)) (viaSplit (viaSplit c92_32.down c92_40.down) (viaSplit c92_48.down c92_56.down))) (viaSplit (viaSplit c92_64.down c92_72.down) (viaSplit c92_80.down c92_88.down)))

private theorem g96 : gramWitness 96 := gram_product (by decide) (by decide) g2 g48

private theorem g100 : gramWitness 100 := fromColumns (PaleyHadamard.typeII 49 ((isPrimePow_nat_iff _).mpr ⟨7, 2, by norm_num, by decide, by decide⟩) (by decide))

private theorem g104 : gramWitness 104 := gram_product (by decide) (by decide) g2 g52

private theorem g108 : gramWitness 108 := fromColumns (PaleyHadamard.typeI 107 ((isPrimePow_nat_iff _).mpr ⟨107, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g112 : gramWitness 112 := gram_product (by decide) (by decide) g2 g56

set_option maxRecDepth 16000 in
private def c116_0 : PLift (RowRange 116 hadRow116 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_8 : PLift (RowRange 116 hadRow116 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_16 : PLift (RowRange 116 hadRow116 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_24 : PLift (RowRange 116 hadRow116 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_32 : PLift (RowRange 116 hadRow116 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_40 : PLift (RowRange 116 hadRow116 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_48 : PLift (RowRange 116 hadRow116 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_56 : PLift (RowRange 116 hadRow116 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_64 : PLift (RowRange 116 hadRow116 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_72 : PLift (RowRange 116 hadRow116 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_80 : PLift (RowRange 116 hadRow116 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_88 : PLift (RowRange 116 hadRow116 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_96 : PLift (RowRange 116 hadRow116 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_104 : PLift (RowRange 116 hadRow116 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c116_112 : PLift (RowRange 116 hadRow116 112 116) := ⟨viaCheck (by decide +kernel)⟩

private theorem g116 : gramWitness 116 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit c116_0.down c116_8.down) (viaSplit c116_16.down c116_24.down)) (viaSplit (viaSplit c116_32.down c116_40.down) (viaSplit c116_48.down c116_56.down))) (viaSplit (viaSplit (viaSplit c116_64.down c116_72.down) (viaSplit c116_80.down c116_88.down)) (viaSplit (viaSplit c116_96.down c116_104.down) c116_112.down)))

private theorem g120 : gramWitness 120 := gram_product (by decide) (by decide) g2 g60

private theorem g124 : gramWitness 124 := fromColumns (PaleyHadamard.typeII 61 ((isPrimePow_nat_iff _).mpr ⟨61, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g128 : gramWitness 128 := gram_product (by decide) (by decide) g2 g64

private theorem g132 : gramWitness 132 := fromColumns (PaleyHadamard.typeI 131 ((isPrimePow_nat_iff _).mpr ⟨131, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g136 : gramWitness 136 := gram_product (by decide) (by decide) g2 g68

private theorem g140 : gramWitness 140 := fromColumns (PaleyHadamard.typeI 139 ((isPrimePow_nat_iff _).mpr ⟨139, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g144 : gramWitness 144 := gram_product (by decide) (by decide) g2 g72

private theorem g148 : gramWitness 148 := fromColumns (PaleyHadamard.typeII 73 ((isPrimePow_nat_iff _).mpr ⟨73, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g152 : gramWitness 152 := gram_product (by decide) (by decide) g2 g76

set_option maxRecDepth 16000 in
private def c156_0 : PLift (RowRange 156 hadRow156 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_8 : PLift (RowRange 156 hadRow156 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_16 : PLift (RowRange 156 hadRow156 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_24 : PLift (RowRange 156 hadRow156 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_32 : PLift (RowRange 156 hadRow156 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_40 : PLift (RowRange 156 hadRow156 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_48 : PLift (RowRange 156 hadRow156 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_56 : PLift (RowRange 156 hadRow156 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_64 : PLift (RowRange 156 hadRow156 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_72 : PLift (RowRange 156 hadRow156 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_80 : PLift (RowRange 156 hadRow156 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_88 : PLift (RowRange 156 hadRow156 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_96 : PLift (RowRange 156 hadRow156 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_104 : PLift (RowRange 156 hadRow156 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_112 : PLift (RowRange 156 hadRow156 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_120 : PLift (RowRange 156 hadRow156 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_128 : PLift (RowRange 156 hadRow156 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_136 : PLift (RowRange 156 hadRow156 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_144 : PLift (RowRange 156 hadRow156 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c156_152 : PLift (RowRange 156 hadRow156 152 156) := ⟨viaCheck (by decide +kernel)⟩

private theorem g156 : gramWitness 156 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c156_0.down c156_8.down) (viaSplit c156_16.down c156_24.down)) (viaSplit (viaSplit c156_32.down c156_40.down) (viaSplit c156_48.down c156_56.down))) (viaSplit (viaSplit (viaSplit c156_64.down c156_72.down) (viaSplit c156_80.down c156_88.down)) (viaSplit (viaSplit c156_96.down c156_104.down) (viaSplit c156_112.down c156_120.down)))) (viaSplit (viaSplit c156_128.down c156_136.down) (viaSplit c156_144.down c156_152.down)))

private theorem g160 : gramWitness 160 := gram_product (by decide) (by decide) g2 g80

private theorem g164 : gramWitness 164 := fromColumns (PaleyHadamard.typeI 163 ((isPrimePow_nat_iff _).mpr ⟨163, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g168 : gramWitness 168 := gram_product (by decide) (by decide) g2 g84

set_option maxRecDepth 16000 in
private def c172_0 : PLift (RowRange 172 hadRow172 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_8 : PLift (RowRange 172 hadRow172 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_16 : PLift (RowRange 172 hadRow172 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_24 : PLift (RowRange 172 hadRow172 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_32 : PLift (RowRange 172 hadRow172 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_40 : PLift (RowRange 172 hadRow172 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_48 : PLift (RowRange 172 hadRow172 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_56 : PLift (RowRange 172 hadRow172 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_64 : PLift (RowRange 172 hadRow172 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_72 : PLift (RowRange 172 hadRow172 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_80 : PLift (RowRange 172 hadRow172 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_88 : PLift (RowRange 172 hadRow172 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_96 : PLift (RowRange 172 hadRow172 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_104 : PLift (RowRange 172 hadRow172 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_112 : PLift (RowRange 172 hadRow172 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_120 : PLift (RowRange 172 hadRow172 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_128 : PLift (RowRange 172 hadRow172 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_136 : PLift (RowRange 172 hadRow172 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_144 : PLift (RowRange 172 hadRow172 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_152 : PLift (RowRange 172 hadRow172 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_160 : PLift (RowRange 172 hadRow172 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c172_168 : PLift (RowRange 172 hadRow172 168 172) := ⟨viaCheck (by decide +kernel)⟩

private theorem g172 : gramWitness 172 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c172_0.down c172_8.down) (viaSplit c172_16.down c172_24.down)) (viaSplit (viaSplit c172_32.down c172_40.down) (viaSplit c172_48.down c172_56.down))) (viaSplit (viaSplit (viaSplit c172_64.down c172_72.down) (viaSplit c172_80.down c172_88.down)) (viaSplit (viaSplit c172_96.down c172_104.down) (viaSplit c172_112.down c172_120.down)))) (viaSplit (viaSplit (viaSplit c172_128.down c172_136.down) (viaSplit c172_144.down c172_152.down)) (viaSplit c172_160.down c172_168.down)))

private theorem g176 : gramWitness 176 := gram_product (by decide) (by decide) g2 g88

private theorem g180 : gramWitness 180 := fromColumns (PaleyHadamard.typeI 179 ((isPrimePow_nat_iff _).mpr ⟨179, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g184 : gramWitness 184 := gram_product (by decide) (by decide) g2 g92

set_option maxRecDepth 16000 in
private def c188_0 : PLift (RowRange 188 hadRow188 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_8 : PLift (RowRange 188 hadRow188 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_16 : PLift (RowRange 188 hadRow188 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_24 : PLift (RowRange 188 hadRow188 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_32 : PLift (RowRange 188 hadRow188 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_40 : PLift (RowRange 188 hadRow188 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_48 : PLift (RowRange 188 hadRow188 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_56 : PLift (RowRange 188 hadRow188 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_64 : PLift (RowRange 188 hadRow188 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_72 : PLift (RowRange 188 hadRow188 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_80 : PLift (RowRange 188 hadRow188 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_88 : PLift (RowRange 188 hadRow188 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_96 : PLift (RowRange 188 hadRow188 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_104 : PLift (RowRange 188 hadRow188 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_112 : PLift (RowRange 188 hadRow188 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_120 : PLift (RowRange 188 hadRow188 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_128 : PLift (RowRange 188 hadRow188 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_136 : PLift (RowRange 188 hadRow188 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_144 : PLift (RowRange 188 hadRow188 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_152 : PLift (RowRange 188 hadRow188 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_160 : PLift (RowRange 188 hadRow188 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_168 : PLift (RowRange 188 hadRow188 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_176 : PLift (RowRange 188 hadRow188 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c188_184 : PLift (RowRange 188 hadRow188 184 188) := ⟨viaCheck (by decide +kernel)⟩

private theorem g188 : gramWitness 188 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c188_0.down c188_8.down) (viaSplit c188_16.down c188_24.down)) (viaSplit (viaSplit c188_32.down c188_40.down) (viaSplit c188_48.down c188_56.down))) (viaSplit (viaSplit (viaSplit c188_64.down c188_72.down) (viaSplit c188_80.down c188_88.down)) (viaSplit (viaSplit c188_96.down c188_104.down) (viaSplit c188_112.down c188_120.down)))) (viaSplit (viaSplit (viaSplit c188_128.down c188_136.down) (viaSplit c188_144.down c188_152.down)) (viaSplit (viaSplit c188_160.down c188_168.down) (viaSplit c188_176.down c188_184.down))))

private theorem g192 : gramWitness 192 := gram_product (by decide) (by decide) g2 g96

private theorem g196 : gramWitness 196 := fromColumns (PaleyHadamard.typeII 97 ((isPrimePow_nat_iff _).mpr ⟨97, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g200 : gramWitness 200 := gram_product (by decide) (by decide) g2 g100

private theorem g204 : gramWitness 204 := fromColumns (PaleyHadamard.typeII 101 ((isPrimePow_nat_iff _).mpr ⟨101, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g208 : gramWitness 208 := gram_product (by decide) (by decide) g2 g104

private theorem g212 : gramWitness 212 := fromColumns (PaleyHadamard.typeI 211 ((isPrimePow_nat_iff _).mpr ⟨211, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g216 : gramWitness 216 := gram_product (by decide) (by decide) g2 g108

private theorem g220 : gramWitness 220 := fromColumns (PaleyHadamard.typeII 109 ((isPrimePow_nat_iff _).mpr ⟨109, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g224 : gramWitness 224 := gram_product (by decide) (by decide) g2 g112

private theorem g228 : gramWitness 228 := fromColumns (PaleyHadamard.typeI 227 ((isPrimePow_nat_iff _).mpr ⟨227, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g232 : gramWitness 232 := gram_product (by decide) (by decide) g2 g116

set_option maxRecDepth 16000 in
private def c236_0 : PLift (RowRange 236 hadRow236 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_8 : PLift (RowRange 236 hadRow236 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_16 : PLift (RowRange 236 hadRow236 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_24 : PLift (RowRange 236 hadRow236 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_32 : PLift (RowRange 236 hadRow236 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_40 : PLift (RowRange 236 hadRow236 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_48 : PLift (RowRange 236 hadRow236 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_56 : PLift (RowRange 236 hadRow236 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_64 : PLift (RowRange 236 hadRow236 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_72 : PLift (RowRange 236 hadRow236 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_80 : PLift (RowRange 236 hadRow236 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_88 : PLift (RowRange 236 hadRow236 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_96 : PLift (RowRange 236 hadRow236 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_104 : PLift (RowRange 236 hadRow236 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_112 : PLift (RowRange 236 hadRow236 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_120 : PLift (RowRange 236 hadRow236 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_128 : PLift (RowRange 236 hadRow236 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_136 : PLift (RowRange 236 hadRow236 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_144 : PLift (RowRange 236 hadRow236 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_152 : PLift (RowRange 236 hadRow236 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_160 : PLift (RowRange 236 hadRow236 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_168 : PLift (RowRange 236 hadRow236 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_176 : PLift (RowRange 236 hadRow236 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_184 : PLift (RowRange 236 hadRow236 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_192 : PLift (RowRange 236 hadRow236 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_200 : PLift (RowRange 236 hadRow236 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_208 : PLift (RowRange 236 hadRow236 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_216 : PLift (RowRange 236 hadRow236 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_224 : PLift (RowRange 236 hadRow236 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c236_232 : PLift (RowRange 236 hadRow236 232 236) := ⟨viaCheck (by decide +kernel)⟩

private theorem g236 : gramWitness 236 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c236_0.down c236_8.down) (viaSplit c236_16.down c236_24.down)) (viaSplit (viaSplit c236_32.down c236_40.down) (viaSplit c236_48.down c236_56.down))) (viaSplit (viaSplit (viaSplit c236_64.down c236_72.down) (viaSplit c236_80.down c236_88.down)) (viaSplit (viaSplit c236_96.down c236_104.down) (viaSplit c236_112.down c236_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c236_128.down c236_136.down) (viaSplit c236_144.down c236_152.down)) (viaSplit (viaSplit c236_160.down c236_168.down) (viaSplit c236_176.down c236_184.down))) (viaSplit (viaSplit (viaSplit c236_192.down c236_200.down) (viaSplit c236_208.down c236_216.down)) (viaSplit c236_224.down c236_232.down))))

private theorem g240 : gramWitness 240 := gram_product (by decide) (by decide) g2 g120

private theorem g244 : gramWitness 244 := fromColumns (PaleyHadamard.typeI 243 ((isPrimePow_nat_iff _).mpr ⟨3, 5, by norm_num, by decide, by decide⟩) (by decide))

private theorem g248 : gramWitness 248 := gram_product (by decide) (by decide) g2 g124

private theorem g252 : gramWitness 252 := fromColumns (PaleyHadamard.typeI 251 ((isPrimePow_nat_iff _).mpr ⟨251, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g256 : gramWitness 256 := gram_product (by decide) (by decide) g2 g128

set_option maxRecDepth 16000 in
private def c260_0 : PLift (RowRange 260 hadRow260 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_8 : PLift (RowRange 260 hadRow260 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_16 : PLift (RowRange 260 hadRow260 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_24 : PLift (RowRange 260 hadRow260 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_32 : PLift (RowRange 260 hadRow260 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_40 : PLift (RowRange 260 hadRow260 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_48 : PLift (RowRange 260 hadRow260 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_56 : PLift (RowRange 260 hadRow260 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_64 : PLift (RowRange 260 hadRow260 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_72 : PLift (RowRange 260 hadRow260 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_80 : PLift (RowRange 260 hadRow260 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_88 : PLift (RowRange 260 hadRow260 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_96 : PLift (RowRange 260 hadRow260 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_104 : PLift (RowRange 260 hadRow260 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_112 : PLift (RowRange 260 hadRow260 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_120 : PLift (RowRange 260 hadRow260 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_128 : PLift (RowRange 260 hadRow260 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_136 : PLift (RowRange 260 hadRow260 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_144 : PLift (RowRange 260 hadRow260 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_152 : PLift (RowRange 260 hadRow260 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_160 : PLift (RowRange 260 hadRow260 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_168 : PLift (RowRange 260 hadRow260 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_176 : PLift (RowRange 260 hadRow260 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_184 : PLift (RowRange 260 hadRow260 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_192 : PLift (RowRange 260 hadRow260 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_200 : PLift (RowRange 260 hadRow260 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_208 : PLift (RowRange 260 hadRow260 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_216 : PLift (RowRange 260 hadRow260 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_224 : PLift (RowRange 260 hadRow260 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_232 : PLift (RowRange 260 hadRow260 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_240 : PLift (RowRange 260 hadRow260 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_248 : PLift (RowRange 260 hadRow260 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c260_256 : PLift (RowRange 260 hadRow260 256 260) := ⟨viaCheck (by decide +kernel)⟩

private theorem g260 : gramWitness 260 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c260_0.down c260_8.down) (viaSplit c260_16.down c260_24.down)) (viaSplit (viaSplit c260_32.down c260_40.down) (viaSplit c260_48.down c260_56.down))) (viaSplit (viaSplit (viaSplit c260_64.down c260_72.down) (viaSplit c260_80.down c260_88.down)) (viaSplit (viaSplit c260_96.down c260_104.down) (viaSplit c260_112.down c260_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c260_128.down c260_136.down) (viaSplit c260_144.down c260_152.down)) (viaSplit (viaSplit c260_160.down c260_168.down) (viaSplit c260_176.down c260_184.down))) (viaSplit (viaSplit (viaSplit c260_192.down c260_200.down) (viaSplit c260_208.down c260_216.down)) (viaSplit (viaSplit c260_224.down c260_232.down) (viaSplit c260_240.down c260_248.down))))) c260_256.down)

private theorem g264 : gramWitness 264 := gram_product (by decide) (by decide) g2 g132

set_option maxRecDepth 16000 in
private def c268_0 : PLift (RowRange 268 hadRow268 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_8 : PLift (RowRange 268 hadRow268 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_16 : PLift (RowRange 268 hadRow268 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_24 : PLift (RowRange 268 hadRow268 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_32 : PLift (RowRange 268 hadRow268 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_40 : PLift (RowRange 268 hadRow268 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_48 : PLift (RowRange 268 hadRow268 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_56 : PLift (RowRange 268 hadRow268 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_64 : PLift (RowRange 268 hadRow268 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_72 : PLift (RowRange 268 hadRow268 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_80 : PLift (RowRange 268 hadRow268 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_88 : PLift (RowRange 268 hadRow268 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_96 : PLift (RowRange 268 hadRow268 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_104 : PLift (RowRange 268 hadRow268 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_112 : PLift (RowRange 268 hadRow268 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_120 : PLift (RowRange 268 hadRow268 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_128 : PLift (RowRange 268 hadRow268 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_136 : PLift (RowRange 268 hadRow268 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_144 : PLift (RowRange 268 hadRow268 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_152 : PLift (RowRange 268 hadRow268 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_160 : PLift (RowRange 268 hadRow268 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_168 : PLift (RowRange 268 hadRow268 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_176 : PLift (RowRange 268 hadRow268 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_184 : PLift (RowRange 268 hadRow268 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_192 : PLift (RowRange 268 hadRow268 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_200 : PLift (RowRange 268 hadRow268 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_208 : PLift (RowRange 268 hadRow268 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_216 : PLift (RowRange 268 hadRow268 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_224 : PLift (RowRange 268 hadRow268 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_232 : PLift (RowRange 268 hadRow268 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_240 : PLift (RowRange 268 hadRow268 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_248 : PLift (RowRange 268 hadRow268 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_256 : PLift (RowRange 268 hadRow268 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c268_264 : PLift (RowRange 268 hadRow268 264 268) := ⟨viaCheck (by decide +kernel)⟩

private theorem g268 : gramWitness 268 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c268_0.down c268_8.down) (viaSplit c268_16.down c268_24.down)) (viaSplit (viaSplit c268_32.down c268_40.down) (viaSplit c268_48.down c268_56.down))) (viaSplit (viaSplit (viaSplit c268_64.down c268_72.down) (viaSplit c268_80.down c268_88.down)) (viaSplit (viaSplit c268_96.down c268_104.down) (viaSplit c268_112.down c268_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c268_128.down c268_136.down) (viaSplit c268_144.down c268_152.down)) (viaSplit (viaSplit c268_160.down c268_168.down) (viaSplit c268_176.down c268_184.down))) (viaSplit (viaSplit (viaSplit c268_192.down c268_200.down) (viaSplit c268_208.down c268_216.down)) (viaSplit (viaSplit c268_224.down c268_232.down) (viaSplit c268_240.down c268_248.down))))) (viaSplit c268_256.down c268_264.down))

private theorem g272 : gramWitness 272 := gram_product (by decide) (by decide) g2 g136

private theorem g276 : gramWitness 276 := fromColumns (PaleyHadamard.typeII 137 ((isPrimePow_nat_iff _).mpr ⟨137, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g280 : gramWitness 280 := gram_product (by decide) (by decide) g2 g140

private theorem g284 : gramWitness 284 := fromColumns (PaleyHadamard.typeI 283 ((isPrimePow_nat_iff _).mpr ⟨283, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g288 : gramWitness 288 := gram_product (by decide) (by decide) g2 g144

set_option maxRecDepth 16000 in
private def c292_0 : PLift (RowRange 292 hadRow292 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_8 : PLift (RowRange 292 hadRow292 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_16 : PLift (RowRange 292 hadRow292 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_24 : PLift (RowRange 292 hadRow292 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_32 : PLift (RowRange 292 hadRow292 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_40 : PLift (RowRange 292 hadRow292 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_48 : PLift (RowRange 292 hadRow292 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_56 : PLift (RowRange 292 hadRow292 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_64 : PLift (RowRange 292 hadRow292 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_72 : PLift (RowRange 292 hadRow292 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_80 : PLift (RowRange 292 hadRow292 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_88 : PLift (RowRange 292 hadRow292 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_96 : PLift (RowRange 292 hadRow292 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_104 : PLift (RowRange 292 hadRow292 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_112 : PLift (RowRange 292 hadRow292 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_120 : PLift (RowRange 292 hadRow292 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_128 : PLift (RowRange 292 hadRow292 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_136 : PLift (RowRange 292 hadRow292 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_144 : PLift (RowRange 292 hadRow292 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_152 : PLift (RowRange 292 hadRow292 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_160 : PLift (RowRange 292 hadRow292 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_168 : PLift (RowRange 292 hadRow292 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_176 : PLift (RowRange 292 hadRow292 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_184 : PLift (RowRange 292 hadRow292 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_192 : PLift (RowRange 292 hadRow292 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_200 : PLift (RowRange 292 hadRow292 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_208 : PLift (RowRange 292 hadRow292 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_216 : PLift (RowRange 292 hadRow292 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_224 : PLift (RowRange 292 hadRow292 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_232 : PLift (RowRange 292 hadRow292 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_240 : PLift (RowRange 292 hadRow292 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_248 : PLift (RowRange 292 hadRow292 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_256 : PLift (RowRange 292 hadRow292 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_264 : PLift (RowRange 292 hadRow292 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_272 : PLift (RowRange 292 hadRow292 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_280 : PLift (RowRange 292 hadRow292 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c292_288 : PLift (RowRange 292 hadRow292 288 292) := ⟨viaCheck (by decide +kernel)⟩

private theorem g292 : gramWitness 292 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c292_0.down c292_8.down) (viaSplit c292_16.down c292_24.down)) (viaSplit (viaSplit c292_32.down c292_40.down) (viaSplit c292_48.down c292_56.down))) (viaSplit (viaSplit (viaSplit c292_64.down c292_72.down) (viaSplit c292_80.down c292_88.down)) (viaSplit (viaSplit c292_96.down c292_104.down) (viaSplit c292_112.down c292_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c292_128.down c292_136.down) (viaSplit c292_144.down c292_152.down)) (viaSplit (viaSplit c292_160.down c292_168.down) (viaSplit c292_176.down c292_184.down))) (viaSplit (viaSplit (viaSplit c292_192.down c292_200.down) (viaSplit c292_208.down c292_216.down)) (viaSplit (viaSplit c292_224.down c292_232.down) (viaSplit c292_240.down c292_248.down))))) (viaSplit (viaSplit (viaSplit c292_256.down c292_264.down) (viaSplit c292_272.down c292_280.down)) c292_288.down))

private theorem g296 : gramWitness 296 := gram_product (by decide) (by decide) g2 g148

private theorem g300 : gramWitness 300 := fromColumns (PaleyHadamard.typeII 149 ((isPrimePow_nat_iff _).mpr ⟨149, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g304 : gramWitness 304 := gram_product (by decide) (by decide) g2 g152

private theorem g308 : gramWitness 308 := fromColumns (PaleyHadamard.typeI 307 ((isPrimePow_nat_iff _).mpr ⟨307, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g312 : gramWitness 312 := gram_product (by decide) (by decide) g2 g156

private theorem g316 : gramWitness 316 := fromColumns (PaleyHadamard.typeII 157 ((isPrimePow_nat_iff _).mpr ⟨157, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g320 : gramWitness 320 := gram_product (by decide) (by decide) g2 g160

set_option maxRecDepth 16000 in
private def c324_0 : PLift (RowRange 324 hadRow324 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_8 : PLift (RowRange 324 hadRow324 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_16 : PLift (RowRange 324 hadRow324 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_24 : PLift (RowRange 324 hadRow324 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_32 : PLift (RowRange 324 hadRow324 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_40 : PLift (RowRange 324 hadRow324 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_48 : PLift (RowRange 324 hadRow324 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_56 : PLift (RowRange 324 hadRow324 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_64 : PLift (RowRange 324 hadRow324 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_72 : PLift (RowRange 324 hadRow324 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_80 : PLift (RowRange 324 hadRow324 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_88 : PLift (RowRange 324 hadRow324 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_96 : PLift (RowRange 324 hadRow324 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_104 : PLift (RowRange 324 hadRow324 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_112 : PLift (RowRange 324 hadRow324 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_120 : PLift (RowRange 324 hadRow324 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_128 : PLift (RowRange 324 hadRow324 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_136 : PLift (RowRange 324 hadRow324 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_144 : PLift (RowRange 324 hadRow324 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_152 : PLift (RowRange 324 hadRow324 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_160 : PLift (RowRange 324 hadRow324 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_168 : PLift (RowRange 324 hadRow324 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_176 : PLift (RowRange 324 hadRow324 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_184 : PLift (RowRange 324 hadRow324 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_192 : PLift (RowRange 324 hadRow324 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_200 : PLift (RowRange 324 hadRow324 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_208 : PLift (RowRange 324 hadRow324 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_216 : PLift (RowRange 324 hadRow324 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_224 : PLift (RowRange 324 hadRow324 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_232 : PLift (RowRange 324 hadRow324 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_240 : PLift (RowRange 324 hadRow324 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_248 : PLift (RowRange 324 hadRow324 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_256 : PLift (RowRange 324 hadRow324 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_264 : PLift (RowRange 324 hadRow324 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_272 : PLift (RowRange 324 hadRow324 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_280 : PLift (RowRange 324 hadRow324 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_288 : PLift (RowRange 324 hadRow324 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_296 : PLift (RowRange 324 hadRow324 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_304 : PLift (RowRange 324 hadRow324 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_312 : PLift (RowRange 324 hadRow324 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c324_320 : PLift (RowRange 324 hadRow324 320 324) := ⟨viaCheck (by decide +kernel)⟩

private theorem g324 : gramWitness 324 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c324_0.down c324_8.down) (viaSplit c324_16.down c324_24.down)) (viaSplit (viaSplit c324_32.down c324_40.down) (viaSplit c324_48.down c324_56.down))) (viaSplit (viaSplit (viaSplit c324_64.down c324_72.down) (viaSplit c324_80.down c324_88.down)) (viaSplit (viaSplit c324_96.down c324_104.down) (viaSplit c324_112.down c324_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c324_128.down c324_136.down) (viaSplit c324_144.down c324_152.down)) (viaSplit (viaSplit c324_160.down c324_168.down) (viaSplit c324_176.down c324_184.down))) (viaSplit (viaSplit (viaSplit c324_192.down c324_200.down) (viaSplit c324_208.down c324_216.down)) (viaSplit (viaSplit c324_224.down c324_232.down) (viaSplit c324_240.down c324_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit c324_256.down c324_264.down) (viaSplit c324_272.down c324_280.down)) (viaSplit (viaSplit c324_288.down c324_296.down) (viaSplit c324_304.down c324_312.down))) c324_320.down))

private theorem g328 : gramWitness 328 := gram_product (by decide) (by decide) g2 g164

private theorem g332 : gramWitness 332 := fromColumns (PaleyHadamard.typeI 331 ((isPrimePow_nat_iff _).mpr ⟨331, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g336 : gramWitness 336 := gram_product (by decide) (by decide) g2 g168

private theorem g340 : gramWitness 340 := fromColumns (PaleyHadamard.typeII 169 ((isPrimePow_nat_iff _).mpr ⟨13, 2, by norm_num, by decide, by decide⟩) (by decide))

private theorem g344 : gramWitness 344 := gram_product (by decide) (by decide) g2 g172

private theorem g348 : gramWitness 348 := fromColumns (PaleyHadamard.typeI 347 ((isPrimePow_nat_iff _).mpr ⟨347, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g352 : gramWitness 352 := gram_product (by decide) (by decide) g2 g176

set_option maxRecDepth 16000 in
private def c356_0 : PLift (RowRange 356 hadRow356 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_8 : PLift (RowRange 356 hadRow356 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_16 : PLift (RowRange 356 hadRow356 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_24 : PLift (RowRange 356 hadRow356 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_32 : PLift (RowRange 356 hadRow356 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_40 : PLift (RowRange 356 hadRow356 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_48 : PLift (RowRange 356 hadRow356 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_56 : PLift (RowRange 356 hadRow356 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_64 : PLift (RowRange 356 hadRow356 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_72 : PLift (RowRange 356 hadRow356 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_80 : PLift (RowRange 356 hadRow356 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_88 : PLift (RowRange 356 hadRow356 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_96 : PLift (RowRange 356 hadRow356 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_104 : PLift (RowRange 356 hadRow356 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_112 : PLift (RowRange 356 hadRow356 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_120 : PLift (RowRange 356 hadRow356 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_128 : PLift (RowRange 356 hadRow356 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_136 : PLift (RowRange 356 hadRow356 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_144 : PLift (RowRange 356 hadRow356 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_152 : PLift (RowRange 356 hadRow356 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_160 : PLift (RowRange 356 hadRow356 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_168 : PLift (RowRange 356 hadRow356 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_176 : PLift (RowRange 356 hadRow356 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_184 : PLift (RowRange 356 hadRow356 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_192 : PLift (RowRange 356 hadRow356 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_200 : PLift (RowRange 356 hadRow356 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_208 : PLift (RowRange 356 hadRow356 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_216 : PLift (RowRange 356 hadRow356 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_224 : PLift (RowRange 356 hadRow356 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_232 : PLift (RowRange 356 hadRow356 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_240 : PLift (RowRange 356 hadRow356 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_248 : PLift (RowRange 356 hadRow356 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_256 : PLift (RowRange 356 hadRow356 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_264 : PLift (RowRange 356 hadRow356 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_272 : PLift (RowRange 356 hadRow356 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_280 : PLift (RowRange 356 hadRow356 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_288 : PLift (RowRange 356 hadRow356 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_296 : PLift (RowRange 356 hadRow356 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_304 : PLift (RowRange 356 hadRow356 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_312 : PLift (RowRange 356 hadRow356 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_320 : PLift (RowRange 356 hadRow356 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_328 : PLift (RowRange 356 hadRow356 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_336 : PLift (RowRange 356 hadRow356 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_344 : PLift (RowRange 356 hadRow356 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c356_352 : PLift (RowRange 356 hadRow356 352 356) := ⟨viaCheck (by decide +kernel)⟩

private theorem g356 : gramWitness 356 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c356_0.down c356_8.down) (viaSplit c356_16.down c356_24.down)) (viaSplit (viaSplit c356_32.down c356_40.down) (viaSplit c356_48.down c356_56.down))) (viaSplit (viaSplit (viaSplit c356_64.down c356_72.down) (viaSplit c356_80.down c356_88.down)) (viaSplit (viaSplit c356_96.down c356_104.down) (viaSplit c356_112.down c356_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c356_128.down c356_136.down) (viaSplit c356_144.down c356_152.down)) (viaSplit (viaSplit c356_160.down c356_168.down) (viaSplit c356_176.down c356_184.down))) (viaSplit (viaSplit (viaSplit c356_192.down c356_200.down) (viaSplit c356_208.down c356_216.down)) (viaSplit (viaSplit c356_224.down c356_232.down) (viaSplit c356_240.down c356_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit c356_256.down c356_264.down) (viaSplit c356_272.down c356_280.down)) (viaSplit (viaSplit c356_288.down c356_296.down) (viaSplit c356_304.down c356_312.down))) (viaSplit (viaSplit (viaSplit c356_320.down c356_328.down) (viaSplit c356_336.down c356_344.down)) c356_352.down)))

private theorem g360 : gramWitness 360 := gram_product (by decide) (by decide) g2 g180

private theorem g364 : gramWitness 364 := fromColumns (PaleyHadamard.typeII 181 ((isPrimePow_nat_iff _).mpr ⟨181, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g368 : gramWitness 368 := gram_product (by decide) (by decide) g2 g184

set_option maxRecDepth 16000 in
private def c372_0 : PLift (RowRange 372 hadRow372 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_8 : PLift (RowRange 372 hadRow372 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_16 : PLift (RowRange 372 hadRow372 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_24 : PLift (RowRange 372 hadRow372 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_32 : PLift (RowRange 372 hadRow372 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_40 : PLift (RowRange 372 hadRow372 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_48 : PLift (RowRange 372 hadRow372 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_56 : PLift (RowRange 372 hadRow372 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_64 : PLift (RowRange 372 hadRow372 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_72 : PLift (RowRange 372 hadRow372 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_80 : PLift (RowRange 372 hadRow372 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_88 : PLift (RowRange 372 hadRow372 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_96 : PLift (RowRange 372 hadRow372 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_104 : PLift (RowRange 372 hadRow372 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_112 : PLift (RowRange 372 hadRow372 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_120 : PLift (RowRange 372 hadRow372 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_128 : PLift (RowRange 372 hadRow372 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_136 : PLift (RowRange 372 hadRow372 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_144 : PLift (RowRange 372 hadRow372 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_152 : PLift (RowRange 372 hadRow372 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_160 : PLift (RowRange 372 hadRow372 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_168 : PLift (RowRange 372 hadRow372 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_176 : PLift (RowRange 372 hadRow372 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_184 : PLift (RowRange 372 hadRow372 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_192 : PLift (RowRange 372 hadRow372 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_200 : PLift (RowRange 372 hadRow372 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_208 : PLift (RowRange 372 hadRow372 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_216 : PLift (RowRange 372 hadRow372 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_224 : PLift (RowRange 372 hadRow372 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_232 : PLift (RowRange 372 hadRow372 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_240 : PLift (RowRange 372 hadRow372 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_248 : PLift (RowRange 372 hadRow372 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_256 : PLift (RowRange 372 hadRow372 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_264 : PLift (RowRange 372 hadRow372 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_272 : PLift (RowRange 372 hadRow372 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_280 : PLift (RowRange 372 hadRow372 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_288 : PLift (RowRange 372 hadRow372 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_296 : PLift (RowRange 372 hadRow372 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_304 : PLift (RowRange 372 hadRow372 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_312 : PLift (RowRange 372 hadRow372 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_320 : PLift (RowRange 372 hadRow372 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_328 : PLift (RowRange 372 hadRow372 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_336 : PLift (RowRange 372 hadRow372 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_344 : PLift (RowRange 372 hadRow372 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_352 : PLift (RowRange 372 hadRow372 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_360 : PLift (RowRange 372 hadRow372 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c372_368 : PLift (RowRange 372 hadRow372 368 372) := ⟨viaCheck (by decide +kernel)⟩

private theorem g372 : gramWitness 372 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c372_0.down c372_8.down) (viaSplit c372_16.down c372_24.down)) (viaSplit (viaSplit c372_32.down c372_40.down) (viaSplit c372_48.down c372_56.down))) (viaSplit (viaSplit (viaSplit c372_64.down c372_72.down) (viaSplit c372_80.down c372_88.down)) (viaSplit (viaSplit c372_96.down c372_104.down) (viaSplit c372_112.down c372_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c372_128.down c372_136.down) (viaSplit c372_144.down c372_152.down)) (viaSplit (viaSplit c372_160.down c372_168.down) (viaSplit c372_176.down c372_184.down))) (viaSplit (viaSplit (viaSplit c372_192.down c372_200.down) (viaSplit c372_208.down c372_216.down)) (viaSplit (viaSplit c372_224.down c372_232.down) (viaSplit c372_240.down c372_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit c372_256.down c372_264.down) (viaSplit c372_272.down c372_280.down)) (viaSplit (viaSplit c372_288.down c372_296.down) (viaSplit c372_304.down c372_312.down))) (viaSplit (viaSplit (viaSplit c372_320.down c372_328.down) (viaSplit c372_336.down c372_344.down)) (viaSplit (viaSplit c372_352.down c372_360.down) c372_368.down))))

private theorem g376 : gramWitness 376 := gram_product (by decide) (by decide) g2 g188

private theorem g380 : gramWitness 380 := fromColumns (PaleyHadamard.typeI 379 ((isPrimePow_nat_iff _).mpr ⟨379, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g384 : gramWitness 384 := gram_product (by decide) (by decide) g2 g192

private theorem g388 : gramWitness 388 := fromColumns (PaleyHadamard.typeII 193 ((isPrimePow_nat_iff _).mpr ⟨193, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g392 : gramWitness 392 := gram_product (by decide) (by decide) g2 g196

private theorem g396 : gramWitness 396 := fromColumns (PaleyHadamard.typeII 197 ((isPrimePow_nat_iff _).mpr ⟨197, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g400 : gramWitness 400 := gram_product (by decide) (by decide) g2 g200

set_option maxRecDepth 16000 in
private def c404_0 : PLift (RowRange 404 hadRow404 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_8 : PLift (RowRange 404 hadRow404 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_16 : PLift (RowRange 404 hadRow404 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_24 : PLift (RowRange 404 hadRow404 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_32 : PLift (RowRange 404 hadRow404 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_40 : PLift (RowRange 404 hadRow404 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_48 : PLift (RowRange 404 hadRow404 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_56 : PLift (RowRange 404 hadRow404 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_64 : PLift (RowRange 404 hadRow404 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_72 : PLift (RowRange 404 hadRow404 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_80 : PLift (RowRange 404 hadRow404 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_88 : PLift (RowRange 404 hadRow404 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_96 : PLift (RowRange 404 hadRow404 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_104 : PLift (RowRange 404 hadRow404 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_112 : PLift (RowRange 404 hadRow404 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_120 : PLift (RowRange 404 hadRow404 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_128 : PLift (RowRange 404 hadRow404 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_136 : PLift (RowRange 404 hadRow404 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_144 : PLift (RowRange 404 hadRow404 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_152 : PLift (RowRange 404 hadRow404 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_160 : PLift (RowRange 404 hadRow404 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_168 : PLift (RowRange 404 hadRow404 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_176 : PLift (RowRange 404 hadRow404 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_184 : PLift (RowRange 404 hadRow404 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_192 : PLift (RowRange 404 hadRow404 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_200 : PLift (RowRange 404 hadRow404 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_208 : PLift (RowRange 404 hadRow404 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_216 : PLift (RowRange 404 hadRow404 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_224 : PLift (RowRange 404 hadRow404 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_232 : PLift (RowRange 404 hadRow404 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_240 : PLift (RowRange 404 hadRow404 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_248 : PLift (RowRange 404 hadRow404 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_256 : PLift (RowRange 404 hadRow404 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_264 : PLift (RowRange 404 hadRow404 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_272 : PLift (RowRange 404 hadRow404 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_280 : PLift (RowRange 404 hadRow404 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_288 : PLift (RowRange 404 hadRow404 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_296 : PLift (RowRange 404 hadRow404 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_304 : PLift (RowRange 404 hadRow404 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_312 : PLift (RowRange 404 hadRow404 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_320 : PLift (RowRange 404 hadRow404 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_328 : PLift (RowRange 404 hadRow404 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_336 : PLift (RowRange 404 hadRow404 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_344 : PLift (RowRange 404 hadRow404 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_352 : PLift (RowRange 404 hadRow404 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_360 : PLift (RowRange 404 hadRow404 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_368 : PLift (RowRange 404 hadRow404 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_376 : PLift (RowRange 404 hadRow404 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_384 : PLift (RowRange 404 hadRow404 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_392 : PLift (RowRange 404 hadRow404 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c404_400 : PLift (RowRange 404 hadRow404 400 404) := ⟨viaCheck (by decide +kernel)⟩

private theorem g404 : gramWitness 404 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c404_0.down c404_8.down) (viaSplit c404_16.down c404_24.down)) (viaSplit (viaSplit c404_32.down c404_40.down) (viaSplit c404_48.down c404_56.down))) (viaSplit (viaSplit (viaSplit c404_64.down c404_72.down) (viaSplit c404_80.down c404_88.down)) (viaSplit (viaSplit c404_96.down c404_104.down) (viaSplit c404_112.down c404_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c404_128.down c404_136.down) (viaSplit c404_144.down c404_152.down)) (viaSplit (viaSplit c404_160.down c404_168.down) (viaSplit c404_176.down c404_184.down))) (viaSplit (viaSplit (viaSplit c404_192.down c404_200.down) (viaSplit c404_208.down c404_216.down)) (viaSplit (viaSplit c404_224.down c404_232.down) (viaSplit c404_240.down c404_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c404_256.down c404_264.down) (viaSplit c404_272.down c404_280.down)) (viaSplit (viaSplit c404_288.down c404_296.down) (viaSplit c404_304.down c404_312.down))) (viaSplit (viaSplit (viaSplit c404_320.down c404_328.down) (viaSplit c404_336.down c404_344.down)) (viaSplit (viaSplit c404_352.down c404_360.down) (viaSplit c404_368.down c404_376.down)))) (viaSplit (viaSplit c404_384.down c404_392.down) c404_400.down)))

private theorem g408 : gramWitness 408 := gram_product (by decide) (by decide) g2 g204

set_option maxRecDepth 16000 in
private def c412_0 : PLift (RowRange 412 hadRow412 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_8 : PLift (RowRange 412 hadRow412 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_16 : PLift (RowRange 412 hadRow412 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_24 : PLift (RowRange 412 hadRow412 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_32 : PLift (RowRange 412 hadRow412 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_40 : PLift (RowRange 412 hadRow412 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_48 : PLift (RowRange 412 hadRow412 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_56 : PLift (RowRange 412 hadRow412 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_64 : PLift (RowRange 412 hadRow412 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_72 : PLift (RowRange 412 hadRow412 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_80 : PLift (RowRange 412 hadRow412 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_88 : PLift (RowRange 412 hadRow412 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_96 : PLift (RowRange 412 hadRow412 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_104 : PLift (RowRange 412 hadRow412 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_112 : PLift (RowRange 412 hadRow412 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_120 : PLift (RowRange 412 hadRow412 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_128 : PLift (RowRange 412 hadRow412 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_136 : PLift (RowRange 412 hadRow412 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_144 : PLift (RowRange 412 hadRow412 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_152 : PLift (RowRange 412 hadRow412 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_160 : PLift (RowRange 412 hadRow412 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_168 : PLift (RowRange 412 hadRow412 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_176 : PLift (RowRange 412 hadRow412 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_184 : PLift (RowRange 412 hadRow412 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_192 : PLift (RowRange 412 hadRow412 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_200 : PLift (RowRange 412 hadRow412 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_208 : PLift (RowRange 412 hadRow412 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_216 : PLift (RowRange 412 hadRow412 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_224 : PLift (RowRange 412 hadRow412 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_232 : PLift (RowRange 412 hadRow412 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_240 : PLift (RowRange 412 hadRow412 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_248 : PLift (RowRange 412 hadRow412 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_256 : PLift (RowRange 412 hadRow412 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_264 : PLift (RowRange 412 hadRow412 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_272 : PLift (RowRange 412 hadRow412 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_280 : PLift (RowRange 412 hadRow412 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_288 : PLift (RowRange 412 hadRow412 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_296 : PLift (RowRange 412 hadRow412 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_304 : PLift (RowRange 412 hadRow412 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_312 : PLift (RowRange 412 hadRow412 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_320 : PLift (RowRange 412 hadRow412 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_328 : PLift (RowRange 412 hadRow412 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_336 : PLift (RowRange 412 hadRow412 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_344 : PLift (RowRange 412 hadRow412 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_352 : PLift (RowRange 412 hadRow412 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_360 : PLift (RowRange 412 hadRow412 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_368 : PLift (RowRange 412 hadRow412 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_376 : PLift (RowRange 412 hadRow412 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_384 : PLift (RowRange 412 hadRow412 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_392 : PLift (RowRange 412 hadRow412 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_400 : PLift (RowRange 412 hadRow412 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c412_408 : PLift (RowRange 412 hadRow412 408 412) := ⟨viaCheck (by decide +kernel)⟩

private theorem g412 : gramWitness 412 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c412_0.down c412_8.down) (viaSplit c412_16.down c412_24.down)) (viaSplit (viaSplit c412_32.down c412_40.down) (viaSplit c412_48.down c412_56.down))) (viaSplit (viaSplit (viaSplit c412_64.down c412_72.down) (viaSplit c412_80.down c412_88.down)) (viaSplit (viaSplit c412_96.down c412_104.down) (viaSplit c412_112.down c412_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c412_128.down c412_136.down) (viaSplit c412_144.down c412_152.down)) (viaSplit (viaSplit c412_160.down c412_168.down) (viaSplit c412_176.down c412_184.down))) (viaSplit (viaSplit (viaSplit c412_192.down c412_200.down) (viaSplit c412_208.down c412_216.down)) (viaSplit (viaSplit c412_224.down c412_232.down) (viaSplit c412_240.down c412_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c412_256.down c412_264.down) (viaSplit c412_272.down c412_280.down)) (viaSplit (viaSplit c412_288.down c412_296.down) (viaSplit c412_304.down c412_312.down))) (viaSplit (viaSplit (viaSplit c412_320.down c412_328.down) (viaSplit c412_336.down c412_344.down)) (viaSplit (viaSplit c412_352.down c412_360.down) (viaSplit c412_368.down c412_376.down)))) (viaSplit (viaSplit c412_384.down c412_392.down) (viaSplit c412_400.down c412_408.down))))

private theorem g416 : gramWitness 416 := gram_product (by decide) (by decide) g2 g208

private theorem g420 : gramWitness 420 := fromColumns (PaleyHadamard.typeI 419 ((isPrimePow_nat_iff _).mpr ⟨419, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g424 : gramWitness 424 := gram_product (by decide) (by decide) g2 g212

set_option maxRecDepth 16000 in
private def c428_0 : PLift (RowRange 428 hadRow428 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_8 : PLift (RowRange 428 hadRow428 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_16 : PLift (RowRange 428 hadRow428 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_24 : PLift (RowRange 428 hadRow428 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_32 : PLift (RowRange 428 hadRow428 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_40 : PLift (RowRange 428 hadRow428 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_48 : PLift (RowRange 428 hadRow428 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_56 : PLift (RowRange 428 hadRow428 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_64 : PLift (RowRange 428 hadRow428 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_72 : PLift (RowRange 428 hadRow428 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_80 : PLift (RowRange 428 hadRow428 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_88 : PLift (RowRange 428 hadRow428 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_96 : PLift (RowRange 428 hadRow428 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_104 : PLift (RowRange 428 hadRow428 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_112 : PLift (RowRange 428 hadRow428 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_120 : PLift (RowRange 428 hadRow428 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_128 : PLift (RowRange 428 hadRow428 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_136 : PLift (RowRange 428 hadRow428 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_144 : PLift (RowRange 428 hadRow428 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_152 : PLift (RowRange 428 hadRow428 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_160 : PLift (RowRange 428 hadRow428 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_168 : PLift (RowRange 428 hadRow428 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_176 : PLift (RowRange 428 hadRow428 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_184 : PLift (RowRange 428 hadRow428 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_192 : PLift (RowRange 428 hadRow428 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_200 : PLift (RowRange 428 hadRow428 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_208 : PLift (RowRange 428 hadRow428 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_216 : PLift (RowRange 428 hadRow428 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_224 : PLift (RowRange 428 hadRow428 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_232 : PLift (RowRange 428 hadRow428 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_240 : PLift (RowRange 428 hadRow428 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_248 : PLift (RowRange 428 hadRow428 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_256 : PLift (RowRange 428 hadRow428 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_264 : PLift (RowRange 428 hadRow428 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_272 : PLift (RowRange 428 hadRow428 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_280 : PLift (RowRange 428 hadRow428 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_288 : PLift (RowRange 428 hadRow428 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_296 : PLift (RowRange 428 hadRow428 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_304 : PLift (RowRange 428 hadRow428 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_312 : PLift (RowRange 428 hadRow428 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_320 : PLift (RowRange 428 hadRow428 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_328 : PLift (RowRange 428 hadRow428 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_336 : PLift (RowRange 428 hadRow428 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_344 : PLift (RowRange 428 hadRow428 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_352 : PLift (RowRange 428 hadRow428 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_360 : PLift (RowRange 428 hadRow428 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_368 : PLift (RowRange 428 hadRow428 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_376 : PLift (RowRange 428 hadRow428 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_384 : PLift (RowRange 428 hadRow428 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_392 : PLift (RowRange 428 hadRow428 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_400 : PLift (RowRange 428 hadRow428 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_408 : PLift (RowRange 428 hadRow428 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_416 : PLift (RowRange 428 hadRow428 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c428_424 : PLift (RowRange 428 hadRow428 424 428) := ⟨viaCheck (by decide +kernel)⟩

private theorem g428 : gramWitness 428 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c428_0.down c428_8.down) (viaSplit c428_16.down c428_24.down)) (viaSplit (viaSplit c428_32.down c428_40.down) (viaSplit c428_48.down c428_56.down))) (viaSplit (viaSplit (viaSplit c428_64.down c428_72.down) (viaSplit c428_80.down c428_88.down)) (viaSplit (viaSplit c428_96.down c428_104.down) (viaSplit c428_112.down c428_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c428_128.down c428_136.down) (viaSplit c428_144.down c428_152.down)) (viaSplit (viaSplit c428_160.down c428_168.down) (viaSplit c428_176.down c428_184.down))) (viaSplit (viaSplit (viaSplit c428_192.down c428_200.down) (viaSplit c428_208.down c428_216.down)) (viaSplit (viaSplit c428_224.down c428_232.down) (viaSplit c428_240.down c428_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c428_256.down c428_264.down) (viaSplit c428_272.down c428_280.down)) (viaSplit (viaSplit c428_288.down c428_296.down) (viaSplit c428_304.down c428_312.down))) (viaSplit (viaSplit (viaSplit c428_320.down c428_328.down) (viaSplit c428_336.down c428_344.down)) (viaSplit (viaSplit c428_352.down c428_360.down) (viaSplit c428_368.down c428_376.down)))) (viaSplit (viaSplit (viaSplit c428_384.down c428_392.down) (viaSplit c428_400.down c428_408.down)) (viaSplit c428_416.down c428_424.down))))

private theorem g432 : gramWitness 432 := gram_product (by decide) (by decide) g2 g216

set_option maxRecDepth 16000 in
private def c436_0 : PLift (RowRange 436 hadRow436 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_8 : PLift (RowRange 436 hadRow436 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_16 : PLift (RowRange 436 hadRow436 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_24 : PLift (RowRange 436 hadRow436 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_32 : PLift (RowRange 436 hadRow436 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_40 : PLift (RowRange 436 hadRow436 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_48 : PLift (RowRange 436 hadRow436 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_56 : PLift (RowRange 436 hadRow436 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_64 : PLift (RowRange 436 hadRow436 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_72 : PLift (RowRange 436 hadRow436 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_80 : PLift (RowRange 436 hadRow436 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_88 : PLift (RowRange 436 hadRow436 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_96 : PLift (RowRange 436 hadRow436 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_104 : PLift (RowRange 436 hadRow436 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_112 : PLift (RowRange 436 hadRow436 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_120 : PLift (RowRange 436 hadRow436 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_128 : PLift (RowRange 436 hadRow436 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_136 : PLift (RowRange 436 hadRow436 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_144 : PLift (RowRange 436 hadRow436 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_152 : PLift (RowRange 436 hadRow436 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_160 : PLift (RowRange 436 hadRow436 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_168 : PLift (RowRange 436 hadRow436 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_176 : PLift (RowRange 436 hadRow436 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_184 : PLift (RowRange 436 hadRow436 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_192 : PLift (RowRange 436 hadRow436 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_200 : PLift (RowRange 436 hadRow436 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_208 : PLift (RowRange 436 hadRow436 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_216 : PLift (RowRange 436 hadRow436 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_224 : PLift (RowRange 436 hadRow436 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_232 : PLift (RowRange 436 hadRow436 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_240 : PLift (RowRange 436 hadRow436 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_248 : PLift (RowRange 436 hadRow436 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_256 : PLift (RowRange 436 hadRow436 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_264 : PLift (RowRange 436 hadRow436 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_272 : PLift (RowRange 436 hadRow436 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_280 : PLift (RowRange 436 hadRow436 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_288 : PLift (RowRange 436 hadRow436 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_296 : PLift (RowRange 436 hadRow436 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_304 : PLift (RowRange 436 hadRow436 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_312 : PLift (RowRange 436 hadRow436 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_320 : PLift (RowRange 436 hadRow436 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_328 : PLift (RowRange 436 hadRow436 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_336 : PLift (RowRange 436 hadRow436 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_344 : PLift (RowRange 436 hadRow436 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_352 : PLift (RowRange 436 hadRow436 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_360 : PLift (RowRange 436 hadRow436 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_368 : PLift (RowRange 436 hadRow436 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_376 : PLift (RowRange 436 hadRow436 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_384 : PLift (RowRange 436 hadRow436 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_392 : PLift (RowRange 436 hadRow436 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_400 : PLift (RowRange 436 hadRow436 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_408 : PLift (RowRange 436 hadRow436 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_416 : PLift (RowRange 436 hadRow436 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_424 : PLift (RowRange 436 hadRow436 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c436_432 : PLift (RowRange 436 hadRow436 432 436) := ⟨viaCheck (by decide +kernel)⟩

private theorem g436 : gramWitness 436 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c436_0.down c436_8.down) (viaSplit c436_16.down c436_24.down)) (viaSplit (viaSplit c436_32.down c436_40.down) (viaSplit c436_48.down c436_56.down))) (viaSplit (viaSplit (viaSplit c436_64.down c436_72.down) (viaSplit c436_80.down c436_88.down)) (viaSplit (viaSplit c436_96.down c436_104.down) (viaSplit c436_112.down c436_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c436_128.down c436_136.down) (viaSplit c436_144.down c436_152.down)) (viaSplit (viaSplit c436_160.down c436_168.down) (viaSplit c436_176.down c436_184.down))) (viaSplit (viaSplit (viaSplit c436_192.down c436_200.down) (viaSplit c436_208.down c436_216.down)) (viaSplit (viaSplit c436_224.down c436_232.down) (viaSplit c436_240.down c436_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c436_256.down c436_264.down) (viaSplit c436_272.down c436_280.down)) (viaSplit (viaSplit c436_288.down c436_296.down) (viaSplit c436_304.down c436_312.down))) (viaSplit (viaSplit (viaSplit c436_320.down c436_328.down) (viaSplit c436_336.down c436_344.down)) (viaSplit (viaSplit c436_352.down c436_360.down) (viaSplit c436_368.down c436_376.down)))) (viaSplit (viaSplit (viaSplit c436_384.down c436_392.down) (viaSplit c436_400.down c436_408.down)) (viaSplit (viaSplit c436_416.down c436_424.down) c436_432.down))))

private theorem g440 : gramWitness 440 := gram_product (by decide) (by decide) g2 g220

private theorem g444 : gramWitness 444 := fromColumns (PaleyHadamard.typeI 443 ((isPrimePow_nat_iff _).mpr ⟨443, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g448 : gramWitness 448 := gram_product (by decide) (by decide) g2 g224

set_option maxRecDepth 16000 in
private def c452_0 : PLift (RowRange 452 hadRow452 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_8 : PLift (RowRange 452 hadRow452 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_16 : PLift (RowRange 452 hadRow452 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_24 : PLift (RowRange 452 hadRow452 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_32 : PLift (RowRange 452 hadRow452 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_40 : PLift (RowRange 452 hadRow452 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_48 : PLift (RowRange 452 hadRow452 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_56 : PLift (RowRange 452 hadRow452 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_64 : PLift (RowRange 452 hadRow452 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_72 : PLift (RowRange 452 hadRow452 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_80 : PLift (RowRange 452 hadRow452 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_88 : PLift (RowRange 452 hadRow452 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_96 : PLift (RowRange 452 hadRow452 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_104 : PLift (RowRange 452 hadRow452 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_112 : PLift (RowRange 452 hadRow452 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_120 : PLift (RowRange 452 hadRow452 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_128 : PLift (RowRange 452 hadRow452 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_136 : PLift (RowRange 452 hadRow452 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_144 : PLift (RowRange 452 hadRow452 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_152 : PLift (RowRange 452 hadRow452 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_160 : PLift (RowRange 452 hadRow452 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_168 : PLift (RowRange 452 hadRow452 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_176 : PLift (RowRange 452 hadRow452 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_184 : PLift (RowRange 452 hadRow452 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_192 : PLift (RowRange 452 hadRow452 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_200 : PLift (RowRange 452 hadRow452 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_208 : PLift (RowRange 452 hadRow452 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_216 : PLift (RowRange 452 hadRow452 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_224 : PLift (RowRange 452 hadRow452 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_232 : PLift (RowRange 452 hadRow452 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_240 : PLift (RowRange 452 hadRow452 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_248 : PLift (RowRange 452 hadRow452 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_256 : PLift (RowRange 452 hadRow452 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_264 : PLift (RowRange 452 hadRow452 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_272 : PLift (RowRange 452 hadRow452 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_280 : PLift (RowRange 452 hadRow452 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_288 : PLift (RowRange 452 hadRow452 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_296 : PLift (RowRange 452 hadRow452 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_304 : PLift (RowRange 452 hadRow452 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_312 : PLift (RowRange 452 hadRow452 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_320 : PLift (RowRange 452 hadRow452 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_328 : PLift (RowRange 452 hadRow452 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_336 : PLift (RowRange 452 hadRow452 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_344 : PLift (RowRange 452 hadRow452 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_352 : PLift (RowRange 452 hadRow452 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_360 : PLift (RowRange 452 hadRow452 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_368 : PLift (RowRange 452 hadRow452 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_376 : PLift (RowRange 452 hadRow452 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_384 : PLift (RowRange 452 hadRow452 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_392 : PLift (RowRange 452 hadRow452 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_400 : PLift (RowRange 452 hadRow452 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_408 : PLift (RowRange 452 hadRow452 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_416 : PLift (RowRange 452 hadRow452 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_424 : PLift (RowRange 452 hadRow452 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_432 : PLift (RowRange 452 hadRow452 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_440 : PLift (RowRange 452 hadRow452 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c452_448 : PLift (RowRange 452 hadRow452 448 452) := ⟨viaCheck (by decide +kernel)⟩

private theorem g452 : gramWitness 452 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c452_0.down c452_8.down) (viaSplit c452_16.down c452_24.down)) (viaSplit (viaSplit c452_32.down c452_40.down) (viaSplit c452_48.down c452_56.down))) (viaSplit (viaSplit (viaSplit c452_64.down c452_72.down) (viaSplit c452_80.down c452_88.down)) (viaSplit (viaSplit c452_96.down c452_104.down) (viaSplit c452_112.down c452_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c452_128.down c452_136.down) (viaSplit c452_144.down c452_152.down)) (viaSplit (viaSplit c452_160.down c452_168.down) (viaSplit c452_176.down c452_184.down))) (viaSplit (viaSplit (viaSplit c452_192.down c452_200.down) (viaSplit c452_208.down c452_216.down)) (viaSplit (viaSplit c452_224.down c452_232.down) (viaSplit c452_240.down c452_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c452_256.down c452_264.down) (viaSplit c452_272.down c452_280.down)) (viaSplit (viaSplit c452_288.down c452_296.down) (viaSplit c452_304.down c452_312.down))) (viaSplit (viaSplit (viaSplit c452_320.down c452_328.down) (viaSplit c452_336.down c452_344.down)) (viaSplit (viaSplit c452_352.down c452_360.down) (viaSplit c452_368.down c452_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c452_384.down c452_392.down) (viaSplit c452_400.down c452_408.down)) (viaSplit (viaSplit c452_416.down c452_424.down) (viaSplit c452_432.down c452_440.down))) c452_448.down)))

private theorem g456 : gramWitness 456 := gram_product (by decide) (by decide) g2 g228

private theorem g460 : gramWitness 460 := fromColumns (PaleyHadamard.typeII 229 ((isPrimePow_nat_iff _).mpr ⟨229, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g464 : gramWitness 464 := gram_product (by decide) (by decide) g2 g232

private theorem g468 : gramWitness 468 := fromColumns (PaleyHadamard.typeI 467 ((isPrimePow_nat_iff _).mpr ⟨467, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g472 : gramWitness 472 := gram_product (by decide) (by decide) g2 g236

set_option maxRecDepth 16000 in
private def c476_0 : PLift (RowRange 476 hadRow476 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_8 : PLift (RowRange 476 hadRow476 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_16 : PLift (RowRange 476 hadRow476 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_24 : PLift (RowRange 476 hadRow476 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_32 : PLift (RowRange 476 hadRow476 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_40 : PLift (RowRange 476 hadRow476 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_48 : PLift (RowRange 476 hadRow476 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_56 : PLift (RowRange 476 hadRow476 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_64 : PLift (RowRange 476 hadRow476 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_72 : PLift (RowRange 476 hadRow476 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_80 : PLift (RowRange 476 hadRow476 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_88 : PLift (RowRange 476 hadRow476 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_96 : PLift (RowRange 476 hadRow476 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_104 : PLift (RowRange 476 hadRow476 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_112 : PLift (RowRange 476 hadRow476 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_120 : PLift (RowRange 476 hadRow476 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_128 : PLift (RowRange 476 hadRow476 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_136 : PLift (RowRange 476 hadRow476 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_144 : PLift (RowRange 476 hadRow476 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_152 : PLift (RowRange 476 hadRow476 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_160 : PLift (RowRange 476 hadRow476 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_168 : PLift (RowRange 476 hadRow476 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_176 : PLift (RowRange 476 hadRow476 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_184 : PLift (RowRange 476 hadRow476 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_192 : PLift (RowRange 476 hadRow476 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_200 : PLift (RowRange 476 hadRow476 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_208 : PLift (RowRange 476 hadRow476 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_216 : PLift (RowRange 476 hadRow476 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_224 : PLift (RowRange 476 hadRow476 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_232 : PLift (RowRange 476 hadRow476 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_240 : PLift (RowRange 476 hadRow476 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_248 : PLift (RowRange 476 hadRow476 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_256 : PLift (RowRange 476 hadRow476 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_264 : PLift (RowRange 476 hadRow476 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_272 : PLift (RowRange 476 hadRow476 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_280 : PLift (RowRange 476 hadRow476 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_288 : PLift (RowRange 476 hadRow476 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_296 : PLift (RowRange 476 hadRow476 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_304 : PLift (RowRange 476 hadRow476 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_312 : PLift (RowRange 476 hadRow476 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_320 : PLift (RowRange 476 hadRow476 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_328 : PLift (RowRange 476 hadRow476 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_336 : PLift (RowRange 476 hadRow476 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_344 : PLift (RowRange 476 hadRow476 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_352 : PLift (RowRange 476 hadRow476 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_360 : PLift (RowRange 476 hadRow476 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_368 : PLift (RowRange 476 hadRow476 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_376 : PLift (RowRange 476 hadRow476 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_384 : PLift (RowRange 476 hadRow476 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_392 : PLift (RowRange 476 hadRow476 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_400 : PLift (RowRange 476 hadRow476 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_408 : PLift (RowRange 476 hadRow476 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_416 : PLift (RowRange 476 hadRow476 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_424 : PLift (RowRange 476 hadRow476 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_432 : PLift (RowRange 476 hadRow476 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_440 : PLift (RowRange 476 hadRow476 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_448 : PLift (RowRange 476 hadRow476 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_456 : PLift (RowRange 476 hadRow476 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_464 : PLift (RowRange 476 hadRow476 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c476_472 : PLift (RowRange 476 hadRow476 472 476) := ⟨viaCheck (by decide +kernel)⟩

private theorem g476 : gramWitness 476 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c476_0.down c476_8.down) (viaSplit c476_16.down c476_24.down)) (viaSplit (viaSplit c476_32.down c476_40.down) (viaSplit c476_48.down c476_56.down))) (viaSplit (viaSplit (viaSplit c476_64.down c476_72.down) (viaSplit c476_80.down c476_88.down)) (viaSplit (viaSplit c476_96.down c476_104.down) (viaSplit c476_112.down c476_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c476_128.down c476_136.down) (viaSplit c476_144.down c476_152.down)) (viaSplit (viaSplit c476_160.down c476_168.down) (viaSplit c476_176.down c476_184.down))) (viaSplit (viaSplit (viaSplit c476_192.down c476_200.down) (viaSplit c476_208.down c476_216.down)) (viaSplit (viaSplit c476_224.down c476_232.down) (viaSplit c476_240.down c476_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c476_256.down c476_264.down) (viaSplit c476_272.down c476_280.down)) (viaSplit (viaSplit c476_288.down c476_296.down) (viaSplit c476_304.down c476_312.down))) (viaSplit (viaSplit (viaSplit c476_320.down c476_328.down) (viaSplit c476_336.down c476_344.down)) (viaSplit (viaSplit c476_352.down c476_360.down) (viaSplit c476_368.down c476_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c476_384.down c476_392.down) (viaSplit c476_400.down c476_408.down)) (viaSplit (viaSplit c476_416.down c476_424.down) (viaSplit c476_432.down c476_440.down))) (viaSplit (viaSplit c476_448.down c476_456.down) (viaSplit c476_464.down c476_472.down)))))

private theorem g480 : gramWitness 480 := gram_product (by decide) (by decide) g2 g240

private theorem g484 : gramWitness 484 := fromColumns (PaleyHadamard.typeII 241 ((isPrimePow_nat_iff _).mpr ⟨241, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g488 : gramWitness 488 := gram_product (by decide) (by decide) g2 g244

private theorem g492 : gramWitness 492 := fromColumns (PaleyHadamard.typeI 491 ((isPrimePow_nat_iff _).mpr ⟨491, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g496 : gramWitness 496 := gram_product (by decide) (by decide) g2 g248

private theorem g500 : gramWitness 500 := fromColumns (PaleyHadamard.typeI 499 ((isPrimePow_nat_iff _).mpr ⟨499, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g504 : gramWitness 504 := gram_product (by decide) (by decide) g2 g252

set_option maxRecDepth 16000 in
private def c508_0 : PLift (RowRange 508 hadRow508 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_8 : PLift (RowRange 508 hadRow508 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_16 : PLift (RowRange 508 hadRow508 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_24 : PLift (RowRange 508 hadRow508 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_32 : PLift (RowRange 508 hadRow508 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_40 : PLift (RowRange 508 hadRow508 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_48 : PLift (RowRange 508 hadRow508 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_56 : PLift (RowRange 508 hadRow508 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_64 : PLift (RowRange 508 hadRow508 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_72 : PLift (RowRange 508 hadRow508 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_80 : PLift (RowRange 508 hadRow508 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_88 : PLift (RowRange 508 hadRow508 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_96 : PLift (RowRange 508 hadRow508 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_104 : PLift (RowRange 508 hadRow508 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_112 : PLift (RowRange 508 hadRow508 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_120 : PLift (RowRange 508 hadRow508 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_128 : PLift (RowRange 508 hadRow508 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_136 : PLift (RowRange 508 hadRow508 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_144 : PLift (RowRange 508 hadRow508 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_152 : PLift (RowRange 508 hadRow508 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_160 : PLift (RowRange 508 hadRow508 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_168 : PLift (RowRange 508 hadRow508 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_176 : PLift (RowRange 508 hadRow508 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_184 : PLift (RowRange 508 hadRow508 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_192 : PLift (RowRange 508 hadRow508 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_200 : PLift (RowRange 508 hadRow508 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_208 : PLift (RowRange 508 hadRow508 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_216 : PLift (RowRange 508 hadRow508 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_224 : PLift (RowRange 508 hadRow508 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_232 : PLift (RowRange 508 hadRow508 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_240 : PLift (RowRange 508 hadRow508 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_248 : PLift (RowRange 508 hadRow508 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_256 : PLift (RowRange 508 hadRow508 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_264 : PLift (RowRange 508 hadRow508 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_272 : PLift (RowRange 508 hadRow508 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_280 : PLift (RowRange 508 hadRow508 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_288 : PLift (RowRange 508 hadRow508 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_296 : PLift (RowRange 508 hadRow508 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_304 : PLift (RowRange 508 hadRow508 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_312 : PLift (RowRange 508 hadRow508 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_320 : PLift (RowRange 508 hadRow508 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_328 : PLift (RowRange 508 hadRow508 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_336 : PLift (RowRange 508 hadRow508 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_344 : PLift (RowRange 508 hadRow508 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_352 : PLift (RowRange 508 hadRow508 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_360 : PLift (RowRange 508 hadRow508 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_368 : PLift (RowRange 508 hadRow508 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_376 : PLift (RowRange 508 hadRow508 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_384 : PLift (RowRange 508 hadRow508 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_392 : PLift (RowRange 508 hadRow508 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_400 : PLift (RowRange 508 hadRow508 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_408 : PLift (RowRange 508 hadRow508 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_416 : PLift (RowRange 508 hadRow508 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_424 : PLift (RowRange 508 hadRow508 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_432 : PLift (RowRange 508 hadRow508 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_440 : PLift (RowRange 508 hadRow508 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_448 : PLift (RowRange 508 hadRow508 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_456 : PLift (RowRange 508 hadRow508 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_464 : PLift (RowRange 508 hadRow508 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_472 : PLift (RowRange 508 hadRow508 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_480 : PLift (RowRange 508 hadRow508 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_488 : PLift (RowRange 508 hadRow508 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_496 : PLift (RowRange 508 hadRow508 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c508_504 : PLift (RowRange 508 hadRow508 504 508) := ⟨viaCheck (by decide +kernel)⟩

private theorem g508 : gramWitness 508 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c508_0.down c508_8.down) (viaSplit c508_16.down c508_24.down)) (viaSplit (viaSplit c508_32.down c508_40.down) (viaSplit c508_48.down c508_56.down))) (viaSplit (viaSplit (viaSplit c508_64.down c508_72.down) (viaSplit c508_80.down c508_88.down)) (viaSplit (viaSplit c508_96.down c508_104.down) (viaSplit c508_112.down c508_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c508_128.down c508_136.down) (viaSplit c508_144.down c508_152.down)) (viaSplit (viaSplit c508_160.down c508_168.down) (viaSplit c508_176.down c508_184.down))) (viaSplit (viaSplit (viaSplit c508_192.down c508_200.down) (viaSplit c508_208.down c508_216.down)) (viaSplit (viaSplit c508_224.down c508_232.down) (viaSplit c508_240.down c508_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c508_256.down c508_264.down) (viaSplit c508_272.down c508_280.down)) (viaSplit (viaSplit c508_288.down c508_296.down) (viaSplit c508_304.down c508_312.down))) (viaSplit (viaSplit (viaSplit c508_320.down c508_328.down) (viaSplit c508_336.down c508_344.down)) (viaSplit (viaSplit c508_352.down c508_360.down) (viaSplit c508_368.down c508_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c508_384.down c508_392.down) (viaSplit c508_400.down c508_408.down)) (viaSplit (viaSplit c508_416.down c508_424.down) (viaSplit c508_432.down c508_440.down))) (viaSplit (viaSplit (viaSplit c508_448.down c508_456.down) (viaSplit c508_464.down c508_472.down)) (viaSplit (viaSplit c508_480.down c508_488.down) (viaSplit c508_496.down c508_504.down))))))

private theorem g512 : gramWitness 512 := gram_product (by decide) (by decide) g2 g256

private theorem g516 : gramWitness 516 := fromColumns (PaleyHadamard.typeII 257 ((isPrimePow_nat_iff _).mpr ⟨257, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g520 : gramWitness 520 := gram_product (by decide) (by decide) g2 g260

private theorem g524 : gramWitness 524 := fromColumns (PaleyHadamard.typeI 523 ((isPrimePow_nat_iff _).mpr ⟨523, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g528 : gramWitness 528 := gram_product (by decide) (by decide) g2 g264

set_option maxRecDepth 16000 in
private def c532_0 : PLift (RowRange 532 hadRow532 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_8 : PLift (RowRange 532 hadRow532 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_16 : PLift (RowRange 532 hadRow532 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_24 : PLift (RowRange 532 hadRow532 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_32 : PLift (RowRange 532 hadRow532 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_40 : PLift (RowRange 532 hadRow532 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_48 : PLift (RowRange 532 hadRow532 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_56 : PLift (RowRange 532 hadRow532 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_64 : PLift (RowRange 532 hadRow532 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_72 : PLift (RowRange 532 hadRow532 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_80 : PLift (RowRange 532 hadRow532 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_88 : PLift (RowRange 532 hadRow532 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_96 : PLift (RowRange 532 hadRow532 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_104 : PLift (RowRange 532 hadRow532 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_112 : PLift (RowRange 532 hadRow532 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_120 : PLift (RowRange 532 hadRow532 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_128 : PLift (RowRange 532 hadRow532 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_136 : PLift (RowRange 532 hadRow532 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_144 : PLift (RowRange 532 hadRow532 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_152 : PLift (RowRange 532 hadRow532 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_160 : PLift (RowRange 532 hadRow532 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_168 : PLift (RowRange 532 hadRow532 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_176 : PLift (RowRange 532 hadRow532 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_184 : PLift (RowRange 532 hadRow532 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_192 : PLift (RowRange 532 hadRow532 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_200 : PLift (RowRange 532 hadRow532 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_208 : PLift (RowRange 532 hadRow532 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_216 : PLift (RowRange 532 hadRow532 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_224 : PLift (RowRange 532 hadRow532 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_232 : PLift (RowRange 532 hadRow532 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_240 : PLift (RowRange 532 hadRow532 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_248 : PLift (RowRange 532 hadRow532 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_256 : PLift (RowRange 532 hadRow532 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_264 : PLift (RowRange 532 hadRow532 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_272 : PLift (RowRange 532 hadRow532 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_280 : PLift (RowRange 532 hadRow532 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_288 : PLift (RowRange 532 hadRow532 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_296 : PLift (RowRange 532 hadRow532 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_304 : PLift (RowRange 532 hadRow532 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_312 : PLift (RowRange 532 hadRow532 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_320 : PLift (RowRange 532 hadRow532 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_328 : PLift (RowRange 532 hadRow532 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_336 : PLift (RowRange 532 hadRow532 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_344 : PLift (RowRange 532 hadRow532 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_352 : PLift (RowRange 532 hadRow532 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_360 : PLift (RowRange 532 hadRow532 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_368 : PLift (RowRange 532 hadRow532 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_376 : PLift (RowRange 532 hadRow532 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_384 : PLift (RowRange 532 hadRow532 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_392 : PLift (RowRange 532 hadRow532 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_400 : PLift (RowRange 532 hadRow532 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_408 : PLift (RowRange 532 hadRow532 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_416 : PLift (RowRange 532 hadRow532 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_424 : PLift (RowRange 532 hadRow532 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_432 : PLift (RowRange 532 hadRow532 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_440 : PLift (RowRange 532 hadRow532 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_448 : PLift (RowRange 532 hadRow532 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_456 : PLift (RowRange 532 hadRow532 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_464 : PLift (RowRange 532 hadRow532 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_472 : PLift (RowRange 532 hadRow532 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_480 : PLift (RowRange 532 hadRow532 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_488 : PLift (RowRange 532 hadRow532 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_496 : PLift (RowRange 532 hadRow532 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_504 : PLift (RowRange 532 hadRow532 504 512) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_512 : PLift (RowRange 532 hadRow532 512 520) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_520 : PLift (RowRange 532 hadRow532 520 528) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c532_528 : PLift (RowRange 532 hadRow532 528 532) := ⟨viaCheck (by decide +kernel)⟩

private theorem g532 : gramWitness 532 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c532_0.down c532_8.down) (viaSplit c532_16.down c532_24.down)) (viaSplit (viaSplit c532_32.down c532_40.down) (viaSplit c532_48.down c532_56.down))) (viaSplit (viaSplit (viaSplit c532_64.down c532_72.down) (viaSplit c532_80.down c532_88.down)) (viaSplit (viaSplit c532_96.down c532_104.down) (viaSplit c532_112.down c532_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c532_128.down c532_136.down) (viaSplit c532_144.down c532_152.down)) (viaSplit (viaSplit c532_160.down c532_168.down) (viaSplit c532_176.down c532_184.down))) (viaSplit (viaSplit (viaSplit c532_192.down c532_200.down) (viaSplit c532_208.down c532_216.down)) (viaSplit (viaSplit c532_224.down c532_232.down) (viaSplit c532_240.down c532_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c532_256.down c532_264.down) (viaSplit c532_272.down c532_280.down)) (viaSplit (viaSplit c532_288.down c532_296.down) (viaSplit c532_304.down c532_312.down))) (viaSplit (viaSplit (viaSplit c532_320.down c532_328.down) (viaSplit c532_336.down c532_344.down)) (viaSplit (viaSplit c532_352.down c532_360.down) (viaSplit c532_368.down c532_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c532_384.down c532_392.down) (viaSplit c532_400.down c532_408.down)) (viaSplit (viaSplit c532_416.down c532_424.down) (viaSplit c532_432.down c532_440.down))) (viaSplit (viaSplit (viaSplit c532_448.down c532_456.down) (viaSplit c532_464.down c532_472.down)) (viaSplit (viaSplit c532_480.down c532_488.down) (viaSplit c532_496.down c532_504.down)))))) (viaSplit (viaSplit c532_512.down c532_520.down) c532_528.down))

private theorem g536 : gramWitness 536 := gram_product (by decide) (by decide) g2 g268

private theorem g540 : gramWitness 540 := fromColumns (PaleyHadamard.typeII 269 ((isPrimePow_nat_iff _).mpr ⟨269, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g544 : gramWitness 544 := gram_product (by decide) (by decide) g2 g272

private theorem g548 : gramWitness 548 := fromColumns (PaleyHadamard.typeI 547 ((isPrimePow_nat_iff _).mpr ⟨547, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g552 : gramWitness 552 := gram_product (by decide) (by decide) g2 g276

private theorem g556 : gramWitness 556 := fromColumns (PaleyHadamard.typeII 277 ((isPrimePow_nat_iff _).mpr ⟨277, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g560 : gramWitness 560 := gram_product (by decide) (by decide) g2 g280

private theorem g564 : gramWitness 564 := fromColumns (PaleyHadamard.typeI 563 ((isPrimePow_nat_iff _).mpr ⟨563, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g568 : gramWitness 568 := gram_product (by decide) (by decide) g2 g284

private theorem g572 : gramWitness 572 := fromColumns (PaleyHadamard.typeI 571 ((isPrimePow_nat_iff _).mpr ⟨571, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g576 : gramWitness 576 := gram_product (by decide) (by decide) g2 g288

private theorem g580 : gramWitness 580 := fromColumns (PaleyHadamard.typeII 289 ((isPrimePow_nat_iff _).mpr ⟨17, 2, by norm_num, by decide, by decide⟩) (by decide))

private theorem g584 : gramWitness 584 := gram_product (by decide) (by decide) g2 g292

private theorem g588 : gramWitness 588 := fromColumns (PaleyHadamard.typeI 587 ((isPrimePow_nat_iff _).mpr ⟨587, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g592 : gramWitness 592 := gram_product (by decide) (by decide) g2 g296

set_option maxRecDepth 16000 in
private def c596_0 : PLift (RowRange 596 hadRow596 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_8 : PLift (RowRange 596 hadRow596 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_16 : PLift (RowRange 596 hadRow596 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_24 : PLift (RowRange 596 hadRow596 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_32 : PLift (RowRange 596 hadRow596 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_40 : PLift (RowRange 596 hadRow596 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_48 : PLift (RowRange 596 hadRow596 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_56 : PLift (RowRange 596 hadRow596 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_64 : PLift (RowRange 596 hadRow596 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_72 : PLift (RowRange 596 hadRow596 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_80 : PLift (RowRange 596 hadRow596 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_88 : PLift (RowRange 596 hadRow596 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_96 : PLift (RowRange 596 hadRow596 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_104 : PLift (RowRange 596 hadRow596 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_112 : PLift (RowRange 596 hadRow596 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_120 : PLift (RowRange 596 hadRow596 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_128 : PLift (RowRange 596 hadRow596 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_136 : PLift (RowRange 596 hadRow596 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_144 : PLift (RowRange 596 hadRow596 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_152 : PLift (RowRange 596 hadRow596 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_160 : PLift (RowRange 596 hadRow596 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_168 : PLift (RowRange 596 hadRow596 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_176 : PLift (RowRange 596 hadRow596 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_184 : PLift (RowRange 596 hadRow596 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_192 : PLift (RowRange 596 hadRow596 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_200 : PLift (RowRange 596 hadRow596 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_208 : PLift (RowRange 596 hadRow596 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_216 : PLift (RowRange 596 hadRow596 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_224 : PLift (RowRange 596 hadRow596 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_232 : PLift (RowRange 596 hadRow596 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_240 : PLift (RowRange 596 hadRow596 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_248 : PLift (RowRange 596 hadRow596 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_256 : PLift (RowRange 596 hadRow596 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_264 : PLift (RowRange 596 hadRow596 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_272 : PLift (RowRange 596 hadRow596 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_280 : PLift (RowRange 596 hadRow596 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_288 : PLift (RowRange 596 hadRow596 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_296 : PLift (RowRange 596 hadRow596 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_304 : PLift (RowRange 596 hadRow596 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_312 : PLift (RowRange 596 hadRow596 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_320 : PLift (RowRange 596 hadRow596 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_328 : PLift (RowRange 596 hadRow596 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_336 : PLift (RowRange 596 hadRow596 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_344 : PLift (RowRange 596 hadRow596 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_352 : PLift (RowRange 596 hadRow596 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_360 : PLift (RowRange 596 hadRow596 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_368 : PLift (RowRange 596 hadRow596 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_376 : PLift (RowRange 596 hadRow596 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_384 : PLift (RowRange 596 hadRow596 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_392 : PLift (RowRange 596 hadRow596 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_400 : PLift (RowRange 596 hadRow596 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_408 : PLift (RowRange 596 hadRow596 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_416 : PLift (RowRange 596 hadRow596 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_424 : PLift (RowRange 596 hadRow596 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_432 : PLift (RowRange 596 hadRow596 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_440 : PLift (RowRange 596 hadRow596 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_448 : PLift (RowRange 596 hadRow596 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_456 : PLift (RowRange 596 hadRow596 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_464 : PLift (RowRange 596 hadRow596 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_472 : PLift (RowRange 596 hadRow596 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_480 : PLift (RowRange 596 hadRow596 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_488 : PLift (RowRange 596 hadRow596 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_496 : PLift (RowRange 596 hadRow596 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_504 : PLift (RowRange 596 hadRow596 504 512) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_512 : PLift (RowRange 596 hadRow596 512 520) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_520 : PLift (RowRange 596 hadRow596 520 528) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_528 : PLift (RowRange 596 hadRow596 528 536) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_536 : PLift (RowRange 596 hadRow596 536 544) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_544 : PLift (RowRange 596 hadRow596 544 552) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_552 : PLift (RowRange 596 hadRow596 552 560) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_560 : PLift (RowRange 596 hadRow596 560 568) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_568 : PLift (RowRange 596 hadRow596 568 576) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_576 : PLift (RowRange 596 hadRow596 576 584) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_584 : PLift (RowRange 596 hadRow596 584 592) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c596_592 : PLift (RowRange 596 hadRow596 592 596) := ⟨viaCheck (by decide +kernel)⟩

private theorem g596 : gramWitness 596 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c596_0.down c596_8.down) (viaSplit c596_16.down c596_24.down)) (viaSplit (viaSplit c596_32.down c596_40.down) (viaSplit c596_48.down c596_56.down))) (viaSplit (viaSplit (viaSplit c596_64.down c596_72.down) (viaSplit c596_80.down c596_88.down)) (viaSplit (viaSplit c596_96.down c596_104.down) (viaSplit c596_112.down c596_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c596_128.down c596_136.down) (viaSplit c596_144.down c596_152.down)) (viaSplit (viaSplit c596_160.down c596_168.down) (viaSplit c596_176.down c596_184.down))) (viaSplit (viaSplit (viaSplit c596_192.down c596_200.down) (viaSplit c596_208.down c596_216.down)) (viaSplit (viaSplit c596_224.down c596_232.down) (viaSplit c596_240.down c596_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c596_256.down c596_264.down) (viaSplit c596_272.down c596_280.down)) (viaSplit (viaSplit c596_288.down c596_296.down) (viaSplit c596_304.down c596_312.down))) (viaSplit (viaSplit (viaSplit c596_320.down c596_328.down) (viaSplit c596_336.down c596_344.down)) (viaSplit (viaSplit c596_352.down c596_360.down) (viaSplit c596_368.down c596_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c596_384.down c596_392.down) (viaSplit c596_400.down c596_408.down)) (viaSplit (viaSplit c596_416.down c596_424.down) (viaSplit c596_432.down c596_440.down))) (viaSplit (viaSplit (viaSplit c596_448.down c596_456.down) (viaSplit c596_464.down c596_472.down)) (viaSplit (viaSplit c596_480.down c596_488.down) (viaSplit c596_496.down c596_504.down)))))) (viaSplit (viaSplit (viaSplit (viaSplit c596_512.down c596_520.down) (viaSplit c596_528.down c596_536.down)) (viaSplit (viaSplit c596_544.down c596_552.down) (viaSplit c596_560.down c596_568.down))) (viaSplit (viaSplit c596_576.down c596_584.down) c596_592.down)))

private theorem g600 : gramWitness 600 := gram_product (by decide) (by decide) g2 g300

set_option maxRecDepth 16000 in
private def c604_0 : PLift (RowRange 604 hadRow604 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_8 : PLift (RowRange 604 hadRow604 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_16 : PLift (RowRange 604 hadRow604 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_24 : PLift (RowRange 604 hadRow604 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_32 : PLift (RowRange 604 hadRow604 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_40 : PLift (RowRange 604 hadRow604 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_48 : PLift (RowRange 604 hadRow604 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_56 : PLift (RowRange 604 hadRow604 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_64 : PLift (RowRange 604 hadRow604 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_72 : PLift (RowRange 604 hadRow604 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_80 : PLift (RowRange 604 hadRow604 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_88 : PLift (RowRange 604 hadRow604 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_96 : PLift (RowRange 604 hadRow604 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_104 : PLift (RowRange 604 hadRow604 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_112 : PLift (RowRange 604 hadRow604 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_120 : PLift (RowRange 604 hadRow604 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_128 : PLift (RowRange 604 hadRow604 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_136 : PLift (RowRange 604 hadRow604 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_144 : PLift (RowRange 604 hadRow604 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_152 : PLift (RowRange 604 hadRow604 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_160 : PLift (RowRange 604 hadRow604 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_168 : PLift (RowRange 604 hadRow604 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_176 : PLift (RowRange 604 hadRow604 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_184 : PLift (RowRange 604 hadRow604 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_192 : PLift (RowRange 604 hadRow604 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_200 : PLift (RowRange 604 hadRow604 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_208 : PLift (RowRange 604 hadRow604 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_216 : PLift (RowRange 604 hadRow604 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_224 : PLift (RowRange 604 hadRow604 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_232 : PLift (RowRange 604 hadRow604 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_240 : PLift (RowRange 604 hadRow604 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_248 : PLift (RowRange 604 hadRow604 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_256 : PLift (RowRange 604 hadRow604 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_264 : PLift (RowRange 604 hadRow604 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_272 : PLift (RowRange 604 hadRow604 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_280 : PLift (RowRange 604 hadRow604 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_288 : PLift (RowRange 604 hadRow604 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_296 : PLift (RowRange 604 hadRow604 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_304 : PLift (RowRange 604 hadRow604 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_312 : PLift (RowRange 604 hadRow604 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_320 : PLift (RowRange 604 hadRow604 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_328 : PLift (RowRange 604 hadRow604 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_336 : PLift (RowRange 604 hadRow604 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_344 : PLift (RowRange 604 hadRow604 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_352 : PLift (RowRange 604 hadRow604 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_360 : PLift (RowRange 604 hadRow604 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_368 : PLift (RowRange 604 hadRow604 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_376 : PLift (RowRange 604 hadRow604 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_384 : PLift (RowRange 604 hadRow604 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_392 : PLift (RowRange 604 hadRow604 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_400 : PLift (RowRange 604 hadRow604 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_408 : PLift (RowRange 604 hadRow604 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_416 : PLift (RowRange 604 hadRow604 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_424 : PLift (RowRange 604 hadRow604 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_432 : PLift (RowRange 604 hadRow604 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_440 : PLift (RowRange 604 hadRow604 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_448 : PLift (RowRange 604 hadRow604 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_456 : PLift (RowRange 604 hadRow604 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_464 : PLift (RowRange 604 hadRow604 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_472 : PLift (RowRange 604 hadRow604 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_480 : PLift (RowRange 604 hadRow604 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_488 : PLift (RowRange 604 hadRow604 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_496 : PLift (RowRange 604 hadRow604 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_504 : PLift (RowRange 604 hadRow604 504 512) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_512 : PLift (RowRange 604 hadRow604 512 520) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_520 : PLift (RowRange 604 hadRow604 520 528) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_528 : PLift (RowRange 604 hadRow604 528 536) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_536 : PLift (RowRange 604 hadRow604 536 544) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_544 : PLift (RowRange 604 hadRow604 544 552) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_552 : PLift (RowRange 604 hadRow604 552 560) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_560 : PLift (RowRange 604 hadRow604 560 568) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_568 : PLift (RowRange 604 hadRow604 568 576) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_576 : PLift (RowRange 604 hadRow604 576 584) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_584 : PLift (RowRange 604 hadRow604 584 592) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_592 : PLift (RowRange 604 hadRow604 592 600) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c604_600 : PLift (RowRange 604 hadRow604 600 604) := ⟨viaCheck (by decide +kernel)⟩

private theorem g604 : gramWitness 604 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c604_0.down c604_8.down) (viaSplit c604_16.down c604_24.down)) (viaSplit (viaSplit c604_32.down c604_40.down) (viaSplit c604_48.down c604_56.down))) (viaSplit (viaSplit (viaSplit c604_64.down c604_72.down) (viaSplit c604_80.down c604_88.down)) (viaSplit (viaSplit c604_96.down c604_104.down) (viaSplit c604_112.down c604_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c604_128.down c604_136.down) (viaSplit c604_144.down c604_152.down)) (viaSplit (viaSplit c604_160.down c604_168.down) (viaSplit c604_176.down c604_184.down))) (viaSplit (viaSplit (viaSplit c604_192.down c604_200.down) (viaSplit c604_208.down c604_216.down)) (viaSplit (viaSplit c604_224.down c604_232.down) (viaSplit c604_240.down c604_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c604_256.down c604_264.down) (viaSplit c604_272.down c604_280.down)) (viaSplit (viaSplit c604_288.down c604_296.down) (viaSplit c604_304.down c604_312.down))) (viaSplit (viaSplit (viaSplit c604_320.down c604_328.down) (viaSplit c604_336.down c604_344.down)) (viaSplit (viaSplit c604_352.down c604_360.down) (viaSplit c604_368.down c604_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c604_384.down c604_392.down) (viaSplit c604_400.down c604_408.down)) (viaSplit (viaSplit c604_416.down c604_424.down) (viaSplit c604_432.down c604_440.down))) (viaSplit (viaSplit (viaSplit c604_448.down c604_456.down) (viaSplit c604_464.down c604_472.down)) (viaSplit (viaSplit c604_480.down c604_488.down) (viaSplit c604_496.down c604_504.down)))))) (viaSplit (viaSplit (viaSplit (viaSplit c604_512.down c604_520.down) (viaSplit c604_528.down c604_536.down)) (viaSplit (viaSplit c604_544.down c604_552.down) (viaSplit c604_560.down c604_568.down))) (viaSplit (viaSplit c604_576.down c604_584.down) (viaSplit c604_592.down c604_600.down))))

private theorem g608 : gramWitness 608 := gram_product (by decide) (by decide) g2 g304

set_option maxRecDepth 16000 in
private def c612_0 : PLift (RowRange 612 hadRow612 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_8 : PLift (RowRange 612 hadRow612 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_16 : PLift (RowRange 612 hadRow612 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_24 : PLift (RowRange 612 hadRow612 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_32 : PLift (RowRange 612 hadRow612 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_40 : PLift (RowRange 612 hadRow612 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_48 : PLift (RowRange 612 hadRow612 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_56 : PLift (RowRange 612 hadRow612 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_64 : PLift (RowRange 612 hadRow612 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_72 : PLift (RowRange 612 hadRow612 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_80 : PLift (RowRange 612 hadRow612 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_88 : PLift (RowRange 612 hadRow612 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_96 : PLift (RowRange 612 hadRow612 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_104 : PLift (RowRange 612 hadRow612 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_112 : PLift (RowRange 612 hadRow612 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_120 : PLift (RowRange 612 hadRow612 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_128 : PLift (RowRange 612 hadRow612 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_136 : PLift (RowRange 612 hadRow612 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_144 : PLift (RowRange 612 hadRow612 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_152 : PLift (RowRange 612 hadRow612 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_160 : PLift (RowRange 612 hadRow612 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_168 : PLift (RowRange 612 hadRow612 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_176 : PLift (RowRange 612 hadRow612 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_184 : PLift (RowRange 612 hadRow612 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_192 : PLift (RowRange 612 hadRow612 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_200 : PLift (RowRange 612 hadRow612 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_208 : PLift (RowRange 612 hadRow612 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_216 : PLift (RowRange 612 hadRow612 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_224 : PLift (RowRange 612 hadRow612 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_232 : PLift (RowRange 612 hadRow612 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_240 : PLift (RowRange 612 hadRow612 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_248 : PLift (RowRange 612 hadRow612 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_256 : PLift (RowRange 612 hadRow612 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_264 : PLift (RowRange 612 hadRow612 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_272 : PLift (RowRange 612 hadRow612 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_280 : PLift (RowRange 612 hadRow612 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_288 : PLift (RowRange 612 hadRow612 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_296 : PLift (RowRange 612 hadRow612 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_304 : PLift (RowRange 612 hadRow612 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_312 : PLift (RowRange 612 hadRow612 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_320 : PLift (RowRange 612 hadRow612 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_328 : PLift (RowRange 612 hadRow612 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_336 : PLift (RowRange 612 hadRow612 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_344 : PLift (RowRange 612 hadRow612 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_352 : PLift (RowRange 612 hadRow612 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_360 : PLift (RowRange 612 hadRow612 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_368 : PLift (RowRange 612 hadRow612 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_376 : PLift (RowRange 612 hadRow612 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_384 : PLift (RowRange 612 hadRow612 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_392 : PLift (RowRange 612 hadRow612 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_400 : PLift (RowRange 612 hadRow612 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_408 : PLift (RowRange 612 hadRow612 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_416 : PLift (RowRange 612 hadRow612 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_424 : PLift (RowRange 612 hadRow612 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_432 : PLift (RowRange 612 hadRow612 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_440 : PLift (RowRange 612 hadRow612 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_448 : PLift (RowRange 612 hadRow612 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_456 : PLift (RowRange 612 hadRow612 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_464 : PLift (RowRange 612 hadRow612 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_472 : PLift (RowRange 612 hadRow612 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_480 : PLift (RowRange 612 hadRow612 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_488 : PLift (RowRange 612 hadRow612 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_496 : PLift (RowRange 612 hadRow612 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_504 : PLift (RowRange 612 hadRow612 504 512) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_512 : PLift (RowRange 612 hadRow612 512 520) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_520 : PLift (RowRange 612 hadRow612 520 528) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_528 : PLift (RowRange 612 hadRow612 528 536) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_536 : PLift (RowRange 612 hadRow612 536 544) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_544 : PLift (RowRange 612 hadRow612 544 552) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_552 : PLift (RowRange 612 hadRow612 552 560) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_560 : PLift (RowRange 612 hadRow612 560 568) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_568 : PLift (RowRange 612 hadRow612 568 576) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_576 : PLift (RowRange 612 hadRow612 576 584) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_584 : PLift (RowRange 612 hadRow612 584 592) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_592 : PLift (RowRange 612 hadRow612 592 600) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_600 : PLift (RowRange 612 hadRow612 600 608) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c612_608 : PLift (RowRange 612 hadRow612 608 612) := ⟨viaCheck (by decide +kernel)⟩

private theorem g612 : gramWitness 612 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c612_0.down c612_8.down) (viaSplit c612_16.down c612_24.down)) (viaSplit (viaSplit c612_32.down c612_40.down) (viaSplit c612_48.down c612_56.down))) (viaSplit (viaSplit (viaSplit c612_64.down c612_72.down) (viaSplit c612_80.down c612_88.down)) (viaSplit (viaSplit c612_96.down c612_104.down) (viaSplit c612_112.down c612_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c612_128.down c612_136.down) (viaSplit c612_144.down c612_152.down)) (viaSplit (viaSplit c612_160.down c612_168.down) (viaSplit c612_176.down c612_184.down))) (viaSplit (viaSplit (viaSplit c612_192.down c612_200.down) (viaSplit c612_208.down c612_216.down)) (viaSplit (viaSplit c612_224.down c612_232.down) (viaSplit c612_240.down c612_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c612_256.down c612_264.down) (viaSplit c612_272.down c612_280.down)) (viaSplit (viaSplit c612_288.down c612_296.down) (viaSplit c612_304.down c612_312.down))) (viaSplit (viaSplit (viaSplit c612_320.down c612_328.down) (viaSplit c612_336.down c612_344.down)) (viaSplit (viaSplit c612_352.down c612_360.down) (viaSplit c612_368.down c612_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c612_384.down c612_392.down) (viaSplit c612_400.down c612_408.down)) (viaSplit (viaSplit c612_416.down c612_424.down) (viaSplit c612_432.down c612_440.down))) (viaSplit (viaSplit (viaSplit c612_448.down c612_456.down) (viaSplit c612_464.down c612_472.down)) (viaSplit (viaSplit c612_480.down c612_488.down) (viaSplit c612_496.down c612_504.down)))))) (viaSplit (viaSplit (viaSplit (viaSplit c612_512.down c612_520.down) (viaSplit c612_528.down c612_536.down)) (viaSplit (viaSplit c612_544.down c612_552.down) (viaSplit c612_560.down c612_568.down))) (viaSplit (viaSplit (viaSplit c612_576.down c612_584.down) (viaSplit c612_592.down c612_600.down)) c612_608.down)))

private theorem g616 : gramWitness 616 := gram_product (by decide) (by decide) g2 g308

private theorem g620 : gramWitness 620 := fromColumns (PaleyHadamard.typeI 619 ((isPrimePow_nat_iff _).mpr ⟨619, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g624 : gramWitness 624 := gram_product (by decide) (by decide) g2 g312

private theorem g628 : gramWitness 628 := fromColumns (PaleyHadamard.typeII 313 ((isPrimePow_nat_iff _).mpr ⟨313, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g632 : gramWitness 632 := gram_product (by decide) (by decide) g2 g316

private theorem g636 : gramWitness 636 := fromColumns (PaleyHadamard.typeII 317 ((isPrimePow_nat_iff _).mpr ⟨317, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g640 : gramWitness 640 := gram_product (by decide) (by decide) g2 g320

private theorem g644 : gramWitness 644 := fromColumns (PaleyHadamard.typeI 643 ((isPrimePow_nat_iff _).mpr ⟨643, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g648 : gramWitness 648 := gram_product (by decide) (by decide) g2 g324

set_option maxRecDepth 16000 in
private def c652_0 : PLift (RowRange 652 hadRow652 0 8) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_8 : PLift (RowRange 652 hadRow652 8 16) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_16 : PLift (RowRange 652 hadRow652 16 24) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_24 : PLift (RowRange 652 hadRow652 24 32) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_32 : PLift (RowRange 652 hadRow652 32 40) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_40 : PLift (RowRange 652 hadRow652 40 48) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_48 : PLift (RowRange 652 hadRow652 48 56) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_56 : PLift (RowRange 652 hadRow652 56 64) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_64 : PLift (RowRange 652 hadRow652 64 72) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_72 : PLift (RowRange 652 hadRow652 72 80) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_80 : PLift (RowRange 652 hadRow652 80 88) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_88 : PLift (RowRange 652 hadRow652 88 96) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_96 : PLift (RowRange 652 hadRow652 96 104) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_104 : PLift (RowRange 652 hadRow652 104 112) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_112 : PLift (RowRange 652 hadRow652 112 120) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_120 : PLift (RowRange 652 hadRow652 120 128) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_128 : PLift (RowRange 652 hadRow652 128 136) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_136 : PLift (RowRange 652 hadRow652 136 144) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_144 : PLift (RowRange 652 hadRow652 144 152) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_152 : PLift (RowRange 652 hadRow652 152 160) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_160 : PLift (RowRange 652 hadRow652 160 168) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_168 : PLift (RowRange 652 hadRow652 168 176) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_176 : PLift (RowRange 652 hadRow652 176 184) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_184 : PLift (RowRange 652 hadRow652 184 192) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_192 : PLift (RowRange 652 hadRow652 192 200) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_200 : PLift (RowRange 652 hadRow652 200 208) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_208 : PLift (RowRange 652 hadRow652 208 216) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_216 : PLift (RowRange 652 hadRow652 216 224) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_224 : PLift (RowRange 652 hadRow652 224 232) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_232 : PLift (RowRange 652 hadRow652 232 240) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_240 : PLift (RowRange 652 hadRow652 240 248) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_248 : PLift (RowRange 652 hadRow652 248 256) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_256 : PLift (RowRange 652 hadRow652 256 264) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_264 : PLift (RowRange 652 hadRow652 264 272) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_272 : PLift (RowRange 652 hadRow652 272 280) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_280 : PLift (RowRange 652 hadRow652 280 288) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_288 : PLift (RowRange 652 hadRow652 288 296) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_296 : PLift (RowRange 652 hadRow652 296 304) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_304 : PLift (RowRange 652 hadRow652 304 312) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_312 : PLift (RowRange 652 hadRow652 312 320) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_320 : PLift (RowRange 652 hadRow652 320 328) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_328 : PLift (RowRange 652 hadRow652 328 336) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_336 : PLift (RowRange 652 hadRow652 336 344) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_344 : PLift (RowRange 652 hadRow652 344 352) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_352 : PLift (RowRange 652 hadRow652 352 360) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_360 : PLift (RowRange 652 hadRow652 360 368) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_368 : PLift (RowRange 652 hadRow652 368 376) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_376 : PLift (RowRange 652 hadRow652 376 384) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_384 : PLift (RowRange 652 hadRow652 384 392) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_392 : PLift (RowRange 652 hadRow652 392 400) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_400 : PLift (RowRange 652 hadRow652 400 408) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_408 : PLift (RowRange 652 hadRow652 408 416) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_416 : PLift (RowRange 652 hadRow652 416 424) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_424 : PLift (RowRange 652 hadRow652 424 432) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_432 : PLift (RowRange 652 hadRow652 432 440) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_440 : PLift (RowRange 652 hadRow652 440 448) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_448 : PLift (RowRange 652 hadRow652 448 456) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_456 : PLift (RowRange 652 hadRow652 456 464) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_464 : PLift (RowRange 652 hadRow652 464 472) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_472 : PLift (RowRange 652 hadRow652 472 480) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_480 : PLift (RowRange 652 hadRow652 480 488) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_488 : PLift (RowRange 652 hadRow652 488 496) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_496 : PLift (RowRange 652 hadRow652 496 504) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_504 : PLift (RowRange 652 hadRow652 504 512) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_512 : PLift (RowRange 652 hadRow652 512 520) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_520 : PLift (RowRange 652 hadRow652 520 528) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_528 : PLift (RowRange 652 hadRow652 528 536) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_536 : PLift (RowRange 652 hadRow652 536 544) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_544 : PLift (RowRange 652 hadRow652 544 552) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_552 : PLift (RowRange 652 hadRow652 552 560) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_560 : PLift (RowRange 652 hadRow652 560 568) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_568 : PLift (RowRange 652 hadRow652 568 576) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_576 : PLift (RowRange 652 hadRow652 576 584) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_584 : PLift (RowRange 652 hadRow652 584 592) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_592 : PLift (RowRange 652 hadRow652 592 600) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_600 : PLift (RowRange 652 hadRow652 600 608) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_608 : PLift (RowRange 652 hadRow652 608 616) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_616 : PLift (RowRange 652 hadRow652 616 624) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_624 : PLift (RowRange 652 hadRow652 624 632) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_632 : PLift (RowRange 652 hadRow652 632 640) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_640 : PLift (RowRange 652 hadRow652 640 648) := ⟨viaCheck (by decide +kernel)⟩

set_option maxRecDepth 16000 in
private def c652_648 : PLift (RowRange 652 hadRow652 648 652) := ⟨viaCheck (by decide +kernel)⟩

private theorem g652 : gramWitness 652 := viaRows _ _ (by decide) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c652_0.down c652_8.down) (viaSplit c652_16.down c652_24.down)) (viaSplit (viaSplit c652_32.down c652_40.down) (viaSplit c652_48.down c652_56.down))) (viaSplit (viaSplit (viaSplit c652_64.down c652_72.down) (viaSplit c652_80.down c652_88.down)) (viaSplit (viaSplit c652_96.down c652_104.down) (viaSplit c652_112.down c652_120.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c652_128.down c652_136.down) (viaSplit c652_144.down c652_152.down)) (viaSplit (viaSplit c652_160.down c652_168.down) (viaSplit c652_176.down c652_184.down))) (viaSplit (viaSplit (viaSplit c652_192.down c652_200.down) (viaSplit c652_208.down c652_216.down)) (viaSplit (viaSplit c652_224.down c652_232.down) (viaSplit c652_240.down c652_248.down))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c652_256.down c652_264.down) (viaSplit c652_272.down c652_280.down)) (viaSplit (viaSplit c652_288.down c652_296.down) (viaSplit c652_304.down c652_312.down))) (viaSplit (viaSplit (viaSplit c652_320.down c652_328.down) (viaSplit c652_336.down c652_344.down)) (viaSplit (viaSplit c652_352.down c652_360.down) (viaSplit c652_368.down c652_376.down)))) (viaSplit (viaSplit (viaSplit (viaSplit c652_384.down c652_392.down) (viaSplit c652_400.down c652_408.down)) (viaSplit (viaSplit c652_416.down c652_424.down) (viaSplit c652_432.down c652_440.down))) (viaSplit (viaSplit (viaSplit c652_448.down c652_456.down) (viaSplit c652_464.down c652_472.down)) (viaSplit (viaSplit c652_480.down c652_488.down) (viaSplit c652_496.down c652_504.down)))))) (viaSplit (viaSplit (viaSplit (viaSplit (viaSplit c652_512.down c652_520.down) (viaSplit c652_528.down c652_536.down)) (viaSplit (viaSplit c652_544.down c652_552.down) (viaSplit c652_560.down c652_568.down))) (viaSplit (viaSplit (viaSplit c652_576.down c652_584.down) (viaSplit c652_592.down c652_600.down)) (viaSplit (viaSplit c652_608.down c652_616.down) (viaSplit c652_624.down c652_632.down)))) (viaSplit c652_640.down c652_648.down)))

private theorem g656 : gramWitness 656 := gram_product (by decide) (by decide) g2 g328

private theorem g660 : gramWitness 660 := fromColumns (PaleyHadamard.typeI 659 ((isPrimePow_nat_iff _).mpr ⟨659, 1, by norm_num, by decide, by decide⟩) (by decide))

private theorem g664 : gramWitness 664 := gram_product (by decide) (by decide) g2 g332

set_option maxHeartbeats 6000000 in
private theorem below (k : ℕ) (hk : k ≤ 166) : ∃ M : Matrix (Fin (4*k)) (Fin (4*k)) ℝ, Hadamard.IsHadamard M := by
  interval_cases k

  · exact Hadamard.exists_hadamard_zero

  · exact gram_to_det g4

  · exact gram_to_det g8

  · exact gram_to_det g12

  · exact gram_to_det g16

  · exact gram_to_det g20

  · exact gram_to_det g24

  · exact gram_to_det g28

  · exact gram_to_det g32

  · exact gram_to_det g36

  · exact gram_to_det g40

  · exact gram_to_det g44

  · exact gram_to_det g48

  · exact gram_to_det g52

  · exact gram_to_det g56

  · exact gram_to_det g60

  · exact gram_to_det g64

  · exact gram_to_det g68

  · exact gram_to_det g72

  · exact gram_to_det g76

  · exact gram_to_det g80

  · exact gram_to_det g84

  · exact gram_to_det g88

  · exact gram_to_det g92

  · exact gram_to_det g96

  · exact gram_to_det g100

  · exact gram_to_det g104

  · exact gram_to_det g108

  · exact gram_to_det g112

  · exact gram_to_det g116

  · exact gram_to_det g120

  · exact gram_to_det g124

  · exact gram_to_det g128

  · exact gram_to_det g132

  · exact gram_to_det g136

  · exact gram_to_det g140

  · exact gram_to_det g144

  · exact gram_to_det g148

  · exact gram_to_det g152

  · exact gram_to_det g156

  · exact gram_to_det g160

  · exact gram_to_det g164

  · exact gram_to_det g168

  · exact gram_to_det g172

  · exact gram_to_det g176

  · exact gram_to_det g180

  · exact gram_to_det g184

  · exact gram_to_det g188

  · exact gram_to_det g192

  · exact gram_to_det g196

  · exact gram_to_det g200

  · exact gram_to_det g204

  · exact gram_to_det g208

  · exact gram_to_det g212

  · exact gram_to_det g216

  · exact gram_to_det g220

  · exact gram_to_det g224

  · exact gram_to_det g228

  · exact gram_to_det g232

  · exact gram_to_det g236

  · exact gram_to_det g240

  · exact gram_to_det g244

  · exact gram_to_det g248

  · exact gram_to_det g252

  · exact gram_to_det g256

  · exact gram_to_det g260

  · exact gram_to_det g264

  · exact gram_to_det g268

  · exact gram_to_det g272

  · exact gram_to_det g276

  · exact gram_to_det g280

  · exact gram_to_det g284

  · exact gram_to_det g288

  · exact gram_to_det g292

  · exact gram_to_det g296

  · exact gram_to_det g300

  · exact gram_to_det g304

  · exact gram_to_det g308

  · exact gram_to_det g312

  · exact gram_to_det g316

  · exact gram_to_det g320

  · exact gram_to_det g324

  · exact gram_to_det g328

  · exact gram_to_det g332

  · exact gram_to_det g336

  · exact gram_to_det g340

  · exact gram_to_det g344

  · exact gram_to_det g348

  · exact gram_to_det g352

  · exact gram_to_det g356

  · exact gram_to_det g360

  · exact gram_to_det g364

  · exact gram_to_det g368

  · exact gram_to_det g372

  · exact gram_to_det g376

  · exact gram_to_det g380

  · exact gram_to_det g384

  · exact gram_to_det g388

  · exact gram_to_det g392

  · exact gram_to_det g396

  · exact gram_to_det g400

  · exact gram_to_det g404

  · exact gram_to_det g408

  · exact gram_to_det g412

  · exact gram_to_det g416

  · exact gram_to_det g420

  · exact gram_to_det g424

  · exact gram_to_det g428

  · exact gram_to_det g432

  · exact gram_to_det g436

  · exact gram_to_det g440

  · exact gram_to_det g444

  · exact gram_to_det g448

  · exact gram_to_det g452

  · exact gram_to_det g456

  · exact gram_to_det g460

  · exact gram_to_det g464

  · exact gram_to_det g468

  · exact gram_to_det g472

  · exact gram_to_det g476

  · exact gram_to_det g480

  · exact gram_to_det g484

  · exact gram_to_det g488

  · exact gram_to_det g492

  · exact gram_to_det g496

  · exact gram_to_det g500

  · exact gram_to_det g504

  · exact gram_to_det g508

  · exact gram_to_det g512

  · exact gram_to_det g516

  · exact gram_to_det g520

  · exact gram_to_det g524

  · exact gram_to_det g528

  · exact gram_to_det g532

  · exact gram_to_det g536

  · exact gram_to_det g540

  · exact gram_to_det g544

  · exact gram_to_det g548

  · exact gram_to_det g552

  · exact gram_to_det g556

  · exact gram_to_det g560

  · exact gram_to_det g564

  · exact gram_to_det g568

  · exact gram_to_det g572

  · exact gram_to_det g576

  · exact gram_to_det g580

  · exact gram_to_det g584

  · exact gram_to_det g588

  · exact gram_to_det g592

  · exact gram_to_det g596

  · exact gram_to_det g600

  · exact gram_to_det g604

  · exact gram_to_det g608

  · exact gram_to_det g612

  · exact gram_to_det g616

  · exact gram_to_det g620

  · exact gram_to_det g624

  · exact gram_to_det g628

  · exact gram_to_det g632

  · exact gram_to_det g636

  · exact gram_to_det g640

  · exact gram_to_det g644

  · exact gram_to_det g648

  · exact gram_to_det g652

  · exact gram_to_det g656

  · exact gram_to_det g660

  · exact gram_to_det g664

private theorem small_orders : 668 ≤ Hadamard.hadamardConstant := by
  have h := constant_of_orders 166 below
  norm_num at h ⊢
  exact h

end HadamardBits

/-!
# A cyclic proof of the order-668 Hadamard matrix

This is the width-four bordered array from Levent Alpöge, Philippe Voinov, and
Saul Reynolds-Haertle, *Hadamard matrices of orders 668, 716, 892, 1132, 1244, 1388,
1436, 1676, 1772, 1916, 1948 and 1964*, §5.2 (https://hexagonmath.org/2611.00637v1).
The seeds and the constant borders are extracted from their published sign matrix.
-/

namespace Hadamard668Cyclic

open scoped BigOperators Matrix
open Finset

section Cyclic

variable {G : Type*} [AddCommGroup G] [Fintype G]

private def corr (a b : G → ℤ) (d : G) : ℤ := ∑ x, a x * b (x + d)

private def reflect (u : G) (a : G → ℤ) (x : G) : ℤ := a (u - x)

private theorem corr_shift (a b : G → ℤ) (r s : G) :
    (∑ x, a (x + r) * b (x + s)) = corr a b (s - r) := by
  calc
    _ = ∑ x, a (x + r) * b ((x + r) + (s - r)) := by
      apply sum_congr rfl
      intro x _
      have hh : x + s = x + r + (s - r) := by abel
      rw [hh]
    _ = _ := by
      simpa only [corr, Equiv.coe_addRight] using
        (Equiv.sum_comp (Equiv.addRight r : G ≃ G) (fun x => a x * b (x + (s - r))))

private theorem corr_swap (a b : G → ℤ) (d : G) :
    corr a b d = corr b a (-d) := by
  simpa only [corr, add_zero, zero_sub, mul_comm] using corr_shift b a d 0

private theorem corr_reflect_reflect (u : G) (a b : G → ℤ) (d : G) :
    corr (reflect u a) (reflect u b) d = corr a b (-d) := by
  calc
    _ = ∑ x, a (u - x) * b ((u - x) + -d) := by
      unfold corr reflect
      apply sum_congr rfl
      intro x _
      have h : u - (x + d) = u - x + -d := by abel
      rw [h]
    _ = _ := by
      simpa only [corr, Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft u : G ≃ G) (fun x => a x * b (x + -d)))

private theorem corr_reflect_right (u : G) (a b : G → ℤ) (d : G) :
    corr a (reflect u b) d = corr b (reflect u a) d := by
  calc
    _ = ∑ x, b ((u - d) - x) * a (u - (((u - d) - x) + d)) := by
      unfold corr reflect
      apply sum_congr rfl
      intro x _
      have h₁ : u - (x + d) = (u - d) - x := by abel
      have h₂ : u - (((u - d) - x) + d) = x := by abel
      rw [h₁, h₂, mul_comm]
    _ = _ := by
      simpa only [corr, reflect, Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft (u - d) : G ≃ G)
          (fun x => b x * a (u - (x + d))))

@[simp] private theorem corr_neg_left (a b : G → ℤ) (d : G) :
    corr (-a) b d = -corr a b d := by simp only [corr, Pi.neg_apply, neg_mul, sum_neg_distrib]

@[simp] private theorem corr_neg_right (a b : G → ℤ) (d : G) :
    corr a (-b) d = -corr a b d := by simp only [corr, Pi.neg_apply, mul_neg, sum_neg_distrib]

@[simp] private theorem corr_self_neg (a : G → ℤ) (d : G) :
    corr a a (-d) = corr a a d := (corr_swap a a d).symm

@[simp] private theorem corr_reflect_self (u : G) (a : G → ℤ) (d : G) :
    corr (reflect u a) (reflect u a) d = corr a a d := by
  rw [corr_reflect_reflect, corr_self_neg]

private def core (u : G) (a b c d : G → ℤ) : Fin 4 → Fin 4 → G → ℤ :=
  ![![a, b, c, d],
    ![-b, a, reflect u d, -reflect u c],
    ![-c, -reflect u d, a, reflect u b],
    ![-d, reflect u c, -reflect u b, a]]

private def offset (g j : Fin 4) (x : G) : G := if g = j then -x else x

private def autoSum (a b c d : G → ℤ) (x : G) : ℤ :=
  corr a a x + corr b b x + corr c c x + corr d d x

@[simp] private theorem autoSum_neg (a b c d : G → ℤ) (x : G) :
    autoSum a b c d (-x) = autoSum a b c d x := by
  simp only [autoSum, corr_self_neg]

private theorem self_core (u : G) (a b c d : G → ℤ) (g : Fin 4) (r s : G) :
    (∑ j : Fin 4, ∑ x, core u a b c d g j (x + offset g j r) *
      core u a b c d g j (x + offset g j s)) = autoSum a b c d (s - r) := by
  simp only [corr_shift]
  fin_cases g <;> simp [core, offset, Fin.sum_univ_succ, autoSum]
  all_goals
    rw [show -s + r = -(s - r) by abel, corr_self_neg]
    ac_rfl

private theorem different_core_lt (u : G) (a b c d : G → ℤ) (g h : Fin 4)
    (hh : g < h) (r s : G) :
    (∑ j : Fin 4, ∑ x, core u a b c d g j (x + offset g j r) *
      core u a b c d h j (x + offset h j s)) = 0 := by
  simp only [corr_shift]
  have hs : (-s) - r = -(s + r) := by abel
  fin_cases g <;> fin_cases h
  all_goals try (exfalso; exact (by decide : ¬ _) hh)
  all_goals simp [core, offset, Fin.sum_univ_succ]
  all_goals rw [hs]
  · rw [← corr_swap a b (s + r), corr_reflect_right u c d (s - r)]
    abel
  · rw [← corr_swap a c (s + r), corr_reflect_right u b d (s - r)]
    abel
  · rw [← corr_swap a d (s + r), corr_reflect_right u b c (s - r)]
    abel
  · rw [← corr_swap a (reflect u d) (s + r), corr_reflect_reflect, ← corr_swap b c (s - r)]
    abel
  · rw [← corr_swap a (reflect u c) (s + r), corr_reflect_reflect, ← corr_swap b d (s - r)]
    abel
  · rw [← corr_swap a (reflect u b) (s + r), corr_reflect_reflect, ← corr_swap c d (s - r)]
    abel

private theorem different_core (u : G) (a b c d : G → ℤ) (g h : Fin 4)
    (hh : g ≠ h) (r s : G) :
    (∑ j : Fin 4, ∑ x, core u a b c d g j (x + offset g j r) *
      core u a b c d h j (x + offset h j s)) = 0 := by
  rcases lt_or_gt_of_ne hh with hlt | hgt
  · exact different_core_lt u a b c d g h hlt r s
  · simpa only [mul_comm] using different_core_lt u a b c d h g hgt s r

private theorem sum_reflect (u : G) (a : G → ℤ) :
    (∑ x, reflect u a x) = ∑ x, a x := by
  simpa only [reflect, Equiv.subLeft_apply] using
    (Equiv.sum_comp (Equiv.subLeft u : G ≃ G) a)

private theorem core_sum (u : G) (a b c d : G → ℤ)
    (ha : ∑ x, a x = 2) (hb : ∑ x, b x = 0) (hc : ∑ x, c x = 0) (hd : ∑ x, d x = 0)
    (g j : Fin 4) (r : G) :
    (∑ x, core u a b c d g j (x + offset g j r)) = if g = j then 2 else 0 := by
  have s := Equiv.sum_comp (Equiv.addRight (offset g j r) : G ≃ G) (core u a b c d g j)
  simp only [Equiv.coe_addRight] at s
  rw [s]
  fin_cases g <;> fin_cases j <;> simp [core, sum_reflect, ha, hb, hc, hd]

private def signs (a : G → ℤ) : Prop := ∀ x, a x = 1 ∨ a x = -1

omit [AddCommGroup G] [Fintype G] in
private theorem signs_neg {a : G → ℤ} (ha : signs a) : signs (-a) := by
  intro x
  rcases ha x with h | h <;> simp [h]

omit [Fintype G] in
private theorem signs_reflect (u : G) {a : G → ℤ} (h : signs a) : signs (reflect u a) :=
  fun x => h (u - x)

omit [Fintype G] in
private theorem core_signs (u : G) (a b c d : G → ℤ)
    (ha : signs a) (hb : signs b) (hc : signs c) (hd : signs d) (g j : Fin 4) :
    signs (core u a b c d g j) := by
  fin_cases g <;> fin_cases j <;> simp only [core, Fin.cons_zero, Fin.cons_succ] <;>
    solve_by_elim [signs_neg, signs_reflect]

end Cyclic


private abbrev Cycle := ZMod 166
private abbrev Index := Fin 4 ⊕ (Fin 4 × Cycle)

private def bitSign (word : ℕ) (x : Cycle) : ℤ :=
  if word.testBit x.val then -1 else 1

private def A := bitSign 0x2da6ac01d3b04261b92abdb4d5a03a71f7b3c8daa8
private def B := bitSign 0x3c44a12dbf34aed56707c0776b5a481495daace0f8
private def C := bitSign 0x3d4e9ee0dd9016ef23ce38562c23e44402dde479c7
private def D := bitSign 0x759ed167e302cd3b3b9af14c25d3038059a367735

private def corner : Fin 4 → Fin 4 → ℤ :=
  ![![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1], ![-1, -1, -1, -1]]

private def top : Fin 4 → Fin 4 → ℤ :=
  ![![-1, -1, -1, 1], ![-1, -1, 1, -1], ![-1, 1, -1, -1], ![1, -1, -1, -1]]

private def left : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 1, -1], ![-1, -1, 1, -1], ![-1, 1, -1, -1], ![1, -1, -1, -1]]

private def entry : Index → Index → ℤ
  | .inl i, .inl j => corner i j
  | .inl i, .inr (j, _) => top i j
  | .inr (i, _), .inl j => left i j
  | .inr (i, r), .inr (j, x) => core (-2 : Cycle) A B C D i j (x + offset i j r)

private theorem word_signs (word : ℕ) : signs (bitSign word) := by
  intro x
  unfold bitSign
  split <;> simp

private theorem entry_signs (i j : Index) : entry i j = 1 ∨ entry i j = -1 := by
  rcases i with i | ⟨i, r⟩ <;> rcases j with j | ⟨j, x⟩
  · change corner i j = 1 ∨ corner i j = -1
    revert i j
    decide +kernel
  · change top i j = 1 ∨ top i j = -1
    revert i j
    decide +kernel
  · change left i j = 1 ∨ left i j = -1
    revert i j
    decide +kernel
  · exact core_signs (-2) A B C D (word_signs _) (word_signs _) (word_signs _)
      (word_signs _) i j (x + offset i j r)

private theorem seed_sum_A : (∑ x, A x) = 2 := by decide +kernel
private theorem seed_sum_B : (∑ x, B x) = 0 := by decide +kernel
private theorem seed_sum_C : (∑ x, C x) = 0 := by decide +kernel
private theorem seed_sum_D : (∑ x, D x) = 0 := by decide +kernel

private theorem corner_dot (i j : Fin 4) :
    (∑ x, corner i x * corner j x) = if i = j then 4 else 0 := by revert i j; decide +kernel

private theorem top_dot (i j : Fin 4) :
    (∑ x, top i x * top j x) = if i = j then 4 else 0 := by revert i j; decide +kernel

private theorem left_dot (i j : Fin 4) :
    (∑ x, left i x * left j x) = if i = j then 4 else 0 := by revert i j; decide +kernel

private theorem corner_left_dot (i j : Fin 4) :
    (∑ x, corner i x * left j x) = -2 * top i j := by revert i j; decide +kernel

private def Checked (l width : ℕ) : Prop :=
  ∀ t : Fin width, autoSum A B C D ((l + t.val + 1 : ℕ) : Cycle) = -4

private theorem checked_of_le {l width i : ℕ} (h : Checked l width) (h₁ : l ≤ i)
    (h₂ : i < l + width) : autoSum A B C D ((i + 1 : ℕ) : Cycle) = -4 := by
  have h' := h ⟨i - l, by omega⟩
  change autoSum A B C D ((l + (i - l) + 1 : ℕ) : Cycle) = -4 at h'
  rwa [show l + (i - l) = i by omega] at h'

-- One certificate per undirected nonzero shift of the cyclic seeds.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified0 : Checked 0 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified8 : Checked 8 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified16 : Checked 16 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified24 : Checked 24 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified32 : Checked 32 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified40 : Checked 40 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified48 : Checked 48 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified56 : Checked 56 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified64 : Checked 64 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified72 : Checked 72 8 := by
  unfold Checked
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem certified80 : Checked 80 3 := by
  unfold Checked
  decide +kernel

private theorem autocorr_small (i : ℕ) (hi : i < 83) :
    autoSum A B C D ((i + 1 : ℕ) : Cycle) = -4 := by
  by_cases h0 : i < 8
  · exact checked_of_le certified0 (by omega) (by omega)
  by_cases h8 : i < 16
  · exact checked_of_le certified8 (by omega) (by omega)
  by_cases h16 : i < 24
  · exact checked_of_le certified16 (by omega) (by omega)
  by_cases h24 : i < 32
  · exact checked_of_le certified24 (by omega) (by omega)
  by_cases h32 : i < 40
  · exact checked_of_le certified32 (by omega) (by omega)
  by_cases h40 : i < 48
  · exact checked_of_le certified40 (by omega) (by omega)
  by_cases h48 : i < 56
  · exact checked_of_le certified48 (by omega) (by omega)
  by_cases h56 : i < 64
  · exact checked_of_le certified56 (by omega) (by omega)
  by_cases h64 : i < 72
  · exact checked_of_le certified64 (by omega) (by omega)
  by_cases h72 : i < 80
  · exact checked_of_le certified72 (by omega) (by omega)
  exact checked_of_le certified80 (by omega) (by omega)

private theorem autocorr_nonzero (t : Cycle) (ht : t ≠ 0) : autoSum A B C D t = -4 := by
  have small (v : Cycle) (hv : v ≠ 0) (hsmall : v.val ≤ 83) : autoSum A B C D v = -4 := by
    have hpos : 0 < v.val := Nat.pos_of_ne_zero (fun h => hv ((ZMod.val_eq_zero v).mp h))
    have he := autocorr_small (v.val - 1) (by omega)
    rwa [show v.val - 1 + 1 = v.val by omega, ZMod.natCast_zmod_val] at he
  by_cases h : t.val ≤ 83
  · exact small t ht h
  · let _ : NeZero t := ⟨ht⟩
    have hneg : (-t).val ≤ 83 := by
      rw [ZMod.val_neg_of_ne_zero]
      omega
    simpa only [autoSum_neg] using small (-t) (neg_ne_zero.mpr ht) hneg

private theorem top_lower_dot (i j : Fin 4) (r : Cycle) :
    (∑ x : Index, entry (.inl i) x * entry (.inr (j, r)) x) = 0 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, entry]
  rw [corner_left_dot]
  simp_rw [← mul_sum, core_sum (-2) A B C D seed_sum_A seed_sum_B seed_sum_C seed_sum_D]
  simp [mul_comm]

private theorem entry_dot_of_ne (i j : Index) (h : i ≠ j) :
    (∑ x, entry i x * entry j x) = 0 := by
  rcases i with i | ⟨i, r⟩ <;> rcases j with j | ⟨j, s⟩
  · have h' : i ≠ j := fun he => h (congrArg Sum.inl he)
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, entry, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul]
    rw [← mul_sum, corner_dot, top_dot]
    simp [h']
  · exact top_lower_dot i j s
  · simpa only [mul_comm] using top_lower_dot j i r
  · simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, entry]
    by_cases h' : i = j
    · subst j
      have hs : s - r ≠ 0 := by
        intro hz
        have hr : s = r := sub_eq_zero.mp hz
        subst s
        exact h rfl
      rw [left_dot, if_pos rfl, self_core, autocorr_nonzero _ hs]
      norm_num
    · rw [left_dot, if_neg h', different_core (-2) A B C D i j h']
      norm_num

private theorem card_index : Fintype.card Index = 668 := by
  simp [Fintype.card_sum, Fintype.card_prod, ZMod.card]

private theorem entry_dot_self (i : Index) : (∑ x : Index, entry i x * entry i x) = 668 := by
  calc
    _ = ∑ _ : Index, (1 : ℤ) := by
      apply sum_congr rfl
      intro x _
      rcases entry_signs i x with h | h <;> simp [h]
    _ = _ := by simp

private theorem determinant_of_gram {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hs : ∀ i j, M i j ∈ ({1, -1} : Finset ℝ))
    (hg : M * M.transpose = (n : ℝ) • 1) : Hadamard.IsHadamard M := by
  refine ⟨hs, ?_⟩
  have hd : M.det ^ 2 = (n : ℝ) ^ n := by
    simpa [Matrix.det_smul, ← sq] using congrArg Matrix.det hg
  rw [← Real.sqrt_sq_eq_abs, hd, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

set_option maxRecDepth 12000 in
/-- The published order-668 example, with kernel checks only on cyclic correlations and borders. -/
theorem order668 : ∃ M : Matrix (Fin 668) (Fin 668) ℝ, Hadamard.IsHadamard M := by
  let e := (Fintype.equivFinOfCardEq card_index).symm
  let M : Matrix (Fin 668) (Fin 668) ℝ := fun i j => (entry (e i) (e j) : ℝ)
  refine ⟨M, determinant_of_gram (fun i j => ?_) ?_⟩
  · rcases entry_signs (e i) (e j) with h | h <;> simp [M, h]
  · apply Matrix.ext
    intro i j
    calc
      (M * M.transpose) i j = ((∑ k : Index, entry (e i) k * entry (e j) k : ℤ) : ℝ) := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin 668, (entry (e i) (e k) : ℝ) * (entry (e j) (e k) : ℝ)) = _
        rw [Int.cast_sum]
        simp only [Int.cast_mul]
        exact e.sum_comp (fun k => (entry (e i) k : ℝ) * (entry (e j) k : ℝ))
      _ = _ := by
        by_cases h : i = j
        · subst j
          rw [entry_dot_self]
          simp [Matrix.smul_apply]
        · rw [entry_dot_of_ne _ _ (fun he => h (e.injective he))]
          simp [h, Matrix.smul_apply]

end Hadamard668Cyclic

namespace HadamardBits

private theorem through167 (k : ℕ) (hk : k ≤ 167) :
    ∃ M : Matrix (Fin (4*k)) (Fin (4*k)) ℝ, Hadamard.IsHadamard M := by
  rcases eq_or_lt_of_le hk with h|h
  · subst k; exact Hadamard668Cyclic.order668
  · exact below k (by omega)

private theorem past668 : 668 < Hadamard.hadamardConstant := by
  have h : (672 : ℕ∞) ≤ Hadamard.hadamardConstant := by
    have hh := constant_of_orders 167 through167
    norm_num at hh ⊢
    exact hh
  exact lt_of_lt_of_le (by norm_num : (668 : ℕ∞) < 672) h
end HadamardBits

theorem OMA.solution : type_of% @Hadamard.HadamardConjecture.variants.«167» := by
  exact HadamardBits.past668
