import FormalConjectures.Arxiv.«2208.14736».ZariskiCancellation
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Counterexample to the Zariski Cancellation Problem in dimension 3 in characteristic `p`

We formalize Neena Gupta's proof (Invent. Math. 2014, arXiv:1208.0483) that the Asanuma
threefold
`A = k[X, Y, Z, T] / (X^2 Y + Z^(p^2) + T + T^(p*(p+1)))`
over `k = ZMod p` satisfies `A[W] ≃ₐ[k] k[X_0, X_1, X_2, X_3]` while `A ≇ₐ[k] k[X_0, X_1, X_2]`.
-/

noncomputable section

open Polynomial MvPolynomial LaurentPolynomial

namespace ZariskiCancelPosChar

/- ## Section 1: Elementary divisibility lemma for polynomial evaluations -/

lemma dvd_aeval_sub_aeval {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {σ : Type*} (d : S) (u v : σ → S) (huv : ∀ i, d ∣ u i - v i) (P : MvPolynomial σ R) :
    d ∣ MvPolynomial.aeval u P - MvPolynomial.aeval v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    have h : MvPolynomial.aeval u p * u i - MvPolynomial.aeval v p * v i =
        (MvPolynomial.aeval u p - MvPolynomial.aeval v p) * u i +
        MvPolynomial.aeval v p * (u i - v i) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right (huv i) _)

lemma dvd_poly_aeval_sub_aeval {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (d a b : S) (hab : d ∣ a - b) (P : Polynomial R) :
    d ∣ Polynomial.aeval a P - Polynomial.aeval b P := by
  induction P using Polynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | monomial n r _ =>
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, ← mul_sub]
    exact dvd_mul_of_dvd_right (dvd_trans hab (sub_dvd_pow_sub_pow a b (n + 1))) _

/- ## Section 2: The Asanuma–Gupta ring `AsanumaRing K p` inside `LaurentPolynomial` -/

section AsanumaDef

variable (K : Type*) [CommRing K] (p : ℕ)

/-- Base 2-variable polynomial ring `K[Z, T]`. -/
abbrev P2 := MvPolynomial (Fin 2) K

/-- Ambient Laurent polynomial ring `(K[Z, T])[X, X⁻¹]`. -/
abbrev Ambient := LaurentPolynomial (P2 K)

/-- The polynomial `Z^(p^2) + T + T^(p*(p+1))` in `K[Z, T]`. -/
def fPoly : P2 K :=
  MvPolynomial.X 0 ^ (p ^ 2) + MvPolynomial.X 1 + MvPolynomial.X 1 ^ (p * (p + 1))

/-- The four generators `x, y, z, t` inside `Ambient K`. -/
def genX : Ambient K := LaurentPolynomial.T 1
def genY : Ambient K := LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.T (-2)
def genZ : Ambient K := LaurentPolynomial.C (MvPolynomial.X 0)
def genT : Ambient K := LaurentPolynomial.C (MvPolynomial.X 1)

/-- The Asanuma–Gupta `K`-subalgebra `A = K[x, y, z, t] ⊆ (K[Z, T])[X, X⁻¹]`. -/
def AsanumaSubalg : Subalgebra K (Ambient K) :=
  Algebra.adjoin K ({genX K, genY K p, genZ K, genT K} : Set (Ambient K))

abbrev AsanumaRing := ↥(AsanumaSubalg K p)

instance : CommRing (AsanumaRing K p) := Subalgebra.toCommRing (AsanumaSubalg K p)
instance [IsDomain K] : IsDomain (AsanumaRing K p) := Subalgebra.isDomain (AsanumaSubalg K p)
instance : Algebra.FiniteType K (AsanumaRing K p) :=
  Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)

def aX : AsanumaRing K p := ⟨genX K, Algebra.subset_adjoin (by simp)⟩
def aY : AsanumaRing K p := ⟨genY K p, Algebra.subset_adjoin (by simp)⟩
def aZ : AsanumaRing K p := ⟨genZ K, Algebra.subset_adjoin (by simp)⟩
def aT : AsanumaRing K p := ⟨genT K, Algebra.subset_adjoin (by simp)⟩

lemma aX_sq_mul_aY : aX K p ^ 2 * aY K p +
    (aZ K p ^ (p ^ 2) + aT K p + aT K p ^ (p * (p + 1))) = 0 := by
  apply Subtype.ext
  change (genX K) ^ 2 * genY K p +
    (genZ K ^ (p ^ 2) + genT K + genT K ^ (p * (p + 1))) = 0
  simp only [genX, genY, genZ, genT, fPoly, ← map_pow, ← map_add]
  have hT2 : (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ 2 = LaurentPolynomial.T 2 := by
    rw [sq, ← LaurentPolynomial.T_add]; norm_num
  rw [hT2, mul_left_comm, ← LaurentPolynomial.T_add]
  norm_num
  ring

lemma aX_ne_zero [Nontrivial K] : aX K p ≠ 0 := by
  intro h
  have h1 : LaurentPolynomial.T (1 : ℤ) = (0 : Ambient K) := congrArg Subtype.val h
  have h2 := congrArg (· * LaurentPolynomial.T (-1 : ℤ)) h1
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, zero_mul] at h2
  exact one_ne_zero h2

end AsanumaDef

/- ## Section 3: Explicit Asanuma Isomorphism `A[W] ≃ₐ[k] k[X, U, V_1, V_2]` -/

section AsanumaIso

variable (k : Type*) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- `α(U) = U - U^(p*(p+1)) ∈ k[U]`. -/
def alphaPoly : Polynomial k :=
  Polynomial.X - Polynomial.X ^ (p * (p + 1))

/-- `β(U) = -U^(p^2) ∈ k[U]`. -/
def betaPoly : Polynomial k :=
  -(Polynomial.X ^ (p ^ 2))

/-- `w(Z, T) = Z^p + (-T)^(p+1) ∈ k[Z, T]`. -/
def wPoly : P2 k :=
  MvPolynomial.X 0 ^ p + (-MvPolynomial.X 1) ^ (p + 1)

/-- `g(Z, T) = Z + w(Z, T)^(p+1) ∈ k[Z, T]`. -/
def gPoly : P2 k :=
  MvPolynomial.X 0 + (wPoly k p) ^ (p + 1)

omit hp in
lemma even_p_mul_succ : Even (p * (p + 1)) := Nat.even_mul_succ_self p

omit hp in
lemma neg_one_pow_p_mul_succ {R : Type*} [Ring R] : (-1 : R) ^ (p * (p + 1)) = 1 :=
  (even_p_mul_succ p).neg_one_pow

omit hp in
lemma neg_pow_p_mul_succ {R : Type*} [CommRing R] (r : R) :
    (-r) ^ (p * (p + 1)) = r ^ (p * (p + 1)) := by
  rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_p_mul_succ, one_mul]

lemma add_pow_p {R : Type*} [CommRing R] [CharP R p] (a b : R) :
    (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p

lemma sub_pow_p {R : Type*} [CommRing R] [CharP R p] (a b : R) :
    (a - b) ^ p = a ^ p - b ^ p :=
  sub_pow_char a b

lemma add_pow_p_sq {R : Type*} [CommRing R] [CharP R p] (a b : R) :
    (a + b) ^ (p ^ 2) = a ^ (p ^ 2) + b ^ (p ^ 2) := by
  rw [sq, pow_mul, pow_mul, pow_mul, add_pow_p p, add_pow_p p]

lemma sub_pow_p_sq {R : Type*} [CommRing R] [CharP R p] (a b : R) :
    (a - b) ^ (p ^ 2) = a ^ (p ^ 2) - b ^ (p ^ 2) := by
  rw [sq, pow_mul, pow_mul, pow_mul, sub_pow_p p, sub_pow_p p]

omit [CharP k p] in
lemma fPoly_eval_alpha_beta {R : Type*} [CommRing R] [Algebra k R] [CharP R p] (u : R) :
    MvPolynomial.aeval ![Polynomial.aeval u (alphaPoly k p), Polynomial.aeval u (betaPoly k p)]
      (fPoly k p) = 0 := by
  simp only [fPoly, alphaPoly, betaPoly, map_add, map_sub, map_neg, map_pow,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.aeval_X]
  rw [sub_pow_p_sq p, neg_pow_p_mul_succ p, ← pow_mul, ← pow_mul]
  have hmul : p * (p + 1) * p ^ 2 = p ^ 2 * (p * (p + 1)) := by ring
  rw [hmul]
  ring

omit [CharP k p] in
lemma gPoly_eval_alpha_beta {R : Type*} [CommRing R] [Algebra k R] [CharP R p] (u : R) :
    MvPolynomial.aeval ![Polynomial.aeval u (alphaPoly k p), Polynomial.aeval u (betaPoly k p)]
      (gPoly k p) = u := by
  simp only [gPoly, wPoly, alphaPoly, betaPoly, map_add, map_sub, map_neg, map_pow,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.aeval_X, neg_neg]
  rw [sub_pow_p p, ← pow_mul, ← pow_mul]
  have h1 : p * (p + 1) * p = p ^ 2 * (p + 1) := by ring
  rw [h1, sub_add_cancel, ← pow_mul]
  ring

lemma wPoly_pow_p : (wPoly k p) ^ p = fPoly k p - MvPolynomial.X 1 := by
  simp only [wPoly, fPoly]
  rw [add_pow_p p, ← pow_mul, ← sq, ← pow_mul, mul_comm (p + 1) p, neg_pow_p_mul_succ p]
  ring

lemma fPoly_dvd_gPoly_pow_p_sub_wPoly : fPoly k p ∣ (gPoly k p) ^ p - wPoly k p := by
  have h1 : (gPoly k p) ^ p = MvPolynomial.X 0 ^ p + ((wPoly k p) ^ p) ^ (p + 1) := by
    rw [gPoly, add_pow_p p, ← pow_mul, mul_comm (p + 1) p, pow_mul]
  have hgp : (gPoly k p) ^ p - wPoly k p =
      (fPoly k p - MvPolynomial.X 1) ^ (p + 1) - (-MvPolynomial.X 1) ^ (p + 1) := by
    rw [h1, wPoly_pow_p k p, wPoly, add_sub_add_left_eq_sub]
  rw [hgp]
  have h := sub_dvd_pow_sub_pow (fPoly k p - MvPolynomial.X 1) (-MvPolynomial.X 1) (p + 1)
  rw [sub_neg_eq_add, sub_add_cancel] at h
  exact h

lemma fPoly_dvd_T_sub_beta_g :
    fPoly k p ∣ MvPolynomial.X 1 - Polynomial.aeval (gPoly k p) (betaPoly k p) := by
  obtain ⟨h1, hh1⟩ := fPoly_dvd_gPoly_pow_p_sub_wPoly k p
  have hgp : (gPoly k p) ^ p = wPoly k p + fPoly k p * h1 := eq_add_of_sub_eq' hh1
  have hadd : (wPoly k p + fPoly k p * h1) ^ p = (wPoly k p) ^ p + (fPoly k p * h1) ^ p :=
    add_pow_p p _ _
  have hg_p2 : (gPoly k p) ^ (p ^ 2) = fPoly k p - MvPolynomial.X 1 + (fPoly k p) ^ p * h1 ^ p := by
    rw [sq, pow_mul, hgp, hadd, wPoly_pow_p k p, mul_pow]
  simp only [betaPoly, map_neg, map_pow, Polynomial.aeval_X, sub_neg_eq_add]
  rw [hg_p2]
  have hp1 : p ≥ 1 := hp.out.one_le
  refine ⟨1 + fPoly k p ^ (p - 1) * h1 ^ p, ?_⟩
  generalize fPoly k p = F
  have hFp : F * F ^ (p - 1) = F ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [mul_add, mul_one, ← mul_assoc, hFp]
  abel

lemma fPoly_dvd_Z_sub_alpha_g :
    fPoly k p ∣ MvPolynomial.X 0 - Polynomial.aeval (gPoly k p) (alphaPoly k p) := by
  have hdiv1 := fPoly_dvd_gPoly_pow_p_sub_wPoly k p
  simp only [alphaPoly, map_sub, map_pow, Polynomial.aeval_X]
  have heq : MvPolynomial.X 0 - (gPoly k p - gPoly k p ^ (p * (p + 1))) =
      ((gPoly k p) ^ p) ^ (p + 1) - (wPoly k p) ^ (p + 1) := by
    rw [← pow_mul, gPoly]
    abel
  rw [heq]
  exact dvd_trans hdiv1 (sub_dvd_pow_sub_pow _ _ (p + 1))

set_option maxHeartbeats 400000 in
/-- Explicit `k`-algebra isomorphism `A[W] ≃ₐ[k] k[X, U, V_1, V_2]`. -/
theorem asanuma_poly_algEquiv :
    Nonempty (Polynomial (AsanumaRing k p) ≃ₐ[k] MvPolynomial (Fin 4) k) := by
  -- Variables in `MvPolynomial (Fin 4) k`: 0 = X, 1 = U, 2 = V_1, 3 = V_2
  let X4 : MvPolynomial (Fin 4) k := MvPolynomial.X 0
  let U4 : MvPolynomial (Fin 4) k := MvPolynomial.X 1
  let V1 : MvPolynomial (Fin 4) k := MvPolynomial.X 2
  let V2 : MvPolynomial (Fin 4) k := MvPolynomial.X 3
  let Zimg : MvPolynomial (Fin 4) k := Polynomial.aeval U4 (alphaPoly k p) + X4 ^ 2 * V1
  let Timg : MvPolynomial (Fin 4) k := Polynomial.aeval U4 (betaPoly k p) + X4 ^ 2 * V2
  -- `X4^2 ∣ f(Zimg, Timg)`
  have hY_dvd : X4 ^ 2 ∣ MvPolynomial.aeval ![Zimg, Timg] (fPoly k p) := by
    have h0 := fPoly_eval_alpha_beta k p U4
    have h1 := dvd_aeval_sub_aeval (X4 ^ 2) ![Zimg, Timg]
      ![Polynomial.aeval U4 (alphaPoly k p), Polynomial.aeval U4 (betaPoly k p)]
      (fun i => by fin_cases i <;> simp [Zimg, Timg]) (fPoly k p)
    rw [h0, sub_zero] at h1
    exact h1
  obtain ⟨Yneg, hYneg⟩ := hY_dvd
  let Yimg : MvPolynomial (Fin 4) k := -Yneg
  have hrel_img : X4 ^ 2 * Yimg + MvPolynomial.aeval ![Zimg, Timg] (fPoly k p) = 0 := by
    simp only [Yimg, hYneg]; ring
  -- `X4^2 ∣ g(Zimg, Timg) - U4`
  have hQ_dvd : X4 ^ 2 ∣ MvPolynomial.aeval ![Zimg, Timg] (gPoly k p) - U4 := by
    have h0 := gPoly_eval_alpha_beta k p U4
    have h1 := dvd_aeval_sub_aeval (X4 ^ 2) ![Zimg, Timg]
      ![Polynomial.aeval U4 (alphaPoly k p), Polynomial.aeval U4 (betaPoly k p)]
      (fun i => by fin_cases i <;> simp [Zimg, Timg]) (gPoly k p)
    rw [h0] at h1
    exact h1
  obtain ⟨Qimg, hQimg⟩ := hQ_dvd
  let Wimg : MvPolynomial (Fin 4) k := -Qimg
  have hg_img : MvPolynomial.aeval ![Zimg, Timg] (gPoly k p) + X4 ^ 2 * Wimg = U4 := by
    simp only [Wimg]; linear_combination hQimg
  -- Build `ψA : AsanumaRing k p →ₐ[k] MvPolynomial (Fin 4) k` via `Localization.Away X4`
  let L4 := Localization.Away X4
  have hinjL4 : Function.Injective (algebraMap (MvPolynomial (Fin 4) k) L4) :=
    IsLocalization.injective L4 (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero 0)))
  have : Nontrivial L4 := hinjL4.nontrivial
  have hX4_unit : IsUnit (algebraMap (MvPolynomial (Fin 4) k) L4 X4) :=
    IsLocalization.Away.algebraMap_isUnit X4
  let uX4 : L4ˣ := hX4_unit.unit
  let coeffMap : P2 k →ₐ[k] L4 :=
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin 4) k) L4).comp
      (MvPolynomial.aeval ![Zimg, Timg])
  let gX4 : Multiplicative ℤ →* L4 :=
    { toFun := fun n => ((uX4 ^ Multiplicative.toAdd n : L4ˣ) : L4)
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add] }
  let ψAmb : Ambient k →ₐ[k] L4 :=
    AddMonoidAlgebra.liftNCAlgHom coeffMap gX4 (fun _ _ => Commute.all _ _)
  have hψAmb_C : ∀ r : P2 k, ψAmb (LaurentPolynomial.C r) = coeffMap r := fun r => by
    change AddMonoidAlgebra.liftNC (coeffMap.toRingHom : P2 k →+* L4) gX4 (AddMonoidAlgebra.single (0 : ℤ) r) = coeffMap r
    rw [AddMonoidAlgebra.liftNC_single]
    simp [gX4]
  have hψAmb_T : ∀ n : ℤ, ψAmb (LaurentPolynomial.T n) = ((uX4 ^ n : L4ˣ) : L4) := fun n => by
    change AddMonoidAlgebra.liftNC (coeffMap.toRingHom : P2 k →+* L4) gX4 (AddMonoidAlgebra.single n (1 : P2 k)) = _
    rw [AddMonoidAlgebra.liftNC_single]
    simp [gX4]
  have hψAmb_genX : ψAmb (genX k) = algebraMap (MvPolynomial (Fin 4) k) L4 X4 := by
    simp [genX, hψAmb_T, uX4]
  have hψAmb_genZ : ψAmb (genZ k) = algebraMap (MvPolynomial (Fin 4) k) L4 Zimg := by
    simp [genZ, hψAmb_C, coeffMap]
  have hψAmb_genT : ψAmb (genT k) = algebraMap (MvPolynomial (Fin 4) k) L4 Timg := by
    simp [genT, hψAmb_C, coeffMap]
  have hψAmb_genY : ψAmb (genY k p) = algebraMap (MvPolynomial (Fin 4) k) L4 Yimg := by
    have hX4_sq_ne : (algebraMap (MvPolynomial (Fin 4) k) L4 X4) ^ 2 ≠ 0 :=
      pow_ne_zero 2 hX4_unit.ne_zero
    apply mul_left_cancel₀ hX4_sq_ne
    have hmul : (algebraMap (MvPolynomial (Fin 4) k) L4 X4) ^ 2 * ψAmb (genY k p) =
        ψAmb (genX k ^ 2 * genY k p) := by
      rw [map_mul, map_pow, hψAmb_genX]
    rw [hmul]
    have hgen : genX k ^ 2 * genY k p = LaurentPolynomial.C (-fPoly k p) := by
      simp only [genX, genY]
      have hT2 : (LaurentPolynomial.T (1 : ℤ) : Ambient k) ^ 2 = LaurentPolynomial.T 2 := by
        rw [sq, ← LaurentPolynomial.T_add]; norm_num
      rw [hT2, mul_left_comm, ← LaurentPolynomial.T_add]
      norm_num
    rw [hgen, hψAmb_C]
    simp only [coeffMap, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', map_neg,
      ← map_pow, ← map_mul]
    rw [← map_neg]
    congr 1
    linear_combination -hrel_img
  have hrange : ∀ a : AsanumaRing k p,
      ∃ r : MvPolynomial (Fin 4) k, ψAmb a.val = algebraMap (MvPolynomial (Fin 4) k) L4 r := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · rintro b (rfl | rfl | rfl | rfl)
      · exact ⟨X4, hψAmb_genX⟩
      · exact ⟨Yimg, hψAmb_genY⟩
      · exact ⟨Zimg, hψAmb_genZ⟩
      · exact ⟨Timg, hψAmb_genT⟩
    · intro c
      exact ⟨algebraMap k _ c, by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 4) k) L4]⟩
    · rintro x y _ _ ⟨rx, hrx⟩ ⟨ry, hry⟩
      exact ⟨rx + ry, by rw [map_add, hrx, hry, map_add]⟩
    · rintro x y _ _ ⟨rx, hrx⟩ ⟨ry, hry⟩
      exact ⟨rx * ry, by rw [map_mul, hrx, hry, map_mul]⟩
  choose ψA_fun hψA_fun using hrange
  let ψA : AsanumaRing k p →ₐ[k] MvPolynomial (Fin 4) k :=
    { toFun := ψA_fun
      map_one' := hinjL4 (by rw [← hψA_fun 1, Subalgebra.coe_one, map_one, map_one])
      map_mul' := fun a b => hinjL4 (by
        rw [← hψA_fun (a * b), Subalgebra.coe_mul, map_mul, hψA_fun a, hψA_fun b, map_mul])
      map_zero' := hinjL4 (by rw [← hψA_fun 0, Subalgebra.coe_zero, map_zero, map_zero])
      map_add' := fun a b => hinjL4 (by
        rw [← hψA_fun (a + b), Subalgebra.coe_add, map_add, hψA_fun a, hψA_fun b, map_add])
      commutes' := fun c => hinjL4 (by
        rw [← hψA_fun (algebraMap k _ c)]
        change ψAmb (algebraMap k (Ambient k) c) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 4) k) L4]) }
  have hψA_X : ψA (aX k p) = X4 := hinjL4 (by change algebraMap _ L4 (ψA_fun (aX k p)) = _; rw [← hψA_fun]; exact hψAmb_genX)
  have hψA_Y : ψA (aY k p) = Yimg := hinjL4 (by change algebraMap _ L4 (ψA_fun (aY k p)) = _; rw [← hψA_fun]; exact hψAmb_genY)
  have hψA_Z : ψA (aZ k p) = Zimg := hinjL4 (by change algebraMap _ L4 (ψA_fun (aZ k p)) = _; rw [← hψA_fun]; exact hψAmb_genZ)
  have hψA_T : ψA (aT k p) = Timg := hinjL4 (by change algebraMap _ L4 (ψA_fun (aT k p)) = _; rw [← hψA_fun]; exact hψAmb_genT)
  -- Extend `ψA` to `Ψ : Polynomial (AsanumaRing k p) →ₐ[k] MvPolynomial (Fin 4) k` sending `W ↦ Wimg`
  let Ψ : Polynomial (AsanumaRing k p) →ₐ[k] MvPolynomial (Fin 4) k :=
    { toRingHom := Polynomial.eval₂RingHom ψA.toRingHom Wimg
      commutes' := fun c => by
        change Polynomial.eval₂ ψA.toRingHom Wimg (Polynomial.C (algebraMap k _ c)) = _
        rw [Polynomial.eval₂_C]
        exact ψA.commutes c }
  have hΨ_C : ∀ a : AsanumaRing k p, Ψ (Polynomial.C a) = ψA a := fun a => by
    change Polynomial.eval₂ ψA.toRingHom Wimg (Polynomial.C a) = ψA a
    rw [Polynomial.eval₂_C]; rfl
  have hΨ_X : Ψ Polynomial.X = Wimg := by
    change Polynomial.eval₂ ψA.toRingHom Wimg Polynomial.X = Wimg
    rw [Polynomial.eval₂_X]
  -- Now construct the inverse `Φ : MvPolynomial (Fin 4) k →ₐ[k] Polynomial (AsanumaRing k p)`
  let xW : Polynomial (AsanumaRing k p) := Polynomial.C (aX k p)
  let yW : Polynomial (AsanumaRing k p) := Polynomial.C (aY k p)
  let zW : Polynomial (AsanumaRing k p) := Polynomial.C (aZ k p)
  let tW : Polynomial (AsanumaRing k p) := Polynomial.C (aT k p)
  let W : Polynomial (AsanumaRing k p) := Polynomial.X
  let gW : Polynomial (AsanumaRing k p) := MvPolynomial.aeval ![zW, tW] (gPoly k p)
  let fW : Polynomial (AsanumaRing k p) := MvPolynomial.aeval ![zW, tW] (fPoly k p)
  have hfW_eq : fW = -(xW ^ 2 * yW) := by
    have h0 := congrArg Polynomial.C (aX_sq_mul_aY k p)
    simp only [map_add, map_mul, map_pow, map_zero] at h0
    have hf : fW = zW ^ (p ^ 2) + tW + tW ^ (p * (p + 1)) := by
      simp [fW, fPoly]
    rw [hf]
    linear_combination h0
  let ΦU : Polynomial (AsanumaRing k p) := gW + xW ^ 2 * W
  -- `xW^2 ∣ zW - α(ΦU)`
  have hV1_dvd : xW ^ 2 ∣ zW - Polynomial.aeval ΦU (alphaPoly k p) := by
    have h1 : xW ^ 2 ∣ Polynomial.aeval ΦU (alphaPoly k p) - Polynomial.aeval gW (alphaPoly k p) :=
      dvd_poly_aeval_sub_aeval (xW ^ 2) ΦU gW (by simp [ΦU]) (alphaPoly k p)
    obtain ⟨q2, hq2⟩ := fPoly_dvd_Z_sub_alpha_g k p
    have h2 : zW - Polynomial.aeval gW (alphaPoly k p) =
        fW * MvPolynomial.aeval ![zW, tW] q2 := by
      have hmap := congrArg (MvPolynomial.aeval ![zW, tW]) hq2
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero] at hmap
      have hcomm : MvPolynomial.aeval ![zW, tW] (Polynomial.aeval (gPoly k p) (alphaPoly k p)) =
          Polynomial.aeval gW (alphaPoly k p) := by
        simp only [alphaPoly, map_sub, map_pow, Polynomial.aeval_X, gW]
      rw [hcomm] at hmap
      exact hmap
    have h2' : xW ^ 2 ∣ zW - Polynomial.aeval gW (alphaPoly k p) := by
      rw [h2, hfW_eq]
      exact ⟨-(yW * MvPolynomial.aeval ![zW, tW] q2), by ring⟩
    have hsplit : zW - Polynomial.aeval ΦU (alphaPoly k p) =
        (zW - Polynomial.aeval gW (alphaPoly k p)) -
        (Polynomial.aeval ΦU (alphaPoly k p) - Polynomial.aeval gW (alphaPoly k p)) := by ring
    rw [hsplit]
    exact dvd_sub h2' h1
  obtain ⟨ΦV1, hΦV1⟩ := hV1_dvd
  -- `xW^2 ∣ tW - β(ΦU)`
  have hV2_dvd : xW ^ 2 ∣ tW - Polynomial.aeval ΦU (betaPoly k p) := by
    have h1 : xW ^ 2 ∣ Polynomial.aeval ΦU (betaPoly k p) - Polynomial.aeval gW (betaPoly k p) :=
      dvd_poly_aeval_sub_aeval (xW ^ 2) ΦU gW (by simp [ΦU]) (betaPoly k p)
    obtain ⟨q1, hq1⟩ := fPoly_dvd_T_sub_beta_g k p
    have h2 : tW - Polynomial.aeval gW (betaPoly k p) =
        fW * MvPolynomial.aeval ![zW, tW] q1 := by
      have hmap := congrArg (MvPolynomial.aeval ![zW, tW]) hq1
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at hmap
      have hcomm : MvPolynomial.aeval ![zW, tW] (Polynomial.aeval (gPoly k p) (betaPoly k p)) =
          Polynomial.aeval gW (betaPoly k p) := by
        simp only [betaPoly, map_neg, map_pow, Polynomial.aeval_X, gW]
      rw [hcomm] at hmap
      exact hmap
    have h2' : xW ^ 2 ∣ tW - Polynomial.aeval gW (betaPoly k p) := by
      rw [h2, hfW_eq]
      exact ⟨-(yW * MvPolynomial.aeval ![zW, tW] q1), by ring⟩
    have hsplit : tW - Polynomial.aeval ΦU (betaPoly k p) =
        (tW - Polynomial.aeval gW (betaPoly k p)) -
        (Polynomial.aeval ΦU (betaPoly k p) - Polynomial.aeval gW (betaPoly k p)) := by ring
    rw [hsplit]
    exact dvd_sub h2' h1
  obtain ⟨ΦV2, hΦV2⟩ := hV2_dvd
  let Φ : MvPolynomial (Fin 4) k →ₐ[k] Polynomial (AsanumaRing k p) :=
    MvPolynomial.aeval ![xW, ΦU, ΦV1, ΦV2]
  -- Verify `Ψ ∘ Φ = id`
  have hΨΦ_X : Ψ (Φ X4) = X4 := by simp [Φ, X4, xW, hΨ_C, hψA_X]
  have hΨ_gW : Ψ gW = MvPolynomial.aeval ![Zimg, Timg] (gPoly k p) := by
    simp only [gW, gPoly, wPoly, map_add, map_neg, map_pow, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    simp [zW, tW, hΨ_C, hψA_Z, hψA_T]
  have hΦ_U4 : Φ U4 = ΦU := by simp [Φ, U4]
  have hΨΦ_U : Ψ (Φ U4) = U4 := by
    rw [hΦ_U4]
    simp only [ΦU, map_add, map_mul, map_pow, hΨ_gW, xW, W, hΨ_C, hΨ_X, hψA_X]
    exact hg_img
  have hX4_sq_ne : X4 ^ 2 ≠ 0 := pow_ne_zero 2 (MvPolynomial.X_ne_zero 0)
  have hΨΦ_V1 : Ψ (Φ V1) = V1 := by
    apply mul_left_cancel₀ hX4_sq_ne
    have h1 := congrArg Ψ hΦV1
    simp only [map_sub, map_mul, map_pow] at h1
    have hcomm : Ψ (Polynomial.aeval ΦU (alphaPoly k p)) =
        Polynomial.aeval U4 (alphaPoly k p) := by
      have hU : Ψ ΦU = U4 := by simpa [Φ, U4] using hΨΦ_U
      simp only [alphaPoly, map_sub, map_pow, Polynomial.aeval_X, hU]
    rw [hcomm] at h1
    simp only [zW, xW, hΨ_C, hψA_Z, hψA_X] at h1
    have hV1 : Ψ (Φ V1) = Ψ ΦV1 := by simp [Φ, V1]
    rw [hV1, ← h1]
    simp [Zimg]
  have hΨΦ_V2 : Ψ (Φ V2) = V2 := by
    apply mul_left_cancel₀ hX4_sq_ne
    have h1 := congrArg Ψ hΦV2
    simp only [map_sub, map_mul, map_pow] at h1
    have hcomm : Ψ (Polynomial.aeval ΦU (betaPoly k p)) =
        Polynomial.aeval U4 (betaPoly k p) := by
      have hU : Ψ ΦU = U4 := by simpa [Φ, U4] using hΨΦ_U
      simp only [betaPoly, map_neg, map_pow, Polynomial.aeval_X, hU]
    rw [hcomm] at h1
    simp only [tW, xW, hΨ_C, hψA_T, hψA_X] at h1
    have hV2 : Ψ (Φ V2) = Ψ ΦV2 := by simp [Φ, V2]
    rw [hV2, ← h1]
    simp [Timg]
  have hΨΦ : ∀ r : MvPolynomial (Fin 4) k, Ψ (Φ r) = r := by
    intro r
    have hcomp : Ψ.comp Φ = AlgHom.id k (MvPolynomial (Fin 4) k) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · exact hΨΦ_X
      · exact hΨΦ_U
      · exact hΨΦ_V1
      · exact hΨΦ_V2
    exact AlgHom.congr_fun hcomp r
  -- Verify `Φ ∘ Ψ = id`
  have hxW_sq_ne : xW ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Polynomial.C_ne_zero.mpr (aX_ne_zero k p))
  have hΦΨ_Z : Φ (Ψ zW) = zW := by
    have h1 : Ψ zW = Zimg := by simp [zW, hΨ_C, hψA_Z]
    rw [h1]
    simp only [Zimg, map_add, map_mul, map_pow]
    have hα : Φ (Polynomial.aeval U4 (alphaPoly k p)) = Polynomial.aeval ΦU (alphaPoly k p) := by
      simp only [alphaPoly, map_sub, map_pow, Polynomial.aeval_X, hΦ_U4]
    rw [hα]
    have hX : Φ X4 = xW := by simp [Φ, X4]
    have hV : Φ V1 = ΦV1 := by simp [Φ, V1]
    rw [hX, hV, ← hΦV1]
    ring
  have hΦΨ_T : Φ (Ψ tW) = tW := by
    have h1 : Ψ tW = Timg := by simp [tW, hΨ_C, hψA_T]
    rw [h1]
    simp only [Timg, map_add, map_mul, map_pow]
    have hβ : Φ (Polynomial.aeval U4 (betaPoly k p)) = Polynomial.aeval ΦU (betaPoly k p) := by
      simp only [betaPoly, map_neg, map_pow, Polynomial.aeval_X, hΦ_U4]
    rw [hβ]
    have hX : Φ X4 = xW := by simp [Φ, X4]
    have hV : Φ V2 = ΦV2 := by simp [Φ, V2]
    rw [hX, hV, ← hΦV2]
    ring
  have hΦΨ_X : Φ (Ψ xW) = xW := by
    simp [xW, hΨ_C, hψA_X, Φ, X4]
  have hΦΨ_Y : Φ (Ψ yW) = yW := by
    apply mul_left_cancel₀ hxW_sq_ne
    have h1 := congrArg Φ hrel_img
    simp only [map_add, map_mul, map_pow, map_zero] at h1
    have hX : Φ X4 = xW := by simp [Φ, X4]
    have hf : Φ (MvPolynomial.aeval ![Zimg, Timg] (fPoly k p)) = fW := by
      have hZ : Φ Zimg = zW := by simpa [zW, hΨ_C, hψA_Z] using hΦΨ_Z
      have hT : Φ Timg = tW := by simpa [tW, hΨ_C, hψA_T] using hΦΨ_T
      simp only [fPoly, fW, map_add, map_pow, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, hZ, hT]
    rw [hX, hf, hfW_eq] at h1
    have hY : Ψ yW = Yimg := by simp [yW, hΨ_C, hψA_Y]
    rw [hY]
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h1)
  have hΦΨ_W : Φ (Ψ W) = W := by
    apply mul_left_cancel₀ hxW_sq_ne
    have h1 := congrArg Φ hg_img
    simp only [map_add, map_mul, map_pow] at h1
    have hX : Φ X4 = xW := by simp [Φ, X4]
    have hg : Φ (MvPolynomial.aeval ![Zimg, Timg] (gPoly k p)) = gW := by
      have hZ : Φ Zimg = zW := by simpa [zW, hΨ_C, hψA_Z] using hΦΨ_Z
      have hT : Φ Timg = tW := by simpa [tW, hΨ_C, hψA_T] using hΦΨ_T
      simp only [gPoly, wPoly, gW, map_add, map_neg, map_pow, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, hZ, hT]
    rw [hX, hΦ_U4, hg] at h1
    have hW : Ψ W = Wimg := by simp [W, hΨ_X]
    rw [hW]
    exact add_left_cancel h1
  have hΦΨ_C : ∀ a : AsanumaRing k p, Φ (Ψ (Polynomial.C a)) = Polynomial.C a := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · rintro b (rfl | rfl | rfl | rfl)
      · exact hΦΨ_X
      · exact hΦΨ_Y
      · exact hΦΨ_Z
      · exact hΦΨ_T
    · intro c
      have hc : Polynomial.C (⟨algebraMap k (Ambient k) c, Subalgebra.algebraMap_mem _ c⟩ : AsanumaRing k p) =
          algebraMap k (Polynomial (AsanumaRing k p)) c := rfl
      rw [hc, AlgHom.commutes, AlgHom.commutes]
    · rintro x y hx hy ihx ihy
      have hadd : (⟨x + y, add_mem hx hy⟩ : AsanumaRing k p) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [hadd, map_add, map_add, map_add, ihx, ihy]
    · rintro x y hx hy ihx ihy
      have hmul : (⟨x * y, mul_mem hx hy⟩ : AsanumaRing k p) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [hmul, map_mul, map_mul, map_mul, ihx, ihy]
  have hΦΨ : ∀ q : Polynomial (AsanumaRing k p), Φ (Ψ q) = q := by
    intro q
    induction q using Polynomial.induction_on with
    | C a => exact hΦΨ_C a
    | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | monomial n a _ =>
      rw [map_mul, map_mul, map_pow, map_pow, hΦΨ_C a, hΦΨ_W]
  exact ⟨AlgEquiv.ofAlgHom Ψ Φ (AlgHom.ext hΨΦ) (AlgHom.ext hΦΨ)⟩

end AsanumaIso

/- ## Section 4: Exponential maps (`G_a`-actions) and Lemma 2.1 / Lemma 2.4 -/

section ExpMaps

/-- An exponential map (`G_a`-action) on a `K`-algebra `D`. -/
structure ExpMap (K D : Type*) [CommSemiring K] [CommRing D] [Algebra K D] where
  toAlgHom : D →ₐ[K] Polynomial D
  eval_zero : ∀ a : D, (toAlgHom a).eval 0 = a
  coassoc : ∀ a : D,
    Polynomial.map toAlgHom.toRingHom (toAlgHom a) =
    Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      (Polynomial.C Polynomial.X + Polynomial.X) (toAlgHom a)

namespace ExpMap

variable {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]

instance : CoeFun (ExpMap K D) (fun _ => D → Polynomial D) := ⟨fun φ => φ.toAlgHom⟩

lemma coeff_zero (φ : ExpMap K D) (a : D) : (φ a).coeff 0 = a := by
  rw [Polynomial.coeff_zero_eq_eval_zero]; exact φ.eval_zero a

lemma injective (φ : ExpMap K D) : Function.Injective φ := by
  intro a b h
  have := congrArg (fun q : Polynomial D => q.coeff 0) h
  simpa [φ.coeff_zero] using this

/-- The `K`-subalgebra of `φ`-invariants `D^φ = {a ∈ D | φ a = C a}`. -/
def invSubalg (φ : ExpMap K D) : Subalgebra K D where
  carrier := {a | φ a = Polynomial.C a}
  mul_mem' {a b} ha hb := by
    change φ.toAlgHom (a * b) = Polynomial.C (a * b)
    rw [map_mul, ha, hb, map_mul]
  one_mem' := by
    change φ.toAlgHom 1 = Polynomial.C 1
    rw [map_one, map_one]
  add_mem' {a b} ha hb := by
    change φ.toAlgHom (a + b) = Polynomial.C (a + b)
    rw [map_add, ha, hb, map_add]
  zero_mem' := by
    change φ.toAlgHom 0 = Polynomial.C 0
    rw [map_zero, map_zero]
  algebraMap_mem' c := by
    change φ.toAlgHom (algebraMap K D c) = Polynomial.C (algebraMap K D c)
    rw [AlgHom.commutes]
    rfl

def IsNontrivial (φ : ExpMap K D) : Prop :=
  ∃ a : D, a ∉ φ.invSubalg

lemma mem_invSubalg_iff_natDegree_eq_zero (φ : ExpMap K D) (a : D) :
    a ∈ φ.invSubalg ↔ (φ a).natDegree = 0 := by
  constructor
  · intro ha
    change φ a = Polynomial.C a at ha
    rw [ha, Polynomial.natDegree_C]
  · intro hdeg
    change φ a = Polynomial.C a
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, φ.coeff_zero]

/-- Key coassociativity coefficient identity:
    `coeff r (φ (coeff i (φ a))) = ((i + r).choose i : D) * coeff (i + r) (φ a)`. -/
lemma coeff_coeff_coassoc (φ : ExpMap K D) (a : D) (i r : ℕ) :
    (φ ((φ a).coeff i)).coeff r = ((i + r).choose i : D) * (φ a).coeff (i + r) := by
  have h := congrArg (fun Q : Polynomial (Polynomial D) => (Q.coeff i).coeff r) (φ.coassoc a)
  rw [Polynomial.coeff_map] at h
  change (φ.toAlgHom.toRingHom ((φ.toAlgHom a).coeff i)).coeff r = _
  rw [h]
  -- Compute coefficient of `X^i` (outer) and `X^r` (inner) in `eval₂ (C ∘ C) (C X + X) P`
  generalize φ a = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, mul_add]
    rw [hp, hq]
  | monomial n c =>
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply]
    rw [add_pow, Finset.mul_sum, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D)))).coeff i).coeff r) =
        if k = r ∧ n - k = i then (n.choose i : D) * c else 0 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D))) =
          Polynomial.C (Polynomial.C (c * (n.choose k : D)) * Polynomial.X ^ k) *
          Polynomial.X ^ (n - k) := by
        simp only [map_mul, map_natCast, Polynomial.C_pow]
        ring
      rw [h1, Polynomial.coeff_C_mul_X_pow]
      by_cases hni : i = n - k
      · rw [if_pos hni, Polynomial.coeff_C_mul_X_pow]
        by_cases hkr : r = k
        · rw [if_pos hkr, if_pos ⟨hkr.symm, hni.symm⟩]
          have hki : n.choose k = n.choose i := by
            rw [hni]; exact (Nat.choose_symm hkn).symm
          rw [hki, mul_comm]
        · rw [if_neg hkr, if_neg (fun h => hkr h.1.symm)]
      · rw [if_neg hni, Polynomial.coeff_zero, if_neg (fun h => hni h.2.symm)]
    rw [Finset.sum_congr rfl hterm]
    rw [Polynomial.coeff_monomial]
    by_cases hnir : n = i + r
    · subst hnir
      rw [if_pos rfl]
      rw [Finset.sum_eq_single r]
      · simp [Nat.add_sub_cancel]
      · intro k _ hkr
        rw [if_neg (fun h => hkr h.1)]
      · intro hr
        exfalso; apply hr; exact Finset.mem_range.mpr (by omega)
    · rw [if_neg hnir, mul_zero]
      apply Finset.sum_eq_zero
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg]
      rintro ⟨rfl, hsub⟩
      exact hnir (by omega)

/-- Lemma 2.1 (i): `D^φ` is factorially closed in a domain `D`. -/
lemma mem_invSubalg_of_mul [IsDomain D] (φ : ExpMap K D) {a b : D}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ∈ φ.invSubalg) :
    a ∈ φ.invSubalg ∧ b ∈ φ.invSubalg := by
  have hφa : φ a ≠ 0 := fun h => ha (φ.injective (by rw [h, map_zero]))
  have hφb : φ b ≠ 0 := fun h => hb (φ.injective (by rw [h, map_zero]))
  have hdeg : (φ a).natDegree + (φ b).natDegree = 0 := by
    rw [← Polynomial.natDegree_mul hφa hφb, ← map_mul]
    exact (φ.mem_invSubalg_iff_natDegree_eq_zero (a * b)).mp hab
  exact ⟨(φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr (Nat.eq_zero_of_add_eq_zero_right hdeg),
         (φ.mem_invSubalg_iff_natDegree_eq_zero b).mpr (Nat.eq_zero_of_add_eq_zero_left hdeg)⟩

/-- Leading coefficient of `φ a` is always `φ`-invariant. -/
lemma leadingCoeff_mem_invSubalg (φ : ExpMap K D) (a : D) :
    (φ a).leadingCoeff ∈ φ.invSubalg := by
  rw [mem_invSubalg_iff_natDegree_eq_zero]
  by_contra hne
  have hpos : 0 < (φ (φ a).leadingCoeff).natDegree := Nat.pos_of_ne_zero hne
  have hlc : (φ (φ a).leadingCoeff).coeff (φ (φ a).leadingCoeff).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega)
  have hco := φ.coeff_coeff_coassoc a (φ a).natDegree (φ (φ a).leadingCoeff).natDegree
  rw [Polynomial.coeff_natDegree] at hco
  have h0 : (φ a).coeff ((φ a).natDegree + (φ (φ a).leadingCoeff).natDegree) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h0, mul_zero] at hco
  exact hlc hco

/-- Lemma 2.1 (ii): `D^φ` is algebraically closed in a domain `D`. -/
lemma mem_invSubalg_of_isIntegral [IsDomain D] (φ : ExpMap K D) {a : D}
    (P : Polynomial φ.invSubalg) (hP : P ≠ 0) (ha : Polynomial.aeval a P = 0) :
    a ∈ φ.invSubalg := by
  by_contra hnot
  have hpos : 0 < (φ a).natDegree :=
    Nat.pos_of_ne_zero (mt (φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr hnot)
  have hφa_ne : φ a ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega
  -- Apply `φ` to `aeval a P = 0`: the top `U`-degree term has degree `P.natDegree * (φ a).natDegree`
  have hmap0 : φ (Polynomial.aeval a P) = 0 := by rw [ha, map_zero]
  have htop : (φ (Polynomial.aeval a P)).coeff (P.natDegree * (φ a).natDegree) =
      (P.leadingCoeff : D) * (φ a).leadingCoeff ^ P.natDegree := by
    have hPsum : Polynomial.aeval a P =
        ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : D) * a ^ i := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      rfl
    rw [hPsum, map_sum, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single P.natDegree]
    · rw [map_mul, map_pow]
      have hinv : φ (P.coeff P.natDegree : D) = Polynomial.C (P.coeff P.natDegree : D) :=
        (P.coeff P.natDegree).2
      rw [hinv, Polynomial.coeff_C_mul]
      have hdeg : ((φ a) ^ P.natDegree).natDegree = P.natDegree * (φ a).natDegree :=
        Polynomial.natDegree_pow _ _
      rw [← hdeg, Polynomial.coeff_natDegree, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow]
    · intro i hi hine
      have hilt : i < P.natDegree := by
        have := Finset.mem_range.mp hi; omega
      rw [map_mul, map_pow]
      have hinv : φ (P.coeff i : D) = Polynomial.C (P.coeff i : D) := (P.coeff i).2
      rw [hinv, Polynomial.coeff_C_mul]
      have hlt : ((φ a) ^ i).natDegree < P.natDegree * (φ a).natDegree := by
        rw [Polynomial.natDegree_pow]
        exact Nat.mul_lt_mul_of_pos_right hilt hpos
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro hnotmem
      exfalso; exact hnotmem (Finset.mem_range.mpr (Nat.lt_succ_self _))
  rw [hmap0, Polynomial.coeff_zero] at htop
  have hlcP : (P.leadingCoeff : D) ≠ 0 := by
    intro h
    exact Polynomial.leadingCoeff_ne_zero.mpr hP (Subtype.ext h)
  have hlcφ : (φ a).leadingCoeff ^ P.natDegree ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hφa_ne)
  exact mul_ne_zero hlcP hlcφ htop.symm

/-- Elementary char-`p` binomial lemma: if `(d.choose i : D) = 0` for all `0 < i < d`
    in a domain `D` of prime characteristic `p`, then `d = p ^ k` for some `k`. -/
lemma eq_prime_pow_of_choose_eq_zero {p : ℕ} [hp : Fact p.Prime] [IsDomain D] [CharP D p]
    {d : ℕ} (hd : 0 < d) (hchoose : ∀ i, 0 < i → i < d → (d.choose i : D) = 0) :
    ∃ k : ℕ, d = p ^ k := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    by_cases hd1 : d = 1
    · exact ⟨0, by simp [hd1]⟩
    · have hp_dvd : p ∣ d := by
        have h1 : (d.choose 1 : D) = 0 := hchoose 1 (by omega) (by omega)
        rw [Nat.choose_one_right, CharP.cast_eq_zero_iff D p] at h1
        exact h1
      obtain ⟨m, rfl⟩ := hp_dvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hd
        · exact hpos
      have hm_lt : m < p * m := lt_mul_of_one_lt_left hm_pos hp.out.one_lt
      have hm_choose : ∀ j, 0 < j → j < m → (m.choose j : D) = 0 := by
        intro j hj hjm
        -- Compare coefficient of `X^(p*j)` in `(1 + X)^(p*m) = (1 + X^p)^m` in `D[X]`
        have hpoly : (1 + (Polynomial.X : Polynomial D)) ^ (p * m) =
            (1 + Polynomial.X ^ p) ^ m := by
          rw [pow_mul, add_pow_char (1 : Polynomial D) Polynomial.X p, one_pow]
        have hcoeff := congrArg (fun q : Polynomial D => q.coeff (p * j)) hpoly
        have hlhs : ((1 + (Polynomial.X : Polynomial D)) ^ (p * m)).coeff (p * j) =
            ((p * m).choose (p * j) : D) := by
          rw [add_comm, add_pow, Polynomial.finset_sum_coeff]
          rw [Finset.sum_eq_single (p * j)]
          · simp
          · intro b _ hne
            simp [Polynomial.coeff_X_pow, Ne.symm hne]
          · intro hnm
            exfalso; apply hnm; exact Finset.mem_range.mpr (by nlinarith [hp.out.pos])
        have hrhs : ((1 + (Polynomial.X : Polynomial D) ^ p) ^ m).coeff (p * j) =
            (m.choose j : D) := by
          rw [add_comm, add_pow, Polynomial.finset_sum_coeff]
          rw [Finset.sum_eq_single j]
          · simp [← pow_mul, mul_comm]
          · intro b _ hne
            have hne' : p * b ≠ p * j := fun h => hne (mul_left_cancel₀ hp.out.ne_zero h)
            simp [← pow_mul, mul_comm b p, Polynomial.coeff_X_pow, Ne.symm hne']
          · intro hnm
            exfalso; apply hnm; exact Finset.mem_range.mpr (by omega)
        rw [hlhs, hrhs] at hcoeff
        have h0 : ((p * m).choose (p * j) : D) = 0 :=
          hchoose (p * j) (by nlinarith [hp.out.pos]) (by nlinarith [hp.out.pos])
        rw [← hcoeff, h0]
      obtain ⟨k, hk⟩ := ih m hm_lt hm_pos hm_choose
      exact ⟨k + 1, by rw [hk, pow_succ']⟩

/-- In characteristic `p`, if `0 < r < p^k` and `n = q * p^k + r`, then `(n.choose r : D) ≠ 0`. -/
lemma choose_mod_prime_pow_ne_zero {p : ℕ} [hp : Fact p.Prime] [IsDomain D] [CharP D p]
    (k q r : ℕ) (hr : r < p ^ k) :
    (((q * p ^ k + r).choose r : ℕ) : D) ≠ 0 := by
  have hpoly : (1 + (Polynomial.X : Polynomial D)) ^ (q * p ^ k + r) =
      (1 + Polynomial.X ^ (p ^ k)) ^ q * (1 + Polynomial.X) ^ r := by
    rw [pow_add, mul_comm q (p ^ k), pow_mul, add_pow_char_pow (1 : Polynomial D) Polynomial.X p k,
      one_pow]
  have hcoeff := congrArg (fun f : Polynomial D => f.coeff r) hpoly
  have hlhs : ((1 + (Polynomial.X : Polynomial D)) ^ (q * p ^ k + r)).coeff r =
      ((q * p ^ k + r).choose r : D) := by
    rw [add_comm, add_pow, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro hnm; exfalso; apply hnm; exact Finset.mem_range.mpr (by omega)
  have hrhs : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q * (1 + Polynomial.X) ^ r).coeff r =
      1 := by
    rw [Polynomial.coeff_mul]
    rw [Finset.sum_eq_single (0, r)]
    · have h0 : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp [zero_pow (pow_ne_zero k hp.out.ne_zero)]
      have hr1 : ((1 + (Polynomial.X : Polynomial D)) ^ r).coeff r = 1 := by
        rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single r]
        · simp
        · intro b _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
        · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr (Nat.lt_succ_self _))
      rw [h0, hr1, mul_one]
    · rintro ⟨a, b⟩ hab hne
      have hab_sum : a + b = r := by simpa using hab
      have ha_pos : 0 < a := by
        by_contra h
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero (not_lt.mp h)
        exact hne (Prod.ext ha0 (by omega))
      have ha_lt : a < p ^ k := by omega
      have hca : ((1 + (Polynomial.X : Polynomial D) ^ (p ^ k)) ^ q).coeff a = 0 := by
        rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro j _
        have hne' : p ^ k * j ≠ a := by
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · simp; omega
          · have : p ^ k ≤ p ^ k * j := Nat.le_mul_of_pos_right _ hj
            omega
        simp [← pow_mul, Polynomial.coeff_X_pow, Ne.symm hne']
      rw [hca, zero_mul]
    · intro hnm
      exfalso; exact hnm (by simp)
  rw [hlhs, hrhs] at hcoeff
  rw [hcoeff]
  exact one_ne_zero

/-- Lemma 2.1 (iv) (char `p` local slice): for any non-trivial exponential map `φ` on a domain `D`
    of prime characteristic `p`, there exist `s ∈ D \ D^φ` and `c ∈ D^φ \ {0}` such that
    for every `a ∈ D`, there exists `N : ℕ` with `c ^ N * a ∈ (D^φ)[s]`. -/
lemma exists_local_slice {p : ℕ} [hp : Fact p.Prime] [IsDomain D] [CharP D p]
    (φ : ExpMap K D) (hnt : φ.IsNontrivial) :
    ∃ (s : D) (c : φ.invSubalg), (c : D) ≠ 0 ∧ s ∉ φ.invSubalg ∧
      ∀ a : D, ∃ (N : ℕ) (P : Polynomial φ.invSubalg), (c : D) ^ N * a = Polynomial.aeval s P := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ s : D, (φ s).natDegree = d := by
    obtain ⟨a, ha⟩ := hnt
    exact ⟨(φ a).natDegree, Nat.pos_of_ne_zero (mt (φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr ha),
      a, rfl⟩
  let d := Nat.find hex
  have hd_spec := Nat.find_spec hex
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨s, hs_deg0⟩ := hd_spec.2
  have hs_deg : (φ s).natDegree = d := hs_deg0
  have hd_min : ∀ a : D, 0 < (φ a).natDegree → d ≤ (φ a).natDegree := fun a ha =>
    Nat.find_min' hex ⟨ha, a, rfl⟩
  have hs_ne : φ s ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hs_deg; omega
  have hchoose : ∀ i, 0 < i → i < d → (d.choose i : D) = 0 := by
    intro i hi hid
    have hcoeff_deg : (φ ((φ s).coeff i)).natDegree = 0 := by
      by_contra hne
      have hpos : 0 < (φ ((φ s).coeff i)).natDegree := Nat.pos_of_ne_zero hne
      have hge : d ≤ (φ ((φ s).coeff i)).natDegree := hd_min _ hpos
      have hco := φ.coeff_coeff_coassoc s i (φ ((φ s).coeff i)).natDegree
      have hlc : (φ ((φ s).coeff i)).coeff (φ ((φ s).coeff i)).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega)
      have hgt : d < i + (φ ((φ s).coeff i)).natDegree := by omega
      have h0 : (φ s).coeff (i + (φ ((φ s).coeff i)).natDegree) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0, mul_zero] at hco
      exact hlc hco
    have hco := φ.coeff_coeff_coassoc s i (d - i)
    rw [Nat.add_sub_cancel' (le_of_lt hid)] at hco
    have hlhs0 : (φ ((φ s).coeff i)).coeff (d - i) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hlhs0] at hco
    have hslc : (φ s).coeff d ≠ 0 := by
      rw [← hs_deg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hs_ne
    exact (mul_eq_zero.mp hco.symm).resolve_right hslc
  obtain ⟨k, hk⟩ := eq_prime_pow_of_choose_eq_zero (D := D) hd_pos hchoose
  have hd_dvd : ∀ a : D, d ∣ (φ a).natDegree := by
    intro a
    by_contra hndvd
    let n := (φ a).natDegree
    let r := n % d
    have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
    have hr_lt : r < d := Nat.mod_lt n hd_pos
    have hn_eq : n = (n / d) * p ^ k + r := by
      rw [← hk, mul_comm]; exact (Nat.div_add_mod n d).symm
    have hch : ((n.choose r : ℕ) : D) ≠ 0 := by
      rw [hn_eq]; exact choose_mod_prime_pow_ne_zero (D := D) k (n / d) r (by omega)
    have hco := φ.coeff_coeff_coassoc a (n - r) r
    have hsub : n - r + r = n := Nat.sub_add_cancel (by omega)
    rw [hsub] at hco
    have hch' : ((n.choose (n - r) : ℕ) : D) ≠ 0 := by
      rw [Nat.choose_symm (by omega)]; exact hch
    have halc : (φ a).coeff n ≠ 0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by
        exact hndvd (by rw [h, Polynomial.natDegree_zero]; exact dvd_zero d))
    have hne0 : (φ ((φ a).coeff (n - r))).coeff r ≠ 0 := by
      rw [hco]; exact mul_ne_zero hch' halc
    have hdeg_ge : r ≤ (φ ((φ a).coeff (n - r))).natDegree :=
      Polynomial.le_natDegree_of_ne_zero hne0
    have hdeg_le : (φ ((φ a).coeff (n - r))).natDegree ≤ r := by
      by_contra hgt; push_neg at hgt
      have hco2 := φ.coeff_coeff_coassoc a (n - r) (φ ((φ a).coeff (n - r))).natDegree
      have h0 : (φ a).coeff (n - r + (φ ((φ a).coeff (n - r))).natDegree) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0, mul_zero] at hco2
      have hlc2 : (φ ((φ a).coeff (n - r))).coeff (φ ((φ a).coeff (n - r))).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hgt; omega)
      exact hlc2 hco2
    have hmin := hd_min ((φ a).coeff (n - r)) (by omega)
    omega
  let c : φ.invSubalg := ⟨(φ s).leadingCoeff, φ.leadingCoeff_mem_invSubalg s⟩
  have hc_ne : (c : D) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hs_ne
  have hs_not : s ∉ φ.invSubalg := by
    rw [mem_invSubalg_iff_natDegree_eq_zero]; omega
  refine ⟨s, c, hc_ne, hs_not, ?_⟩
  intro a
  generalize hn : (φ a).natDegree = n
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hn0 : n = 0
    · have ha_inv : a ∈ φ.invSubalg := (φ.mem_invSubalg_iff_natDegree_eq_zero a).mpr (by omega)
      exact ⟨0, Polynomial.C ⟨a, ha_inv⟩, by simp⟩
    · obtain ⟨q, hq⟩ := hd_dvd a
      rw [hn] at hq
      let an : φ.invSubalg := ⟨(φ a).leadingCoeff, φ.leadingCoeff_mem_invSubalg a⟩
      let b : D := (c : D) ^ q * a - (an : D) * s ^ q
      have hb_deg : (φ b).natDegree < n := by
        have hφb : φ b = Polynomial.C ((c : D) ^ q) * φ a -
            Polynomial.C (an : D) * (φ s) ^ q := by
          simp only [b, map_sub, map_mul, map_pow]
          have hc_inv : φ (c : D) = Polynomial.C (c : D) := c.2
          have han_inv : φ (an : D) = Polynomial.C (an : D) := an.2
          rw [hc_inv, han_inv, ← map_pow]
        have hφa_ne : φ a ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hn; exact hn0 hn.symm
        have h1_deg : (Polynomial.C ((c : D) ^ q) * φ a).natDegree = n := by
          rw [Polynomial.natDegree_C_mul (pow_ne_zero q hc_ne), hn]
        have h2_deg : (Polynomial.C (an : D) * (φ s) ^ q).natDegree = n := by
          have han_ne : (an : D) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hφa_ne
          rw [Polynomial.natDegree_C_mul han_ne, Polynomial.natDegree_pow, hs_deg, mul_comm, ← hq]
        have hle : (φ b).natDegree ≤ n := by
          rw [hφb]
          exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq h1_deg) (le_of_eq h2_deg))
        have hcn : (φ b).coeff n = 0 := by
          rw [hφb, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
          have hsq : ((φ s) ^ q).natDegree = n := by
            rw [Polynomial.natDegree_pow, hs_deg, mul_comm, ← hq]
          rw [← hn, Polynomial.coeff_natDegree, hn, ← hsq, Polynomial.coeff_natDegree,
            Polynomial.leadingCoeff_pow]
          change (φ s).leadingCoeff ^ q * (φ a).leadingCoeff -
            (φ a).leadingCoeff * (φ s).leadingCoeff ^ q = 0
          ring
        by_contra hge
        have heq : (φ b).natDegree = n := le_antisymm hle (not_lt.mp hge)
        have hne : (φ b).coeff n ≠ 0 := by
          rw [← heq, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at heq; exact hn0 heq.symm)
        exact hne hcn
      obtain ⟨N, P, hNP⟩ := ih (φ b).natDegree hb_deg b rfl
      refine ⟨N + q, P + Polynomial.C ((c ^ N : φ.invSubalg) * an) * Polynomial.X ^ q, ?_⟩
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        Subalgebra.coe_mul, Subalgebra.coe_pow]
      change (c : D) ^ (N + q) * a =
        Polynomial.aeval s P + (c : D) ^ N * (an : D) * s ^ q
      rw [← hNP]
      simp only [b, pow_add]
      ring

/-- Transport an exponential map along a `K`-algebra isomorphism. -/
def compAlgEquiv {D' : Type*} [CommRing D'] [Algebra K D']
    (e : D ≃ₐ[K] D') (φ : ExpMap K D) : ExpMap K D' where
  toAlgHom := (Polynomial.mapAlgHom e.toAlgHom).comp (φ.toAlgHom.comp e.symm.toAlgHom)
  eval_zero a := by
    change (Polynomial.map e.toRingHom (φ (e.symm a))).eval 0 = a
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      φ.eval_zero]
    exact e.apply_symm_apply a
  coassoc a := by
    have h := congrArg (Polynomial.map (Polynomial.mapRingHom e.toRingHom)) (φ.coassoc (e.symm a))
    simp only [Polynomial.map_map] at h
    have hlhs : Polynomial.map ((Polynomial.mapAlgHom e.toAlgHom).comp
        (φ.toAlgHom.comp e.symm.toAlgHom)).toRingHom
        (Polynomial.map e.toRingHom (φ (e.symm a))) =
        Polynomial.map ((Polynomial.mapRingHom e.toRingHom).comp φ.toAlgHom.toRingHom)
          (φ (e.symm a)) := by
      rw [Polynomial.map_map]
      congr 1; ext x
      simp [e.symm_apply_apply]
    change Polynomial.map ((Polynomial.mapAlgHom e.toAlgHom).comp
        (φ.toAlgHom.comp e.symm.toAlgHom)).toRingHom
        (Polynomial.map e.toRingHom (φ (e.symm a))) =
      Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        (Polynomial.C Polynomial.X + Polynomial.X)
        (Polynomial.map e.toRingHom (φ (e.symm a)))
    rw [hlhs, h]
    generalize φ (e.symm a) = P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add, map_add, Polynomial.map_add, hp, hq]
    | monomial n c =>
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.map_monomial,
        RingHom.comp_apply, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- Coordinate translation exponential map on `MvPolynomial (Fin 3) K`:
    `X i ↦ C (X i) + X` and `X j ↦ C (X j)` for `j ≠ i`. -/
def mvPolyShift (K : Type*) [CommRing K] (i : Fin 3) : ExpMap K (MvPolynomial (Fin 3) K) where
  toAlgHom := MvPolynomial.aeval (fun j =>
    Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)
  eval_zero a := by
    have hcomp : (Polynomial.evalRingHom (0 : MvPolynomial (Fin 3) K)).comp
        (MvPolynomial.aeval (fun j =>
          Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)).toRingHom =
        RingHom.id (MvPolynomial (Fin 3) K) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp
      · intro j; by_cases hj : j = i <;> simp [hj]
    exact RingHom.congr_fun hcomp a
  coassoc a := by
    let ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
      MvPolynomial.aeval (fun j =>
        Polynomial.C (MvPolynomial.X j) + if j = i then Polynomial.X else 0)
    let cc : MvPolynomial (Fin 3) K →+*
        Polynomial (Polynomial (MvPolynomial (Fin 3) K)) :=
      Polynomial.C.comp Polynomial.C
    let evVU : Polynomial (MvPolynomial (Fin 3) K) →+*
        Polynomial (Polynomial (MvPolynomial (Fin 3) K)) :=
      Polynomial.eval₂RingHom cc
        ((Polynomial.C Polynomial.X + Polynomial.X :
          Polynomial (Polynomial (MvPolynomial (Fin 3) K))))
    have hcomp : (Polynomial.mapRingHom ψ.toRingHom).comp ψ.toRingHom =
        evVU.comp ψ.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [ψ, evVU, cc]
      · intro j
        by_cases hj : j = i
        · subst hj
          simp [ψ, evVU, cc, add_assoc]
        · simp [ψ, evVU, cc, hj]
    exact RingHom.congr_fun hcomp a

/-- Lemma 2.4: If every non-trivial exponential map `φ` on `D` has `D^φ ⊆ S` for some
    proper subalgebra `S < ⊤`, then `D ≇ₐ[K] MvPolynomial (Fin 3) K`. -/
lemma not_algEquiv_mvPoly3_of_invSubalg_le [Nontrivial K]
    (S : Subalgebra K D) (hS : S ≠ ⊤)
    (hinv : ∀ φ : ExpMap K D, φ.IsNontrivial → φ.invSubalg ≤ S) :
    ¬ Nonempty (D ≃ₐ[K] MvPolynomial (Fin 3) K) := by
  rintro ⟨e⟩
  apply hS
  rw [eq_top_iff]
  intro a _
  have hgen : ∀ j : Fin 3, e.symm (MvPolynomial.X j) ∈ S := by
    intro j
    -- Pick `i ≠ j`
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, j ≠ i := by
      fin_cases j
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    let φ0 := mvPolyShift K i
    let φ := φ0.compAlgEquiv e.symm
    have hnt : φ.IsNontrivial := by
      refine ⟨e.symm (MvPolynomial.X i), ?_⟩
      intro hmem
      change φ (e.symm (MvPolynomial.X i)) = Polynomial.C (e.symm (MvPolynomial.X i)) at hmem
      have h1 : φ (e.symm (MvPolynomial.X i)) =
          Polynomial.C (e.symm (MvPolynomial.X i)) + Polynomial.X := by
        simp [φ, compAlgEquiv, φ0, mvPolyShift]
      rw [h1] at hmem
      have hX0 : (Polynomial.X : Polynomial D) = 0 := add_left_cancel (hmem.trans (add_zero _).symm)
      have h10 := congrArg (fun q : Polynomial D => q.coeff 1) hX0
      simp at h10
      haveI : Nontrivial D := e.symm.injective.nontrivial
      exact one_ne_zero h10
    have hj_mem : e.symm (MvPolynomial.X j) ∈ φ.invSubalg := by
      change φ (e.symm (MvPolynomial.X j)) = Polynomial.C (e.symm (MvPolynomial.X j))
      simp [φ, compAlgEquiv, φ0, mvPolyShift, hij]
    exact hinv φ hnt hj_mem
  have ha_eq : a = e.symm (e a) := (e.symm_apply_apply a).symm
  rw [ha_eq]
  generalize e a = P
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    exact S.algebraMap_mem c
  | add p q hp hq =>
    rw [map_add]; exact S.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]; exact S.mul_mem hp (hgen j)

end ExpMap

end ExpMaps

/- ## Section 5: `ℤ`-gradings and homogenization of exponential maps (Theorem 2.3) -/

section Homogenization

/-- A `ℤ`-grading on a `K`-domain `E` given by `K`-linear projections `proj n : E →ₗ[K] E`. -/
structure ZGrading (K E : Type*) [Field K] [CommRing E] [IsDomain E] [Algebra K E] where
  proj : ℤ → (E →ₗ[K] E)
  supp : E → Finset ℤ
  mem_supp : ∀ x n, n ∈ supp x ↔ proj n x ≠ 0
  sum_proj : ∀ x : E, ∑ n ∈ supp x, proj n x = x
  proj_proj : ∀ m n : ℤ, ∀ x : E, proj m (proj n x) = if m = n then proj n x else 0
  proj_mul_hom : ∀ m n : ℤ, ∀ x y : E,
    proj m x = x → proj n y = y → proj (m + n) (x * y) = x * y
  proj_algebraMap : ∀ n : ℤ, ∀ c : K,
    proj n (algebraMap K E c) = if n = 0 then algebraMap K E c else 0

namespace ZGrading

variable {K E : Type*} [Field K] [CommRing E] [IsDomain E] [Algebra K E]

lemma supp_nonempty (gr : ZGrading K E) {x : E} (hx : x ≠ 0) : (gr.supp x).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hsum := gr.sum_proj x
  rw [h, Finset.sum_empty] at hsum
  exact hx hsum.symm

def topDeg (gr : ZGrading K E) (x : E) (hx : x ≠ 0) : ℤ :=
  (gr.supp x).max' (gr.supp_nonempty hx)

open scoped Classical in
def topComp (gr : ZGrading K E) (x : E) : E :=
  if h : x = 0 then 0 else gr.proj (gr.topDeg x h) x

lemma topComp_ne_zero (gr : ZGrading K E) {x : E} (hx : x ≠ 0) : gr.topComp x ≠ 0 := by
  rw [topComp, dif_neg hx]
  exact (gr.mem_supp x _).mp (Finset.max'_mem _ _)

lemma proj_eq_zero_of_gt_topDeg (gr : ZGrading K E) {x : E} (hx : x ≠ 0) {n : ℤ}
    (hn : gr.topDeg x hx < n) : gr.proj n x = 0 := by
  by_contra hne
  have hmem : n ∈ gr.supp x := (gr.mem_supp x n).mpr hne
  have hle : n ≤ gr.topDeg x hx := Finset.le_max' _ _ hmem
  omega

/-- Degree bound predicate: `DegLe gr x d` means `proj n x = 0` for all `n > d`. -/
def DegLe (gr : ZGrading K E) (x : E) (d : ℤ) : Prop :=
  ∀ n : ℤ, d < n → gr.proj n x = 0

lemma degLe_zero (gr : ZGrading K E) (d : ℤ) : gr.DegLe 0 d := fun _ _ => by simp

lemma degLe_topDeg (gr : ZGrading K E) {x : E} (hx : x ≠ 0) : gr.DegLe x (gr.topDeg x hx) :=
  fun _ hn => gr.proj_eq_zero_of_gt_topDeg hx hn

lemma topDeg_le_of_degLe (gr : ZGrading K E) {x : E} (hx : x ≠ 0) {d : ℤ}
    (h : gr.DegLe x d) : gr.topDeg x hx ≤ d := by
  by_contra hgt
  exact gr.topComp_ne_zero hx (by rw [topComp, dif_neg hx]; exact h _ (not_le.mp hgt))

lemma degLe_mono (gr : ZGrading K E) {x : E} {d₁ d₂ : ℤ} (h : gr.DegLe x d₁) (hle : d₁ ≤ d₂) :
    gr.DegLe x d₂ := fun n hn => h n (lt_of_le_of_lt hle hn)

lemma degLe_add (gr : ZGrading K E) {x y : E} {d : ℤ}
    (hx : gr.DegLe x d) (hy : gr.DegLe y d) : gr.DegLe (x + y) d := fun n hn => by
  rw [map_add, hx n hn, hy n hn, add_zero]

lemma degLe_sub (gr : ZGrading K E) {x y : E} {d : ℤ}
    (hx : gr.DegLe x d) (hy : gr.DegLe y d) : gr.DegLe (x - y) d := fun n hn => by
  rw [map_sub, hx n hn, hy n hn, sub_zero]

lemma degLe_smul (gr : ZGrading K E) {x : E} {d : ℤ} (c : K) (hx : gr.DegLe x d) :
    gr.DegLe (c • x) d := fun n hn => by
  rw [map_smul, hx n hn, smul_zero]

lemma degLe_algebraMap (gr : ZGrading K E) (c : K) : gr.DegLe (algebraMap K E c) 0 :=
  fun n hn => by rw [gr.proj_algebraMap, if_neg (ne_of_gt hn)]

lemma proj_mul_of_hom (gr : ZGrading K E) (m n k : ℤ) (x y : E)
    (hx : gr.proj m x = x) (hy : gr.proj n y = y) :
    gr.proj k (x * y) = if k = m + n then x * y else 0 := by
  have hmn : gr.proj (m + n) (x * y) = x * y := gr.proj_mul_hom m n x y hx hy
  rw [← hmn, gr.proj_proj, hmn]

lemma proj_mul_eq_sum (gr : ZGrading K E) (k : ℤ) (x y : E) :
    gr.proj k (x * y) =
      ∑ i ∈ gr.supp x, ∑ j ∈ gr.supp y, if k = i + j then gr.proj i x * gr.proj j y else 0 := by
  conv_lhs => rw [← gr.sum_proj x, ← gr.sum_proj y]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact gr.proj_mul_of_hom i j k _ _ (by rw [gr.proj_proj, if_pos rfl])
    (by rw [gr.proj_proj, if_pos rfl])

lemma degLe_mul (gr : ZGrading K E) {x y : E} {a b : ℤ}
    (hx : gr.DegLe x a) (hy : gr.DegLe y b) : gr.DegLe (x * y) (a + b) := by
  intro k hk
  rw [gr.proj_mul_eq_sum]
  apply Finset.sum_eq_zero; intro i hi
  apply Finset.sum_eq_zero; intro j hj
  have hi_le : i ≤ a := by
    by_contra hgt; exact (gr.mem_supp x i).mp hi (hx i (not_le.mp hgt))
  have hj_le : j ≤ b := by
    by_contra hgt; exact (gr.mem_supp y j).mp hj (hy j (not_le.mp hgt))
  rw [if_neg (by omega)]

lemma proj_mul_top (gr : ZGrading K E) {x y : E} {a b : ℤ}
    (hx : gr.DegLe x a) (hy : gr.DegLe y b) :
    gr.proj (a + b) (x * y) = gr.proj a x * gr.proj b y := by
  rw [gr.proj_mul_eq_sum]
  by_cases ha : a ∈ gr.supp x
  · rw [Finset.sum_eq_single a]
    · by_cases hb : b ∈ gr.supp y
      · rw [Finset.sum_eq_single b]
        · simp
        · intro j _ hjb; rw [if_neg (by omega)]
        · intro hnm; exact absurd hb hnm
      · have hb0 : gr.proj b y = 0 := not_not.mp (mt (gr.mem_supp y b).mpr hb)
        rw [hb0, mul_zero]
        apply Finset.sum_eq_zero; intro j hj
        have hjb : j ≠ b := fun h => hb (h ▸ hj)
        rw [if_neg (by omega)]
    · intro i hi hia
      have hi_lt : i < a := by
        have hle : i ≤ a := by
          by_contra hgt; exact (gr.mem_supp x i).mp hi (hx i (not_le.mp hgt))
        omega
      apply Finset.sum_eq_zero; intro j hj
      have hj_le : j ≤ b := by
        by_contra hgt; exact (gr.mem_supp y j).mp hj (hy j (not_le.mp hgt))
      rw [if_neg (by omega)]
    · intro hnm; exact absurd ha hnm
  · have ha0 : gr.proj a x = 0 := not_not.mp (mt (gr.mem_supp x a).mpr ha)
    rw [ha0, zero_mul]
    apply Finset.sum_eq_zero; intro i hi
    have hi_lt : i < a := by
      have hle : i ≤ a := by
        by_contra hgt; exact (gr.mem_supp x i).mp hi (hx i (not_le.mp hgt))
      have hne : i ≠ a := fun h => ha (h ▸ hi)
      omega
    apply Finset.sum_eq_zero; intro j hj
    have hj_le : j ≤ b := by
      by_contra hgt; exact (gr.mem_supp y j).mp hj (hy j (not_le.mp hgt))
    rw [if_neg (by omega)]

lemma topDeg_mul (gr : ZGrading K E) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    gr.topDeg (x * y) (mul_ne_zero hx hy) = gr.topDeg x hx + gr.topDeg y hy := by
  apply le_antisymm
  · exact gr.topDeg_le_of_degLe (mul_ne_zero hx hy)
      (gr.degLe_mul (gr.degLe_topDeg hx) (gr.degLe_topDeg hy))
  · have hne : gr.proj (gr.topDeg x hx + gr.topDeg y hy) (x * y) ≠ 0 := by
      rw [gr.proj_mul_top (gr.degLe_topDeg hx) (gr.degLe_topDeg hy)]
      exact mul_ne_zero ((gr.mem_supp x _).mp (Finset.max'_mem _ _))
        ((gr.mem_supp y _).mp (Finset.max'_mem _ _))
    exact Finset.le_max' _ _ ((gr.mem_supp (x * y) _).mpr hne)

lemma topComp_mul (gr : ZGrading K E) (x y : E) :
    gr.topComp (x * y) = gr.topComp x * gr.topComp y := by
  by_cases hx : x = 0
  · subst hx; simp [topComp]
  · by_cases hy : y = 0
    · subst hy; simp [topComp]
    · rw [topComp, dif_neg (mul_ne_zero hx hy), topComp, dif_neg hx, topComp, dif_neg hy,
        gr.topDeg_mul hx hy, gr.proj_mul_top (gr.degLe_topDeg hx) (gr.degLe_topDeg hy)]

/-- Helper: `ExpMap.coassoc` is equivalent to the coefficient identity
    `∀ a i r, (φ ((φ a).coeff i)).coeff r = ((i + r).choose i : D) * (φ a).coeff (i + r)`. -/
lemma coassoc_of_coeff_coeff {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (f : D →ₐ[K] Polynomial D)
    (hcoeff : ∀ (a : D) (i r : ℕ),
      (f ((f a).coeff i)).coeff r = ((i + r).choose i : D) * (f a).coeff (i + r))
    (a : D) :
    Polynomial.map f.toRingHom (f a) =
    Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      (Polynomial.C Polynomial.X + Polynomial.X) (f a) := by
  ext i r
  rw [Polynomial.coeff_map]
  change (f ((f a).coeff i)).coeff r = _
  rw [hcoeff a i r]
  generalize f a = P
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, mul_add]
    rw [hp, hq]
  | monomial n c =>
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, RingHom.comp_apply]
    rw [add_pow, Finset.mul_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D)))).coeff i).coeff r) =
        if k = r ∧ n - k = i then (n.choose i : D) * c else 0 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : Polynomial.C (Polynomial.C c) *
          (Polynomial.C Polynomial.X ^ k * Polynomial.X ^ (n - k) *
            (n.choose k : Polynomial (Polynomial D))) =
          Polynomial.C (Polynomial.C (c * (n.choose k : D)) * Polynomial.X ^ k) *
          Polynomial.X ^ (n - k) := by
        simp only [map_mul, map_natCast, Polynomial.C_pow]; ring
      rw [h1, Polynomial.coeff_C_mul_X_pow]
      by_cases hni : i = n - k
      · rw [if_pos hni, Polynomial.coeff_C_mul_X_pow]
        by_cases hkr : r = k
        · rw [if_pos hkr, if_pos ⟨hkr.symm, hni.symm⟩]
          rw [show n.choose k = n.choose i by rw [hni]; exact (Nat.choose_symm hkn).symm, mul_comm]
        · rw [if_neg hkr, if_neg (fun h => hkr h.1.symm)]
      · rw [if_neg hni, Polynomial.coeff_zero, if_neg (fun h => hni h.2.symm)]
    rw [Finset.sum_congr rfl hterm, Polynomial.coeff_monomial]
    by_cases hnir : n = i + r
    · subst hnir
      rw [if_pos rfl, Finset.sum_eq_single r]
      · simp [Nat.add_sub_cancel]
      · intro k _ hkr; rw [if_neg (fun h => hkr h.1)]
      · intro hr; exfalso; exact hr (Finset.mem_range.mpr (by omega))
    · rw [if_neg hnir, mul_zero]
      symm
      apply Finset.sum_eq_zero; intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg]; rintro ⟨rfl, hsub⟩; exact hnir (by omega)

set_option maxHeartbeats 800000 in
/-- Theorem 2.3 (Derksen–Hadas–Makar-Limanov homogenization of exponential maps). -/
theorem homogenizeExpMap (gr : ZGrading K E)
    (D G : Subalgebra K E)
    (hG_graded : ∀ b ∈ G, ∀ n : ℤ, gr.proj n b ∈ G)
    (hDG : ∀ a ∈ D, ∀ d : ℤ, gr.DegLe a d → gr.proj d a ∈ G)
    (hGD : ∀ b ∈ G, ∀ d : ℤ, gr.proj d b = b → ∃ a ∈ D, gr.DegLe a d ∧ gr.proj d a = b)
    (Γ : Finset D)
    (hΓ_ne : ∀ g ∈ Γ, (g : E) ≠ 0)
    (hΓ_admiss : ∀ (a : D) (d : ℤ), gr.DegLe (a : E) d →
      ∃ (L : List (K × List D)),
        (∀ p ∈ L, ∀ g ∈ p.2, g ∈ Γ) ∧
        (∀ p ∈ L, gr.DegLe ((p.2.map Subtype.val).prod) d) ∧
        (a : E) = (L.map (fun p => p.1 • (p.2.map Subtype.val).prod)).sum)
    (φ : ExpMap K D) (hnt : φ.IsNontrivial) :
    ∃ φbar : ExpMap K G, φbar.IsNontrivial ∧
      ∀ a : D, a ∈ φ.invSubalg →
        (⟨gr.topComp (a : E), by
          by_cases ha : (a : E) = 0
          · simp [topComp, ha, G.zero_mem]
          · rw [topComp, dif_neg ha]; exact hDG a a.2 _ (gr.degLe_topDeg ha)⟩ : G) ∈
          φbar.invSubalg := by
  classical
  -- Step 1: Collect all pairs `(g, i)` with `g ∈ Γ`, `1 ≤ i ≤ natDegree (φ g)`, `(φ g).coeff i ≠ 0`
  let pairs : Finset (D × ℕ) :=
    Γ.biUnion fun g =>
      ((Finset.Icc 1 (φ g).natDegree).filter fun i => ((φ g).coeff i : E) ≠ 0).map
        ⟨fun i => (g, i), fun _ _ h => (Prod.mk.inj h).2⟩
  have hpairs_ne : pairs.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hΓ_inv : ∀ g ∈ Γ, g ∈ φ.invSubalg := by
      intro g hg
      rw [φ.mem_invSubalg_iff_natDegree_eq_zero]
      by_contra hne
      have hpos : 0 < (φ g).natDegree := Nat.pos_of_ne_zero hne
      have hlc : ((φ g).coeff (φ g).natDegree : E) ≠ 0 := by
        intro h0
        exact Polynomial.leadingCoeff_ne_zero.mpr
          (fun h => by rw [h, Polynomial.natDegree_zero] at hpos; omega)
          (Subtype.ext h0)
      have hmem : (g, (φ g).natDegree) ∈ pairs := by
        simp only [pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_Icc,
          Function.Embedding.coeFn_mk]
        exact ⟨g, hg, (φ g).natDegree, ⟨⟨hpos, le_refl _⟩, hlc⟩, rfl⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
    obtain ⟨a, ha⟩ := hnt
    apply ha
    by_cases ha0 : (a : E) = 0
    · have : a = 0 := Subtype.ext ha0; rw [this]; exact φ.invSubalg.zero_mem
    · obtain ⟨L, hLΓ, _, hLsum⟩ := hΓ_admiss a (gr.topDeg (a : E) ha0) (gr.degLe_topDeg ha0)
      have hcoe_list : ∀ M : List (K × List D),
          (((M.map (fun p => (p.1 • p.2.prod : D))).sum : D) : E) =
          (M.map (fun p => p.1 • (p.2.map Subtype.val).prod)).sum := by
        intro M
        induction M with
        | nil => simp
        | cons hd tl ih =>
          simp only [List.map_cons, List.sum_cons, Subalgebra.coe_add, Subalgebra.coe_smul, ih]
          congr 2
          induction hd.2 with
          | nil => simp
          | cons x xs ihx => simp [ihx]
      have ha_eq : a = (L.map (fun p => p.1 • p.2.prod)).sum :=
        Subtype.ext (hLsum.trans (hcoe_list L).symm)
      rw [ha_eq]
      have hmem_sum : ∀ M : List (K × List D), (∀ p ∈ M, ∀ g ∈ p.2, g ∈ Γ) →
          (M.map (fun p => p.1 • p.2.prod)).sum ∈ φ.invSubalg := by
        intro M hM
        induction M with
        | nil => simp [φ.invSubalg.zero_mem]
        | cons hd tl ih =>
          simp only [List.map_cons, List.sum_cons]
          refine φ.invSubalg.add_mem ?_ (ih (fun p hp => hM p (List.mem_cons_of_mem _ hp)))
          refine φ.invSubalg.smul_mem ?_ hd.1
          have hprod : ∀ l : List D, (∀ g ∈ l, g ∈ Γ) → l.prod ∈ φ.invSubalg := by
            intro l hl
            induction l with
            | nil => simp [φ.invSubalg.one_mem]
            | cons x xs ihx =>
              simp only [List.prod_cons]
              exact φ.invSubalg.mul_mem (hΓ_inv x (hl x List.mem_cons_self))
                (ihx (fun g hg => hl g (List.mem_cons_of_mem _ hg)))
          exact hprod hd.2 (hM hd List.mem_cons_self)
      exact hmem_sum L hLΓ
  -- Step 2: Pick `(g₀, den)` maximizing the rational slope `(topDeg (coeff i (φ g)) - topDeg g) / i`
  let slope : D × ℕ → ℚ := fun x =>
    if h : x ∈ pairs then
      have hg : x.1 ∈ Γ := by
        simp only [pairs, Finset.mem_biUnion, Finset.mem_map] at h
        rcases h with ⟨g, hg, _, _, hEq⟩
        cases hEq; exact hg
      have hc : ((φ x.1).coeff x.2 : E) ≠ 0 := by
        simp only [pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter] at h
        rcases h with ⟨g, _, i, ⟨_, hi⟩, hEq⟩
        cases hEq; exact hi
      ((gr.topDeg ((φ x.1).coeff x.2 : E) hc - gr.topDeg (x.1 : E) (hΓ_ne x.1 hg) : ℤ) : ℚ) /
        (x.2 : ℚ)
    else 0
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := Finset.exists_max_image pairs slope hpairs_ne
  let g₀ : D := x₀.1
  let den : ℕ := x₀.2
  have hg₀_mem : g₀ ∈ Γ := by
    simp only [pairs, Finset.mem_biUnion, Finset.mem_map] at hx₀_mem
    rcases hx₀_mem with ⟨g, hg, _, _, hEq⟩
    cases hEq; exact hg
  have hden_pos : 0 < den := by
    simp only [pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_Icc] at hx₀_mem
    rcases hx₀_mem with ⟨_, _, i, ⟨⟨hi, _⟩, _⟩, hEq⟩
    cases hEq; exact hi
  have hc₀_ne : ((φ g₀).coeff den : E) ≠ 0 := by
    simp only [pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter] at hx₀_mem
    rcases hx₀_mem with ⟨_, _, i, ⟨_, hi⟩, hEq⟩
    cases hEq; exact hi
  let num : ℤ := gr.topDeg ((φ g₀).coeff den : E) hc₀_ne - gr.topDeg (g₀ : E) (hΓ_ne g₀ hg₀_mem)
  -- Step 3: Slope bound predicate `SlopeBound a d`
  let SlopeBound (a : D) (d : ℤ) : Prop :=
    ∀ (i : ℕ) (n : ℤ), (den : ℤ) * d + (i : ℤ) * num < (den : ℤ) * n →
      gr.proj n ((φ a).coeff i : E) = 0
  have hSB_mono : ∀ {a d₁ d₂}, SlopeBound a d₁ → d₁ ≤ d₂ → SlopeBound a d₂ := by
    intro a d₁ d₂ h hle i n hn
    apply h i n
    have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
    nlinarith
  have hSB_zero : ∀ d, SlopeBound 0 d := fun d i n _ => by simp
  have hSB_add : ∀ {a b d}, SlopeBound a d → SlopeBound b d → SlopeBound (a + b) d := by
    intro a b d ha hb i n hn
    simp only [map_add, Polynomial.coeff_add, Subalgebra.coe_add]
    rw [ha i n hn, hb i n hn, add_zero]
  have hSB_smul : ∀ {a d} (c : K), SlopeBound a d → SlopeBound (c • a) d := by
    intro a d c ha i n hn
    simp only [map_smul, Polynomial.coeff_smul, Subalgebra.coe_smul, map_smul]
    rw [ha i n hn, smul_zero]
  have hSB_one : SlopeBound 1 0 := by
    intro i n hn
    rw [map_one]
    by_cases hi : i = 0
    · subst hi
      simp only [Polynomial.coeff_one_zero, Subalgebra.coe_one]
      have h0 : (1 : E) = algebraMap K E 1 := (map_one _).symm
      rw [h0, gr.proj_algebraMap, if_neg]
      intro hn0; subst hn0; simp at hn
    · rw [Polynomial.coeff_one, if_neg hi, Subalgebra.coe_zero, map_zero]
  have hSB_mul : ∀ {a b da db}, SlopeBound a da → SlopeBound b db → SlopeBound (a * b) (da + db) := by
    intro a b da db ha hb k n hn
    rw [map_mul, Polynomial.coeff_mul]
    simp only [AddSubmonoidClass.coe_finset_sum, map_sum]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij_sum : i + j = k := by simpa using hij
    simp only [Subalgebra.coe_mul]
    rw [gr.proj_mul_eq_sum]
    apply Finset.sum_eq_zero; intro m hm
    apply Finset.sum_eq_zero; intro l hl
    by_cases hml : n = m + l
    · exfalso
      subst hml
      have hm_le : (den : ℤ) * m ≤ (den : ℤ) * da + (i : ℤ) * num := by
        by_contra hgt; exact (gr.mem_supp _ m).mp hm (ha i m (not_le.mp hgt))
      have hl_le : (den : ℤ) * l ≤ (den : ℤ) * db + (j : ℤ) * num := by
        by_contra hgt; exact (gr.mem_supp _ l).mp hl (hb j l (not_le.mp hgt))
      have hk_z : (i : ℤ) + (j : ℤ) = (k : ℤ) := by exact_mod_cast hij_sum
      rw [← hk_z] at hn
      linarith
    · rw [if_neg hml]
  have hSB_Γ : ∀ (g : D) (hg : g ∈ Γ), SlopeBound g (gr.topDeg (g : E) (hΓ_ne g hg)) := by
    intro g hg i n hn
    by_cases hi : i = 0
    · subst hi
      rw [φ.coeff_zero]
      have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
      simp only [Nat.cast_zero, zero_mul, add_zero] at hn
      have hgt : gr.topDeg (g : E) (hΓ_ne g hg) < n := by nlinarith
      exact gr.proj_eq_zero_of_gt_topDeg (hΓ_ne g hg) hgt
    · by_cases hc0 : ((φ g).coeff i : E) = 0
      · rw [hc0, map_zero]
      · have hi_le : i ≤ (φ g).natDegree :=
          Polynomial.le_natDegree_of_ne_zero (fun h => hc0 (by rw [h]; rfl))
        have hmem : (g, i) ∈ pairs := by
          simp only [pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_Icc,
            Function.Embedding.coeFn_mk]
          exact ⟨g, hg, i, ⟨⟨Nat.pos_of_ne_zero hi, hi_le⟩, hc0⟩, rfl⟩
        have hle_q : slope (g, i) ≤ slope x₀ := hx₀_max (g, i) hmem
        simp only [slope, dif_pos hmem, dif_pos hx₀_mem] at hle_q
        have hi_pos_q : (0 : ℚ) < (i : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)
        have hden_pos_q : (0 : ℚ) < (den : ℚ) := Nat.cast_pos.mpr hden_pos
        rw [div_le_div_iff₀ hi_pos_q hden_pos_q] at hle_q
        have hle_z : (gr.topDeg ((φ g).coeff i : E) hc0 - gr.topDeg (g : E) (hΓ_ne g hg)) * (den : ℤ) ≤
            num * (i : ℤ) := by
          exact_mod_cast hle_q
        have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
        have hgt : gr.topDeg ((φ g).coeff i : E) hc0 < n := by nlinarith
        exact gr.proj_eq_zero_of_gt_topDeg hc0 hgt
  -- Step 4: By admissibility, EVERY `a ∈ D` with `DegLe a d` satisfies `SlopeBound a d`!
  have hSB_all : ∀ (a : D) (d : ℤ), gr.DegLe (a : E) d → SlopeBound a d := by
    intro a d hda
    obtain ⟨L, hLΓ, hLdeg, hLsum⟩ := hΓ_admiss a d hda
    have ha_eq : a = (L.map (fun p => p.1 • p.2.prod)).sum := by
      apply Subtype.ext; rw [hLsum]; clear hLsum
      induction L with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons, Subalgebra.coe_add, Subalgebra.coe_smul]
        congr 1
        · congr 1
          induction hd.2 with
          | nil => simp
          | cons x xs ihx => simp [ihx]
        · exact ih (fun p hp => hLΓ p (List.mem_cons_of_mem _ hp))
            (fun p hp => hLdeg p (List.mem_cons_of_mem _ hp))
    rw [ha_eq]
    have hprod_SB : ∀ l : List D, (∀ g ∈ l, g ∈ Γ) →
        ∃ hne : (l.prod : E) ≠ 0, SlopeBound l.prod (gr.topDeg (l.prod : E) hne) := by
      intro l hl
      induction l with
      | nil =>
        simp only [List.prod_nil]
        have h1ne : ((1 : D) : E) ≠ 0 := one_ne_zero
        refine ⟨h1ne, ?_⟩
        have hdeg0 : gr.topDeg ((1 : D) : E) h1ne = 0 := by
          apply le_antisymm
          · exact gr.topDeg_le_of_degLe h1ne (by
              have h1 : ((1 : D) : E) = algebraMap K E 1 := (map_one _).symm
              rw [h1]; exact gr.degLe_algebraMap 1)
          · apply Finset.le_max'
            rw [gr.mem_supp]
            have h1 : ((1 : D) : E) = algebraMap K E 1 := (map_one _).symm
            rw [h1, gr.proj_algebraMap, if_pos rfl, map_one]; exact one_ne_zero
        rw [hdeg0]; exact hSB_one
      | cons x xs ih =>
        simp only [List.prod_cons]
        have hxΓ : x ∈ Γ := hl x List.mem_cons_self
        obtain ⟨hxs_ne, hxs_SB⟩ := ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))
        have hmul_ne : ((x * xs.prod : D) : E) ≠ 0 :=
          mul_ne_zero (hΓ_ne x hxΓ) hxs_ne
        refine ⟨hmul_ne, ?_⟩
        have hdeg_mul : gr.topDeg ((x * xs.prod : D) : E) hmul_ne =
            gr.topDeg (x : E) (hΓ_ne x hxΓ) + gr.topDeg (xs.prod : E) hxs_ne :=
          gr.topDeg_mul (hΓ_ne x hxΓ) hxs_ne
        rw [hdeg_mul]
        exact hSB_mul (hSB_Γ x hxΓ) hxs_SB
    clear ha_eq hLsum
    induction L with
    | nil => exact hSB_zero d
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      refine hSB_add (hSB_smul hd.1 ?_)
        (ih (fun p hp => hLΓ p (List.mem_cons_of_mem _ hp))
            (fun p hp => hLdeg p (List.mem_cons_of_mem _ hp)))
      obtain ⟨hne, hSB⟩ := hprod_SB hd.2 (hLΓ hd List.mem_cons_self)
      have hval_eq : (hd.2.prod : E) = (hd.2.map Subtype.val).prod := by
        induction hd.2 with
        | nil => simp
        | cons x xs ihx => simp [ihx]
      have hle : gr.topDeg (hd.2.prod : E) hne ≤ d :=
        gr.topDeg_le_of_degLe hne (hval_eq ▸ hLdeg hd List.mem_cons_self)
      exact hSB_mono hSB hle
  -- Step 5: Define the homogeneous projection map on each homogeneous `b ∈ G` of degree `d`
  let liftOf (b : G) (d : ℤ) (hb : gr.proj d (b : E) = (b : E)) : D :=
    ⟨(hGD (b : E) b.2 d hb).choose, (hGD (b : E) b.2 d hb).choose_spec.1⟩
  have hlift_deg : ∀ b d hb, gr.DegLe ((liftOf b d hb : D) : E) d :=
    fun b d hb => (hGD (b : E) b.2 d hb).choose_spec.2.1
  have hlift_proj : ∀ b d hb, gr.proj d ((liftOf b d hb : D) : E) = (b : E) :=
    fun b d hb => (hGD (b : E) b.2 d hb).choose_spec.2.2
  -- Top-slope coefficient of `(φ a).coeff i` relative to degree `d`
  let coeffTop (a : D) (d : ℤ) (i : ℕ) : E :=
    if (den : ℤ) ∣ (i : ℤ) * num then
      gr.proj (d + ((i : ℤ) * num) / (den : ℤ)) ((φ a).coeff i : E)
    else 0
  have hcoeffTop_mem : ∀ (a : D) (d : ℤ) (hda : gr.DegLe (a : E) d) (i : ℕ),
      coeffTop a d i ∈ G := by
    intro a d hda i
    simp only [coeffTop]
    split_ifs with hdiv
    · apply hDG _ ((φ a).coeff i).2
      intro n hn
      apply hSB_all a d hda i n
      have hmul : (den : ℤ) * (((i : ℤ) * num) / (den : ℤ)) = (i : ℤ) * num :=
        Int.mul_ediv_cancel' hdiv
      have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
      nlinarith
    · exact G.zero_mem
  -- Independence of the lift `a` with `DegLe a d` and `proj d a = b`
  have hcoeffTop_indep : ∀ (a₁ a₂ : D) (d : ℤ),
      gr.DegLe (a₁ : E) d → gr.DegLe (a₂ : E) d →
      gr.proj d (a₁ : E) = gr.proj d (a₂ : E) →
      ∀ i : ℕ, coeffTop a₁ d i = coeffTop a₂ d i := by
    intro a₁ a₂ d h1 h2 hproj i
    have hdiff_deg : gr.DegLe ((a₁ - a₂ : D) : E) (d - 1) := by
      intro n hn
      simp only [Subalgebra.coe_sub, map_sub]
      by_cases hnd : n = d
      · subst hnd; exact sub_eq_zero.mpr hproj
      · have hgt : d < n := by omega
        rw [h1 n hgt, h2 n hgt, sub_zero]
    have hdiff_SB := hSB_all (a₁ - a₂) (d - 1) hdiff_deg
    simp only [coeffTop]
    split_ifs with hdiv
    · apply sub_eq_zero.mp
      rw [← map_sub]
      have hsub : ((φ a₁).coeff i : E) - ((φ a₂).coeff i : E) = ((φ (a₁ - a₂)).coeff i : E) := by
        simp [map_sub]
      rw [hsub]
      apply hdiff_SB i
      have hmul : (den : ℤ) * (((i : ℤ) * num) / (den : ℤ)) = (i : ℤ) * num :=
        Int.mul_ediv_cancel' hdiv
      have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
      nlinarith
    · rfl
  -- Build the `K`-linear polynomial `homPoly b d hb : Polynomial G`
  let homPoly (b : G) (d : ℤ) (hb : gr.proj d (b : E) = (b : E)) : Polynomial G :=
    ∑ i ∈ Finset.range ((φ (liftOf b d hb)).natDegree + 1),
      Polynomial.monomial i
        ⟨coeffTop (liftOf b d hb) d i, hcoeffTop_mem _ d (hlift_deg b d hb) i⟩
  have hhomPoly_coeff : ∀ (b : G) (d : ℤ) (hb : gr.proj d (b : E) = (b : E))
      (a : D) (hda : gr.DegLe (a : E) d)
      (hpa : gr.proj d (a : E) = (b : E)) (i : ℕ),
      ((homPoly b d hb).coeff i : E) = coeffTop a d i := by
    intro b d hb a hda hpa i
    have h1 : (homPoly b d hb).coeff i =
        if i < (φ (liftOf b d hb)).natDegree + 1 then
          ⟨coeffTop (liftOf b d hb) d i, hcoeffTop_mem _ d (hlift_deg b d hb) i⟩
        else 0 := by
      simp only [homPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      by_cases hi : i ∈ Finset.range ((φ (liftOf b d hb)).natDegree + 1)
      · rw [Finset.sum_eq_single i]
        · simp [Finset.mem_range.mp hi]
        · intro j _ hji; rw [if_neg hji]
        · intro hnm; exact absurd hi hnm
      · rw [if_neg (mt Finset.mem_range.mpr hi)]
        apply Finset.sum_eq_zero; intro j hj
        rw [if_neg (fun h => by subst h; exact hi hj)]
    rw [h1]
    split_ifs with hilt
    · exact hcoeffTop_indep (liftOf b d hb) a d (hlift_deg b d hb) hda
        (by rw [hlift_proj b d hb, hpa]) i
    · have hge : (φ (liftOf b d hb)).natDegree < i := by omega
      have h0 : (φ (liftOf b d hb)).coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hge
      have hct0 : coeffTop (liftOf b d hb) d i = 0 := by
        simp [coeffTop, h0]
      rw [← hcoeffTop_indep (liftOf b d hb) a d (hlift_deg b d hb) hda
            (by rw [hlift_proj b d hb, hpa]) i, hct0]
      rfl
  -- Step 6: Define `φbar_fun : G → Polynomial G` by summing over `gr.supp b`
  let projG (n : ℤ) (b : G) : G := ⟨gr.proj n (b : E), hG_graded (b : E) b.2 n⟩
  have hprojG_hom : ∀ n (b : G), gr.proj n ((projG n b : G) : E) = ((projG n b : G) : E) :=
    fun n b => by simp [projG, gr.proj_proj]
  let φbar_fun (b : G) : Polynomial G :=
    ∑ d ∈ gr.supp (b : E), homPoly (projG d b) d (hprojG_hom d b)
  have hφbar_hom : ∀ (b : G) (d : ℤ) (hb : gr.proj d (b : E) = (b : E)),
      φbar_fun b = homPoly b d hb := by
    intro b d hb
    by_cases hb0 : (b : E) = 0
    · have hsupp : gr.supp (b : E) = ∅ := by
        ext n; simp [gr.mem_supp, hb0]
      rw [show φbar_fun b = 0 by simp [φbar_fun, hsupp]]
      ext i
      rw [Polynomial.coeff_zero, Subalgebra.coe_zero,
        hhomPoly_coeff b d hb 0 (gr.degLe_zero d) (by simp [hb0]) i]
      simp [coeffTop]
    · have hsupp : gr.supp (b : E) = {d} := by
        ext n
        rw [gr.mem_supp, Finset.mem_singleton]
        rw [← hb, gr.proj_proj]
        by_cases hnd : n = d
        · subst hnd; simp [hb, hb0]
        · simp [hnd]
      simp only [φbar_fun, hsupp, Finset.sum_singleton]
      have hpg : (projG d b : E) = (b : E) := by simp [projG, hb]
      ext i
      rw [hhomPoly_coeff (projG d b) d (hprojG_hom d b) (liftOf b d hb) (hlift_deg b d hb)
            (by rw [hlift_proj b d hb, ← hpg]) i,
          hhomPoly_coeff b d hb (liftOf b d hb) (hlift_deg b d hb) (hlift_proj b d hb) i]
  have hφbar_zero : φbar_fun 0 = 0 := by
    have hsupp : gr.supp (0 : E) = ∅ := by ext n; simp [gr.mem_supp]
    simp only [φbar_fun, Subalgebra.coe_zero, hsupp, Finset.sum_empty]
  have hφbar_add_hom : ∀ (b₁ b₂ : G) (d : ℤ)
      (h1 : gr.proj d (b₁ : E) = (b₁ : E)) (h2 : gr.proj d (b₂ : E) = (b₂ : E)),
      φbar_fun (b₁ + b₂) = φbar_fun b₁ + φbar_fun b₂ := by
    intro b₁ b₂ d h1 h2
    have h12 : gr.proj d ((b₁ + b₂ : G) : E) = ((b₁ + b₂ : G) : E) := by
      simp [map_add, h1, h2]
    rw [hφbar_hom (b₁ + b₂) d h12, hφbar_hom b₁ d h1, hφbar_hom b₂ d h2]
    ext i
    rw [Polynomial.coeff_add, Subalgebra.coe_add]
    let a₁ := liftOf b₁ d h1
    let a₂ := liftOf b₂ d h2
    rw [hhomPoly_coeff (b₁ + b₂) d h12 (a₁ + a₂)
          (gr.degLe_add (hlift_deg b₁ d h1) (hlift_deg b₂ d h2))
          (by simp [a₁, a₂, map_add, hlift_proj]) i,
        hhomPoly_coeff b₁ d h1 a₁ (hlift_deg b₁ d h1) (hlift_proj b₁ d h1) i,
        hhomPoly_coeff b₂ d h2 a₂ (hlift_deg b₂ d h2) (hlift_proj b₂ d h2) i]
    simp only [coeffTop]
    split_ifs <;> simp [map_add]
  have hφbar_sum_supp : ∀ (b : G) (S : Finset ℤ), gr.supp (b : E) ⊆ S →
      φbar_fun b = ∑ d ∈ S, homPoly (projG d b) d (hprojG_hom d b) := by
    intro b S hS
    simp only [φbar_fun]
    refine Finset.sum_subset hS fun d _ hd => ?_
    have h0 : gr.proj d (b : E) = 0 := not_not.mp (mt (gr.mem_supp _ d).mpr hd)
    have hpg0 : (projG d b : E) = 0 := h0
    ext i
    rw [Polynomial.coeff_zero, Subalgebra.coe_zero,
      hhomPoly_coeff (projG d b) d (hprojG_hom d b) 0 (gr.degLe_zero d) (by simp [hpg0]) i]
    simp [coeffTop]
  have hφbar_add : ∀ b₁ b₂ : G, φbar_fun (b₁ + b₂) = φbar_fun b₁ + φbar_fun b₂ := by
    intro b₁ b₂
    let S := gr.supp (b₁ : E) ∪ gr.supp (b₂ : E)
    have hsub12 : gr.supp ((b₁ + b₂ : G) : E) ⊆ S := by
      intro d hd
      rw [gr.mem_supp, Subalgebra.coe_add, map_add] at hd
      rw [Finset.mem_union, gr.mem_supp, gr.mem_supp]
      by_contra h; push_neg at h
      exact hd (by rw [h.1, h.2, add_zero])
    rw [hφbar_sum_supp (b₁ + b₂) S hsub12,
        hφbar_sum_supp b₁ S Finset.subset_union_left,
        hφbar_sum_supp b₂ S Finset.subset_union_right,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hpg : projG d (b₁ + b₂) = projG d b₁ + projG d b₂ := Subtype.ext (by simp [projG, map_add])
    rw [← hφbar_hom (projG d (b₁ + b₂)) d (hprojG_hom d (b₁ + b₂)),
        ← hφbar_hom (projG d b₁) d (hprojG_hom d b₁),
        ← hφbar_hom (projG d b₂) d (hprojG_hom d b₂), hpg]
    exact hφbar_add_hom (projG d b₁) (projG d b₂) d (hprojG_hom d b₁) (hprojG_hom d b₂)
  have hφbar_mul_hom : ∀ (b₁ b₂ : G) (d₁ d₂ : ℤ)
      (h1 : gr.proj d₁ (b₁ : E) = (b₁ : E)) (h2 : gr.proj d₂ (b₂ : E) = (b₂ : E)),
      φbar_fun (b₁ * b₂) = φbar_fun b₁ * φbar_fun b₂ := by
    intro b₁ b₂ d₁ d₂ h1 h2
    have h12 : gr.proj (d₁ + d₂) ((b₁ * b₂ : G) : E) = ((b₁ * b₂ : G) : E) :=
      gr.proj_mul_hom d₁ d₂ (b₁ : E) (b₂ : E) h1 h2
    rw [hφbar_hom (b₁ * b₂) (d₁ + d₂) h12, hφbar_hom b₁ d₁ h1, hφbar_hom b₂ d₂ h2]
    let a₁ := liftOf b₁ d₁ h1
    let a₂ := liftOf b₂ d₂ h2
    have ha₁_deg := hlift_deg b₁ d₁ h1
    have ha₂_deg := hlift_deg b₂ d₂ h2
    have ha₁_SB := hSB_all a₁ d₁ ha₁_deg
    have ha₂_SB := hSB_all a₂ d₂ ha₂_deg
    ext k
    rw [hhomPoly_coeff (b₁ * b₂) (d₁ + d₂) h12 (a₁ * a₂) (gr.degLe_mul ha₁_deg ha₂_deg)
          (by rw [Subalgebra.coe_mul, Subalgebra.coe_mul, gr.proj_mul_top ha₁_deg ha₂_deg,
                  hlift_proj b₁ d₁ h1, hlift_proj b₂ d₂ h2]) k]
    rw [Polynomial.coeff_mul, AddSubmonoidClass.coe_finsetSum]
    have hrhs_term : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
        (((homPoly b₁ d₁ h1).coeff x.1 * (homPoly b₂ d₂ h2).coeff x.2 : G) : E) =
        coeffTop a₁ d₁ x.1 * coeffTop a₂ d₂ x.2 := by
      rintro ⟨i, j⟩ _
      rw [Subalgebra.coe_mul,
          hhomPoly_coeff b₁ d₁ h1 a₁ ha₁_deg (hlift_proj b₁ d₁ h1) i,
          hhomPoly_coeff b₂ d₂ h2 a₂ ha₂_deg (hlift_proj b₂ d₂ h2) j]
    rw [Finset.sum_congr rfl hrhs_term]
    simp only [coeffTop]
    split_ifs with hkdiv
    · rw [map_mul, Polynomial.coeff_mul, AddSubmonoidClass.coe_finset_sum, map_sum]
      refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
      have hij_sum : i + j = k := by simpa using hij
      have hk_z : (i : ℤ) + (j : ℤ) = (k : ℤ) := by exact_mod_cast hij_sum
      have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
      have hkmul : (den : ℤ) * (((k : ℤ) * num) / (den : ℤ)) = (k : ℤ) * num :=
        Int.mul_ediv_cancel' hkdiv
      simp only [Subalgebra.coe_mul]
      rw [gr.proj_mul_eq_sum]
      by_cases hidiv : (den : ℤ) ∣ (i : ℤ) * num
      · have hjdiv : (den : ℤ) ∣ (j : ℤ) * num := by
          have hsum : (i : ℤ) * num + (j : ℤ) * num = (k : ℤ) * num := by
            rw [← add_mul, hk_z]
          have : (j : ℤ) * num = (k : ℤ) * num - (i : ℤ) * num := by omega
          rw [this]; exact dvd_sub hkdiv hidiv
        rw [if_pos hidiv, if_pos hjdiv]
        let m₀ : ℤ := d₁ + ((i : ℤ) * num) / (den : ℤ)
        let l₀ : ℤ := d₂ + ((j : ℤ) * num) / (den : ℤ)
        have hml₀ : m₀ + l₀ = d₁ + d₂ + ((k : ℤ) * num) / (den : ℤ) := by
          have hi_mul := Int.mul_ediv_cancel' hidiv
          have hj_mul := Int.mul_ediv_cancel' hjdiv
          apply mul_left_cancel₀ (ne_of_gt hden_z)
          have h1 : (den : ℤ) * (m₀ + l₀) =
              (den : ℤ) * (d₁ + d₂) + ((i : ℤ) + (j : ℤ)) * num := by
            simp only [m₀, l₀]; linarith
          rw [h1, hk_z]; linarith
        have h1_le : gr.DegLe ((φ a₁).coeff i : E) m₀ := fun m hm => by
          apply ha₁_SB i m
          have hi_mul := Int.mul_ediv_cancel' hidiv
          nlinarith
        have h2_le : gr.DegLe ((φ a₂).coeff j : E) l₀ := fun l hl => by
          apply ha₂_SB j l
          have hj_mul := Int.mul_ediv_cancel' hjdiv
          nlinarith
        rw [← hml₀, ← gr.proj_mul_eq_sum, gr.proj_mul_top h1_le h2_le]
      · rw [if_neg hidiv, zero_mul]
        apply Finset.sum_eq_zero; intro m hm
        apply Finset.sum_eq_zero; intro l hl
        by_cases hml : d₁ + d₂ + (k : ℤ) * num / (den : ℤ) = m + l
        · exfalso
          have hm_le : (den : ℤ) * m ≤ (den : ℤ) * d₁ + (i : ℤ) * num := by
            by_contra hgt; exact (gr.mem_supp _ m).mp hm (ha₁_SB i m (not_le.mp hgt))
          have hl_le : (den : ℤ) * l ≤ (den : ℤ) * d₂ + (j : ℤ) * num := by
            by_contra hgt; exact (gr.mem_supp _ l).mp hl (ha₂_SB j l (not_le.mp hgt))
          have htot : (den : ℤ) * (m + l) =
              (den : ℤ) * (d₁ + d₂) + ((i : ℤ) + (j : ℤ)) * num := by
            rw [← hml, mul_add, hkmul, hk_z]
          have hm_eq : (den : ℤ) * m = (den : ℤ) * d₁ + (i : ℤ) * num := by linarith
          exact hidiv ⟨m - d₁, by linarith⟩
        · rw [if_neg hml]
    · symm
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      have hij_sum : i + j = k := by simpa using hij
      have hk_z : (i : ℤ) + (j : ℤ) = (k : ℤ) := by exact_mod_cast hij_sum
      by_cases hidiv : (den : ℤ) ∣ (i : ℤ) * num
      · have hjndiv : ¬ ((den : ℤ) ∣ (j : ℤ) * num) := by
          intro hjdiv
          apply hkdiv
          have : (k : ℤ) * num = (i : ℤ) * num + (j : ℤ) * num := by rw [← hk_z, add_mul]
          rw [this]; exact dvd_add hidiv hjdiv
        rw [if_pos hidiv, if_neg hjndiv, mul_zero]
      · rw [if_neg hidiv, zero_mul]
  have hφbar_mul : ∀ b₁ b₂ : G, φbar_fun (b₁ * b₂) = φbar_fun b₁ * φbar_fun b₂ := by
    intro b₁ b₂
    have hb₁ : b₁ = ∑ d ∈ gr.supp (b₁ : E), projG d b₁ :=
      Subtype.ext (by simp [projG, gr.sum_proj])
    have hb₂ : b₂ = ∑ d ∈ gr.supp (b₂ : E), projG d b₂ :=
      Subtype.ext (by simp [projG, gr.sum_proj])
    have hsum_add : ∀ (s : Finset ℤ) (f : ℤ → G),
        φbar_fun (∑ x ∈ s, f x) = ∑ x ∈ s, φbar_fun (f x) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp [hφbar_zero]
      | insert a s ha ih => simp [Finset.sum_insert ha, hφbar_add, ih]
    have h1 : φbar_fun b₁ = ∑ d ∈ gr.supp (b₁ : E), φbar_fun (projG d b₁) := by
      have h := congrArg φbar_fun hb₁
      rw [hsum_add] at h
      exact h
    have h2 : φbar_fun b₂ = ∑ d ∈ gr.supp (b₂ : E), φbar_fun (projG d b₂) := by
      have h := congrArg φbar_fun hb₂
      rw [hsum_add] at h
      exact h
    have h12 : b₁ * b₂ =
        ∑ d₁ ∈ gr.supp (b₁ : E), ∑ d₂ ∈ gr.supp (b₂ : E), projG d₁ b₁ * projG d₂ b₂ := by
      calc b₁ * b₂ = (∑ d₁ ∈ gr.supp (b₁ : E), projG d₁ b₁) * (∑ d₂ ∈ gr.supp (b₂ : E), projG d₂ b₂) :=
            congrArg₂ (· * ·) hb₁ hb₂
        _ = ∑ d₁ ∈ gr.supp (b₁ : E), ∑ d₂ ∈ gr.supp (b₂ : E), projG d₁ b₁ * projG d₂ b₂ := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
    rw [h12, hsum_add, h1, h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [hsum_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    exact hφbar_mul_hom (projG d₁ b₁) (projG d₂ b₂) d₁ d₂ (hprojG_hom d₁ b₁) (hprojG_hom d₂ b₂)
  have hφbar_algMap : ∀ c : K, φbar_fun (algebraMap K G c) = Polynomial.C (algebraMap K G c) := by
    intro c
    have hc_hom : gr.proj 0 ((algebraMap K G c : G) : E) = ((algebraMap K G c : G) : E) := by
      change gr.proj 0 (algebraMap K E c) = algebraMap K E c
      rw [gr.proj_algebraMap, if_pos rfl]
    rw [hφbar_hom (algebraMap K G c) 0 hc_hom]
    ext i
    rw [hhomPoly_coeff (algebraMap K G c) 0 hc_hom (algebraMap K D c)
          (gr.degLe_algebraMap c) hc_hom i]
    by_cases hi : i = 0
    · subst hi
      simp only [coeffTop, Nat.cast_zero, zero_mul, dvd_zero, ↓reduceIte, Int.zero_ediv, add_zero,
        φ.coeff_zero, Polynomial.coeff_C_zero]
      exact hc_hom
    · rw [Polynomial.coeff_C, if_neg hi, Subalgebra.coe_zero]
      simp only [coeffTop]
      split_ifs
      · have h0 : (φ (algebraMap K D c)).coeff i = 0 := by
          have : φ (algebraMap K D c) = Polynomial.C (algebraMap K D c) :=
            AlgHom.commutes φ.toAlgHom c
          rw [this, Polynomial.coeff_C, if_neg hi]
        rw [h0, Subalgebra.coe_zero, map_zero]
      · rfl
  let φbar_alg : G →ₐ[K] Polynomial G :=
    { toFun := φbar_fun
      map_one' := by simpa using hφbar_algMap 1
      map_mul' := hφbar_mul
      map_zero' := hφbar_zero
      map_add' := hφbar_add
      commutes' := fun c => hφbar_algMap c }
  -- Step 7: Verify `eval_zero` and `coassoc` on homogeneous elements, then extend by linearity
  have hφbar_coeff0 : ∀ b : G, (φbar_alg b).coeff 0 = b := by
    intro b
    have hb : b = ∑ d ∈ gr.supp (b : E), projG d b :=
      Subtype.ext (by simp [projG, gr.sum_proj])
    conv_lhs => rw [hb, map_sum, Polynomial.finsetSum_coeff]
    conv_rhs => rw [hb]
    refine Finset.sum_congr rfl fun d _ => ?_
    apply Subtype.ext
    change ((φbar_fun (projG d b)).coeff 0 : E) = (projG d b : E)
    rw [hφbar_hom (projG d b) d (hprojG_hom d b),
        hhomPoly_coeff (projG d b) d (hprojG_hom d b) (liftOf (projG d b) d (hprojG_hom d b))
          (hlift_deg (projG d b) d (hprojG_hom d b)) (hlift_proj (projG d b) d (hprojG_hom d b)) 0]
    simp only [coeffTop, Nat.cast_zero, zero_mul, dvd_zero, ↓reduceIte, Int.zero_ediv, add_zero,
      φ.coeff_zero, hlift_proj (projG d b) d (hprojG_hom d b)]
  have hφbar_coassoc_hom : ∀ (b : G) (d : ℤ) (hb : gr.proj d (b : E) = (b : E)) (i r : ℕ),
      ((φbar_alg ((φbar_alg b).coeff i)).coeff r : E) =
      (((i + r).choose i : G) * (φbar_alg b).coeff (i + r) : G) := by
    intro b d hb i r
    let a := liftOf b d hb
    have hda := hlift_deg b d hb
    have hpa := hlift_proj b d hb
    have hci : ((φbar_alg b).coeff i : E) = coeffTop a d i := by
      change ((φbar_fun b).coeff i : E) = _
      rw [hφbar_hom b d hb, hhomPoly_coeff b d hb a hda hpa i]
    have hcir : ((φbar_alg b).coeff (i + r) : E) = coeffTop a d (i + r) := by
      change ((φbar_fun b).coeff (i + r) : E) = _
      rw [hφbar_hom b d hb, hhomPoly_coeff b d hb a hda hpa (i + r)]
    have hden_z : (0 : ℤ) < den := Int.natCast_pos.mpr hden_pos
    by_cases hidiv : (den : ℤ) ∣ (i : ℤ) * num
    · let di : ℤ := d + ((i : ℤ) * num) / (den : ℤ)
      have hci_hom : gr.proj di ((φbar_alg b).coeff i : E) = ((φbar_alg b).coeff i : E) := by
        rw [hci]; simp [coeffTop, if_pos hidiv, di, gr.proj_proj]
      have ha_i_deg : gr.DegLe ((φ a).coeff i : E) di := fun n hn => by
        apply hSB_all a d hda i n
        have hi_mul := Int.mul_ediv_cancel' hidiv
        nlinarith
      have ha_i_proj : gr.proj di ((φ a).coeff i : E) = ((φbar_alg b).coeff i : E) := by
        rw [hci]; simp [coeffTop, if_pos hidiv, di]
      have hlhs : ((φbar_alg ((φbar_alg b).coeff i)).coeff r : E) =
          coeffTop ((φ a).coeff i) di r := by
        change ((φbar_fun ((φbar_alg b).coeff i)).coeff r : E) = _
        rw [hφbar_hom _ di hci_hom, hhomPoly_coeff _ di hci_hom ((φ a).coeff i) ha_i_deg ha_i_proj r]
      rw [hlhs, Subalgebra.coe_mul, show (((i + r).choose i : G) : E) = ((i + r).choose i : E) from
          map_natCast G.val _, hcir]
      simp only [coeffTop]
      by_cases hrdiv : (den : ℤ) ∣ (r : ℤ) * num
      · have hirdiv : (den : ℤ) ∣ ((i + r : ℕ) : ℤ) * num := by
          push_cast; rw [add_mul]; exact dvd_add hidiv hrdiv
        rw [if_pos hrdiv, if_pos hirdiv]
        have hdeg_eq : di + ((r : ℤ) * num) / (den : ℤ) =
            d + (((i + r : ℕ) : ℤ) * num) / (den : ℤ) := by
          have hi_mul := Int.mul_ediv_cancel' hidiv
          have hr_mul := Int.mul_ediv_cancel' hrdiv
          have hir_mul := Int.mul_ediv_cancel' hirdiv
          push_cast at hir_mul ⊢
          nlinarith
        rw [hdeg_eq]
        have hco : ((φ ((φ a).coeff i)).coeff r : E) =
            ((i + r).choose i : E) * ((φ a).coeff (i + r) : E) := by
          have := congrArg Subtype.val (φ.coeff_coeff_coassoc a i r)
          simpa using this
        rw [hco]
        have hsmul : ((i + r).choose i : E) * ((φ a).coeff (i + r) : E) =
            ((i + r).choose i : K) • ((φ a).coeff (i + r) : E) := by
          rw [Algebra.smul_def, map_natCast]
        rw [hsmul, map_smul, Algebra.smul_def, map_natCast]
      · have hirndiv : ¬ ((den : ℤ) ∣ ((i + r : ℕ) : ℤ) * num) := by
          intro hirdiv
          apply hrdiv
          have : (r : ℤ) * num = ((i + r : ℕ) : ℤ) * num - (i : ℤ) * num := by
            push_cast; ring
          rw [this]; exact dvd_sub hirdiv hidiv
        rw [if_neg hrdiv, if_neg hirndiv, mul_zero]
    · have hci0 : (φbar_alg b).coeff i = 0 := Subtype.ext (by rw [hci]; simp [coeffTop, if_neg hidiv])
      rw [hci0, map_zero, Polynomial.coeff_zero, Subalgebra.coe_zero,
          Subalgebra.coe_mul, show (((i + r).choose i : G) : E) = ((i + r).choose i : E) from
          map_natCast G.val _, hcir]
      simp only [coeffTop]
      split_ifs with hirdiv
      · symm
        have hsmul : ((i + r).choose i : E) *
            gr.proj (d + (((i + r : ℕ) : ℤ) * num) / (den : ℤ)) ((φ a).coeff (i + r) : E) =
            gr.proj (d + (((i + r : ℕ) : ℤ) * num) / (den : ℤ))
              (((i + r).choose i : E) * ((φ a).coeff (i + r) : E)) := by
          have h1 : ((i + r).choose i : E) * ((φ a).coeff (i + r) : E) =
              ((i + r).choose i : K) • ((φ a).coeff (i + r) : E) := by
            rw [Algebra.smul_def, map_natCast]
          rw [h1, map_smul, Algebra.smul_def, map_natCast]
        rw [hsmul]
        have hco : ((i + r).choose i : E) * ((φ a).coeff (i + r) : E) =
            ((φ ((φ a).coeff i)).coeff r : E) := by
          have := congrArg Subtype.val (φ.coeff_coeff_coassoc a i r)
          simpa using this.symm
        rw [hco]
        -- Since `¬ den ∣ i * num`, `deg((φ a).coeff i) ≤ d + ⌊(i*num)/den⌋` with strict `<`
        let di_floor : ℤ := d + ((i : ℤ) * num) / (den : ℤ)
        have hrem_pos : (den : ℤ) * (((i : ℤ) * num) / (den : ℤ)) < (i : ℤ) * num := by
          have hle : (den : ℤ) * (((i : ℤ) * num) / (den : ℤ)) ≤ (i : ℤ) * num := by
            have := Int.emod_nonneg ((i : ℤ) * num) (ne_of_gt hden_z)
            have := Int.mul_ediv_add_emod ((i : ℤ) * num) (den : ℤ)
            omega
          have hne : (den : ℤ) * (((i : ℤ) * num) / (den : ℤ)) ≠ (i : ℤ) * num := fun h =>
            hidiv ⟨((i : ℤ) * num) / (den : ℤ), h.symm⟩
          omega
        have ha_i_deg : gr.DegLe ((φ a).coeff i : E) di_floor := fun n hn => by
          apply hSB_all a d hda i n
          have hmod := Int.emod_lt_of_pos ((i : ℤ) * num) hden_z
          have hdiv_eq := Int.mul_ediv_add_emod ((i : ℤ) * num) (den : ℤ)
          nlinarith
        apply hSB_all ((φ a).coeff i) di_floor ha_i_deg r
        have hir_mul := Int.mul_ediv_cancel' hirdiv
        push_cast at hir_mul ⊢
        nlinarith
      · rw [mul_zero]
  let φbar : ExpMap K G :=
    { toAlgHom := φbar_alg
      eval_zero := fun b => by rw [← Polynomial.coeff_zero_eq_eval_zero, hφbar_coeff0]
      coassoc := coassoc_of_coeff_coeff φbar_alg fun b i r => by
        have hb : b = ∑ d ∈ gr.supp (b : E), projG d b :=
          Subtype.ext (by simp [projG, gr.sum_proj])
        conv_lhs => rw [hb, map_sum, Polynomial.finsetSum_coeff, map_sum, Polynomial.finsetSum_coeff]
        conv_rhs => rw [hb, map_sum, Polynomial.finsetSum_coeff, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        exact Subtype.ext (hφbar_coassoc_hom (projG d b) d (hprojG_hom d b) i r) }
  -- Step 8: `φbar` is non-trivial (witnessed by `topComp g₀` at index `den ≥ 1`)
  have hnt_bar : φbar.IsNontrivial := by
    let dg₀ := gr.topDeg (g₀ : E) (hΓ_ne g₀ hg₀_mem)
    let b₀ : G := ⟨gr.proj dg₀ (g₀ : E), hDG (g₀ : E) g₀.2 dg₀ (gr.degLe_topDeg (hΓ_ne g₀ hg₀_mem))⟩
    refine ⟨b₀, ?_⟩
    intro hmem
    have hcoeff_zero : (φbar b₀).coeff den = 0 := by
      change φbar b₀ = Polynomial.C b₀ at hmem
      rw [hmem, Polynomial.coeff_C, if_neg (ne_of_gt hden_pos)]
    have hb₀_hom : gr.proj dg₀ (b₀ : E) = (b₀ : E) := by simp [b₀, gr.proj_proj]
    have hval : ((φbar b₀).coeff den : E) = coeffTop g₀ dg₀ den := by
      change ((φbar_fun b₀).coeff den : E) = _
      rw [hφbar_hom b₀ dg₀ hb₀_hom,
          hhomPoly_coeff b₀ dg₀ hb₀_hom g₀ (gr.degLe_topDeg (hΓ_ne g₀ hg₀_mem)) rfl den]
    rw [hcoeff_zero, Subalgebra.coe_zero] at hval
    have hdiv : (den : ℤ) ∣ (den : ℤ) * num := dvd_mul_right _ _
    simp only [coeffTop, if_pos hdiv, Int.mul_ediv_cancel_left _ (ne_of_gt (Int.natCast_pos.mpr hden_pos))] at hval
    have hdeg_eq : dg₀ + num = gr.topDeg ((φ g₀).coeff den : E) hc₀_ne := by
      simp only [dg₀, num]; ring
    rw [hdeg_eq] at hval
    have hne : gr.proj (gr.topDeg ((φ g₀).coeff den : E) hc₀_ne) ((φ g₀).coeff den : E) ≠ 0 := by
      have := gr.topComp_ne_zero hc₀_ne
      rwa [topComp, dif_neg hc₀_ne] at this
    exact hne hval.symm
  -- Step 9: `a ∈ D^φ → topComp a ∈ G^{φbar}`
  refine ⟨φbar, hnt_bar, ?_⟩
  intro a ha
  by_cases ha0 : (a : E) = 0
  · have hmem0 : gr.topComp (a : E) ∈ G := by
      simp only [topComp, dif_pos ha0]; exact G.zero_mem
    have h0 : (⟨gr.topComp (a : E), hmem0⟩ : G) = 0 := Subtype.ext (by simp only [topComp, dif_pos ha0]; rfl)
    rw [h0]; exact φbar.invSubalg.zero_mem
  · let da := gr.topDeg (a : E) ha0
    let ba : G := ⟨gr.topComp (a : E), by
      rw [topComp, dif_neg ha0]; exact hDG (a : E) a.2 da (gr.degLe_topDeg ha0)⟩
    have hba_hom : gr.proj da (ba : E) = (ba : E) := by
      simp only [ba, topComp, dif_neg ha0, da, gr.proj_proj, ↓reduceIte]
    change φbar ba = Polynomial.C ba
    ext i
    by_cases hi : i = 0
    · subst hi
      rw [Polynomial.coeff_C_zero, φbar.coeff_zero]
    · rw [Polynomial.coeff_C, if_neg hi, Subalgebra.coe_zero]
      change ((φbar_fun ba).coeff i : E) = 0
      rw [hφbar_hom ba da hba_hom,
          hhomPoly_coeff ba da hba_hom a (gr.degLe_topDeg ha0)
            (by simp only [ba, topComp, dif_neg ha0, da]) i]
      have hφa_i : (φ a).coeff i = 0 := by
        change φ a = Polynomial.C a at ha
        rw [ha, Polynomial.coeff_C, if_neg hi]
      simp [coeffTop, hφa_i]

end ZGrading

end Homogenization

/- ## Section 6: Singular curve obstruction (`no_expMap_of_singular_curve`),
   localization/quotient of exponential maps, and irreducibility of `Z^p + α T^(p+1) - β` -/

section SingularCurve

/-- A `K`-derivation at a `K`-algebra evaluation `ev : R →ₐ[K] K`. -/
structure PointDeriv (K R : Type*) [Field K] [CommRing R] [Algebra K R] (ev : R →ₐ[K] K) where
  toLinearMap : R →ₗ[K] K
  leibniz : ∀ a b : R, toLinearMap (a * b) = ev a * toLinearMap b + ev b * toLinearMap a

namespace PointDeriv

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {ev : R →ₐ[K] K}

lemma map_one (D : PointDeriv K R ev) : D.toLinearMap 1 = 0 := by
  have h := D.leibniz 1 1
  have h1 : ev 1 = 1 := _root_.map_one ev
  rw [mul_one, h1, one_mul] at h
  linear_combination -h

lemma map_algebraMap (D : PointDeriv K R ev) (c : K) : D.toLinearMap (algebraMap K R c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, D.map_one, smul_zero]

lemma map_mul_of_ev_zero (D : PointDeriv K R ev) {a b : R} (ha : ev a = 0) :
    D.toLinearMap (a * b) = ev b * D.toLinearMap a := by
  rw [D.leibniz, ha, zero_mul, zero_add]

end PointDeriv

/-- If `R` has a `K`-rational point `ev : R →ₐ[K] K` with two `K`-linearly independent
    point derivations, then `R ≇ₐ[K] Polynomial K`. -/
lemma not_algEquiv_poly_of_two_indep_deriv {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (ev : R →ₐ[K] K) (D₁ D₂ : PointDeriv K R ev) (u₁ u₂ : R)
    (h11 : D₁.toLinearMap u₁ = 1) (h12 : D₁.toLinearMap u₂ = 0)
    (h21 : D₂.toLinearMap u₁ = 0) (h22 : D₂.toLinearMap u₂ = 1) :
    ¬ Nonempty (R ≃ₐ[K] Polynomial K) := by
  rintro ⟨e⟩
  let x₀ : K := ev (e.symm Polynomial.X)
  let t : R := e.symm Polynomial.X - algebraMap K R x₀
  have ht_ev : ev t = 0 := by
    simp [t, x₀, AlgHom.commutes]
  let c₁ : K := D₁.toLinearMap t
  let c₂ : K := D₂.toLinearMap t
  have hlin : ∀ r : R, c₂ * D₁.toLinearMap r - c₁ * D₂.toLinearMap r = 0 := by
    intro r
    let P : Polynomial K := e r
    have hdiv : Polynomial.X - Polynomial.C x₀ ∣ P - Polynomial.C (P.eval x₀) :=
      Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
    obtain ⟨Q, hQ⟩ := hdiv
    have hP : P = Polynomial.C (P.eval x₀) + (Polynomial.X - Polynomial.C x₀) * Q :=
      eq_add_of_sub_eq' hQ
    have hr : r = algebraMap K R (P.eval x₀) + t * e.symm Q := by
      have := congrArg e.symm hP
      simp only [P, AlgEquiv.symm_apply_apply, map_add, map_mul, map_sub] at this
      have hC : ∀ c : K, e.symm (Polynomial.C c) = algebraMap K R c := fun c => by
        rw [← Polynomial.algebraMap_eq, AlgEquiv.commutes]
      simpa [t, hC] using this
    rw [hr, map_add, map_add, D₁.map_algebraMap, D₂.map_algebraMap, zero_add, zero_add,
      D₁.map_mul_of_ev_zero ht_ev, D₂.map_mul_of_ev_zero ht_ev]
    simp only [c₁, c₂]; ring
  have hc2 : c₂ = 0 := by
    have := hlin u₁; rw [h11, h21] at this; linear_combination this
  have hc1 : c₁ = 0 := by
    have := hlin u₂; rw [h12, h22] at this; linear_combination -this
  -- Actually `D₁ r = ev (e.symm Q) * c₁ = 0` for all `r`, contradicting `h11`
  have hD1_zero : ∀ r : R, D₁.toLinearMap r = 0 := by
    intro r
    let P : Polynomial K := e r
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr (show Polynomial.IsRoot (P - Polynomial.C (P.eval x₀)) x₀ by simp)
    have hP : P = Polynomial.C (P.eval x₀) + (Polynomial.X - Polynomial.C x₀) * Q :=
      eq_add_of_sub_eq' hQ
    have hr : r = algebraMap K R (P.eval x₀) + t * e.symm Q := by
      have := congrArg e.symm hP
      simp only [P, AlgEquiv.symm_apply_apply, map_add, map_mul, map_sub] at this
      have hC : ∀ c : K, e.symm (Polynomial.C c) = algebraMap K R c := fun c => by
        rw [← Polynomial.algebraMap_eq, AlgEquiv.commutes]
      simpa [t, hC] using this
    rw [hr, map_add, D₁.map_algebraMap, zero_add, D₁.map_mul_of_ev_zero ht_ev]
    change ev (e.symm Q) * c₁ = 0
    rw [hc1, mul_zero]
  exact one_ne_zero (h11.symm.trans (hD1_zero u₁))

set_option maxHeartbeats 400000 in
/-- Elementary transcendence-degree ≤ 1 lemma via dimension counting:
    if `D` is spanned over `L[t]` by a finite set `B : Finset D`, then any two elements `u, s ∈ D`
    satisfy a non-zero polynomial relation `P(u, s) = 0` over `L`. -/
lemma exists_poly_rel_two_of_fg_over_poly {L D : Type*} [Field L] [CommRing D] [Algebra L D]
    (t : D) (B : Finset D)
    (hspan : ∀ a : D, ∃ (f : D → Polynomial L), a = ∑ b ∈ B, Polynomial.aeval t (f b) * b)
    (u s : D) :
    ∃ P : MvPolynomial (Fin 2) L, P ≠ 0 ∧ MvPolynomial.aeval ![u, s] P = 0 := by
  classical
  -- For every `b ∈ B`, write `u * b` and `s * b` in `L[t] · B`
  choose fu hfu using fun b : D => hspan (u * b)
  choose fs hfs using fun b : D => hspan (s * b)
  choose f1 hf1 using fun _ : Unit => hspan 1
  -- Uniform degree bound `M` on all `fu b b'`, `fs b b'`, `f1 () b'`
  let degs : Finset ℕ :=
    B.biUnion (fun b => B.image (fun b' => max ((fu b b').natDegree) ((fs b b').natDegree))) ∪
    B.image (fun b' => (f1 () b').natDegree)
  let M : ℕ := degs.sup id + 1
  -- By induction on `d`, every `u^i * s^j` (`i + j ≤ d`) lies in `span_L { t^k * b | k ≤ d * M + M, b ∈ B }`
  let spanK (bound : ℕ) : Submodule L D :=
    Submodule.span L (Set.range (fun p : Fin (bound + 1) × B => t ^ (p.1 : ℕ) * (p.2 : D)))
  have hmem_poly : ∀ (bound : ℕ) (g : D → Polynomial L),
      (∀ b ∈ B, (g b).natDegree ≤ bound) →
      (∑ b ∈ B, Polynomial.aeval t (g b) * b) ∈ spanK bound := by
    intro bound g hg
    refine Submodule.sum_mem _ fun b hb => ?_
    have hgb : Polynomial.aeval t (g b) =
        ∑ k ∈ Finset.range (bound + 1), (g b).coeff k • t ^ k := by
      rw [Polynomial.aeval_def,
        Polynomial.eval₂_eq_sum_range' (algebraMap L D) (Nat.lt_succ_of_le (hg b hb))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def]
    rw [hgb, Finset.sum_mul]
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨(⟨k, Finset.mem_range.mp hk⟩, ⟨b, hb⟩), rfl⟩
  have h1_mem : (1 : D) ∈ spanK M := by
    rw [hf1 ()]
    apply hmem_poly
    intro b hb
    have hmem : (f1 () b).natDegree ∈ degs := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)
    have hle : (f1 () b).natDegree ≤ degs.sup id := Finset.le_sup (f := id) hmem
    omega
  have hmul_u : ∀ (bound : ℕ) (x : D), x ∈ spanK bound → u * x ∈ spanK (bound + M) := by
    intro bound x hx
    refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [mul_add]; exact add_mem ha hb)
      (fun c a _ ha => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha) hx
    rintro _ ⟨⟨⟨k, hk⟩, ⟨b, hb⟩⟩, rfl⟩
    have h1 : u * (t ^ k * b) = t ^ k * (u * b) := by ring
    rw [h1, hfu b, Finset.mul_sum]
    have hrew : (∑ b' ∈ B, t ^ k * (Polynomial.aeval t (fu b b') * b')) =
        ∑ b' ∈ B, Polynomial.aeval t (Polynomial.X ^ k * fu b b') * b' := by
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp [map_mul, map_pow, mul_assoc]
    rw [hrew]
    apply hmem_poly
    intro b' hb'
    have hmem : max (fu b b').natDegree (fs b b').natDegree ∈ degs := by
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image_of_mem _ hb'⟩)
    have hle : (fu b b').natDegree ≤ degs.sup id :=
      le_trans (le_max_left _ _) (Finset.le_sup (f := id) hmem)
    calc (Polynomial.X ^ k * fu b b').natDegree
        ≤ (Polynomial.X ^ k : Polynomial L).natDegree + (fu b b').natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ k + degs.sup id := by simp [hle]
      _ ≤ bound + M := by omega
  have hmul_s : ∀ (bound : ℕ) (x : D), x ∈ spanK bound → s * x ∈ spanK (bound + M) := by
    intro bound x hx
    refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [mul_add]; exact add_mem ha hb)
      (fun c a _ ha => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha) hx
    rintro _ ⟨⟨⟨k, hk⟩, ⟨b, hb⟩⟩, rfl⟩
    have h1 : s * (t ^ k * b) = t ^ k * (s * b) := by ring
    rw [h1, hfs b, Finset.mul_sum]
    have hrew : (∑ b' ∈ B, t ^ k * (Polynomial.aeval t (fs b b') * b')) =
        ∑ b' ∈ B, Polynomial.aeval t (Polynomial.X ^ k * fs b b') * b' := by
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp [map_mul, map_pow, mul_assoc]
    rw [hrew]
    apply hmem_poly
    intro b' hb'
    have hmem : max (fu b b').natDegree (fs b b').natDegree ∈ degs := by
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image_of_mem _ hb'⟩)
    have hle : (fs b b').natDegree ≤ degs.sup id :=
      le_trans (le_max_right _ _) (Finset.le_sup (f := id) hmem)
    calc (Polynomial.X ^ k * fs b b').natDegree
        ≤ (Polynomial.X ^ k : Polynomial L).natDegree + (fs b b').natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ k + degs.sup id := by simp [hle]
      _ ≤ bound + M := by omega
  have hmono_span : ∀ {a b : ℕ}, a ≤ b → spanK a ≤ spanK b := by
    intro a b hab
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨⟨k, hk⟩, ⟨x, hx⟩⟩, rfl⟩
    exact Submodule.subset_span ⟨(⟨k, by omega⟩, ⟨x, hx⟩), rfl⟩
  have hmon_mem : ∀ i j : ℕ, u ^ i * s ^ j ∈ spanK ((i + j + 1) * M) := by
    intro i j
    induction i with
    | zero =>
      simp only [pow_zero, one_mul, zero_add]
      induction j with
      | zero => simpa using h1_mem
      | succ j ih =>
        rw [pow_succ']
        have := hmul_s ((j + 1) * M) (s ^ j) ih
        rwa [show (j + 1) * M + M = (j + 1 + 1) * M by ring] at this
    | succ i ih =>
      rw [pow_succ', mul_assoc]
      have := hmul_u ((i + j + 1) * M) (u ^ i * s ^ j) ih
      rwa [show (i + j + 1) * M + M = (i + 1 + j + 1) * M by ring] at this
  -- Choose `N` so that `(N + 1)^2 > ((2*N + 1)*M + 1) * B.card`
  let N : ℕ := 2 * M * B.card + M * B.card + B.card + 2
  let bound : ℕ := (2 * N + 1) * M
  let S := spanK bound
  haveI : Module.Finite L S := Module.Finite.span_of_finite L (Set.finite_range _)
  have hrank_le : Module.finrank L S ≤ (bound + 1) * B.card := by
    have hle := finrank_span_le_card (R := L)
      (Set.range (fun p : Fin (bound + 1) × B => t ^ (p.1 : ℕ) * (p.2 : D)))
    rw [Set.toFinset_card] at hle
    have hcard : Fintype.card (Set.range (fun p : Fin (bound + 1) × B => t ^ (p.1 : ℕ) * (p.2 : D))) ≤
        Fintype.card (Fin (bound + 1) × B) := Fintype.card_range_le _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hcard
    exact le_trans hle hcard
  have hlt : Module.finrank L S < Fintype.card (Fin (N + 1) × Fin (N + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hM1 : 1 ≤ M := by omega
    have hgt : (bound + 1) * B.card < (N + 1) * (N + 1) := by
      have h1 : 2 * M * B.card * N + (M + 1) * B.card = (bound + 1) * B.card := by
        simp only [bound]; ring
      have h2 : 2 * M * B.card + (M + 1) * B.card < N := by
        simp only [N]; nlinarith
      have h3 : 1 ≤ N := by simp only [N]; omega
      nlinarith
    exact lt_of_le_of_lt hrank_le hgt
  let v : Fin (N + 1) × Fin (N + 1) → S := fun p =>
    ⟨u ^ (p.1 : ℕ) * s ^ (p.2 : ℕ),
      hmono_span (by
        have h1 : (p.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp p.1.isLt
        have h2 : (p.2 : ℕ) ≤ N := Nat.lt_succ_iff.mp p.2.isLt
        exact Nat.mul_le_mul_right M (by omega)) (hmon_mem p.1 p.2)⟩
  have hnot_indep : ¬ LinearIndependent L v := fun hind =>
    not_le_of_gt hlt (hind.fintype_card_le_finrank)
  rw [Fintype.linearIndependent_iff] at hnot_indep
  push_neg at hnot_indep
  obtain ⟨g, hg_sum, p₀, hp₀⟩ := hnot_indep
  let P : MvPolynomial (Fin 2) L :=
    ∑ p : Fin (N + 1) × Fin (N + 1),
      MvPolynomial.monomial (Finsupp.single 0 (p.1 : ℕ) + Finsupp.single 1 (p.2 : ℕ)) (g p)
  refine ⟨P, ?_, ?_⟩
  · intro hP0
    let d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (p₀.1 : ℕ) + Finsupp.single 1 (p₀.2 : ℕ)
    have hcoeff : P.coeff d₀ = g p₀ := by
      simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single p₀]
      · rw [if_pos rfl]
      · intro p _ hpne
        rw [if_neg]
        intro hdeq
        apply hpne
        have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hdeq
        have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hdeq
        simp [d₀] at h0 h1
        exact Prod.ext (Fin.ext h0) (Fin.ext h1)
      · intro hnm; exact absurd (Finset.mem_univ p₀) hnm
    rw [hP0, MvPolynomial.coeff_zero] at hcoeff
    exact hp₀ hcoeff.symm
  · have hval := congrArg Subtype.val hg_sum
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, ZeroMemClass.coe_zero, v] at hval
    have heval : MvPolynomial.aeval ![u, s] P =
        ∑ p : Fin (N + 1) × Fin (N + 1), g p • (u ^ (p.1 : ℕ) * s ^ (p.2 : ℕ)) := by
      simp only [P, map_sum, MvPolynomial.aeval_monomial]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two, Algebra.smul_def]
      simp
    rw [heval, hval]

/-- Master obstruction theorem (combining Lemmas 2.1(v), 3.1, 3.2, 3.4(ii)):
    A char-`p` `L`-domain `D` spanned over `L[t]` by a finite set `B` that has an `L`-rational
    singular point (`ev : D →ₐ[L] L` with two `L`-linearly independent point derivations)
    admits NO non-trivial exponential map over `L`. -/
theorem no_expMap_of_singular_curve {L D : Type*} [Field L] [CommRing D] [IsDomain D]
    [Algebra L D] {p : ℕ} [hp : Fact p.Prime] [CharP D p]
    (t : D) (B : Finset D)
    (hspan : ∀ a : D, ∃ (f : D → Polynomial L), a = ∑ b ∈ B, Polynomial.aeval t (f b) * b)
    (ev : D →ₐ[L] L) (D₁ D₂ : PointDeriv L D ev) (u₁ u₂ : D)
    (h11 : D₁.toLinearMap u₁ = 1) (h12 : D₁.toLinearMap u₂ = 0)
    (h21 : D₂.toLinearMap u₁ = 0) (h22 : D₂.toLinearMap u₂ = 1)
    (φ : ExpMap L D) (hnt : φ.IsNontrivial) : False := by
  obtain ⟨s, c, hc_ne, hs_not, hslice⟩ := φ.exists_local_slice hnt
  -- Every `u ∈ D^φ` is algebraic over `L`
  have hinv_alg : ∀ u : φ.invSubalg, ∃ Q : Polynomial L, Q ≠ 0 ∧ Polynomial.aeval (u : D) Q = 0 := by
    intro u
    obtain ⟨P, hP_ne, hP_eval⟩ := exists_poly_rel_two_of_fg_over_poly t B hspan (u : D) s
    let evU : MvPolynomial (Fin 2) L →ₐ[L] Polynomial φ.invSubalg :=
      MvPolynomial.aeval ![Polynomial.C u, Polynomial.X]
    have hevU_s : Polynomial.aeval s (evU P) = 0 := by
      have hcomp : ((Polynomial.aeval s).restrictScalars L).comp evU =
          MvPolynomial.aeval ![(u : D), s] := by
        apply MvPolynomial.algHom_ext
        intro i; fin_cases i <;> simp [evU]
      have := AlgHom.congr_fun hcomp P
      simpa using this.trans hP_eval
    have hevU_zero : evU P = 0 := by
      by_contra hne
      exact hs_not (φ.mem_invSubalg_of_isIntegral (evU P) hne hevU_s)
    -- Since `P ≠ 0`, pick a monomial `(a, b)` in `P.support`; the `X^b`-coeff of `evU P` is
    -- `aeval u (∑ a, P.coeff (a, b) X^a) = 0`, and that polynomial in `L[X]` is non-zero!
    obtain ⟨d₀, hd₀⟩ := MvPolynomial.support_nonempty.mpr hP_ne
    let b₀ : ℕ := d₀ 1
    let Q : Polynomial L :=
      ∑ d ∈ P.support.filter (fun d => d 1 = b₀), Polynomial.monomial (d 0) (P.coeff d)
    refine ⟨Q, ?_, ?_⟩
    · intro hQ0
      have hc0 : Q.coeff (d₀ 0) = P.coeff d₀ := by
        simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single d₀]
        · simp
        · intro d hd hdne
          rw [if_neg]
          intro h0eq
          apply hdne
          ext i; fin_cases i
          · exact h0eq
          · exact (Finset.mem_filter.mp hd).2
        · intro hnm
          exfalso; exact hnm (Finset.mem_filter.mpr ⟨hd₀, rfl⟩)
      rw [hQ0, Polynomial.coeff_zero] at hc0
      exact (MvPolynomial.mem_support_iff.mp hd₀) hc0.symm
    · have hcoeff_b0 := congrArg (fun f : Polynomial φ.invSubalg => (f.coeff b₀ : D)) hevU_zero
      rw [Polynomial.coeff_zero, Subalgebra.coe_zero] at hcoeff_b0
      have hQeval : Polynomial.aeval (u : D) Q = ((evU P).coeff b₀ : D) := by
        conv_rhs => rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff, AddSubmonoidClass.coe_finsetSum]
        simp only [Q, map_sum, Polynomial.aeval_monomial]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        have hmon : evU (MvPolynomial.monomial d (P.coeff d)) =
            Polynomial.C (algebraMap L φ.invSubalg (P.coeff d) * u ^ (d 0)) *
            Polynomial.X ^ (d 1) := by
          rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.aeval_C, Finsupp.prod_fintype _ _ (fun _ => by simp)]
          simp [Fin.prod_univ_two, evU, map_pow, mul_assoc]
        rw [hmon, Polynomial.coeff_C_mul_X_pow]
        by_cases hdb : b₀ = d 1
        · rw [if_pos hdb, if_pos hdb.symm]
          simp [Subalgebra.coe_mul, Subalgebra.coe_pow]
        · rw [if_neg hdb, if_neg (Ne.symm hdb), Subalgebra.coe_zero]
      rw [hQeval, hcoeff_b0]
  -- Every `u ∈ D^φ` lies in `L` (since `ev : D^φ →ₐ[L] L` is injective on an algebraic domain over `L`!)
  have hinv_eq_L : ∀ u : φ.invSubalg, (u : D) = algebraMap L D (ev (u : D)) := by
    intro u
    let v : φ.invSubalg := u - algebraMap L φ.invSubalg (ev (u : D))
    have hv_ev : ev (v : D) = 0 := by simp [v, AlgHom.commutes]
    suffices hv0 : (v : D) = 0 by
      have : (u : D) - algebraMap L D (ev (u : D)) = 0 := hv0
      exact sub_eq_zero.mp this
    by_contra hv_ne
    obtain ⟨Q, hQ_ne, hQ_eval⟩ := hinv_alg v
    -- Divide out factors of `X` from `Q` so `Q₀.coeff 0 ≠ 0` and `aeval v Q₀ = 0`
    have hex_nz : ∃ Q₀ : Polynomial L, Q₀.coeff 0 ≠ 0 ∧ Polynomial.aeval (v : D) Q₀ = 0 := by
      generalize hdeg : Q.natDegree = n
      induction n using Nat.strong_induction_on generalizing Q with
      | _ n ih =>
        by_cases hc0 : Q.coeff 0 = 0
        · have hX : Polynomial.X ∣ Q := Polynomial.X_dvd_iff.mpr hc0
          obtain ⟨R, rfl⟩ := hX
          have hR_ne : R ≠ 0 := right_ne_zero_of_mul hQ_ne
          have hR_eval : Polynomial.aeval (v : D) R = 0 := by
            rw [map_mul, Polynomial.aeval_X] at hQ_eval
            exact (mul_eq_zero.mp hQ_eval).resolve_left hv_ne
          have hR_lt : R.natDegree < n := by
            rw [← hdeg, Polynomial.natDegree_X_mul hR_ne]; omega
          exact ih R.natDegree hR_lt R hR_ne hR_eval rfl
        · exact ⟨Q, hc0, hQ_eval⟩
    obtain ⟨Q₀, hQ₀_c0, hQ₀_eval⟩ := hex_nz
    have hev0 := congrArg ev hQ₀_eval
    rw [map_zero, ← Polynomial.aeval_algHom_apply ev (v : D) Q₀, hv_ev,
      Polynomial.aeval_def, Polynomial.eval₂_at_zero] at hev0
    exact hQ₀_c0 hev0
  -- Hence `c = algebraMap L D c₀` with `c₀ ≠ 0`, so `D ≃ₐ[L] Polynomial L`!
  let c₀ : L := ev (c : D)
  have hc_eq : (c : D) = algebraMap L D c₀ := hinv_eq_L c
  have hc₀_ne : c₀ ≠ 0 := fun h => hc_ne (by rw [hc_eq, h, map_zero])
  let ψ : Polynomial L →ₐ[L] D := Polynomial.aeval s
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    by_contra hP_ne
    let P' : Polynomial φ.invSubalg := P.map (algebraMap L φ.invSubalg)
    have hP'_ne : P' ≠ 0 := by
      intro h0
      apply hP_ne
      ext i
      have := congrArg (fun f : Polynomial φ.invSubalg => (f.coeff i : D)) h0
      simp only [P', Polynomial.coeff_map, Polynomial.coeff_zero, Subalgebra.coe_zero] at this
      have h1 : algebraMap L D (P.coeff i) = 0 := this
      exact (algebraMap L D).injective (h1.trans (map_zero _).symm)
    have hP'_eval : Polynomial.aeval s P' = 0 := by
      have : Polynomial.aeval s P' = Polynomial.aeval s P := by
        simp only [P', Polynomial.aeval_def, Polynomial.eval₂_map]
        rfl
      rw [this]; exact hP
    exact hs_not (φ.mem_invSubalg_of_isIntegral P' hP'_ne hP'_eval)
  have hψ_surj : Function.Surjective ψ := by
    intro a
    obtain ⟨N, P, hNP⟩ := hslice a
    have hPL_eval : ∀ Q : Polynomial φ.invSubalg,
        Polynomial.aeval s (Q.map (ev.toRingHom.comp φ.invSubalg.val.toRingHom)) =
        Polynomial.aeval s Q := by
      intro Q
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [Polynomial.map_add, map_add, map_add, hp, hq]
      | monomial n u =>
        simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, RingHom.comp_apply,
          AlgHom.coe_toRingHom, Subalgebra.coe_val]
        congr 1
        exact (hinv_eq_L u).symm
    refine ⟨Polynomial.C (c₀⁻¹ ^ N) * P.map (ev.toRingHom.comp φ.invSubalg.val.toRingHom), ?_⟩
    simp only [ψ, map_mul, Polynomial.aeval_C, hPL_eval P, ← hNP, hc_eq, ← map_pow, ← mul_assoc]
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hc₀_ne, one_pow, map_one, one_mul]
  exact not_algEquiv_poly_of_two_indep_deriv ev D₁ D₂ u₁ u₂ h11 h12 h21 h22
    ⟨(AlgEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩).symm⟩

/-- Helper algebra hom for `ExpMap.localize`. -/
def ExpMap.localizeAlgHom {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (S : Submonoid D) (hS : ∀ s ∈ S, s ∈ φ.invSubalg) :
    Localization S →ₐ[K] Polynomial (Localization S) :=
  let f : D →ₐ[K] Polynomial (Localization S) :=
    (Polynomial.mapAlgHom (IsScalarTower.toAlgHom K D (Localization S))).comp φ.toAlgHom
  IsLocalization.liftAlgHom (M := S) (f := f) (fun s => by
    have hs : φ s = Polynomial.C (s : D) := hS s s.2
    have hfs : f s = Polynomial.C (algebraMap D (Localization S) s) := by
      change Polynomial.map (algebraMap D (Localization S)) (φ s) = _
      rw [hs, Polynomial.map_C]
    rw [hfs]
    exact (IsLocalization.map_units (Localization S) s).map Polynomial.C)

lemma ExpMap.localizeAlgHom_algebraMap {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (S : Submonoid D) (hS : ∀ s ∈ S, s ∈ φ.invSubalg) (d : D) :
    φ.localizeAlgHom S hS (algebraMap D (Localization S) d) =
    Polynomial.map (algebraMap D (Localization S)) (φ d) := by
  simp only [ExpMap.localizeAlgHom]
  change IsLocalization.lift _ (algebraMap D (Localization S) d) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- Lemma 2.1 (vi): Extending an exponential map `φ` on `D` to a localization `S⁻¹ D`
    where `S ⊆ D^φ` is a submonoid. -/
def ExpMap.localize {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (S : Submonoid D) (hS : ∀ s ∈ S, s ∈ φ.invSubalg) :
    ExpMap K (Localization S) where
  toAlgHom := φ.localizeAlgHom S hS
  eval_zero x := by
    have hcomp : (Polynomial.evalRingHom (0 : Localization S)).comp
        (φ.localizeAlgHom S hS).toRingHom = RingHom.id (Localization S) := by
      apply IsLocalization.ringHom_ext S
      apply RingHom.ext; intro d
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        RingHom.id_apply, Polynomial.coe_evalRingHom, φ.localizeAlgHom_algebraMap S hS]
      rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
        φ.eval_zero]
    exact RingHom.congr_fun hcomp x
  coassoc x := by
    let ψ := φ.localizeAlgHom S hS
    let cc : Localization S →+* Polynomial (Polynomial (Localization S)) :=
      Polynomial.C.comp Polynomial.C
    let evVU : Polynomial (Localization S) →+* Polynomial (Polynomial (Localization S)) :=
      Polynomial.eval₂RingHom cc
        ((Polynomial.C Polynomial.X + Polynomial.X : Polynomial (Polynomial (Localization S))))
    have hcomp : (Polynomial.mapRingHom ψ.toRingHom).comp ψ.toRingHom = evVU.comp ψ.toRingHom := by
      apply IsLocalization.ringHom_ext S
      apply RingHom.ext; intro d
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_mapRingHom]
      rw [φ.localizeAlgHom_algebraMap S hS d, Polynomial.map_map]
      have hcomp2 : (ψ : Localization S →+* Polynomial (Localization S)).comp
          (algebraMap D (Localization S)) =
          (Polynomial.mapRingHom (algebraMap D (Localization S))).comp φ.toAlgHom.toRingHom := by
        apply RingHom.ext; intro r
        exact φ.localizeAlgHom_algebraMap S hS r
      rw [hcomp2, ← Polynomial.map_map, φ.coassoc d]
      generalize φ d = P
      induction P using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [Polynomial.map_add, map_add, map_add, Polynomial.map_add, hp, hq]
      | monomial n c =>
        simp only [evVU, cc, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
          Polynomial.map_monomial, RingHom.comp_apply, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]
    exact RingHom.congr_fun hcomp x

/-- Helper algebra hom for `ExpMap.quotient`. -/
def ExpMap.quotientAlgHom {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (f : D) (hf : f ∈ φ.invSubalg) :
    (D ⧸ Ideal.span ({f} : Set D)) →ₐ[K] Polynomial (D ⧸ Ideal.span ({f} : Set D)) :=
  let I := Ideal.span ({f} : Set D)
  let mk := Ideal.Quotient.mkₐ K I
  Ideal.Quotient.liftₐ I ((Polynomial.mapAlgHom mk).comp φ.toAlgHom) (fun a ha => by
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨q, rfl⟩ := ha
    have hf' : φ f = Polynomial.C f := hf
    change Polynomial.map (Ideal.Quotient.mk I) (φ (f * q)) = 0
    rw [map_mul, hf', Polynomial.map_mul, Polynomial.map_C]
    have hmkf : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hmkf, map_zero, zero_mul])

/-- Pushing an exponential map `φ` on `D` down to a quotient `D ⧸ I` when `I` is generated by
    a `φ`-invariant element `f ∈ D^φ`. -/
def ExpMap.quotient {K D : Type*} [CommRing K] [CommRing D] [Algebra K D]
    (φ : ExpMap K D) (f : D) (hf : f ∈ φ.invSubalg) :
    ExpMap K (D ⧸ Ideal.span ({f} : Set D)) where
  toAlgHom := φ.quotientAlgHom f hf
  eval_zero x := by
    let I := Ideal.span ({f} : Set D)
    refine Submodule.Quotient.induction_on I x fun d => ?_
    change (Polynomial.map (Ideal.Quotient.mk I) (φ d)).eval 0 = Ideal.Quotient.mk I d
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      φ.eval_zero]
  coassoc x := by
    let I := Ideal.span ({f} : Set D)
    refine Submodule.Quotient.induction_on I x fun d => ?_
    let mk := Ideal.Quotient.mk I
    let ψ := φ.quotientAlgHom f hf
    change Polynomial.map ψ.toRingHom (Polynomial.map mk (φ d)) =
      Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        (Polynomial.C Polynomial.X + Polynomial.X) (Polynomial.map mk (φ d))
    rw [Polynomial.map_map]
    have hcomp : ψ.toRingHom.comp mk = (Polynomial.mapRingHom mk).comp φ.toAlgHom.toRingHom := by
      ext r; rfl
    rw [hcomp, ← Polynomial.map_map, φ.coassoc d]
    generalize φ d = P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, map_add, map_add, Polynomial.map_add, hp, hq]
    | monomial n c =>
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.map_monomial,
        RingHom.comp_apply, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

end SingularCurve

/- ## Section 7a: The two `ℤ`-gradings (`grX` and `grZT`) on `Ambient K`,
   the homogenized ring `B_K`, and the unified normal form -/

section GradingsAndNormalForm

variable (K : Type*) [Field K] (p : ℕ)

/-- Helper: single term `C c * T n` in `Ambient K`. -/
def singleT (n : ℤ) (c : P2 K) : Ambient K :=
  AddMonoidAlgebra.single n c

/-- Helper: finite support of `q : Ambient K`. -/
noncomputable def suppA (q : Ambient K) : Finset ℤ :=
  q.coeff.support

lemma mem_suppA_iff (q : Ambient K) (m : ℤ) :
    m ∈ suppA K q ↔ q.coeff m ≠ 0 :=
  Finsupp.mem_support_iff

lemma singleT_eq_C_mul_T (n : ℤ) (c : P2 K) :
    singleT K n c = LaurentPolynomial.C c * LaurentPolynomial.T n := by
  change AddMonoidAlgebra.single n c =
    AddMonoidAlgebra.single 0 c * AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

lemma coeff_singleT (n m : ℤ) (c : P2 K) :
    (singleT K n c).coeff m = if n = m then c else 0 := by
  simp only [singleT, AddMonoidAlgebra.coeff_single]
  by_cases h : n = m
  · subst h; simp
  · simp [h, Ne.symm h]

lemma coeff_add_A (a b : Ambient K) (m : ℤ) :
    (a + b).coeff m = a.coeff m + b.coeff m := by
  rw [AddMonoidAlgebra.coeff_add]; rfl

lemma coeff_smul_A (c : K) (a : Ambient K) (m : ℤ) :
    (c • a).coeff m = c • a.coeff m := rfl

lemma coeff_sum_A {ι : Type*} (s : Finset ι) (f : ι → Ambient K) (m : ℤ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add_A, ih]

lemma coeff_mul_A (a b : Ambient K) (m : ℤ) :
    (a * b).coeff m =
      ∑ i ∈ suppA K a, ∑ j ∈ suppA K b, if i + j = m then a.coeff i * b.coeff j else 0 := by
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum, coeff_sum_A]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  exact coeff_singleT K (i + j) m (a.coeff i * b.coeff j)

lemma sum_singleT (q : Ambient K) :
    ∑ m ∈ suppA K q, singleT K m (q.coeff m) = q := by
  ext m : 1
  rw [coeff_sum_A]
  by_cases hm : m ∈ suppA K q
  · rw [Finset.sum_eq_single m]
    · simp [coeff_singleT]
    · intro k _ hkm; simp [coeff_singleT, hkm]
    · intro hnm; exact absurd hm hnm
  · have h0 : q.coeff m = 0 := not_not.mp ((mem_suppA_iff K q m).not.mp hm)
    rw [h0]
    apply Finset.sum_eq_zero; intro k hk
    have hkm : k ≠ m := fun h => hm (h ▸ hk)
    simp [coeff_singleT, hkm]

/-- First `ℤ`-grading on `Ambient K`: `wt(X) = -1, wt(Z) = 0, wt(T) = 0`
    (so `proj n q = singleT (-n) (q.coeff (-n))`). -/
def grX : ZGrading K (Ambient K) where
  proj n :=
    { toFun := fun q => singleT K (-n) (q.coeff (-n))
      map_add' := fun a b => by
        ext m : 1; simp [coeff_singleT, coeff_add_A]; split_ifs <;> simp
      map_smul' := fun c a => by
        ext m : 1
        simp only [RingHom.id_apply, coeff_smul_A, coeff_singleT]
        split_ifs <;> simp }
  supp q := (suppA K q).image (fun m => -m)
  mem_supp q n := by
    simp only [Finset.mem_image, mem_suppA_iff, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨m, hm, rfl⟩ h0
      have := congrArg (fun r : Ambient K => r.coeff m) h0
      simp [coeff_singleT] at this
      exact hm this
    · intro hne
      refine ⟨-n, ?_, neg_neg n⟩
      intro h0
      apply hne
      ext m : 1; simp [coeff_singleT, h0]
  sum_proj q := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_image (fun a _ b _ h => neg_inj.mp h)]
    simp only [neg_neg]
    exact sum_singleT K q
  proj_proj m n q := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    ext k : 1
    simp only [coeff_singleT]
    by_cases hmn : m = n
    · subst hmn; simp [coeff_singleT]
    · rw [if_neg hmn]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with h1 h2
      · exfalso; exact hmn (neg_inj.mp h2).symm
      · rfl
      · rfl
  proj_mul_hom m n x y hx hy := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at hx hy ⊢
    rw [← hx, ← hy]
    have hmul : singleT K (-m) (x.coeff (-m)) * singleT K (-n) (y.coeff (-n)) =
        singleT K (-(m + n)) (x.coeff (-m) * y.coeff (-n)) := by
      rw [singleT_eq_C_mul_T, singleT_eq_C_mul_T, singleT_eq_C_mul_T, neg_add,
        LaurentPolynomial.T_add, map_mul]
      ring
    rw [hmul]
    ext k : 1
    simp [coeff_singleT]
  proj_algebraMap n c := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have halg : algebraMap K (Ambient K) c = singleT K 0 (MvPolynomial.C c) := by
      rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
      rfl
    rw [halg]
    ext k : 1
    simp only [coeff_singleT]
    by_cases hn : n = 0
    · subst hn; simp [coeff_singleT]
    · rw [if_neg hn]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with h1 h2
      · exfalso; exact hn (neg_eq_zero.mp h2.symm)
      · rfl
      · rfl

/-- Homogeneous weight-`d` part of a polynomial in `P2 K = MvPolynomial (Fin 2) K`
    for weights `wt(Z) = p + 1`, `wt(T) = p`. -/
def projP2 (n : ℤ) (f : P2 K) : P2 K :=
  if n < 0 then 0
  else ∑ d ∈ f.support.filter (fun d => (p + 1) * d 0 + p * d 1 = n.toNat),
    MvPolynomial.monomial d (f.coeff d)

lemma coeff_projP2 (n : ℤ) (f : P2 K) (d : Fin 2 →₀ ℕ) :
    (projP2 K p n f).coeff d =
    if ((p + 1) * d 0 + p * d 1 : ℤ) = n then f.coeff d else 0 := by
  have hnonneg : (0 : ℤ) ≤ ((p + 1) * d 0 + p * d 1 : ℤ) := by positivity
  simp only [projP2]
  by_cases hn : n < 0
  · rw [if_pos hn, MvPolynomial.coeff_zero, if_neg (by linarith)]
  · rw [if_neg hn]
    by_cases hwt : ((p + 1) * d 0 + p * d 1 : ℤ) = n
    · rw [if_pos hwt, MvPolynomial.coeff_sum]
      by_cases hmem : d ∈ f.support
      · rw [Finset.sum_eq_single d]
        · simp
        · intro d' _ hdne; simp [MvPolynomial.coeff_monomial, hdne]
        · intro hnm
          exfalso; apply hnm
          have hnat : (p + 1) * d 0 + p * d 1 = n.toNat := by
            zify
            rw [Int.toNat_of_nonneg (by omega)]
            push_cast; exact hwt
          exact Finset.mem_filter.mpr ⟨hmem, hnat⟩
      · have h0 : f.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hmem
        rw [h0]
        apply Finset.sum_eq_zero; intro d' hd'
        have hne : d' ≠ d := fun h => hmem (h ▸ (Finset.mem_filter.mp hd').1)
        simp [MvPolynomial.coeff_monomial, hne]
    · rw [if_neg hwt, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero; intro d' hd'
      have hwt' := (Finset.mem_filter.mp hd').2
      have hne : d' ≠ d := by
        intro h; subst h; apply hwt
        have hn0 : (0 : ℤ) ≤ n := by omega
        have hcast : (((p + 1) * d' 0 + p * d' 1 : ℕ) : ℤ) = (n.toNat : ℤ) := by exact_mod_cast hwt'
        rw [Int.toNat_of_nonneg hn0] at hcast
        push_cast at hcast
        exact hcast
      simp [MvPolynomial.coeff_monomial, hne]

lemma coeff_sum_projP2 (r : Ambient K) (l : ℤ) (k : ℤ) :
    (∑ j ∈ suppA K r, singleT K j (projP2 K p l (r.coeff j))).coeff k =
    projP2 K p l (r.coeff k) := by
  rw [coeff_sum_A]
  by_cases hk : k ∈ suppA K r
  · rw [Finset.sum_eq_single k]
    · simp [coeff_singleT]
    · intro j _ hjk; simp [coeff_singleT, hjk]
    · intro hnm; exact absurd hk hnm
  · have h0 : r.coeff k = 0 := not_not.mp ((mem_suppA_iff K r k).not.mp hk)
    rw [h0]
    have hp0 : projP2 K p l 0 = 0 := by ext d; simp [coeff_projP2]
    rw [hp0]
    apply Finset.sum_eq_zero; intro j hj
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    simp [coeff_singleT, hjk]

/-- Second `ℤ`-grading on `Ambient K`: `wt(X) = 0, wt(Z) = p + 1, wt(T) = p`. -/
def grZT : ZGrading K (Ambient K) where
  proj n :=
    { toFun := fun q => ∑ m ∈ suppA K q, singleT K m (projP2 K p n (q.coeff m))
      map_add' := fun a b => by
        ext m d
        rw [coeff_add_A, coeff_sum_projP2, coeff_sum_projP2, coeff_sum_projP2,
          coeff_add_A, MvPolynomial.coeff_add, coeff_projP2, coeff_projP2, coeff_projP2,
          MvPolynomial.coeff_add]
        split_ifs <;> simp
      map_smul' := fun c a => by
        ext m d
        simp only [RingHom.id_apply]
        rw [coeff_smul_A, coeff_sum_projP2, coeff_sum_projP2, coeff_smul_A,
          MvPolynomial.coeff_smul, coeff_projP2, coeff_projP2, MvPolynomial.coeff_smul]
        split_ifs <;> simp }
  supp q :=
    ((suppA K q).biUnion fun m =>
      (q.coeff m).support.image fun d => ((p + 1) * d 0 + p * d 1 : ℤ))
  mem_supp q n := by
    simp only [Finset.mem_biUnion, Finset.mem_image, mem_suppA_iff,
      MvPolynomial.mem_support_iff, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨m, hm, d, hd, rfl⟩ h0
      have hm0 := congrArg (fun r : Ambient K => (r.coeff m).coeff d) h0
      rw [coeff_sum_projP2, coeff_projP2, if_pos rfl] at hm0
      exact hd hm0
    · intro hne
      have hexm : ∃ m, projP2 K p n (q.coeff m) ≠ 0 := by
        by_contra hall; push Not at hall
        apply hne; ext m; rw [coeff_sum_projP2, hall m]; rfl
      obtain ⟨m, hm_ne⟩ := hexm
      have hexd : ∃ d, (projP2 K p n (q.coeff m)).coeff d ≠ 0 := by
        by_contra hall; push Not at hall
        apply hm_ne; ext d; exact hall d
      obtain ⟨d, hd_ne⟩ := hexd
      rw [coeff_projP2] at hd_ne
      split_ifs at hd_ne with hwt
      · have hm0 : q.coeff m ≠ 0 := fun h => hd_ne (by rw [h, MvPolynomial.coeff_zero])
        exact ⟨m, hm0, d, hd_ne, hwt⟩
      · exact absurd rfl hd_ne
  sum_proj q := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    ext m d
    rw [coeff_sum_A, MvPolynomial.coeff_sum]
    simp only [coeff_sum_projP2, coeff_projP2]
    let w : ℤ := ((p + 1) * d 0 + p * d 1 : ℤ)
    by_cases hw : w ∈ (suppA K q).biUnion fun m =>
        (q.coeff m).support.image fun d => ((p + 1) * d 0 + p * d 1 : ℤ)
    · rw [Finset.sum_eq_single w]
      · simp [w]
      · intro n _ hnw; rw [if_neg (Ne.symm hnw)]
      · intro hnm; exact absurd hw hnm
    · have h0 : (q.coeff m).coeff d = 0 := by
        by_contra hne
        apply hw
        rw [Finset.mem_biUnion]
        refine ⟨m, (mem_suppA_iff K q m).mpr (fun h => hne (by rw [h, MvPolynomial.coeff_zero])), ?_⟩
        rw [Finset.mem_image]
        exact ⟨d, MvPolynomial.mem_support_iff.mpr hne, rfl⟩
      rw [h0]
      apply Finset.sum_eq_zero; intro n _; split_ifs <;> rfl
  proj_proj m n q := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    ext k d
    rw [coeff_sum_projP2, coeff_projP2, coeff_sum_projP2, coeff_projP2]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, coeff_sum_projP2, coeff_projP2]
      split_ifs <;> rfl
    · rw [if_neg hmn]
      split_ifs with h1 h2
      · exfalso; exact hmn (h1.symm.trans h2)
      · rfl
      · rfl
  proj_mul_hom m n x y hx hy := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at hx hy ⊢
    have hx_d : ∀ k d, (x.coeff k).coeff d ≠ 0 → ((p + 1) * d 0 + p * d 1 : ℤ) = m := by
      intro k d hd
      have h1 := congrArg (fun r : Ambient K => (r.coeff k).coeff d) hx
      rw [coeff_sum_projP2, coeff_projP2] at h1
      split_ifs at h1 with hwt
      · exact hwt
      · exact absurd h1.symm hd
    have hy_d : ∀ k d, (y.coeff k).coeff d ≠ 0 → ((p + 1) * d 0 + p * d 1 : ℤ) = n := by
      intro k d hd
      have h1 := congrArg (fun r : Ambient K => (r.coeff k).coeff d) hy
      rw [coeff_sum_projP2, coeff_projP2] at h1
      split_ifs at h1 with hwt
      · exact hwt
      · exact absurd h1.symm hd
    ext k d
    rw [coeff_sum_projP2, coeff_projP2]
    by_cases hwt : ((p + 1) * d 0 + p * d 1 : ℤ) = m + n
    · rw [if_pos hwt]
    · rw [if_neg hwt]
      symm
      rw [coeff_mul_A, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero; intro i _
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero; intro j _
      by_cases hijk : i + j = k
      · rw [if_pos hijk, MvPolynomial.coeff_mul]
        apply Finset.sum_eq_zero
        rintro ⟨d₁, d₂⟩ hd12
        have hd_sum : d₁ + d₂ = d := by simpa using hd12
        by_cases h1 : (x.coeff i).coeff d₁ = 0
        · rw [h1, zero_mul]
        · by_cases h2 : (y.coeff j).coeff d₂ = 0
          · rw [h2, mul_zero]
          · exfalso
            have hw1 := hx_d i d₁ h1
            have hw2 := hy_d j d₂ h2
            apply hwt
            have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
            have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
            rw [h0, h1']; push_cast; linarith
      · rw [if_neg hijk, MvPolynomial.coeff_zero]
  proj_algebraMap n c := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have halg : algebraMap K (Ambient K) c = singleT K 0 (MvPolynomial.C c) := by
      rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]; rfl
    rw [halg]
    ext k d
    rw [coeff_sum_projP2, coeff_projP2]
    by_cases hn : n = 0
    · subst hn
      rw [if_pos rfl]
      by_cases hk : k = 0
      · subst hk
        simp only [coeff_singleT, ↓reduceIte, MvPolynomial.coeff_C]
        split_ifs with hwt hd0 hd0
        · rfl
        · rfl
        · exfalso; subst hd0; simp at hwt
        · rfl
      · simp [coeff_singleT, Ne.symm hk]
    · rw [if_neg hn]
      by_cases hk : k = 0
      · subst hk
        simp only [coeff_singleT, ↓reduceIte, MvPolynomial.coeff_C]
        split_ifs with hwt hd0
        · exfalso; subst hd0; simp at hwt; exact hn hwt.symm
        · rfl
        · rfl
      · simp [coeff_singleT, Ne.symm hk]

/-- Homogenized polynomial `gHomPoly = Z^(p^2) + T^(p*(p+1)) ∈ K[Z, T]`. -/
def gHomPoly : P2 K :=
  MvPolynomial.X 0 ^ (p ^ 2) + MvPolynomial.X 1 ^ (p * (p + 1))

/-- Generator `y_B = -gHomPoly * X^(-2)` of `B_K`. -/
def genYB : Ambient K :=
  LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2)

/-- The homogenized Asanuma–Gupta `K`-subalgebra `B_K = K[x, y_B, z, t] ⊆ Ambient K`. -/
def HomSubalg : Subalgebra K (Ambient K) :=
  Algebra.adjoin K ({genX K, genYB K p, genZ K, genT K} : Set (Ambient K))

abbrev HomRing := ↥(HomSubalg K p)

instance : CommRing (HomRing K p) := Subalgebra.toCommRing (HomSubalg K p)
instance : IsDomain (HomRing K p) := Subalgebra.isDomain (HomSubalg K p)

def bX : HomRing K p := ⟨genX K, Algebra.subset_adjoin (by simp)⟩
def bY : HomRing K p := ⟨genYB K p, Algebra.subset_adjoin (by simp)⟩
def bZ : HomRing K p := ⟨genZ K, Algebra.subset_adjoin (by simp)⟩
def bT : HomRing K p := ⟨genT K, Algebra.subset_adjoin (by simp)⟩

/-- Unified normal form for any subalgebra `D_h = K[X, -h * X^(-2), Z, T] ⊆ Ambient K`:
    an element `q ∈ Ambient K` belongs to `D_h` iff for every `m < 0`,
    `(-h) ^ ((-m + 1) / 2) ∣ q.coeff m` in `P2 K`. -/
def SubalgOfPoly (h : P2 K) : Subalgebra K (Ambient K) :=
  Algebra.adjoin K ({genX K, LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2),
    genZ K, genT K} : Set (Ambient K))

lemma mem_subalgOfPoly_iff (h : P2 K) (q : Ambient K) :
    q ∈ SubalgOfPoly K h ↔
    ∀ m : ℤ, m < 0 → (-h) ^ (((-m + 1) / 2).toNat) ∣ q.coeff m := by
  let S : Subalgebra K (Ambient K) :=
    { carrier := {q | ∀ m : ℤ, m < 0 → (-h) ^ (((-m + 1) / 2).toNat) ∣ q.coeff m}
      mul_mem' := by
        intro a b ha hb m hm
        rw [coeff_mul_A]
        refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
        by_cases hijk : i + j = m
        · subst hijk
          rw [if_pos rfl]
          by_cases hi : i < 0
          · by_cases hj : j < 0
            · have h1 := ha i hi
              have h2 := hb j hj
              have hle : ((-(i + j) + 1) / 2).toNat ≤ ((-i + 1) / 2).toNat + ((-j + 1) / 2).toNat := by
                omega
              exact dvd_trans (pow_dvd_pow (-h) hle) (by rw [pow_add]; exact mul_dvd_mul h1 h2)
            · have h1 := ha i hi
              have hle : ((-(i + j) + 1) / 2).toNat ≤ ((-i + 1) / 2).toNat := by omega
              exact dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow (-h) hle) h1) _
          · have hj : j < 0 := by omega
            have h2 := hb j hj
            have hle : ((-(i + j) + 1) / 2).toNat ≤ ((-j + 1) / 2).toNat := by omega
            exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow (-h) hle) h2) _
        · rw [if_neg hijk]; exact dvd_zero _
      one_mem' := by
        intro m hm
        have h1 : (1 : Ambient K).coeff m = if (0 : ℤ) = m then 1 else 0 := by
          have : (1 : Ambient K) = singleT K 0 1 := by
            rw [singleT_eq_C_mul_T, map_one, LaurentPolynomial.T_zero, mul_one]
          rw [this, coeff_singleT]
        rw [h1, if_neg (by omega)]
        exact dvd_zero _
      add_mem' := fun {a b} ha hb m hm => by
        rw [coeff_add_A]; exact dvd_add (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by simp
      algebraMap_mem' := fun c m hm => by
        have hc : algebraMap K (Ambient K) c = singleT K 0 (MvPolynomial.C c) := by
          rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]; rfl
        rw [hc, coeff_singleT, if_neg (by omega)]
        exact dvd_zero _ }
  constructor
  · intro hq
    have hle : SubalgOfPoly K h ≤ S := by
      rw [SubalgOfPoly, Algebra.adjoin_le_iff]
      rintro g (rfl | rfl | rfl | rfl)
      · intro m hm
        have hg : genX K = singleT K 1 1 := by
          rw [singleT_eq_C_mul_T, map_one, one_mul]; rfl
        rw [hg, coeff_singleT, if_neg (by omega)]; exact dvd_zero _
      · intro m hm
        have hg : LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2) = singleT K (-2) (-h) :=
          (singleT_eq_C_mul_T K (-2) (-h)).symm
        rw [hg, coeff_singleT]
        by_cases hm2 : (-2 : ℤ) = m
        · subst hm2; simp
        · rw [if_neg hm2]; exact dvd_zero _
      · intro m hm
        have hg : genZ K = singleT K 0 (MvPolynomial.X 0) := by
          rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]; rfl
        rw [hg, coeff_singleT, if_neg (by omega)]; exact dvd_zero _
      · intro m hm
        have hg : genT K = singleT K 0 (MvPolynomial.X 1) := by
          rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]; rfl
        rw [hg, coeff_singleT, if_neg (by omega)]; exact dvd_zero _
    exact hle hq
  · intro hq
    have hC_mem : ∀ f : P2 K, LaurentPolynomial.C f ∈ SubalgOfPoly K h := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C c =>
        have : LaurentPolynomial.C (MvPolynomial.C c) = algebraMap K (Ambient K) c := rfl
        rw [this]; exact (SubalgOfPoly K h).algebraMap_mem c
      | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      | mul_X f i hf =>
        rw [map_mul]
        refine mul_mem hf ?_
        fin_cases i
        · exact Algebra.subset_adjoin (by simp [genZ])
        · exact Algebra.subset_adjoin (by simp [genT])
    have hX_mem : genX K ∈ SubalgOfPoly K h := Algebra.subset_adjoin (by simp)
    have hY_mem : LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2) ∈ SubalgOfPoly K h :=
      Algebra.subset_adjoin (by simp)
    rw [← sum_singleT K q]
    refine Subalgebra.sum_mem _ fun m _ => ?_
    by_cases hm : m < 0
    · obtain ⟨g, hg⟩ := hq m hm
      let j : ℕ := ((-m + 1) / 2).toNat
      let i : ℕ := (m + 2 * (j : ℤ)).toNat
      have hij : (i : ℤ) + (-2) * (j : ℤ) = m := by omega
      have hterm : singleT K m (q.coeff m) =
          LaurentPolynomial.C g * (genX K) ^ i *
          (LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2)) ^ j := by
        rw [singleT_eq_C_mul_T, hg, map_mul, map_pow, mul_pow]
        have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
          change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = LaurentPolynomial.T (i : ℤ)
          rw [LaurentPolynomial.T_pow]; simp
        have hT2 : (LaurentPolynomial.T (-2 : ℤ) : Ambient K) ^ j = LaurentPolynomial.T ((-2) * (j : ℤ)) := by
          rw [LaurentPolynomial.T_pow]; congr 1; ring
        rw [hT1, hT2]
        calc LaurentPolynomial.C (-h) ^ j * LaurentPolynomial.C g * LaurentPolynomial.T m
            = LaurentPolynomial.C (-h) ^ j * LaurentPolynomial.C g *
              (LaurentPolynomial.T (i : ℤ) * LaurentPolynomial.T ((-2) * (j : ℤ))) := by
              rw [← LaurentPolynomial.T_add, hij]
          _ = LaurentPolynomial.C g * LaurentPolynomial.T (i : ℤ) *
              (LaurentPolynomial.C (-h) ^ j * LaurentPolynomial.T ((-2) * (j : ℤ))) := by ring
      rw [hterm]
      exact mul_mem (mul_mem (hC_mem g) (pow_mem hX_mem i)) (pow_mem hY_mem j)
    · have hterm : singleT K m (q.coeff m) = LaurentPolynomial.C (q.coeff m) * (genX K) ^ m.toNat := by
        rw [singleT_eq_C_mul_T]
        have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
          change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = LaurentPolynomial.T m
          rw [LaurentPolynomial.T_pow]; congr 1; omega
        rw [hT1]
      rw [hterm]
      exact mul_mem (hC_mem (q.coeff m)) (pow_mem hX_mem m.toNat)

end GradingsAndNormalForm

/- ## Section 7b1: Admissibility of `A_K` and `B_K` under `grX` and `grZT` -/

section Admissibility

variable (K : Type*) [Field K] (p : ℕ)

private lemma list_map_toList_sum {α β : Type*} [AddCommMonoid β] (s : Finset α) (f : α → β) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl

private lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Helper: expand `C g * X^i * Y^j` as a `K`-linear combination of products from `{gX, gY, gZ, gT}`. -/
private lemma expand_C_mul_XY {D : Subalgebra K (Ambient K)}
    (gX gY gZ gT : D)
    (hX : (gX : Ambient K) = genX K)
    (hZ : (gZ : Ambient K) = genZ K)
    (hT : (gT : Ambient K) = genT K)
    (g : P2 K) (i j : ℕ) :
    ∃ L : List (K × List D),
      (∀ q ∈ L, ∀ u ∈ q.2, u = gX ∨ u = gY ∨ u = gZ ∨ u = gT) ∧
      (∀ q ∈ L, ∃ e ∈ g.support,
        (q.2.map Subtype.val).prod =
          LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
          (genX K) ^ i * (gY : Ambient K) ^ j) ∧
      LaurentPolynomial.C g * (genX K) ^ i * (gY : Ambient K) ^ j =
        (L.map fun q => q.1 • (q.2.map Subtype.val).prod).sum := by
  classical
  let mkList (e : Fin 2 →₀ ℕ) : List D :=
    List.replicate (e 0) gZ ++ List.replicate (e 1) gT ++
    List.replicate i gX ++ List.replicate j gY
  have hmk_prod : ∀ e : Fin 2 →₀ ℕ,
      ((mkList e).map Subtype.val).prod =
        LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
        (genX K) ^ i * (gY : Ambient K) ^ j := by
    intro e
    simp only [mkList, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
      hX, hZ, hT, genZ, genT, map_mul, map_pow, mul_assoc]
  let L : List (K × List D) := g.support.toList.map fun e => (g.coeff e, mkList e)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro q hq u hu
    simp only [L, List.mem_map] at hq
    obtain ⟨e, _, rfl⟩ := hq
    simp only [mkList, List.mem_append, List.mem_replicate] at hu
    rcases hu with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp
  · intro q hq
    simp only [L, List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact ⟨e, Finset.mem_toList.mp he, hmk_prod e⟩
  · have hg : g = ∑ e ∈ g.support, MvPolynomial.monomial e (g.coeff e) :=
      MvPolynomial.as_sum g
    have hmon : ∀ e : Fin 2 →₀ ℕ,
        MvPolynomial.monomial e (g.coeff e) =
        g.coeff e • (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 : P2 K) := by
      intro e
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fin.prod_univ_two, Algebra.smul_def]
      rfl
    have hsum_list : (L.map fun q => q.1 • (q.2.map Subtype.val).prod).sum =
        ∑ e ∈ g.support, g.coeff e •
          (LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
            (genX K) ^ i * (gY : Ambient K) ^ j) := by
      simp only [L, List.map_map, Function.comp_def]
      have hcongr : (g.support.toList.map fun e => g.coeff e • ((mkList e).map Subtype.val).prod).sum =
          (g.support.toList.map fun e => g.coeff e •
            (LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
              (genX K) ^ i * (gY : Ambient K) ^ j)).sum := by
        congr 1; exact List.map_congr_left fun e _ => by rw [hmk_prod e]
      rw [hcongr, list_map_toList_sum]
    rw [hsum_list]
    conv_lhs => rw [hg]
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hmon e]
    change LaurentPolynomial.C (g.coeff e • (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1)) * _ * _ = _
    have hCsmul : ∀ (c : K) (f : P2 K), LaurentPolynomial.C (c • f) = c • LaurentPolynomial.C f := by
      intro c f
      ext m : 1
      change (singleT K 0 (c • f)).coeff m = (c • singleT K 0 f).coeff m
      rw [coeff_smul_A, coeff_singleT, coeff_singleT]
      split_ifs <;> simp
    rw [hCsmul, smul_mul_assoc, smul_mul_assoc]

/-- Helper: `grX` homogenization on `SubalgOfPoly K h` (for any non-zero `h : P2 K`). -/
lemma homogenize_subalgOfPoly_grX (h : P2 K) (hh : h ≠ 0)
    (φ : ExpMap K (SubalgOfPoly K h)) (hnt : φ.IsNontrivial) :
    ∃ φbar : ExpMap K (SubalgOfPoly K h), φbar.IsNontrivial ∧
      ∀ a : SubalgOfPoly K h, a ∈ φ.invSubalg →
        (⟨(grX K).topComp (a : Ambient K), by
          by_cases ha : (a : Ambient K) = 0
          · simp [ZGrading.topComp, ha, (SubalgOfPoly K h).zero_mem]
          · rw [ZGrading.topComp, dif_neg ha, mem_subalgOfPoly_iff]
            intro m hm
            change (-h) ^ (((-m + 1) / 2).toNat) ∣
              (singleT K (-((grX K).topDeg (a : Ambient K) ha))
                ((a : Ambient K).coeff (-((grX K).topDeg (a : Ambient K) ha)))).coeff m
            rw [coeff_singleT]
            split_ifs with hmeq
            · subst hmeq; exact (mem_subalgOfPoly_iff K h _).mp a.2 _ hm
            · exact dvd_zero _⟩ : SubalgOfPoly K h) ∈ φbar.invSubalg := by
  classical
  let D := SubalgOfPoly K h
  let gX : D := ⟨genX K, Algebra.subset_adjoin (by simp)⟩
  let gY : D := ⟨LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2), Algebra.subset_adjoin (by simp)⟩
  let gZ : D := ⟨genZ K, Algebra.subset_adjoin (by simp)⟩
  let gT : D := ⟨genT K, Algebra.subset_adjoin (by simp)⟩
  let Γ : Finset D := {gX, gY, gZ, gT}
  have hG_graded : ∀ b ∈ D, ∀ n : ℤ, (grX K).proj n b ∈ D := by
    intro b hb n
    rw [mem_subalgOfPoly_iff] at hb ⊢
    intro m hm
    change (-h) ^ (((-m + 1) / 2).toNat) ∣ (singleT K (-n) (b.coeff (-n))).coeff m
    rw [coeff_singleT]
    split_ifs with hmn
    · subst hmn; exact hb _ hm
    · exact dvd_zero _
  have hGD : ∀ b ∈ D, ∀ d : ℤ, (grX K).proj d b = b → ∃ a ∈ D, (grX K).DegLe a d ∧ (grX K).proj d a = b := by
    intro b hb d hbd
    refine ⟨b, hb, ?_, hbd⟩
    intro n hn
    rw [← hbd, (grX K).proj_proj, if_neg (by omega)]
  have hΓ_ne : ∀ g ∈ Γ, (g : Ambient K) ≠ 0 := by
    intro g hg h0
    simp only [Γ, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · have := congrArg (fun r : Ambient K => r.coeff 1) h0
      have h1 : (genX K).coeff 1 = 1 := by
        change (singleT K 1 1).coeff 1 = 1; simp [coeff_singleT]
      rw [h1] at this; exact one_ne_zero this
    · have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
      have h1 : (LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2)).coeff (-2) = -h := by
        rw [← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl]
      rw [h1] at this; exact hh (neg_eq_zero.mp this)
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      have h1 : (genZ K).coeff 0 = MvPolynomial.X 0 := by
        change (singleT K 0 (MvPolynomial.X 0)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this
      exact MvPolynomial.X_ne_zero (0 : Fin 2) this
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      have h1 : (genT K).coeff 0 = MvPolynomial.X 1 := by
        change (singleT K 0 (MvPolynomial.X 1)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this
      exact MvPolynomial.X_ne_zero (1 : Fin 2) this
  have hΓ_admiss : ∀ (a : D) (d : ℤ), (grX K).DegLe (a : Ambient K) d →
      ∃ (L : List (K × List D)),
        (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
        (∀ q ∈ L, (grX K).DegLe ((q.2.map Subtype.val).prod) d) ∧
        (a : Ambient K) = (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
    intro a d had
    -- For each `m ∈ suppA K a`, write `singleT K m (a.coeff m)` as a list of monomials of `grX`-deg `-m ≤ d`
    have hterm : ∀ m ∈ suppA K (a : Ambient K),
        ∃ L : List (K × List D),
          (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
          (∀ q ∈ L, (grX K).DegLe ((q.2.map Subtype.val).prod) d) ∧
          singleT K m ((a : Ambient K).coeff m) =
            (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
      intro m hm
      have hmd : -m ≤ d := by
        by_contra hgt
        push Not at hgt
        have h0 := had (-m) hgt
        have h1 := congrArg (fun r : Ambient K => r.coeff m) h0
        change (singleT K (-(-m)) ((a : Ambient K).coeff (-(-m)))).coeff m = 0 at h1
        rw [neg_neg, coeff_singleT, if_pos rfl] at h1
        exact (mem_suppA_iff K _ m).mp hm h1
      by_cases hmneg : m < 0
      · obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K h _).mp a.2 m hmneg
        let j : ℕ := ((-m + 1) / 2).toNat
        let i : ℕ := (m + 2 * (j : ℤ)).toNat
        have hij : (i : ℤ) + (-2) * (j : ℤ) = m := by omega
        obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K gX gY gZ gT rfl rfl rfl g i j
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, _, hqeq⟩ := hLform q hq
          rw [hqeq]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (gY : Ambient K) ^ j = LaurentPolynomial.C ((-h) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2]
          have hsingle : LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
              LaurentPolynomial.T (i : ℤ) * (LaurentPolynomial.C ((-h) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ))) =
              singleT K m (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 * (-h) ^ j) := by
            simp only [singleT_eq_C_mul_T, ← hij, LaurentPolynomial.T_add, map_mul]; ring
          rw [hsingle]
          intro n hn
          change singleT K (-n) ((singleT K m _).coeff (-n)) = 0
          rw [coeff_singleT, if_neg (by omega)]
          ext k : 1; simp [coeff_singleT]
        · have hg' : (a : Ambient K).coeff m = (-h) ^ j * g := hg
          rw [← hLsum, singleT_eq_C_mul_T, hg', map_mul, map_pow]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (gY : Ambient K) ^ j = LaurentPolynomial.C (-h) ^ j * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-h) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2, ← hij, LaurentPolynomial.T_add]; ring
      · obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K gX gY gZ gT rfl rfl rfl ((a : Ambient K).coeff m) m.toNat 0
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, _, hqeq⟩ := hLform q hq
          rw [hqeq, pow_zero, mul_one]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1, ← singleT_eq_C_mul_T]
          intro n hn
          change singleT K (-n) ((singleT K m _).coeff (-n)) = 0
          rw [coeff_singleT, if_neg (by omega)]
          ext k : 1; simp [coeff_singleT]
        · rw [← hLsum, pow_zero, mul_one, singleT_eq_C_mul_T]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1]
    choose fL hfLΓ hfLdeg hfLsum using fun (m : {m // m ∈ suppA K (a : Ambient K)}) => hterm m.1 m.2
    let L : List (K × List D) := (suppA K (a : Ambient K)).attach.toList.flatMap fL
    refine ⟨L, ?_, ?_, ?_⟩
    · intro q hq u hu
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLΓ m q hqm u hu
    · intro q hq
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLdeg m q hqm
    · rw [← sum_singleT K (a : Ambient K)]
      have h1 : ∑ m ∈ suppA K (a : Ambient K), singleT K m ((a : Ambient K).coeff m) =
          ∑ m ∈ (suppA K (a : Ambient K)).attach, singleT K m.1 ((a : Ambient K).coeff m.1) := by
        rw [Finset.sum_attach (suppA K (a : Ambient K)) (fun m => singleT K m ((a : Ambient K).coeff m))]
      rw [h1]
      symm
      simp only [L, List.map_flatMap]
      rw [list_sum_flatMap]
      have h2 : (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => (List.map (fun q => q.1 • (List.map Subtype.val q.2).prod) (fL m)).sum)).sum =
          (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => singleT K m.1 ((a : Ambient K).coeff m.1))).sum := by
        congr 1; exact List.map_congr_left fun m _ => (hfLsum m).symm
      rw [h2, list_map_toList_sum]
  exact ZGrading.homogenizeExpMap (grX K) D D hG_graded (fun a ha d _ => hG_graded a ha d) hGD Γ hΓ_ne hΓ_admiss φ hnt

/-- Helper: `projP2` on a product with a `projP2`-homogeneous polynomial. -/
lemma projP2_mul_hom (m n : ℤ) (f g : P2 K) (hf : projP2 K p m f = f) :
    projP2 K p n (f * g) = f * projP2 K p (n - m) g := by
  have hf_wt : ∀ d, f.coeff d ≠ 0 → ((p + 1) * d 0 + p * d 1 : ℤ) = m := by
    intro d hd
    have h1 := congrArg (fun r : P2 K => r.coeff d) hf
    rw [coeff_projP2] at h1
    split_ifs at h1 with hwt
    · exact hwt
    · exact absurd h1.symm hd
  ext d
  rw [coeff_projP2, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hwt : ((p + 1) * d 0 + p * d 1 : ℤ) = n
  · rw [if_pos hwt]
    refine Finset.sum_congr rfl fun ⟨d₁, d₂⟩ hd12 => ?_
    have hd_sum : d₁ + d₂ = d := by simpa using hd12
    rw [coeff_projP2]
    by_cases h1 : f.coeff d₁ = 0
    · simp [h1]
    · have hw1 := hf_wt d₁ h1
      have hw2 : ((p + 1) * d₂ 0 + p * d₂ 1 : ℤ) = n - m := by
        have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
        have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
        rw [h0, h1'] at hwt; push_cast at hwt; linarith
      rw [if_pos hw2]
  · rw [if_neg hwt]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨d₁, d₂⟩ hd12
    have hd_sum : d₁ + d₂ = d := by simpa using hd12
    rw [coeff_projP2]
    by_cases h1 : f.coeff d₁ = 0
    · simp [h1]
    · have hw1 := hf_wt d₁ h1
      rw [if_neg]
      · simp
      · intro hw2; apply hwt
        have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
        have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
        rw [h0, h1']; push_cast; linarith

lemma projP2_pow_hom (m : ℤ) (k : ℕ) (f : P2 K) (hf : projP2 K p m f = f) :
    projP2 K p (k * m) (f ^ k) = f ^ k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    ext d; rw [coeff_projP2, MvPolynomial.coeff_one]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exfalso; subst h2; simp at h1
    · rfl
  | succ k ih =>
    rw [pow_succ', projP2_mul_hom K p m ((k + 1 : ℕ) * m) f (f ^ k) hf]
    have hsub : ((k + 1 : ℕ) * m : ℤ) - m = k * m := by push_cast; ring
    rw [hsub, ih]

lemma projP2_neg (n : ℤ) (f : P2 K) : projP2 K p n (-f) = -projP2 K p n f := by
  ext d; rw [coeff_projP2, MvPolynomial.coeff_neg, MvPolynomial.coeff_neg, coeff_projP2]
  split_ifs <;> simp

lemma gHomPoly_hom :
    projP2 K p (p ^ 2 * (p + 1) : ℤ) (gHomPoly K p) = gHomPoly K p := by
  ext d
  rw [coeff_projP2]
  simp only [gHomPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow]
  by_cases h0 : Finsupp.single (0 : Fin 2) (p ^ 2) = d
  · subst h0
    have hwt : ((p + 1) * (Finsupp.single (0 : Fin 2) (p ^ 2)) 0 +
        p * (Finsupp.single (0 : Fin 2) (p ^ 2)) 1 : ℤ) = (p ^ 2 * (p + 1) : ℤ) := by
      simp; ring
    rw [if_pos hwt]
  · by_cases h1 : Finsupp.single (1 : Fin 2) (p * (p + 1)) = d
    · subst h1
      have hwt : ((p + 1) * (Finsupp.single (1 : Fin 2) (p * (p + 1))) 0 +
          p * (Finsupp.single (1 : Fin 2) (p * (p + 1))) 1 : ℤ) = (p ^ 2 * (p + 1) : ℤ) := by
        simp; ring
      rw [if_pos hwt]
    · rw [if_neg h0, if_neg h1, add_zero, ite_self]

lemma gHomPoly_ne_zero (hp : 1 < p) : gHomPoly K p ≠ 0 := by
  intro h0
  let d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (p ^ 2)
  have hc := congrArg (fun r : P2 K => r.coeff d₀) h0
  simp only [gHomPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_zero] at hc
  have hne : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ d₀ := by
    intro heq
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
    simp [d₀] at this
    nlinarith
  rw [if_pos rfl, if_neg hne, add_zero] at hc
  exact one_ne_zero hc

lemma fPoly_ne_zero (hp : 1 < p) : fPoly K p ≠ 0 := by
  intro h0
  let d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (p ^ 2)
  have hc := congrArg (fun r : P2 K => r.coeff d₀) h0
  simp only [fPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X',
    MvPolynomial.coeff_zero] at hc
  have hne1 : Finsupp.single (1 : Fin 2) 1 ≠ d₀ := by
    intro heq; have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simp [d₀] at this; nlinarith
  have hne2 : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ d₀ := by
    intro heq; have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simp [d₀] at this; nlinarith
  rw [if_pos rfl, if_neg hne1, if_neg hne2, add_zero, add_zero] at hc
  exact one_ne_zero hc

/-- Degree bound for `projP2`: `f` has all monomials of `grZT`-weight `≤ n`. -/
def DegLeP2 (n : ℤ) (f : P2 K) : Prop :=
  ∀ d ∈ f.support, ((p + 1) * d 0 + p * d 1 : ℤ) ≤ n

lemma degLeP2_iff_projP2 (n : ℤ) (f : P2 K) :
    DegLeP2 K p n f ↔ ∀ k : ℤ, n < k → projP2 K p k f = 0 := by
  constructor
  · intro h k hk
    ext d; rw [coeff_projP2, MvPolynomial.coeff_zero]
    split_ifs with hwt
    · by_contra hne
      have hle := h d (MvPolynomial.mem_support_iff.mpr hne)
      linarith
    · rfl
  · intro h d hd
    by_contra hgt; push Not at hgt
    have h0 := congrArg (fun r : P2 K => r.coeff d) (h _ hgt)
    rw [coeff_projP2, if_pos rfl, MvPolynomial.coeff_zero] at h0
    exact MvPolynomial.mem_support_iff.mp hd h0

lemma degLeP2_mul {m n : ℤ} {f g : P2 K} (hf : DegLeP2 K p m f) (hg : DegLeP2 K p n g) :
    DegLeP2 K p (m + n) (f * g) := by
  intro d hd
  have hne : (f * g).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_mul] at hne
  obtain ⟨⟨d₁, d₂⟩, hd12, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hd_sum : d₁ + d₂ = d := by simpa using hd12
  have h1 := hf d₁ (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hprod))
  have h2 := hg d₂ (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hprod))
  have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
  have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
  rw [h0, h1']; push_cast; linarith

lemma projP2_mul_top {m n : ℤ} {f g : P2 K} (hf : DegLeP2 K p m f) (hg : DegLeP2 K p n g) :
    projP2 K p (m + n) (f * g) = projP2 K p m f * projP2 K p n g := by
  ext d
  rw [coeff_projP2, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hwt : ((p + 1) * d 0 + p * d 1 : ℤ) = m + n
  · rw [if_pos hwt]
    refine Finset.sum_congr rfl fun ⟨d₁, d₂⟩ hd12 => ?_
    have hd_sum : d₁ + d₂ = d := by simpa using hd12
    rw [coeff_projP2, coeff_projP2]
    by_cases h1 : f.coeff d₁ = 0
    · simp [h1]
    · by_cases h2 : g.coeff d₂ = 0
      · simp [h2]
      · have hle1 := hf d₁ (MvPolynomial.mem_support_iff.mpr h1)
        have hle2 := hg d₂ (MvPolynomial.mem_support_iff.mpr h2)
        have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
        have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
        rw [h0, h1'] at hwt; push_cast at hwt
        rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [if_neg hwt]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨d₁, d₂⟩ hd12
    have hd_sum : d₁ + d₂ = d := by simpa using hd12
    rw [coeff_projP2, coeff_projP2]
    split_ifs with hw1 hw2
    · exfalso; apply hwt
      have h0 : d 0 = d₁ 0 + d₂ 0 := by rw [← hd_sum]; rfl
      have h1' : d 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
      rw [h0, h1']; push_cast; linarith
    · simp
    · simp
    · simp

lemma fPoly_degLe (hp : 1 < p) :
    DegLeP2 K p (p ^ 2 * (p + 1) : ℤ) (fPoly K p) := by
  intro d hd
  have hne : (fPoly K p).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  simp only [fPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X] at hne
  by_cases h0 : Finsupp.single (0 : Fin 2) (p ^ 2) = d
  · subst h0; simp; ring_nf; omega
  · by_cases h1 : Finsupp.single (1 : Fin 2) 1 = d
    · subst h1; simp; nlinarith
    · by_cases h2 : Finsupp.single (1 : Fin 2) (p * (p + 1)) = d
      · subst h2; simp; ring_nf; omega
      · rw [if_neg h0, if_neg h1, if_neg h2, add_zero, add_zero] at hne
        exact absurd rfl hne

lemma fPoly_proj_top (hp : 1 < p) :
    projP2 K p (p ^ 2 * (p + 1) : ℤ) (fPoly K p) = gHomPoly K p := by
  ext d
  rw [coeff_projP2]
  simp only [fPoly, gHomPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.single (0 : Fin 2) (p ^ 2) = d
  · subst h0
    have hne1 : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single (0 : Fin 2) (p ^ 2) := by
      intro h; have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h; simp at this; nlinarith
    have hwt : ((p + 1) * (Finsupp.single (0 : Fin 2) (p ^ 2)) 0 +
        p * (Finsupp.single (0 : Fin 2) (p ^ 2)) 1 : ℤ) = (p ^ 2 * (p + 1) : ℤ) := by
      simp; ring
    rw [if_pos hwt, if_pos rfl, if_neg hne1, add_zero]
  · by_cases h1 : Finsupp.single (1 : Fin 2) 1 = d
    · subst h1
      have hne2 : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ Finsupp.single (1 : Fin 2) 1 := by
        intro h; have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h; simp at this; nlinarith
      have hwt_ne : ((p + 1) * ((Finsupp.single (1 : Fin 2) 1) 0 : ℕ) +
          p * ((Finsupp.single (1 : Fin 2) 1) 1 : ℕ) : ℤ) ≠ (p ^ 2 * (p + 1) : ℤ) := by
        simp; nlinarith
      rw [if_neg hwt_ne, if_neg h0, if_neg hne2, add_zero]
    · by_cases h2 : Finsupp.single (1 : Fin 2) (p * (p + 1)) = d
      · subst h2
        have hwt_eq : ((p + 1) * (Finsupp.single (1 : Fin 2) (p * (p + 1))) 0 +
            p * (Finsupp.single (1 : Fin 2) (p * (p + 1))) 1 : ℤ) = (p ^ 2 * (p + 1) : ℤ) := by
          simp; ring
        rw [if_pos hwt_eq, if_neg h0, if_neg h1, add_zero]
      · rw [if_neg h0, if_neg h1, if_neg h2, add_zero, add_zero, ite_self]

lemma neg_fPoly_pow_degLe (hp : 1 < p) (j : ℕ) :
    DegLeP2 K p (j * (p ^ 2 * (p + 1) : ℤ)) ((-fPoly K p) ^ j) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    intro d hd
    have hne := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_one] at hne
    split_ifs at hne with hd0
    · subst hd0; simp
    · exact absurd rfl hne
  | succ j ih =>
    rw [pow_succ' (-fPoly K p) j]
    have hneg : DegLeP2 K p (p ^ 2 * (p + 1) : ℤ) (-fPoly K p) := fun d hd =>
      fPoly_degLe K p hp d (by simpa [MvPolynomial.mem_support_iff] using hd)
    have h := degLeP2_mul K p hneg ih
    rwa [show (p ^ 2 * (p + 1) : ℤ) + j * (p ^ 2 * (p + 1) : ℤ) =
        ((j + 1 : ℕ) : ℤ) * (p ^ 2 * (p + 1) : ℤ) by push_cast; ring] at h

lemma neg_fPoly_pow_proj_top (hp : 1 < p) (j : ℕ) :
    projP2 K p (j * (p ^ 2 * (p + 1) : ℤ)) ((-fPoly K p) ^ j) = (-gHomPoly K p) ^ j := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    ext d; rw [coeff_projP2, MvPolynomial.coeff_one]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exfalso; subst h2; simp at h1
    · rfl
  | succ j ih =>
    rw [pow_succ' (-fPoly K p) j, pow_succ' (-gHomPoly K p) j]
    have hneg : DegLeP2 K p (p ^ 2 * (p + 1) : ℤ) (-fPoly K p) := fun d hd =>
      fPoly_degLe K p hp d (by simpa [MvPolynomial.mem_support_iff] using hd)
    have h := projP2_mul_top K p hneg (neg_fPoly_pow_degLe K p hp j)
    rw [show (p ^ 2 * (p + 1) : ℤ) + j * (p ^ 2 * (p + 1) : ℤ) =
        ((j + 1 : ℕ) : ℤ) * (p ^ 2 * (p + 1) : ℤ) by push_cast; ring] at h
    rw [h, ih, projP2_neg, fPoly_proj_top K p hp]

/-- Key division-degree lemma: if `DegLeP2 d (f * g)` and `DegLeP2 m f` with `projP2 m f ≠ 0`,
    then `DegLeP2 (d - m) g`. -/
lemma degLeP2_of_mul {m d : ℤ} {f g : P2 K}
    (hf : DegLeP2 K p m f) (hf_top : projP2 K p m f ≠ 0)
    (hfg : DegLeP2 K p d (f * g)) :
    DegLeP2 K p (d - m) g := by
  classical
  by_cases hg0 : g = 0
  · subst hg0; intro e he; simp at he
  · have hsupp : g.support.Nonempty := MvPolynomial.support_nonempty.mpr hg0
    let wts := g.support.image fun e => ((p + 1) * e 0 + p * e 1 : ℤ)
    let wg : ℤ := wts.max' (hsupp.image _)
    have hwg_le : DegLeP2 K p wg g := fun e he =>
      Finset.le_max' wts _ (Finset.mem_image_of_mem _ he)
    have hwg_ne : projP2 K p wg g ≠ 0 := by
      have hmem : wg ∈ wts := Finset.max'_mem wts _
      obtain ⟨e, he, hwe⟩ := Finset.mem_image.mp hmem
      intro h0
      have hc := congrArg (fun r : P2 K => r.coeff e) h0
      rw [coeff_projP2, if_pos hwe, MvPolynomial.coeff_zero] at hc
      exact MvPolynomial.mem_support_iff.mp he hc
    have htop_ne : projP2 K p (m + wg) (f * g) ≠ 0 := by
      rw [projP2_mul_top K p hf hwg_le]
      exact mul_ne_zero hf_top hwg_ne
    have hle : m + wg ≤ d := by
      by_contra hgt; push Not at hgt
      exact htop_ne ((degLeP2_iff_projP2 K p d (f * g)).mp hfg (m + wg) hgt)
    intro e he
    have := hwg_le e he
    linarith

/-- Helper: `(grZT K p).DegLe q d ↔ ∀ m, DegLeP2 K p d (q.coeff m)`. -/
lemma degLe_grZT_iff (q : Ambient K) (d : ℤ) :
    (grZT K p).DegLe q d ↔ ∀ m : ℤ, DegLeP2 K p d (q.coeff m) := by
  constructor
  · intro h m
    rw [degLeP2_iff_projP2]
    intro k hk
    have h0 := congrArg (fun r : Ambient K => r.coeff m) (h k hk)
    change (∑ j ∈ suppA K q, singleT K j (projP2 K p k (q.coeff j))).coeff m = 0 at h0
    rwa [coeff_sum_projP2] at h0
  · intro h k hk
    ext m : 1
    change (∑ j ∈ suppA K q, singleT K j (projP2 K p k (q.coeff j))).coeff m = 0
    rw [coeff_sum_projP2]
    exact (degLeP2_iff_projP2 K p d (q.coeff m)).mp (h m) k hk

/-- Helper: `grZT` homogenization on `HomSubalg K p` (`B_K → B_K`). -/
lemma homogenize_homSubalg_grZT (hp : 1 < p)
    (φ : ExpMap K (HomSubalg K p)) (hnt : φ.IsNontrivial) :
    ∃ φbar : ExpMap K (HomSubalg K p), φbar.IsNontrivial ∧
      ∀ a : HomSubalg K p, a ∈ φ.invSubalg →
        (⟨(grZT K p).topComp (a : Ambient K), by
          by_cases ha : (a : Ambient K) = 0
          · simp [ZGrading.topComp, ha, (HomSubalg K p).zero_mem]
          · rw [ZGrading.topComp, dif_neg ha]
            change _ ∈ SubalgOfPoly K (gHomPoly K p)
            rw [mem_subalgOfPoly_iff]
            intro m hm
            change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
              (∑ j ∈ suppA K (a : Ambient K), singleT K j
                (projP2 K p ((grZT K p).topDeg (a : Ambient K) ha) ((a : Ambient K).coeff j))).coeff m
            rw [coeff_sum_projP2]
            obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 m hm
            rw [hg, projP2_mul_hom K p _ _ _ g
              (projP2_pow_hom K p _ _ (-gHomPoly K p) (by rw [projP2_neg, gHomPoly_hom]))]
            exact dvd_mul_right _ _⟩ : HomSubalg K p) ∈ φbar.invSubalg := by
  classical
  let D := HomSubalg K p
  let w0 : ℤ := (p ^ 2 * (p + 1) : ℤ)
  let Γ : Finset D := {bX K p, bY K p, bZ K p, bT K p}
  have hG_graded : ∀ b ∈ D, ∀ n : ℤ, (grZT K p).proj n b ∈ D := by
    intro b hb n
    change _ ∈ SubalgOfPoly K (gHomPoly K p)
    rw [mem_subalgOfPoly_iff]
    intro m hm
    change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
      (∑ j ∈ suppA K b, singleT K j (projP2 K p n (b.coeff j))).coeff m
    rw [coeff_sum_projP2]
    obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm
    rw [hg, projP2_mul_hom K p _ _ _ g
      (projP2_pow_hom K p _ _ (-gHomPoly K p) (by rw [projP2_neg, gHomPoly_hom]))]
    exact dvd_mul_right _ _
  have hGD : ∀ b ∈ D, ∀ d : ℤ, (grZT K p).proj d b = b →
      ∃ a ∈ D, (grZT K p).DegLe a d ∧ (grZT K p).proj d a = b := by
    intro b hb d hbd
    refine ⟨b, hb, fun n hn => by rw [← hbd, (grZT K p).proj_proj, if_neg (by omega)], hbd⟩
  have hΓ_ne : ∀ g ∈ Γ, (g : Ambient K) ≠ 0 := by
    intro g hg h0
    simp only [Γ, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · have := congrArg (fun r : Ambient K => r.coeff 1) h0
      change (genX K).coeff 1 = 0 at this
      have h1 : (genX K).coeff 1 = 1 := by change (singleT K 1 1).coeff 1 = 1; simp [coeff_singleT]
      rw [h1] at this; exact one_ne_zero this
    · have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
      change (genYB K p).coeff (-2) = 0 at this
      have h1 : (genYB K p).coeff (-2) = -gHomPoly K p := by
        rw [genYB, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl]
      rw [h1] at this; exact gHomPoly_ne_zero K p hp (neg_eq_zero.mp this)
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      change (genZ K).coeff 0 = 0 at this
      have h1 : (genZ K).coeff 0 = MvPolynomial.X 0 := by
        change (singleT K 0 (MvPolynomial.X 0)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this; exact MvPolynomial.X_ne_zero (0 : Fin 2) this
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      change (genT K).coeff 0 = 0 at this
      have h1 : (genT K).coeff 0 = MvPolynomial.X 1 := by
        change (singleT K 0 (MvPolynomial.X 1)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this; exact MvPolynomial.X_ne_zero (1 : Fin 2) this
  have hΓ_admiss : ∀ (a : D) (d : ℤ), (grZT K p).DegLe (a : Ambient K) d →
      ∃ (L : List (K × List D)),
        (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
        (∀ q ∈ L, (grZT K p).DegLe ((q.2.map Subtype.val).prod) d) ∧
        (a : Ambient K) = (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
    intro a d had
    have had_m := (degLe_grZT_iff K p (a : Ambient K) d).mp had
    have hterm : ∀ m ∈ suppA K (a : Ambient K),
        ∃ L : List (K × List D),
          (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
          (∀ q ∈ L, (grZT K p).DegLe ((q.2.map Subtype.val).prod) d) ∧
          singleT K m ((a : Ambient K).coeff m) =
            (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
      intro m _
      by_cases hmneg : m < 0
      · obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 m hmneg
        let j : ℕ := ((-m + 1) / 2).toNat
        let i : ℕ := (m + 2 * (j : ℤ)).toNat
        have hij : (i : ℤ) + (-2) * (j : ℤ) = m := by omega
        have hhom_j : projP2 K p (j * w0) ((-gHomPoly K p) ^ j) = (-gHomPoly K p) ^ j :=
          projP2_pow_hom K p w0 j (-gHomPoly K p) (by rw [projP2_neg, gHomPoly_hom])
        have hdeg_j : DegLeP2 K p (j * w0) ((-gHomPoly K p) ^ j) := by
          rw [degLeP2_iff_projP2]; intro k hk
          rw [← hhom_j]; ext e; rw [coeff_projP2, coeff_projP2, MvPolynomial.coeff_zero]
          split_ifs with h1 h2
          · exfalso; linarith
          · rfl
          · rfl
        have hg_deg : DegLeP2 K p (d - j * w0) g :=
          degLeP2_of_mul K p hdeg_j
            (by rw [hhom_j]; exact pow_ne_zero j (neg_ne_zero.mpr (gHomPoly_ne_zero K p hp)))
            (hg ▸ had_m m)
        obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K (bX K p) (bY K p) (bZ K p) (bT K p) rfl rfl rfl g i j
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, he, hqeq⟩ := hLform q hq
          rw [hqeq, degLe_grZT_iff]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (bY K p : Ambient K) ^ j =
              LaurentPolynomial.C ((-gHomPoly K p) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2]
          have hsingle : LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
              LaurentPolynomial.T (i : ℤ) *
              (LaurentPolynomial.C ((-gHomPoly K p) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ))) =
              singleT K m (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 * (-gHomPoly K p) ^ j) := by
            simp only [singleT_eq_C_mul_T, ← hij, LaurentPolynomial.T_add, map_mul]; ring
          rw [hsingle]
          intro k; rw [coeff_singleT]
          split_ifs
          · have hmon_deg : DegLeP2 K p (d - j * w0) (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) := by
              intro e' he'
              have hne := MvPolynomial.mem_support_iff.mp he'
              have hmon_eq : (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 : P2 K) =
                  MvPolynomial.monomial e 1 := by
                rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                  Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
              rw [hmon_eq, MvPolynomial.coeff_monomial] at hne
              split_ifs at hne with hee
              · subst hee; exact hg_deg e he
              · exact absurd rfl hne
            have := degLeP2_mul K p hmon_deg hdeg_j
            rwa [sub_add_cancel] at this
          · intro e' he'; simp at he'
        · have hg' : (a : Ambient K).coeff m = (-gHomPoly K p) ^ j * g := hg
          rw [← hLsum, singleT_eq_C_mul_T, hg', map_mul, map_pow]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (bY K p : Ambient K) ^ j =
              LaurentPolynomial.C (-gHomPoly K p) ^ j * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2, ← hij, LaurentPolynomial.T_add]; ring
      · obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K (bX K p) (bY K p) (bZ K p) (bT K p) rfl rfl rfl
            ((a : Ambient K).coeff m) m.toNat 0
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, he, hqeq⟩ := hLform q hq
          rw [hqeq, pow_zero, mul_one, degLe_grZT_iff]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1, ← singleT_eq_C_mul_T]
          intro k; rw [coeff_singleT]
          split_ifs
          · intro e' he'
            have hne := MvPolynomial.mem_support_iff.mp he'
            have hmon_eq : (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 : P2 K) =
                MvPolynomial.monomial e 1 := by
              rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
            rw [hmon_eq, MvPolynomial.coeff_monomial] at hne
            split_ifs at hne with hee
            · subst hee; exact had_m m e he
            · exact absurd rfl hne
          · intro e' he'; simp at he'
        · rw [← hLsum, pow_zero, mul_one, singleT_eq_C_mul_T]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1]
    choose fL hfLΓ hfLdeg hfLsum using fun (m : {m // m ∈ suppA K (a : Ambient K)}) => hterm m.1 m.2
    let L : List (K × List D) := (suppA K (a : Ambient K)).attach.toList.flatMap fL
    refine ⟨L, ?_, ?_, ?_⟩
    · intro q hq u hu
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLΓ m q hqm u hu
    · intro q hq
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLdeg m q hqm
    · rw [← sum_singleT K (a : Ambient K)]
      have h1 : ∑ m ∈ suppA K (a : Ambient K), singleT K m ((a : Ambient K).coeff m) =
          ∑ m ∈ (suppA K (a : Ambient K)).attach, singleT K m.1 ((a : Ambient K).coeff m.1) := by
        rw [Finset.sum_attach (suppA K (a : Ambient K)) (fun m => singleT K m ((a : Ambient K).coeff m))]
      rw [h1]
      symm
      simp only [L, List.map_flatMap]
      rw [list_sum_flatMap]
      have h2 : (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => (List.map (fun q => q.1 • (List.map Subtype.val q.2).prod) (fL m)).sum)).sum =
          (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => singleT K m.1 ((a : Ambient K).coeff m.1))).sum := by
        congr 1; exact List.map_congr_left fun m _ => (hfLsum m).symm
      rw [h2, list_map_toList_sum]
  exact ZGrading.homogenizeExpMap (grZT K p) D D hG_graded (fun a ha d _ => hG_graded a ha d) hGD Γ hΓ_ne hΓ_admiss φ hnt

/-- Helper: `grZT` homogenization from `AsanumaSubalg K p` (`A_K`) to `HomSubalg K p` (`B_K`). -/
lemma homogenize_asanuma_to_hom_grZT (hp : 1 < p)
    (φ : ExpMap K (AsanumaSubalg K p)) (hnt : φ.IsNontrivial) :
    ∃ φbar : ExpMap K (HomSubalg K p), φbar.IsNontrivial ∧
      ∀ a : AsanumaSubalg K p, a ∈ φ.invSubalg →
        (⟨(grZT K p).topComp (a : Ambient K), by
          by_cases ha : (a : Ambient K) = 0
          · simp [ZGrading.topComp, ha, (HomSubalg K p).zero_mem]
          · rw [ZGrading.topComp, dif_neg ha]
            change _ ∈ SubalgOfPoly K (gHomPoly K p)
            rw [mem_subalgOfPoly_iff]
            intro m hm
            let d := (grZT K p).topDeg (a : Ambient K) ha
            have had_m := (degLe_grZT_iff K p (a : Ambient K) d).mp ((grZT K p).degLe_topDeg ha) m
            change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
              (∑ j ∈ suppA K (a : Ambient K), singleT K j
                (projP2 K p d ((a : Ambient K).coeff j))).coeff m
            rw [coeff_sum_projP2]
            obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (fPoly K p) _).mp a.2 m hm
            let j : ℕ := ((-m + 1) / 2).toNat
            let w0 : ℤ := (p ^ 2 * (p + 1) : ℤ)
            have hg_deg : DegLeP2 K p (d - j * w0) g :=
              degLeP2_of_mul K p (neg_fPoly_pow_degLe K p hp j)
                (by rw [neg_fPoly_pow_proj_top K p hp j]
                    exact pow_ne_zero j (neg_ne_zero.mpr (gHomPoly_ne_zero K p hp)))
                (hg ▸ had_m)
            have htop := projP2_mul_top K p (neg_fPoly_pow_degLe K p hp j) hg_deg
            rw [add_sub_cancel, neg_fPoly_pow_proj_top K p hp j] at htop
            rw [hg, htop]
            exact dvd_mul_right _ _⟩ : HomSubalg K p) ∈ φbar.invSubalg := by
  classical
  let D := AsanumaSubalg K p
  let G := HomSubalg K p
  let w0 : ℤ := (p ^ 2 * (p + 1) : ℤ)
  let Γ : Finset D := {aX K p, aY K p, aZ K p, aT K p}
  have hG_graded : ∀ b ∈ G, ∀ n : ℤ, (grZT K p).proj n b ∈ G := by
    intro b hb n
    change _ ∈ SubalgOfPoly K (gHomPoly K p)
    rw [mem_subalgOfPoly_iff]
    intro m hm
    change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
      (∑ j ∈ suppA K b, singleT K j (projP2 K p n (b.coeff j))).coeff m
    rw [coeff_sum_projP2]
    obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm
    rw [hg, projP2_mul_hom K p _ _ _ g
      (projP2_pow_hom K p _ _ (-gHomPoly K p) (by rw [projP2_neg, gHomPoly_hom]))]
    exact dvd_mul_right _ _
  have hDG : ∀ a ∈ D, ∀ d : ℤ, (grZT K p).DegLe a d → (grZT K p).proj d a ∈ G := by
    intro a ha d had
    change _ ∈ SubalgOfPoly K (gHomPoly K p)
    rw [mem_subalgOfPoly_iff]
    intro m hm
    have had_m := (degLe_grZT_iff K p a d).mp had m
    change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
      (∑ j ∈ suppA K a, singleT K j (projP2 K p d (a.coeff j))).coeff m
    rw [coeff_sum_projP2]
    obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (fPoly K p) a).mp ha m hm
    let j : ℕ := ((-m + 1) / 2).toNat
    have hg_deg : DegLeP2 K p (d - j * w0) g :=
      degLeP2_of_mul K p (neg_fPoly_pow_degLe K p hp j)
        (by rw [neg_fPoly_pow_proj_top K p hp j]
            exact pow_ne_zero j (neg_ne_zero.mpr (gHomPoly_ne_zero K p hp)))
        (hg ▸ had_m)
    have htop := projP2_mul_top K p (neg_fPoly_pow_degLe K p hp j) hg_deg
    rw [add_sub_cancel, neg_fPoly_pow_proj_top K p hp j] at htop
    rw [hg, htop]
    exact dvd_mul_right _ _
  have hGD : ∀ b ∈ G, ∀ d : ℤ, (grZT K p).proj d b = b →
      ∃ a ∈ D, (grZT K p).DegLe a d ∧ (grZT K p).proj d a = b := by
    intro b hb d hbd
    have hbd_m : ∀ m : ℤ, projP2 K p d (b.coeff m) = b.coeff m := fun m => by
      have := congrArg (fun r : Ambient K => r.coeff m) hbd
      change (∑ j ∈ suppA K b, singleT K j (projP2 K p d (b.coeff j))).coeff m = b.coeff m at this
      rwa [coeff_sum_projP2] at this
    -- For each `m ∈ suppA K b`, lift `b.coeff m` to `a_m`
    let liftCoeff (m : ℤ) : P2 K :=
      if hm : m < 0 then
        let j : ℕ := ((-m + 1) / 2).toNat
        let g : P2 K := ((mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm).choose
        (-fPoly K p) ^ j * projP2 K p (d - j * w0) g
      else b.coeff m
    let a : Ambient K := ∑ m ∈ suppA K b, singleT K m (liftCoeff m)
    have ha_coeff : ∀ m : ℤ, a.coeff m = if m ∈ suppA K b then liftCoeff m else 0 := by
      intro m
      rw [coeff_sum_A]
      by_cases hm : m ∈ suppA K b
      · rw [if_pos hm, Finset.sum_eq_single m]
        · simp [coeff_singleT]
        · intro k _ hkm; simp [coeff_singleT, hkm]
        · intro hnm; exact absurd hm hnm
      · rw [if_neg hm]
        apply Finset.sum_eq_zero; intro k hk
        simp [coeff_singleT, show k ≠ m from fun h => hm (h ▸ hk)]
    refine ⟨a, ?_, ?_, ?_⟩
    · change a ∈ SubalgOfPoly K (fPoly K p)
      rw [mem_subalgOfPoly_iff]
      intro m hm
      rw [ha_coeff m]
      split_ifs with hmem
      · simp only [liftCoeff, dif_pos hm]; exact dvd_mul_right _ _
      · exact dvd_zero _
    · rw [degLe_grZT_iff]
      intro m
      rw [ha_coeff m]
      split_ifs with hmem
      · by_cases hm : m < 0
        · simp only [liftCoeff, dif_pos hm]
          let j : ℕ := ((-m + 1) / 2).toNat
          let g : P2 K := ((mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm).choose
          have hproj_deg : DegLeP2 K p (d - j * w0) (projP2 K p (d - j * w0) g) := by
            intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            rw [coeff_projP2] at hne
            split_ifs at hne with hwt
            · linarith
            · exact absurd rfl hne
          have := degLeP2_mul K p (neg_fPoly_pow_degLe K p hp j) hproj_deg
          rwa [add_sub_cancel] at this
        · simp only [liftCoeff, dif_neg hm]
          intro e he
          have hne := MvPolynomial.mem_support_iff.mp he
          rw [← hbd_m m, coeff_projP2] at hne
          split_ifs at hne with hwt
          · linarith
          · exact absurd rfl hne
      · intro e he; simp at he
    · ext m : 1
      change (∑ j ∈ suppA K a, singleT K j (projP2 K p d (a.coeff j))).coeff m = b.coeff m
      rw [coeff_sum_projP2, ha_coeff m]
      split_ifs with hmem
      · by_cases hm : m < 0
        · simp only [liftCoeff, dif_pos hm]
          let j : ℕ := ((-m + 1) / 2).toNat
          let g : P2 K := ((mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm).choose
          have hg : b.coeff m = (-gHomPoly K p) ^ j * g :=
            ((mem_subalgOfPoly_iff K (gHomPoly K p) b).mp hb m hm).choose_spec
          have hproj_deg : DegLeP2 K p (d - j * w0) (projP2 K p (d - j * w0) g) := by
            intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            rw [coeff_projP2] at hne
            split_ifs at hne with hwt
            · linarith
            · exact absurd rfl hne
          have htop := projP2_mul_top K p (neg_fPoly_pow_degLe K p hp j) hproj_deg
          rw [add_sub_cancel, neg_fPoly_pow_proj_top K p hp j] at htop
          have hpp : projP2 K p (d - j * w0) (projP2 K p (d - j * w0) g) = projP2 K p (d - j * w0) g := by
            ext e; rw [coeff_projP2, coeff_projP2]; split_ifs <;> rfl
          rw [htop, hpp, ← projP2_mul_hom K p (j * w0) d ((-gHomPoly K p) ^ j) g
            (projP2_pow_hom K p w0 j (-gHomPoly K p) (by rw [projP2_neg, gHomPoly_hom])),
            ← hg, hbd_m m]
        · simp only [liftCoeff, dif_neg hm, hbd_m m]
      · have h0 : b.coeff m = 0 := not_not.mp ((mem_suppA_iff K b m).not.mp hmem)
        rw [h0]; ext e; simp [coeff_projP2]
  have hΓ_ne : ∀ g ∈ Γ, (g : Ambient K) ≠ 0 := by
    intro g hg h0
    simp only [Γ, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · have := congrArg (fun r : Ambient K => r.coeff 1) h0
      change (genX K).coeff 1 = 0 at this
      have h1 : (genX K).coeff 1 = 1 := by change (singleT K 1 1).coeff 1 = 1; simp [coeff_singleT]
      rw [h1] at this; exact one_ne_zero this
    · have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
      change (genY K p).coeff (-2) = 0 at this
      have h1 : (genY K p).coeff (-2) = -fPoly K p := by
        rw [genY, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl]
      rw [h1] at this; exact fPoly_ne_zero K p hp (neg_eq_zero.mp this)
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      change (genZ K).coeff 0 = 0 at this
      have h1 : (genZ K).coeff 0 = MvPolynomial.X 0 := by
        change (singleT K 0 (MvPolynomial.X 0)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this; exact MvPolynomial.X_ne_zero (0 : Fin 2) this
    · have := congrArg (fun r : Ambient K => r.coeff 0) h0
      change (genT K).coeff 0 = 0 at this
      have h1 : (genT K).coeff 0 = MvPolynomial.X 1 := by
        change (singleT K 0 (MvPolynomial.X 1)).coeff 0 = _; simp [coeff_singleT]
      rw [h1] at this; exact MvPolynomial.X_ne_zero (1 : Fin 2) this
  have hΓ_admiss : ∀ (a : D) (d : ℤ), (grZT K p).DegLe (a : Ambient K) d →
      ∃ (L : List (K × List D)),
        (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
        (∀ q ∈ L, (grZT K p).DegLe ((q.2.map Subtype.val).prod) d) ∧
        (a : Ambient K) = (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
    intro a d had
    have had_m := (degLe_grZT_iff K p (a : Ambient K) d).mp had
    have hterm : ∀ m ∈ suppA K (a : Ambient K),
        ∃ L : List (K × List D),
          (∀ q ∈ L, ∀ u ∈ q.2, u ∈ Γ) ∧
          (∀ q ∈ L, (grZT K p).DegLe ((q.2.map Subtype.val).prod) d) ∧
          singleT K m ((a : Ambient K).coeff m) =
            (L.map (fun q => q.1 • (q.2.map Subtype.val).prod)).sum := by
      intro m _
      by_cases hmneg : m < 0
      · obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (fPoly K p) _).mp a.2 m hmneg
        let j : ℕ := ((-m + 1) / 2).toNat
        let i : ℕ := (m + 2 * (j : ℤ)).toNat
        have hij : (i : ℤ) + (-2) * (j : ℤ) = m := by omega
        have hg_deg : DegLeP2 K p (d - j * w0) g :=
          degLeP2_of_mul K p (neg_fPoly_pow_degLe K p hp j)
            (by rw [neg_fPoly_pow_proj_top K p hp j]
                exact pow_ne_zero j (neg_ne_zero.mpr (gHomPoly_ne_zero K p hp)))
            (hg ▸ had_m m)
        obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K (aX K p) (aY K p) (aZ K p) (aT K p) rfl rfl rfl g i j
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, he, hqeq⟩ := hLform q hq
          rw [hqeq, degLe_grZT_iff]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (aY K p : Ambient K) ^ j =
              LaurentPolynomial.C ((-fPoly K p) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2]
          have hsingle : LaurentPolynomial.C (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) *
              LaurentPolynomial.T (i : ℤ) *
              (LaurentPolynomial.C ((-fPoly K p) ^ j) * LaurentPolynomial.T ((-2) * (j : ℤ))) =
              singleT K m (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 * (-fPoly K p) ^ j) := by
            simp only [singleT_eq_C_mul_T, ← hij, LaurentPolynomial.T_add, map_mul]; ring
          rw [hsingle]
          intro k; rw [coeff_singleT]
          split_ifs
          · have hmon_deg : DegLeP2 K p (d - j * w0) (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1) := by
              intro e' he'
              have hne := MvPolynomial.mem_support_iff.mp he'
              have hmon_eq : (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 : P2 K) =
                  MvPolynomial.monomial e 1 := by
                rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                  Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
              rw [hmon_eq, MvPolynomial.coeff_monomial] at hne
              split_ifs at hne with hee
              · subst hee; exact hg_deg e he
              · exact absurd rfl hne
            have := degLeP2_mul K p hmon_deg (neg_fPoly_pow_degLe K p hp j)
            rwa [sub_add_cancel] at this
          · intro e' he'; simp at he'
        · have hg' : (a : Ambient K).coeff m = (-fPoly K p) ^ j * g := hg
          rw [← hLsum, singleT_eq_C_mul_T, hg', map_mul, map_pow]
          have hT1 : (genX K) ^ i = LaurentPolynomial.T (i : ℤ) := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ i = _
            rw [LaurentPolynomial.T_pow]; simp
          have hT2 : (aY K p : Ambient K) ^ j =
              LaurentPolynomial.C (-fPoly K p) ^ j * LaurentPolynomial.T ((-2) * (j : ℤ)) := by
            change (LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.T (-2)) ^ j = _
            rw [mul_pow, LaurentPolynomial.T_pow]; congr 2; ring
          rw [hT1, hT2, ← hij, LaurentPolynomial.T_add]; ring
      · obtain ⟨L, hLΓ, hLform, hLsum⟩ :=
          expand_C_mul_XY K (aX K p) (aY K p) (aZ K p) (aT K p) rfl rfl rfl
            ((a : Ambient K).coeff m) m.toNat 0
        refine ⟨L, fun q hq u hu => by rcases hLΓ q hq u hu with rfl | rfl | rfl | rfl <;> simp [Γ], ?_, ?_⟩
        · intro q hq
          obtain ⟨e, he, hqeq⟩ := hLform q hq
          rw [hqeq, pow_zero, mul_one, degLe_grZT_iff]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1, ← singleT_eq_C_mul_T]
          intro k; rw [coeff_singleT]
          split_ifs
          · intro e' he'
            have hne := MvPolynomial.mem_support_iff.mp he'
            have hmon_eq : (MvPolynomial.X 0 ^ e 0 * MvPolynomial.X 1 ^ e 1 : P2 K) =
                MvPolynomial.monomial e 1 := by
              rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
            rw [hmon_eq, MvPolynomial.coeff_monomial] at hne
            split_ifs at hne with hee
            · subst hee; exact had_m m e he
            · exact absurd rfl hne
          · intro e' he'; simp at he'
        · rw [← hLsum, pow_zero, mul_one, singleT_eq_C_mul_T]
          have hT1 : (genX K) ^ m.toNat = LaurentPolynomial.T m := by
            change (LaurentPolynomial.T (1 : ℤ) : Ambient K) ^ m.toNat = _
            rw [LaurentPolynomial.T_pow]; congr 1; omega
          rw [hT1]
    choose fL hfLΓ hfLdeg hfLsum using fun (m : {m // m ∈ suppA K (a : Ambient K)}) => hterm m.1 m.2
    let L : List (K × List D) := (suppA K (a : Ambient K)).attach.toList.flatMap fL
    refine ⟨L, ?_, ?_, ?_⟩
    · intro q hq u hu
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLΓ m q hqm u hu
    · intro q hq
      simp only [L, List.mem_flatMap] at hq
      obtain ⟨m, _, hqm⟩ := hq
      exact hfLdeg m q hqm
    · rw [← sum_singleT K (a : Ambient K)]
      have h1 : ∑ m ∈ suppA K (a : Ambient K), singleT K m ((a : Ambient K).coeff m) =
          ∑ m ∈ (suppA K (a : Ambient K)).attach, singleT K m.1 ((a : Ambient K).coeff m.1) := by
        rw [Finset.sum_attach (suppA K (a : Ambient K)) (fun m => singleT K m ((a : Ambient K).coeff m))]
      rw [h1]
      symm
      simp only [L, List.map_flatMap]
      rw [list_sum_flatMap]
      have h2 : (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => (List.map (fun q => q.1 • (List.map Subtype.val q.2).prod) (fL m)).sum)).sum =
          (((suppA K (a : Ambient K)).attach.toList).map
          (fun m => singleT K m.1 ((a : Ambient K).coeff m.1))).sum := by
        congr 1; exact List.map_congr_left fun m _ => (hfLsum m).symm
      rw [h2, list_map_toList_sum]
  exact ZGrading.homogenizeExpMap (grZT K p) D G hG_graded hDG hGD Γ hΓ_ne hΓ_admiss φ hnt

end Admissibility

/- ## Section 7b2a: Factoring `grZT`-homogeneous polynomials and extracting an invariant factor -/

section ExtractInvariantFactor

variable (K : Type*) [Field K] (p : ℕ)

set_option maxHeartbeats 400000 in
/-- Every non-constant `grZT`-homogeneous polynomial `f ∈ K[Z, T]` over an algebraically closed field `K`
    is divisible by `Z`, `T`, or `Z^p + μ * T^(p+1)` for some `μ ∈ Kˣ`. -/
lemma hom_P2_factor [IsAlgClosed K] (hp : 1 < p) (n : ℤ) (f : P2 K)
    (hf_hom : projP2 K p n f = f) (hf_nc : ∀ c : K, f ≠ MvPolynomial.C c) :
    (MvPolynomial.X 0 ∣ f) ∨ (MvPolynomial.X 1 ∣ f) ∨
      ∃ μ : K, μ ≠ 0 ∧ (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1) ∣ f) := by
  classical
  have hf_ne : f ≠ 0 := by intro h0; exact hf_nc 0 (by simp [h0])
  have hsupp_ne : f.support.Nonempty := MvPolynomial.support_nonempty.mpr hf_ne
  have hf_wt : ∀ d ∈ f.support, ((p + 1) * d 0 + p * d 1 : ℤ) = n := by
    intro d hd
    have h1 := congrArg (fun r : P2 K => r.coeff d) hf_hom
    rw [coeff_projP2] at h1
    split_ifs at h1 with hwt
    · exact hwt
    · exact absurd h1.symm (MvPolynomial.mem_support_iff.mp hd)
  by_cases hdivZ : ∀ d ∈ f.support, 1 ≤ d 0
  · left
    let g : P2 K := ∑ d ∈ f.support,
      MvPolynomial.monomial (d - Finsupp.single 0 1) (f.coeff d)
    refine ⟨g, ?_⟩
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 : 1 ≤ d 0 := hdivZ d hd
    have hadd : Finsupp.single (0 : Fin 2) 1 + (d - Finsupp.single 0 1) = d := by
      ext i; fin_cases i
      · simp; omega
      · simp
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, hadd]
  · push Not at hdivZ
    obtain ⟨dT, hdT_mem, hdT0_lt⟩ := hdivZ
    have hdT0 : dT 0 = 0 := by omega
    by_cases hdivT : ∀ d ∈ f.support, 1 ≤ d 1
    · right; left
      let g : P2 K := ∑ d ∈ f.support,
        MvPolynomial.monomial (d - Finsupp.single 1 1) (f.coeff d)
      refine ⟨g, ?_⟩
      conv_lhs => rw [MvPolynomial.as_sum f]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have h1 : 1 ≤ d 1 := hdivT d hd
      have hadd : Finsupp.single (1 : Fin 2) 1 + (d - Finsupp.single 1 1) = d := by
        ext i; fin_cases i
        · simp
        · simp; omega
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, hadd]
    · push Not at hdivT
      obtain ⟨dZ, hdZ_mem, hdZ1_lt⟩ := hdivT
      have hdZ1 : dZ 1 = 0 := by omega
      right; right
      have hn_Z : ((p + 1) * dZ 0 : ℤ) = n := by
        have := hf_wt dZ hdZ_mem; simp [hdZ1] at this; exact this
      have hn_T : (p * dT 1 : ℤ) = n := by
        have := hf_wt dT hdT_mem; simp [hdT0] at this; exact this
      have hrel_nat : (p + 1) * dZ 0 = p * dT 1 := by
        have : ((p + 1) * dZ 0 : ℤ) = (p * dT 1 : ℤ) := hn_Z.trans hn_T.symm
        exact_mod_cast this
      have hcop : Nat.Coprime p (p + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
      have hp_dvd_dZ : p ∣ dZ 0 :=
        hcop.dvd_of_dvd_mul_left ⟨dT 1, hrel_nat⟩
      obtain ⟨r, hr_eq⟩ := hp_dvd_dZ
      have hr_pos : 0 < r := by
        by_contra hr0
        have hr0' : r = 0 := by omega
        subst hr0'
        have hn0 : n = 0 := by rw [← hn_Z, hr_eq]; simp
        apply hf_nc (f.coeff 0)
        ext d
        rw [MvPolynomial.coeff_C]
        split_ifs with hd0
        · subst hd0; rfl
        · by_contra hne
          have hwt := hf_wt d (MvPolynomial.mem_support_iff.mpr hne)
          rw [hn0] at hwt
          have h0 : d 0 = 0 := by nlinarith
          have h1 : d 1 = 0 := by nlinarith
          apply hd0; ext i; fin_cases i
          · change 0 = d 0; omega
          · change 0 = d 1; omega
      have hdT1_eq : dT 1 = (p + 1) * r := by
        have : p * dT 1 = p * ((p + 1) * r) := by rw [← hrel_nat, hr_eq]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      have hn_eq : n = ((p * (p + 1) * r : ℕ) : ℤ) := by
        rw [← hn_Z, hr_eq]; push_cast; ring
      -- Every `d ∈ f.support` has `d = single 0 (p * k) + single 1 ((p + 1) * (r - k))` for some `k ≤ r`
      let monD (k : ℕ) : Fin 2 →₀ ℕ :=
        Finsupp.single 0 (p * k) + Finsupp.single 1 ((p + 1) * (r - k))
      have hsupp_form : ∀ d ∈ f.support, ∃ k ≤ r, d = monD k := by
        intro d hd
        have hwt := hf_wt d hd
        rw [hn_eq] at hwt
        have hnat : (p + 1) * d 0 + p * d 1 = p * (p + 1) * r := by exact_mod_cast hwt
        have hp_dvd : p ∣ (p + 1) * d 0 := by
          have : (p + 1) * d 0 = p * ((p + 1) * r - d 1) := by
            zify [show d 1 ≤ (p + 1) * r by nlinarith]; linarith
          exact ⟨(p + 1) * r - d 1, this⟩
        obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hp_dvd
        have hkr : k ≤ r := by nlinarith
        have hd1 : d 1 = (p + 1) * (r - k) := by
          have : p * d 1 = p * ((p + 1) * (r - k)) := by
            rw [hk] at hnat
            zify [hkr]; zify at hnat; linarith
          exact Nat.eq_of_mul_eq_mul_left (by omega) this
        refine ⟨k, hkr, ?_⟩
        ext i; fin_cases i <;> simp [monD, hk, hd1]
      -- Define univariate `Q(U) = ∑_{k=0}^r f.coeff (monD k) * U^k`
      let Q : Polynomial K :=
        ∑ k ∈ Finset.range (r + 1), Polynomial.monomial k (f.coeff (monD k))
      have hQ_coeff : ∀ k, Q.coeff k = if k ≤ r then f.coeff (monD k) else 0 := by
        intro k
        simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
        by_cases hkr : k ≤ r
        · rw [if_pos hkr, Finset.sum_eq_single k]
          · simp
          · intro j _ hjk; simp [hjk]
          · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr (by omega))
        · rw [if_neg hkr]
          apply Finset.sum_eq_zero; intro j hj
          have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
          rw [if_neg (by omega)]
      have hQ_r_ne : Q.coeff r ≠ 0 := by
        rw [hQ_coeff r, if_pos (le_refl r)]
        have heq : monD r = dZ := by ext i; fin_cases i <;> simp [monD, hr_eq, hdZ1]
        rw [heq]; exact MvPolynomial.mem_support_iff.mp hdZ_mem
      have hQ_0_ne : Q.coeff 0 ≠ 0 := by
        rw [hQ_coeff 0, if_pos (Nat.zero_le r)]
        have heq : monD 0 = dT := by ext i; fin_cases i <;> simp [monD, hdT0, hdT1_eq]
        rw [heq]; exact MvPolynomial.mem_support_iff.mp hdT_mem
      have hQ_deg : Q.natDegree = r := by
        apply le_antisymm
        · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
          rw [hQ_coeff m, if_neg (by omega)]
        · exact Polynomial.le_natDegree_of_ne_zero hQ_r_ne
      have hQ_deg_pos : 0 < Q.degree := by
        rw [Polynomial.degree_eq_natDegree (fun h0 => hQ_r_ne (by rw [h0, Polynomial.coeff_zero])),
          hQ_deg]
        exact_mod_cast hr_pos
      obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root Q (ne_of_gt hQ_deg_pos)
      have hα_ne : α ≠ 0 := by
        intro h0; subst h0
        have := hα_root
        rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero] at this
        exact hQ_0_ne this
      obtain ⟨R, hQR⟩ := Polynomial.dvd_iff_isRoot.mpr hα_root
      have hR_deg : ∀ k, r ≤ k → R.coeff k = 0 := by
        intro k hk
        have hR_ne : R ≠ 0 := fun h0 => hQ_r_ne (by rw [hQR, h0, mul_zero, Polynomial.coeff_zero])
        have hdeg_add : Q.natDegree = (Polynomial.X - Polynomial.C α).natDegree + R.natDegree := by
          rw [hQR, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α) hR_ne]
        rw [hQ_deg, Polynomial.natDegree_X_sub_C] at hdeg_add
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      -- Now `μ := -α ≠ 0` and `(Z^p + μ T^(p+1))` divides `f`!
      refine ⟨-α, neg_ne_zero.mpr hα_ne, ?_⟩
      let U : P2 K := MvPolynomial.X 0 ^ p
      let V : P2 K := MvPolynomial.X 1 ^ (p + 1)
      let G : P2 K := ∑ k ∈ Finset.range r,
        MvPolynomial.C (R.coeff k) * U ^ k * V ^ (r - 1 - k)
      refine ⟨G, ?_⟩
      -- Express `f` as `∑ k ∈ range (r + 1), C (Q.coeff k) * U^k * V^(r - k)`
      have hf_sum : f = ∑ k ∈ Finset.range (r + 1),
          MvPolynomial.C (Q.coeff k) * U ^ k * V ^ (r - k) := by
        ext d
        rw [MvPolynomial.coeff_sum]
        have hterm_coeff : ∀ k ∈ Finset.range (r + 1),
            (MvPolynomial.C (Q.coeff k) * U ^ k * V ^ (r - k)).coeff d =
            if monD k = d then Q.coeff k else 0 := by
          intro k _
          have hmon : MvPolynomial.C (Q.coeff k) * U ^ k * V ^ (r - k) =
              MvPolynomial.monomial (monD k) (Q.coeff k) := by
            rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
              Fin.prod_univ_two]
            simp only [U, V, monD, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
              Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero, zero_add,
              ← pow_mul, mul_assoc]
          rw [hmon, MvPolynomial.coeff_monomial]
        rw [Finset.sum_congr rfl hterm_coeff]
        by_cases hd_mem : d ∈ f.support
        · obtain ⟨k, hkr, rfl⟩ := hsupp_form d hd_mem
          rw [Finset.sum_eq_single k]
          · rw [if_pos rfl, hQ_coeff k, if_pos hkr]
          · intro j _ hjk
            rw [if_neg]
            intro heq
            have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) heq
            simp [monD] at h0
            exact hjk (h0.resolve_right (by omega))
          · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr (by omega))
        · have h0 : f.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd_mem
          rw [h0]
          symm; apply Finset.sum_eq_zero; intro k hk
          split_ifs with heq
          · subst heq; rw [hQ_coeff k, if_pos (by have := Finset.mem_range.mp hk; omega), h0]
          · rfl
      rw [hf_sum]
      have hQ_coeff_rel : ∀ k ≤ r,
          Q.coeff k = (if 0 < k then R.coeff (k - 1) else 0) + (-α) * R.coeff k := by
        intro k _
        rw [hQR, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        by_cases hk : 0 < k
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [if_pos hk, Nat.succ_sub_one, Polynomial.coeff_X_mul]; ring
        · have hk0 : k = 0 := by omega
          subst hk0; rw [if_neg (by omega), Polynomial.coeff_X_mul_zero]; ring
      have hG_exp : (U + MvPolynomial.C (-α) * V) * G =
          (∑ k ∈ Finset.range r, MvPolynomial.C (R.coeff k) * U ^ (k + 1) * V ^ (r - 1 - k)) +
          (∑ k ∈ Finset.range r, MvPolynomial.C ((-α) * R.coeff k) * U ^ k * V ^ (r - k)) := by
        rw [add_mul]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_succ', mul_assoc, mul_left_comm U (MvPolynomial.C (R.coeff k)), mul_assoc, mul_assoc]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkr : k < r := Finset.mem_range.mp hk
          have hexp : r - 1 - k + 1 = r - k := by omega
          rw [map_mul]
          calc MvPolynomial.C (-α) * V * (MvPolynomial.C (R.coeff k) * U ^ k * V ^ (r - 1 - k))
              = MvPolynomial.C (-α) * MvPolynomial.C (R.coeff k) * U ^ k * (V ^ (r - 1 - k) * V) := by
                simp only [mul_assoc, mul_left_comm, mul_comm]
            _ = MvPolynomial.C (-α) * MvPolynomial.C (R.coeff k) * U ^ k * V ^ (r - k) := by
                rw [← pow_succ, hexp]
      change ∑ k ∈ Finset.range (r + 1), MvPolynomial.C (Q.coeff k) * U ^ k * V ^ (r - k) =
        (U + MvPolynomial.C (-α) * V) * G
      rw [hG_exp]
      have h1 : ∑ k ∈ Finset.range (r + 1), MvPolynomial.C (Q.coeff k) * U ^ k * V ^ (r - k) =
          (∑ k ∈ Finset.range (r + 1),
            MvPolynomial.C (if 0 < k then R.coeff (k - 1) else 0) * U ^ k * V ^ (r - k)) +
          (∑ k ∈ Finset.range (r + 1),
            MvPolynomial.C ((-α) * R.coeff k) * U ^ k * V ^ (r - k)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkr : k ≤ r := by have := Finset.mem_range.mp hk; omega
        rw [hQ_coeff_rel k hkr, map_add, add_mul, add_mul]
      rw [h1]
      congr 1
      · rw [Finset.sum_range_succ']
        simp only [lt_self_iff_false, ↓reduceIte, map_zero, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [show r - (k + 1) = r - 1 - k by omega]
      · rw [Finset.sum_range_succ, hR_deg r (le_refl r), mul_zero, map_zero, zero_mul, zero_mul, add_zero]

/-- `bX, bZ, bY` are algebraically independent over `K` in `HomRing K p`. -/
lemma bX_bZ_bY_algIndep (hp : 1 < p) (Q : MvPolynomial (Fin 3) K)
    (hQ : MvPolynomial.aeval ![bX K p, bZ K p, bY K p] Q = 0) : Q = 0 := by
  classical
  by_contra hQ_ne
  -- Let `kmax` be the max degree of `X 2` (i.e. `bY`) in `Q.support`
  have hsupp : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ_ne
  let kset : Finset ℕ := Q.support.image fun e => e 2
  let kmax : ℕ := kset.max' (hsupp.image _)
  -- Pick `e₀ ∈ Q.support` with `e₀ 2 = kmax`
  obtain ⟨e₀, he₀_mem, he₀_2⟩ := Finset.mem_image.mp (Finset.max'_mem kset (hsupp.image _))
  -- Look at the `T`-degree `kmax * p * (p + 1)` in the `X`-coefficient `e₀ 0 - 2 * kmax`!
  let m₀ : ℤ := (e₀ 0 : ℤ) - 2 * (kmax : ℤ)
  let d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (e₀ 1) + Finsupp.single 1 (kmax * (p * (p + 1)))
  have hval0 : (((MvPolynomial.aeval ![bX K p, bZ K p, bY K p] Q : HomRing K p) : Ambient K).coeff m₀).coeff d₀ = 0 := by
    rw [hQ]; rfl
  -- Compute the evaluation in `Ambient K`
  have haeval_coe : ((MvPolynomial.aeval ![bX K p, bZ K p, bY K p] Q : HomRing K p) : Ambient K) =
      MvPolynomial.aeval ![genX K, genZ K, genYB K p] Q := by
    have hcomp : (HomSubalg K p).val.comp (MvPolynomial.aeval ![bX K p, bZ K p, bY K p]) =
        MvPolynomial.aeval ![genX K, genZ K, genYB K p] := by
      apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [bX, bZ, bY]
    exact AlgHom.congr_fun hcomp Q
  rw [haeval_coe, MvPolynomial.as_sum Q, map_sum, coeff_sum_A, MvPolynomial.coeff_sum] at hval0
  have hterm : ∀ e ∈ Q.support,
      ((MvPolynomial.aeval ![genX K, genZ K, genYB K p]
        (MvPolynomial.monomial e (Q.coeff e))).coeff m₀).coeff d₀ =
      if e = e₀ then (-1 : K) ^ kmax * Q.coeff e₀ else 0 := by
    intro e he
    have he2_le : e 2 ≤ kmax := Finset.le_max' kset (e 2) (Finset.mem_image_of_mem _ he)
    have hmon : MvPolynomial.aeval ![genX K, genZ K, genYB K p] (MvPolynomial.monomial e (Q.coeff e)) =
        singleT K ((e 0 : ℤ) - 2 * (e 2 : ℤ))
          (MvPolynomial.C (Q.coeff e) * MvPolynomial.X 0 ^ e 1 * (-gHomPoly K p) ^ e 2) := by
      rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.aeval_C,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        genX, genZ, genYB, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
      have hC : (algebraMap K (Ambient K)) (Q.coeff e) = LaurentPolynomial.C (MvPolynomial.C (Q.coeff e)) := rfl
      have hTadd : (LaurentPolynomial.T ((e 0 : ℤ) - 2 * (e 2 : ℤ)) : Ambient K) =
          LaurentPolynomial.T (e 0 : ℤ) * LaurentPolynomial.T ((-2) * (e 2 : ℤ)) := by
        rw [← LaurentPolynomial.T_add]; congr 1
      have hT1 : (LaurentPolynomial.T ((e 0 : ℤ) * 1) : Ambient K) = LaurentPolynomial.T (e 0 : ℤ) := by
        rw [mul_one]
      have hT2 : (LaurentPolynomial.T ((e 2 : ℤ) * (-2)) : Ambient K) = LaurentPolynomial.T ((-2) * (e 2 : ℤ)) := by
        rw [mul_comm]
      rw [hC, hTadd, hT1, hT2]; ring
    rw [hmon, coeff_singleT]
    by_cases hm : (e 0 : ℤ) - 2 * (e 2 : ℤ) = m₀
    · rw [if_pos hm]
      -- Compute `coeff d₀` of `C (Q.coeff e) * Z^(e 1) * (-gHomPoly)^(e 2)`
      -- Notice every monomial in `(-gHomPoly)^(e 2)` has `T`-degree `≤ e 2 * p * (p + 1)`
      have hTdeg_le : ∀ f_d : Fin 2 →₀ ℕ,
          ((-gHomPoly K p) ^ e 2).coeff f_d ≠ 0 → f_d 1 ≤ e 2 * (p * (p + 1)) := by
        intro f_d hne
        suffices ∀ k : ℕ, ∀ fd : Fin 2 →₀ ℕ, ((-gHomPoly K p) ^ k).coeff fd ≠ 0 → fd 1 ≤ k * (p * (p + 1)) by
          exact this (e 2) f_d hne
        intro k
        induction k with
        | zero =>
          intro fd hfd; rw [pow_zero, MvPolynomial.coeff_one] at hfd
          split_ifs at hfd with h0
          · subst h0; simp
          · exact absurd rfl hfd
        | succ k ih =>
          intro fd hfd
          rw [pow_succ', MvPolynomial.coeff_mul] at hfd
          obtain ⟨⟨d₁, d₂⟩, hd12, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfd
          have hd_sum : d₁ + d₂ = fd := by simpa using hd12
          have h1 := left_ne_zero_of_mul hprod
          have h2 := ih d₂ (right_ne_zero_of_mul hprod)
          have h1_le : d₁ 1 ≤ p * (p + 1) := by
            simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add,
              MvPolynomial.coeff_X_pow] at h1
            by_cases ha : Finsupp.single (0 : Fin 2) (p ^ 2) = d₁
            · subst ha; simp
            · by_cases hb : Finsupp.single (1 : Fin 2) (p * (p + 1)) = d₁
              · subst hb; simp
              · rw [if_neg ha, if_neg hb, add_zero, neg_zero] at h1; exact absurd rfl h1
          have hfd1 : fd 1 = d₁ 1 + d₂ 1 := by rw [← hd_sum]; rfl
          rw [hfd1]; nlinarith
      -- Also for `e 2 = kmax`, the ONLY term in `(-gHomPoly)^kmax` with `T`-degree `= kmax * p * (p + 1)`
      -- is `(-1)^kmax * T^(kmax * p * (p + 1))`!
      have htop_coeff : ∀ k : ℕ, ∀ fd : Fin 2 →₀ ℕ,
          fd 1 = k * (p * (p + 1)) →
          ((-gHomPoly K p) ^ k).coeff fd =
            if fd = Finsupp.single 1 (k * (p * (p + 1))) then (-1 : K) ^ k else 0 := by
        intro k
        induction k with
        | zero =>
          intro fd _
          simp only [pow_zero, zero_mul, Finsupp.single_zero, MvPolynomial.coeff_one]
          by_cases h1 : (0 : Fin 2 →₀ ℕ) = fd
          · subst h1; simp
          · rw [if_neg h1, if_neg (Ne.symm h1)]
        | succ k ih =>
          intro fd hfd1
          rw [pow_succ', MvPolynomial.coeff_mul]
          have hsub_le : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≤ fd := by
            intro i; fin_cases i
            · simp
            · simp [hfd1]; nlinarith
          have hmem_anti : (Finsupp.single (1 : Fin 2) (p * (p + 1)),
              fd - Finsupp.single 1 (p * (p + 1))) ∈ Finset.HasAntidiagonal.antidiagonal fd :=
            Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_tsub_cancel_of_le hsub_le)
          rw [Finset.sum_eq_single (Finsupp.single (1 : Fin 2) (p * (p + 1)), fd - Finsupp.single 1 (p * (p + 1)))]
          · have h1val : (-gHomPoly K p).coeff (Finsupp.single 1 (p * (p + 1))) = -1 := by
              simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow]
              have hne01 : Finsupp.single (0 : Fin 2) (p ^ 2) ≠ Finsupp.single 1 (p * (p + 1)) := by
                intro h; have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h; simp at this; nlinarith
              rw [if_neg hne01]; simp
            have h2_1 : (fd - Finsupp.single (1 : Fin 2) (p * (p + 1))) 1 = k * (p * (p + 1)) := by
              simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, hfd1]
              have : (k + 1) * (p * (p + 1)) = k * (p * (p + 1)) + p * (p + 1) := by ring
              omega
            rw [h1val, ih _ h2_1]
            by_cases hfd_eq : fd = Finsupp.single 1 ((k + 1) * (p * (p + 1)))
            · subst hfd_eq
              have hsub_eq : Finsupp.single (1 : Fin 2) ((k + 1) * (p * (p + 1))) -
                  Finsupp.single 1 (p * (p + 1)) = Finsupp.single 1 (k * (p * (p + 1))) := by
                ext i; fin_cases i
                · simp
                · simp; ring_nf; omega
              rw [if_pos hsub_eq, if_pos rfl, pow_succ']
            · rw [if_neg hfd_eq, if_neg]
              · simp
              · intro hsub_eq; apply hfd_eq
                have hadd := congrArg (fun u => Finsupp.single (1 : Fin 2) (p * (p + 1)) + u) hsub_eq
                rw [add_tsub_cancel_of_le hsub_le] at hadd
                rw [hadd]; ext i; fin_cases i
                · simp
                · simp; ring
          · rintro ⟨d₁, d₂⟩ hd12 hne_pair
            have hd_sum : d₁ + d₂ = fd := by simpa using hd12
            by_cases h1 : (-gHomPoly K p).coeff d₁ = 0
            · rw [h1, zero_mul]
            · by_cases h2 : ((-gHomPoly K p) ^ k).coeff d₂ = 0
              · rw [h2, mul_zero]
              · exfalso
                have hd1_cases : d₁ = Finsupp.single 0 (p ^ 2) ∨ d₁ = Finsupp.single 1 (p * (p + 1)) := by
                  simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add,
                    MvPolynomial.coeff_X_pow] at h1
                  by_cases ha : Finsupp.single (0 : Fin 2) (p ^ 2) = d₁
                  · exact Or.inl ha.symm
                  · by_cases hb : Finsupp.single (1 : Fin 2) (p * (p + 1)) = d₁
                    · exact Or.inr hb.symm
                    · rw [if_neg ha, if_neg hb, add_zero, neg_zero] at h1; exact absurd rfl h1
                have h2_le : d₂ 1 ≤ k * (p * (p + 1)) := by
                  clear ih h1 hfd1 hd1_cases hd_sum hd12 hne_pair hsub_le hmem_anti
                  induction k generalizing d₂ with
                  | zero =>
                    rw [pow_zero, MvPolynomial.coeff_one] at h2
                    by_cases h0 : (0 : Fin 2 →₀ ℕ) = d₂
                    · subst h0; simp
                    · rw [if_neg h0] at h2; exact absurd rfl h2
                  | succ m ihm =>
                    rw [pow_succ', MvPolynomial.coeff_mul] at h2
                    obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
                    have has : a₁ + a₂ = d₂ := by simpa using ha12
                    have ha2 := ihm a₂ (right_ne_zero_of_mul hpr)
                    have ha1 : a₁ 1 ≤ p * (p + 1) := by
                      have hne1 := left_ne_zero_of_mul hpr
                      simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add,
                        MvPolynomial.coeff_X_pow] at hne1
                      by_cases ha : Finsupp.single (0 : Fin 2) (p ^ 2) = a₁
                      · subst ha; simp
                      · by_cases hb : Finsupp.single (1 : Fin 2) (p * (p + 1)) = a₁
                        · subst hb; simp
                        · rw [if_neg ha, if_neg hb, add_zero, neg_zero] at hne1; exact absurd rfl hne1
                    have : d₂ 1 = a₁ 1 + a₂ 1 := by rw [← has]; rfl
                    rw [this]; nlinarith
                have hd_sum1 : d₁ 1 + d₂ 1 = fd 1 := by rw [← hd_sum]; rfl
                rcases hd1_cases with rfl | rfl
                · simp at hd_sum1; nlinarith
                · apply hne_pair; exact Prod.ext rfl (by rw [← hd_sum, add_tsub_cancel_left])
          · intro hnm; exact absurd hmem_anti hnm
      -- Now evaluate `(C (Q.coeff e) * Z^(e 1) * (-gHomPoly)^(e 2)).coeff d₀`
      have hmul_c : (MvPolynomial.C (Q.coeff e) * MvPolynomial.X 0 ^ e 1 * (-gHomPoly K p) ^ e 2).coeff d₀ =
          if e 1 ≤ d₀ 0 then
            Q.coeff e * ((-gHomPoly K p) ^ e 2).coeff (d₀ - Finsupp.single 0 (e 1))
          else 0 := by
        rw [mul_assoc, MvPolynomial.coeff_C_mul]
        have hXpow : (MvPolynomial.X (0 : Fin 2) ^ e 1 : P2 K) = MvPolynomial.monomial (Finsupp.single 0 (e 1)) 1 := by
          rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; simp
        rw [hXpow, MvPolynomial.coeff_monomial_mul']
        by_cases hle : Finsupp.single (0 : Fin 2) (e 1) ≤ d₀
        · have hle0 : e 1 ≤ d₀ 0 := by simpa using hle 0
          rw [if_pos hle, if_pos hle0, one_mul]
        · have hnot0 : ¬ e 1 ≤ d₀ 0 := by
            intro h; apply hle; intro i; fin_cases i <;> simp [h]
          rw [if_neg hle, if_neg hnot0, mul_zero]
      rw [hmul_c]
      by_cases heq : e = e₀
      · subst heq
        have hd00 : d₀ 0 = e 1 := by simp [d₀]
        have hsub : d₀ - Finsupp.single 0 (e 1) = Finsupp.single 1 (kmax * (p * (p + 1))) := by
          ext i; fin_cases i <;> simp [d₀]
        rw [if_pos rfl, if_pos (by omega), hsub, he₀_2, htop_coeff kmax _ (by simp), if_pos rfl, mul_comm]
      · rw [if_neg heq]
        split_ifs with hle
        · by_cases he2_eq : e 2 = kmax
          · rw [he2_eq]
            have hsub1 : (d₀ - Finsupp.single (0 : Fin 2) (e 1)) 1 = kmax * (p * (p + 1)) := by simp [d₀]
            rw [htop_coeff kmax _ hsub1, if_neg]
            · simp
            · intro hsub_eq
              apply heq
              have he1_eq : e 1 = e₀ 1 := by
                have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hsub_eq
                simp [d₀] at this hle; omega
              have he0_eq : e 0 = e₀ 0 := by
                simp only [m₀] at hm; omega
              ext i; fin_cases i
              · exact he0_eq
              · exact he1_eq
              · exact he2_eq.trans he₀_2.symm
          · have hlt : e 2 < kmax := by omega
            have hcoeff0 : ((-gHomPoly K p) ^ e 2).coeff (d₀ - Finsupp.single 0 (e 1)) = 0 := by
              by_contra hne
              have hle1 := hTdeg_le _ hne
              have hsub1 : (d₀ - Finsupp.single (0 : Fin 2) (e 1)) 1 = kmax * (p * (p + 1)) := by simp [d₀]
              rw [hsub1] at hle1
              have hpp : 0 < p * (p + 1) := by positivity
              nlinarith
            rw [hcoeff0, mul_zero]
        · rfl
    · rw [if_neg hm, MvPolynomial.coeff_zero, if_neg]
      intro heq; subst heq; exact hm (by simp [m₀, he₀_2, kmax])
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single e₀] at hval0
  · rw [if_pos rfl] at hval0
    exact (mul_ne_zero (pow_ne_zero kmax (neg_ne_zero.mpr one_ne_zero))
      (MvPolynomial.mem_support_iff.mp he₀_mem)) hval0
  · intro e _ hene; rw [if_neg hene]
  · intro hnm; exact absurd he₀_mem hnm

set_option maxHeartbeats 400000 in
/-- For any non-trivial `ExpMap` `φ` on `B_K = HomRing K p`, `φ.invSubalg ⊈ K[bY]`. -/
lemma invSubalg_not_subset_adjoin_bY [CharP K p] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (HomRing K p)) (hnt : φ.IsNontrivial) :
    ∃ a : HomRing K p, a ∈ φ.invSubalg ∧ a ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  have : CharP (HomRing K p) p :=
    charP_of_injective_algebraMap (algebraMap K (HomRing K p)).injective p
  have : Fact (Nat.Prime (ringChar (HomRing K p))) := by
    rw [ringChar.eq (HomRing K p) p]; exact hp_prime
  -- First, `Polynomial.aeval (bY K p) : Polynomial K →ₐ[K] HomRing K p` is injective (from `bX_bZ_bY_algIndep`)
  have haeval_bY_inj : Function.Injective (Polynomial.aeval (bY K p) : Polynomial K →ₐ[K] HomRing K p) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    let Q : MvPolynomial (Fin 3) K := q.aeval (MvPolynomial.X (2 : Fin 3))
    have hQ_eval : MvPolynomial.aeval ![bX K p, bZ K p, bY K p] Q = 0 := by
      dsimp only [Q]
      rw [← Polynomial.aeval_algHom_apply]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val]
      exact hq
    have hQ0 : Q = 0 := bX_bZ_bY_algIndep K p hp Q hQ_eval
    ext n
    have hc := congrArg (fun r : MvPolynomial (Fin 3) K => r.coeff (Finsupp.single 2 n)) hQ0
    rw [MvPolynomial.coeff_zero] at hc
    have hcoeff : ∀ q0 : Polynomial K,
        (q0.aeval (MvPolynomial.X (2 : Fin 3))).coeff (Finsupp.single 2 n) = q0.coeff n := by
      intro q0
      induction q0 using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ => simp [map_add, h₁, h₂]
      | monomial k c =>
        rw [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
        have hmon : (algebraMap K (MvPolynomial (Fin 3) K)) c * (MvPolynomial.X (2 : Fin 3)) ^ k =
            MvPolynomial.monomial (Finsupp.single 2 k) c := by
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            Fin.prod_univ_three]; simp
        rw [hmon, MvPolynomial.coeff_monomial]
        by_cases hkn : k = n
        · subst hkn; simp
        · rw [if_neg hkn, if_neg]
          intro heq; apply hkn
          have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq; simp at this; exact this
    rw [hcoeff q] at hc; exact hc
  by_contra hsub
  push Not at hsub
  have hsub_poly : ∀ a : HomRing K p, a ∈ φ.invSubalg → ∃ q : Polynomial K, a = Polynomial.aeval (bY K p) q := by
    intro a ha
    have hmem := hsub a ha
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    exact hmem.imp fun q hq => hq.symm
  choose polyOf hpolyOf using fun u : φ.invSubalg => hsub_poly u.1 u.2
  have hpolyOf_hom : ∀ u v : φ.invSubalg,
      polyOf (u + v) = polyOf u + polyOf v ∧ polyOf (u * v) = polyOf u * polyOf v := by
    intro u v
    constructor
    · apply haeval_bY_inj; rw [map_add, ← hpolyOf u, ← hpolyOf v, ← hpolyOf (u + v)]; rfl
    · apply haeval_bY_inj; rw [map_mul, ← hpolyOf u, ← hpolyOf v, ← hpolyOf (u * v)]; rfl
  let polyHom : φ.invSubalg →+* Polynomial K :=
    { toFun := polyOf
      map_one' := haeval_bY_inj (by rw [map_one, ← hpolyOf 1]; rfl)
      map_mul' := fun u v => (hpolyOf_hom u v).2
      map_zero' := haeval_bY_inj (by rw [map_zero, ← hpolyOf 0]; rfl)
      map_add' := fun u v => (hpolyOf_hom u v).1 }
  obtain ⟨s, c, hc_ne, _, hslice⟩ := φ.exists_local_slice hnt
  let M : Submonoid (HomRing K p) :=
    (nonZeroDivisors (Polynomial K)).map (Polynomial.aeval (bY K p)).toRingHom.toMonoidHom
  let D := Localization M
  let iR : Polynomial K →+* D := (algebraMap (HomRing K p) D).comp (Polynomial.aeval (bY K p)).toRingHom
  have hiR_unit : ∀ y : nonZeroDivisors (Polynomial K), IsUnit (iR y) := fun y =>
    IsLocalization.map_units D (⟨Polynomial.aeval (bY K p) y.1, y.1, y.2, rfl⟩ : M)
  let iL : FractionRing (Polynomial K) →+* D := IsLocalization.lift hiR_unit
  letI : Algebra (FractionRing (Polynomial K)) D := RingHom.toAlgebra iL
  let t : D := algebraMap (HomRing K p) D s
  have hpolyOf_c_ne : polyOf c ≠ 0 := fun h => hc_ne (by rw [hpolyOf c, h, map_zero])
  have hspan : ∀ a : D, ∃ f : D → Polynomial (FractionRing (Polynomial K)),
      a = ∑ b ∈ ({(1 : D)} : Finset D), Polynomial.aeval t (f b) * b := by
    intro a
    induction a using Localization.induction_on with
    | H p_pair =>
      obtain ⟨r, m⟩ := p_pair
      obtain ⟨qm, hqm_nzd, hqm_eq⟩ := m.2
      obtain ⟨N, P, hNP⟩ := hslice r
      let P_L : Polynomial (FractionRing (Polynomial K)) :=
        P.map ((algebraMap (Polynomial K) (FractionRing (Polynomial K))).comp polyHom)
      let denom_p : Polynomial K := polyOf c ^ N * qm
      have hdenom_ne : denom_p ≠ 0 :=
        mul_ne_zero (pow_ne_zero N hpolyOf_c_ne) (nonZeroDivisors.ne_zero hqm_nzd)
      let denom_L : FractionRing (Polynomial K) :=
        algebraMap (Polynomial K) (FractionRing (Polynomial K)) denom_p
      have hdenom_L_ne : denom_L ≠ 0 := by
        dsimp only [denom_L]
        rw [← map_zero (algebraMap (Polynomial K) (FractionRing (Polynomial K)))]
        exact (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))).ne hdenom_ne
      refine ⟨fun _ => Polynomial.C denom_L⁻¹ * P_L, ?_⟩
      simp only [Finset.sum_singleton, mul_one, map_mul, Polynomial.aeval_C]
      have hdenom_eq : algebraMap (FractionRing (Polynomial K)) D denom_L =
          algebraMap (HomRing K p) D ((c : HomRing K p) ^ N * m.1) := by
        change iL (algebraMap (Polynomial K) (FractionRing (Polynomial K)) denom_p) = _
        rw [IsLocalization.lift_eq]
        simp only [iR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, denom_p,
          map_mul, map_pow, ← hpolyOf c]
        have : Polynomial.aeval (bY K p) qm = m.1 := hqm_eq
        rw [this]
      have hP_eval : Polynomial.aeval t P_L = algebraMap (HomRing K p) D (Polynomial.aeval s P) := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
          Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, map_pow]
        congr 1
        change iL (algebraMap (Polynomial K) (FractionRing (Polynomial K)) (polyOf (P.coeff k))) = _
        rw [IsLocalization.lift_eq]
        simp only [iR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hpolyOf (P.coeff k)]
        rfl
      have hmul : algebraMap (FractionRing (Polynomial K)) D denom_L *
          Localization.mk r m = Polynomial.aeval t P_L := by
        rw [hdenom_eq, hP_eval, ← hNP, map_mul, mul_assoc]
        have hm_cancel : algebraMap (HomRing K p) D m.1 * Localization.mk r m =
            algebraMap (HomRing K p) D r := by
          rw [Localization.mk_eq_mk', IsLocalization.mk'_spec' D r m]
        rw [hm_cancel, ← map_mul]
      have hinv : algebraMap (FractionRing (Polynomial K)) D denom_L⁻¹ *
          algebraMap (FractionRing (Polynomial K)) D denom_L = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hdenom_L_ne, map_one]
      calc Localization.mk r m
          = 1 * Localization.mk r m := (one_mul _).symm
        _ = algebraMap (FractionRing (Polynomial K)) D denom_L⁻¹ *
              (algebraMap (FractionRing (Polynomial K)) D denom_L *
                Localization.mk r m) := by
            rw [← mul_assoc, hinv]
        _ = algebraMap (FractionRing (Polynomial K)) D denom_L⁻¹ * Polynomial.aeval t P_L := by rw [hmul]
  obtain ⟨P, hP_ne, hP_eval⟩ := exists_poly_rel_two_of_fg_over_poly t {(1 : D)} hspan
    (algebraMap (HomRing K p) D (bX K p)) (algebraMap (HomRing K p) D (bZ K p))
  -- Clear denominators of `P ∈ MvPolynomial (Fin 2) (FractionRing (Polynomial K))`
  have hclear : ∃ (d_y : Polynomial K) (P_R : MvPolynomial (Fin 2) (Polynomial K)),
      d_y ≠ 0 ∧ P_R ≠ 0 ∧
      P_R.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))) =
        MvPolynomial.C (algebraMap (Polynomial K) (FractionRing (Polynomial K)) d_y) * P := by
    choose pair hpair using fun e : Fin 2 →₀ ℕ =>
      IsLocalization.surj (nonZeroDivisors (Polynomial K)) (P.coeff e)
    let num := fun e => (pair e).1
    let den := fun e => (pair e).2
    have hden_eq : ∀ e, P.coeff e * algebraMap (Polynomial K) (FractionRing (Polynomial K)) (den e).1 =
        algebraMap (Polynomial K) (FractionRing (Polynomial K)) (num e) := fun e => hpair e
    let d_y : Polynomial K := ∏ e ∈ P.support, (den e).1
    have hd_ne : d_y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => nonZeroDivisors.ne_zero (den e).2
    let P_R : MvPolynomial (Fin 2) (Polynomial K) := ∑ e ∈ P.support,
      MvPolynomial.monomial e (num e * ∏ e' ∈ P.support.erase e, (den e').1)
    have hmap : P_R.map (algebraMap (Polynomial K) (FractionRing (Polynomial K))) =
        MvPolynomial.C (algebraMap (Polynomial K) (FractionRing (Polynomial K)) d_y) * P := by
      ext e
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
      simp only [P_R, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      by_cases he : e ∈ P.support
      · rw [Finset.sum_eq_single e]
        · rw [if_pos rfl, map_mul, map_prod]
          have hd_split : d_y = (den e).1 * ∏ e' ∈ P.support.erase e, (den e').1 :=
            (Finset.mul_prod_erase P.support (fun e' => (den e').1) he).symm
          rw [hd_split, map_mul, map_prod,
            mul_comm (algebraMap (Polynomial K) (FractionRing (Polynomial K)) (den e).1), mul_assoc,
            mul_comm (algebraMap (Polynomial K) (FractionRing (Polynomial K)) (den e).1), hden_eq e, mul_comm]
        · intro e' _ hne; rw [if_neg hne]
        · intro hnm; exact absurd he hnm
      · rw [Finset.sum_eq_zero (fun e' he' => if_neg (fun h : e' = e => he (h ▸ he'))), map_zero,
          MvPolynomial.notMem_support_iff.mp he, mul_zero]
    have hPR_ne : P_R ≠ 0 := by
      intro h0; rw [h0, map_zero] at hmap
      have hdL : MvPolynomial.C (algebraMap (Polynomial K) (FractionRing (Polynomial K)) d_y) ≠
          (0 : MvPolynomial (Fin 2) (FractionRing (Polynomial K))) := by
        intro h
        have h1 := MvPolynomial.C_eq_zero.mp h
        rw [← map_zero (algebraMap (Polynomial K) (FractionRing (Polynomial K)))] at h1
        exact hd_ne (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)) h1)
      exact mul_ne_zero hdL hP_ne hmap.symm
    exact ⟨d_y, P_R, hd_ne, hPR_ne, hmap⟩
  obtain ⟨d_y, P_R, _, hPR_ne, hPR_map⟩ := hclear
  have heval_D : algebraMap (HomRing K p) D
      (MvPolynomial.aeval ![bX K p, bZ K p] (P_R.map (Polynomial.aeval (bY K p)).toRingHom)) = 0 := by
    have h1 : ∀ R0 : MvPolynomial (Fin 2) (Polynomial K),
        algebraMap (HomRing K p) D
          (MvPolynomial.aeval ![bX K p, bZ K p] (R0.map (Polynomial.aeval (bY K p)).toRingHom)) =
        MvPolynomial.aeval ![algebraMap (HomRing K p) D (bX K p), algebraMap (HomRing K p) D (bZ K p)]
          (R0.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))) := by
      intro R0
      induction R0 using MvPolynomial.induction_on with
      | C r =>
        simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
        change iR r = iL (algebraMap (Polynomial K) (FractionRing (Polynomial K)) r)
        exact (IsLocalization.lift_eq hiR_unit r).symm
      | add p₁ p₂ h₁ h₂ => simp only [map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
      | mul_X p₁ j h₁ =>
        simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X] at h₁ ⊢
        rw [h₁]; fin_cases j <;> rfl
    rw [h1 P_R, hPR_map, map_mul, hP_eval, mul_zero]
  have hinj_D : Function.Injective (algebraMap (HomRing K p) D) :=
    IsLocalization.injective (M := M) D (by
      intro x hx
      obtain ⟨q, hq_nzd, rfl⟩ := hx
      exact mem_nonZeroDivisors_of_ne_zero (fun h0 =>
        nonZeroDivisors.ne_zero hq_nzd (haeval_bY_inj (by rw [map_zero]; exact h0))))
  have heval_B : MvPolynomial.aeval ![bX K p, bZ K p] (P_R.map (Polynomial.aeval (bY K p)).toRingHom) = 0 :=
    hinj_D (by rw [heval_D, map_zero])
  let Q : MvPolynomial (Fin 3) K :=
    ∑ e ∈ P_R.support,
      MvPolynomial.monomial (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)) 1 *
      (P_R.coeff e).aeval (MvPolynomial.X (2 : Fin 3))
  have hQ_eval : MvPolynomial.aeval ![bX K p, bZ K p, bY K p] Q = 0 := by
    rw [← heval_B]
    conv_rhs => rw [MvPolynomial.as_sum P_R, map_sum, map_sum]
    simp only [Q, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, map_mul, MvPolynomial.aeval_monomial]
    have hq_eval : MvPolynomial.aeval ![bX K p, bZ K p, bY K p]
        ((P_R.coeff e).aeval (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K)) =
        Polynomial.aeval (bY K p) (P_R.coeff e) := by
      rw [← Polynomial.aeval_algHom_apply]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val]
    rw [hq_eval, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Fin.prod_univ_two]
    simp [mul_comm]
  have hQ0 : Q = 0 := bX_bZ_bY_algIndep K p hp Q hQ_eval
  obtain ⟨e₀, he₀⟩ := MvPolynomial.support_nonempty.mpr hPR_ne
  obtain ⟨k₀, hk₀⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp he₀)
  let d₀ : Fin 3 →₀ ℕ := Finsupp.single 0 (e₀ 0) + Finsupp.single 1 (e₀ 1) + Finsupp.single 2 k₀
  have hc0 := congrArg (fun r : MvPolynomial (Fin 3) K => r.coeff d₀) hQ0
  rw [MvPolynomial.coeff_zero] at hc0
  simp only [Q, MvPolynomial.coeff_sum] at hc0
  have hq_coeff_fn : ∀ (q : Polynomial K) (e : Fin 2 →₀ ℕ),
      (MvPolynomial.monomial (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)) (1 : K) *
        q.aeval (MvPolynomial.X (2 : Fin 3))).coeff d₀ =
      if e = e₀ then q.coeff k₀ else 0 := by
    intro q e
    rw [MvPolynomial.coeff_monomial_mul']
    have hsub_iff : Finsupp.single (0 : Fin 3) (e 0) + Finsupp.single 1 (e 1) ≤ d₀ ↔ e 0 ≤ e₀ 0 ∧ e 1 ≤ e₀ 1 := by
      constructor
      · intro h; exact ⟨by simpa [d₀] using h 0, by simpa [d₀] using h 1⟩
      · rintro ⟨h0, h1⟩ i; fin_cases i <;> simp [d₀, h0, h1]
    have hq_aeval : ∀ m : Fin 3 →₀ ℕ,
        (q.aeval (MvPolynomial.X (2 : Fin 3))).coeff m =
        if m 0 = 0 ∧ m 1 = 0 then q.coeff (m 2) else 0 := by
      intro m
      induction q using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ => simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, h₁, h₂]; split_ifs <;> simp
      | monomial n c =>
        rw [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
        have hmon : (algebraMap K (MvPolynomial (Fin 3) K)) c * (MvPolynomial.X (2 : Fin 3)) ^ n =
            MvPolynomial.monomial (Finsupp.single 2 n) c := by
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
            Fin.prod_univ_three]; simp
        rw [hmon, MvPolynomial.coeff_monomial]
        by_cases hm : m 0 = 0 ∧ m 1 = 0
        · rw [if_pos hm]
          by_cases hn : n = m 2
          · subst hn
            have heqm : Finsupp.single (2 : Fin 3) (m 2) = m := by
              ext i; fin_cases i <;> simp [hm.1, hm.2]
            rw [if_pos heqm, if_pos rfl]
          · rw [if_neg hn, if_neg]
            intro heqm; apply hn
            have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heqm; simp at this; exact this
        · rw [if_neg hm, if_neg]
          intro heqm; apply hm
          have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) heqm
          have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) heqm
          simp at h0 h1; exact ⟨h0.symm, h1.symm⟩
    by_cases heq : e = e₀
    · subst heq
      rw [if_pos (hsub_iff.mpr ⟨le_refl _, le_refl _⟩), if_pos rfl, one_mul, hq_aeval]
      simp [d₀]
    · rw [if_neg heq]
      split_ifs with hle
      · rw [one_mul, hq_aeval, if_neg]
        rintro ⟨h0, h1⟩
        simp [d₀] at h0 h1
        have hle' := hsub_iff.mp hle
        apply heq; ext i; fin_cases i
        · change e 0 = e₀ 0; omega
        · change e 1 = e₀ 1; omega
      · rfl
  rw [Finset.sum_congr rfl (fun e _ => hq_coeff_fn (P_R.coeff e) e),
    Finset.sum_eq_single e₀] at hc0
  · rw [if_pos rfl] at hc0
    exact (Polynomial.mem_support_iff.mp hk₀) hc0
  · intro e _ hne; rw [if_neg hne]
  · intro hnm; exact absurd he₀ hnm

end ExtractInvariantFactor

/- ## Section 7b2b: Extracting the invariant factor, `ExpMap.baseChange`, and irreducibility -/

section FactorAndBaseChange

variable (K : Type*) [Field K] (p : ℕ)

/-- Helper: `C f ∈ HomSubalg K p` for every `f : P2 K`. -/
def bC (f : P2 K) : HomRing K p :=
  ⟨LaurentPolynomial.C f, by
    change LaurentPolynomial.C f ∈ SubalgOfPoly K (gHomPoly K p)
    rw [mem_subalgOfPoly_iff]
    intro m hm
    have h1 : LaurentPolynomial.C f = singleT K 0 f := by
      rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
    rw [h1, coeff_singleT, if_neg (by omega)]
    exact dvd_zero _⟩

/-- Every element of `K[bY]` has `grX.topComp` equal to `c * bY^k` for some `c ∈ K` and `k : ℕ`,
    and if it is non-zero its `grX.topDeg` is `2 * k ≥ 0`. -/
lemma grX_topComp_mem_adjoin_bY_iff (hp : 1 < p) (a : HomRing K p) (ha : (a : Ambient K) ≠ 0)
    (htop : (⟨(grX K).topComp (a : Ambient K), by
      rw [ZGrading.topComp, dif_neg ha]
      change _ ∈ SubalgOfPoly K (gHomPoly K p)
      rw [mem_subalgOfPoly_iff]; intro m hm
      change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
        (singleT K (-((grX K).topDeg (a : Ambient K) ha))
          ((a : Ambient K).coeff (-((grX K).topDeg (a : Ambient K) ha)))).coeff m
      rw [coeff_singleT]; split_ifs with hmeq
      · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 _ hm
      · exact dvd_zero _⟩ : HomRing K p) ∈ Algebra.adjoin K ({bY K p} : Set (HomRing K p))) :
    ∃ (c : K) (k : ℕ), c ≠ 0 ∧ (grX K).topDeg (a : Ambient K) ha = 2 * (k : ℤ) ∧
      (grX K).topComp (a : Ambient K) = algebraMap K (Ambient K) c * (genYB K p) ^ k := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at htop
  obtain ⟨q, hq⟩ := htop
  have hval := congrArg Subtype.val hq
  dsimp only at hval
  rw [ZGrading.topComp, dif_neg ha] at hval
  let d := (grX K).topDeg (a : Ambient K) ha
  have hne_top : (grX K).proj d (a : Ambient K) ≠ 0 := (grX K).topComp_ne_zero ha |> fun h => by
    rwa [ZGrading.topComp, dif_neg ha] at h
  -- `(Polynomial.aeval (bY K p) q : Ambient K)` has coeff at `m` equal to `C (q.coeff k) * (-gHomPoly)^k` if `m = -2k` else `0`
  have hq_val : ((Polynomial.aeval (bY K p) q : HomRing K p) : Ambient K) =
      ∑ k ∈ q.support, singleT K (-2 * (k : ℤ)) (MvPolynomial.C (q.coeff k) * (-gHomPoly K p) ^ k) := by
    have hcomp : (HomSubalg K p).val.comp (Polynomial.aeval (bY K p)) = Polynomial.aeval (genYB K p) := by
      apply Polynomial.algHom_ext; simp [bY]
    rw [show ((Polynomial.aeval (bY K p) q : HomRing K p) : Ambient K) =
        Polynomial.aeval (genYB K p) q from AlgHom.congr_fun hcomp q]
    conv_lhs => rw [Polynomial.as_sum_support q, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.aeval_monomial, genYB, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
    have hC : (algebraMap K (Ambient K)) (q.coeff k) = LaurentPolynomial.C (MvPolynomial.C (q.coeff k)) := rfl
    rw [hC, show (k : ℤ) * (-2) = -2 * (k : ℤ) by ring]; ring
  -- Compare coefficients at `-d`
  have hcoeff_d : (a : Ambient K).coeff (-d) ≠ 0 := by
    intro h0; apply hne_top
    change singleT K (-d) ((a : Ambient K).coeff (-d)) = 0
    rw [h0]; ext m : 1; simp [coeff_singleT]
  have hcm := congrArg (fun r : Ambient K => r.coeff (-d)) hval
  change ((Polynomial.aeval (bY K p) q : HomRing K p) : Ambient K).coeff (-d) =
    (singleT K (-d) ((a : Ambient K).coeff (-d))).coeff (-d) at hcm
  rw [hq_val, coeff_sum_A, coeff_singleT, if_pos rfl] at hcm
  have hexk : ∃ k ∈ q.support, -2 * (k : ℤ) = -d := by
    by_contra hno; push Not at hno
    apply hcoeff_d
    rw [← hcm]
    apply Finset.sum_eq_zero; intro k hk
    rw [coeff_singleT, if_neg (hno k hk)]
  obtain ⟨k, hk_supp, hk_eq⟩ := hexk
  refine ⟨q.coeff k, k, Polynomial.mem_support_iff.mp hk_supp, by omega, ?_⟩
  rw [ZGrading.topComp, dif_neg ha]
  change singleT K (-d) ((a : Ambient K).coeff (-d)) = _
  rw [← hcm, Finset.sum_eq_single k]
  · rw [coeff_singleT, if_pos hk_eq, ← hk_eq, singleT_eq_C_mul_T, genYB, mul_pow,
      LaurentPolynomial.T_pow, map_mul, map_pow]
    have hC : (algebraMap K (Ambient K)) (q.coeff k) = LaurentPolynomial.C (MvPolynomial.C (q.coeff k)) := rfl
    rw [hC, show (k : ℤ) * (-2) = -2 * (k : ℤ) by ring]; ring
  · intro j _ hjk; rw [coeff_singleT, if_neg (by omega)]
  · intro hnm; exact absurd hk_supp hnm

/-- From a non-trivial `φ` on `B_K = HomRing K p` with `bY ∈ φ.invSubalg`, produce a non-trivial `φ₂`
    on `B_K` with `bY ∈ φ₂.invSubalg` and `bC w ∈ φ₂.invSubalg` for some
    `w ∈ {Z, T} ∪ {Z^p + μ T^(p+1) | μ ∈ Kˣ}`. -/
lemma exists_factor_inv_of_bY_inv [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (HomRing K p)) (hnt : φ.IsNontrivial) (hy : bY K p ∈ φ.invSubalg) :
    ∃ (φ₂ : ExpMap K (HomRing K p)) (w : P2 K),
      φ₂.IsNontrivial ∧ bY K p ∈ φ₂.invSubalg ∧ bC K p w ∈ φ₂.invSubalg ∧
      (w = MvPolynomial.X 0 ∨ w = MvPolynomial.X 1 ∨
        ∃ μ : K, μ ≠ 0 ∧ w = MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1)) := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  -- Step 1: Find `a ∈ φ.invSubalg \ K[bY]` whose `grX.topComp` is NOT in `K[bY]`!
  obtain ⟨a₀, ha₀_inv, ha₀_not⟩ := invSubalg_not_subset_adjoin_bY K p φ hnt
  have hex_a : ∃ (a : HomRing K p) (ha : (a : Ambient K) ≠ 0), a ∈ φ.invSubalg ∧
      (⟨(grX K).topComp (a : Ambient K), by
        rw [ZGrading.topComp, dif_neg ha]
        change _ ∈ SubalgOfPoly K (gHomPoly K p)
        rw [mem_subalgOfPoly_iff]; intro m hm
        change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
          (singleT K _ ((a : Ambient K).coeff _)).coeff m
        rw [coeff_singleT]; split_ifs with hmeq
        · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 _ hm
        · exact dvd_zero _⟩ : HomRing K p) ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) := by
    suffices ∀ n : ℕ, ∀ a : HomRing K p, a ∈ φ.invSubalg →
        a ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) →
        ∀ (ha : (a : Ambient K) ≠ 0), ((grX K).topDeg (a : Ambient K) ha).toNat ≤ n →
        ∃ (b : HomRing K p) (hb : (b : Ambient K) ≠ 0), b ∈ φ.invSubalg ∧
          (⟨(grX K).topComp (b : Ambient K), by
            rw [ZGrading.topComp, dif_neg hb]
            change _ ∈ SubalgOfPoly K (gHomPoly K p)
            rw [mem_subalgOfPoly_iff]; intro m hm
            change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
              (singleT K _ ((b : Ambient K).coeff _)).coeff m
            rw [coeff_singleT]; split_ifs with hmeq
            · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp b.2 _ hm
            · exact dvd_zero _⟩ : HomRing K p) ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) by
      have ha₀_ne : (a₀ : Ambient K) ≠ 0 := fun h0 =>
        ha₀_not (by rw [show a₀ = 0 from Subtype.ext h0]; exact (Algebra.adjoin K _).zero_mem)
      exact this ((grX K).topDeg (a₀ : Ambient K) ha₀_ne).toNat a₀ ha₀_inv ha₀_not ha₀_ne (le_refl _)
    intro n
    induction n with
    | zero =>
      intro a ha_inv ha_not ha_ne hdeg0
      by_cases htop : (⟨(grX K).topComp (a : Ambient K), by
          rw [ZGrading.topComp, dif_neg ha_ne]
          change _ ∈ SubalgOfPoly K (gHomPoly K p)
          rw [mem_subalgOfPoly_iff]; intro m hm
          change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
            (singleT K _ ((a : Ambient K).coeff _)).coeff m
          rw [coeff_singleT]; split_ifs with hmeq
          · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 _ hm
          · exact dvd_zero _⟩ : HomRing K p) ∈ Algebra.adjoin K ({bY K p} : Set (HomRing K p))
      · obtain ⟨c, k, hc_ne, hdk, htop_eq⟩ := grX_topComp_mem_adjoin_bY_iff K p hp a ha_ne htop
        have hk0 : k = 0 := by omega
        subst hk0
        let a' : HomRing K p := a - algebraMap K (HomRing K p) c
        have ha'_inv : a' ∈ φ.invSubalg := sub_mem ha_inv (φ.invSubalg.algebraMap_mem c)
        have ha'_not : a' ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) := fun h =>
          ha_not (by
            have : a = a' + algebraMap K (HomRing K p) c := by simp [a']
            rw [this]; exact add_mem h ((Algebra.adjoin K _).algebraMap_mem c))
        have ha'_ne : (a' : Ambient K) ≠ 0 := fun h0 =>
          ha'_not (by rw [show a' = 0 from Subtype.ext h0]; exact (Algebra.adjoin K _).zero_mem)
        have hdeg_lt : (grX K).topDeg (a' : Ambient K) ha'_ne < 0 := by
          have hle : (grX K).DegLe (a' : Ambient K) (-1) := by
            intro m hm
            have hsub_proj : (grX K).proj m (a' : Ambient K) =
                (grX K).proj m (a : Ambient K) - (grX K).proj m (algebraMap K (Ambient K) c) :=
              map_sub ((grX K).proj m) (a : Ambient K) (algebraMap K (Ambient K) c)
            rw [hsub_proj]
            by_cases hm0 : m = 0
            · subst hm0
              have hproj_a : (grX K).proj 0 (a : Ambient K) = algebraMap K (Ambient K) c := by
                have := htop_eq; rw [ZGrading.topComp, dif_neg ha_ne, hdk] at this
                simpa using this
              rw [hproj_a, (grX K).proj_algebraMap, if_pos rfl, sub_self]
            · have hpa : (grX K).proj m (a : Ambient K) = 0 :=
                (grX K).degLe_topDeg ha_ne m (by omega)
              rw [hpa, (grX K).proj_algebraMap, if_neg (by omega), sub_zero]
          have := (grX K).topDeg_le_of_degLe ha'_ne hle
          omega
        refine ⟨a', ha'_ne, ha'_inv, fun htop' => ?_⟩
        obtain ⟨_, k', _, hdk', _⟩ := grX_topComp_mem_adjoin_bY_iff K p hp a' ha'_ne htop'
        omega
      · exact ⟨a, ha_ne, ha_inv, htop⟩
    | succ n ih =>
      intro a ha_inv ha_not ha_ne hdeg_le
      by_cases htop : (⟨(grX K).topComp (a : Ambient K), by
          rw [ZGrading.topComp, dif_neg ha_ne]
          change _ ∈ SubalgOfPoly K (gHomPoly K p)
          rw [mem_subalgOfPoly_iff]; intro m hm
          change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
            (singleT K _ ((a : Ambient K).coeff _)).coeff m
          rw [coeff_singleT]; split_ifs with hmeq
          · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 _ hm
          · exact dvd_zero _⟩ : HomRing K p) ∈ Algebra.adjoin K ({bY K p} : Set (HomRing K p))
      · obtain ⟨c, k, _, hdk, htop_eq⟩ := grX_topComp_mem_adjoin_bY_iff K p hp a ha_ne htop
        let a' : HomRing K p := a - algebraMap K (HomRing K p) c * (bY K p) ^ k
        have ha'_inv : a' ∈ φ.invSubalg :=
          sub_mem ha_inv (mul_mem (φ.invSubalg.algebraMap_mem c) (pow_mem hy k))
        have ha'_not : a' ∉ Algebra.adjoin K ({bY K p} : Set (HomRing K p)) := fun h =>
          ha_not (by
            have : a = a' + algebraMap K (HomRing K p) c * (bY K p) ^ k := by simp [a']
            rw [this]
            exact add_mem h (mul_mem ((Algebra.adjoin K _).algebraMap_mem c)
              (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k)))
        have ha'_ne : (a' : Ambient K) ≠ 0 := fun h0 =>
          ha'_not (by rw [show a' = 0 from Subtype.ext h0]; exact (Algebra.adjoin K _).zero_mem)
        have hdeg_lt : (grX K).topDeg (a' : Ambient K) ha'_ne < 2 * (k : ℤ) := by
          have hle : (grX K).DegLe (a' : Ambient K) (2 * (k : ℤ) - 1) := by
            intro m hm
            have hsub_proj : (grX K).proj m (a' : Ambient K) =
                (grX K).proj m (a : Ambient K) -
                (grX K).proj m (algebraMap K (Ambient K) c * (genYB K p) ^ k) :=
              map_sub ((grX K).proj m) (a : Ambient K) _
            rw [hsub_proj]
            have hcy_hom : (grX K).proj (2 * (k : ℤ)) (algebraMap K (Ambient K) c * (genYB K p) ^ k) =
                algebraMap K (Ambient K) c * (genYB K p) ^ k := by
              rw [← htop_eq, ZGrading.topComp, dif_neg ha_ne, hdk, (grX K).proj_proj, if_pos rfl]
            by_cases hm_eq : m = 2 * (k : ℤ)
            · subst hm_eq
              rw [hcy_hom]
              have hpa : (grX K).proj (2 * (k : ℤ)) (a : Ambient K) =
                  algebraMap K (Ambient K) c * (genYB K p) ^ k := by
                have := htop_eq; rwa [ZGrading.topComp, dif_neg ha_ne, hdk] at this
              rw [hpa, sub_self]
            · have hpa : (grX K).proj m (a : Ambient K) = 0 :=
                (grX K).degLe_topDeg ha_ne m (by omega)
              have hpc : (grX K).proj m (algebraMap K (Ambient K) c * (genYB K p) ^ k) = 0 := by
                rw [← hcy_hom, (grX K).proj_proj, if_neg hm_eq]
              rw [hpa, hpc, sub_zero]
          have := (grX K).topDeg_le_of_degLe ha'_ne hle
          omega
        by_cases hk0 : k = 0
        · subst hk0
          refine ⟨a', ha'_ne, ha'_inv, fun htop' => ?_⟩
          obtain ⟨_, k', _, hdk', _⟩ := grX_topComp_mem_adjoin_bY_iff K p hp a' ha'_ne htop'
          omega
        · exact ih a' ha'_inv ha'_not ha'_ne (by omega)
      · exact ⟨a, ha_ne, ha_inv, htop⟩
  obtain ⟨a, ha_ne, ha_inv, ha_top_not⟩ := hex_a
  -- Step 2: Homogenize `φ` wrt `grX` to get `φ₁` with `bY ∈ φ₁.invSubalg` and `h₁ = grX.topComp a ∈ φ₁.invSubalg \ K[bY]`!
  obtain ⟨φ₁, hnt₁, hinv₁⟩ := homogenize_subalgOfPoly_grX K (gHomPoly K p) (gHomPoly_ne_zero K p hp) φ hnt
  change ExpMap K (HomRing K p) at φ₁
  have hy₁ : bY K p ∈ φ₁.invSubalg := by
    have h := hinv₁ (bY K p) hy
    have htopY : (grX K).topComp (genYB K p) = genYB K p := by
      have hne : genYB K p ≠ 0 := fun h0 => by
        have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
        rw [genYB, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl] at this
        exact gHomPoly_ne_zero K p hp (neg_eq_zero.mp this)
      have hhom : (grX K).proj 2 (genYB K p) = genYB K p := by
        change singleT K (-2) ((genYB K p).coeff (-2)) = genYB K p
        rw [genYB, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl]
      rw [ZGrading.topComp, dif_neg hne]
      have hdeg : (grX K).topDeg (genYB K p) hne = 2 := by
        apply le_antisymm
        · exact (grX K).topDeg_le_of_degLe hne (fun m hm => by rw [← hhom, (grX K).proj_proj, if_neg (by omega)])
        · apply Finset.le_max'; rw [(grX K).mem_supp, hhom]; exact hne
      rw [hdeg, hhom]
    have heq : (bY K p : HomRing K p) = ⟨(grX K).topComp (genYB K p), by rw [htopY]; exact (bY K p).2⟩ :=
      Subtype.ext htopY.symm
    rw [heq]; exact h
  let h₁ : HomRing K p := ⟨(grX K).topComp (a : Ambient K), by
    rw [ZGrading.topComp, dif_neg ha_ne]
    change _ ∈ SubalgOfPoly K (gHomPoly K p)
    rw [mem_subalgOfPoly_iff]; intro m hm
    change (-gHomPoly K p) ^ (((-m + 1) / 2).toNat) ∣
      (singleT K _ ((a : Ambient K).coeff _)).coeff m
    rw [coeff_singleT]; split_ifs with hmeq
    · subst hmeq; exact (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 _ hm
    · exact dvd_zero _⟩
  have hh₁_inv : h₁ ∈ φ₁.invSubalg := hinv₁ a ha_inv
  -- Step 3: Extract a non-constant `h ∈ P2 K` with `bC K p h ∈ φ₁.invSubalg`!
  have hex_h : ∃ h : P2 K, (∀ c : K, h ≠ MvPolynomial.C c) ∧ bC K p h ∈ φ₁.invSubalg := by
    let m : ℤ := -((grX K).topDeg (a : Ambient K) ha_ne)
    let f : P2 K := (a : Ambient K).coeff m
    have hh₁_eq : (h₁ : Ambient K) = singleT K m f := by
      change (grX K).topComp (a : Ambient K) = _
      rw [ZGrading.topComp, dif_neg ha_ne]; rfl
    have hf_ne : f ≠ 0 := by
      intro h0
      have htop0 : (h₁ : Ambient K) = 0 := by rw [hh₁_eq, h0]; ext k : 1; simp [coeff_singleT]
      exact (grX K).topComp_ne_zero ha_ne htop0
    have hX_imp : bX K p ∈ φ₁.invSubalg →
        ∃ h : P2 K, (∀ c : K, h ≠ MvPolynomial.C c) ∧ bC K p h ∈ φ₁.invSubalg := by
      intro hx₁
      refine ⟨gHomPoly K p, ?_, ?_⟩
      · intro c hc
        have h0 := congrArg (fun r : P2 K => r.coeff (Finsupp.single 0 (p ^ 2))) hc
        simp only [gHomPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C] at h0
        have hne1 : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ Finsupp.single 0 (p ^ 2) := by
          intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; nlinarith
        have hne0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 (p ^ 2) := by
          intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; nlinarith
        rw [if_neg hne1, if_neg hne0] at h0; simp at h0
      · have hrel : bC K p (gHomPoly K p) = -(bX K p ^ 2 * bY K p) := by
          apply Subtype.ext
          change LaurentPolynomial.C (gHomPoly K p) = -(genX K ^ 2 * genYB K p)
          rw [genX, genYB, LaurentPolynomial.T_pow]
          calc LaurentPolynomial.C (gHomPoly K p)
              = -(LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T 0) := by
                rw [LaurentPolynomial.T_zero, mul_one, map_neg, neg_neg]
            _ = -(LaurentPolynomial.C (-gHomPoly K p) * (LaurentPolynomial.T (2 * 1) * LaurentPolynomial.T (-2))) := by
                rw [← LaurentPolynomial.T_add]; norm_num
            _ = -(LaurentPolynomial.T (↑(2 : ℕ) * 1) * (LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2))) := by
                push_cast; ring
        rw [hrel]; exact neg_mem (mul_mem (pow_mem hx₁ 2) hy₁)
    by_cases hm : m < 0
    · obtain ⟨g, hg⟩ := (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp a.2 m hm
      let j : ℕ := ((-m + 1) / 2).toNat
      let i : ℕ := (m + 2 * (j : ℤ)).toNat
      have hij : (i : ℤ) + (-2) * (j : ℤ) = m := by omega
      have hfac : h₁ = bC K p g * bX K p ^ i * bY K p ^ j := by
        apply Subtype.ext
        rw [hh₁_eq, singleT_eq_C_mul_T]
        have hg' : f = (-gHomPoly K p) ^ j * g := hg
        change LaurentPolynomial.C f * LaurentPolynomial.T m =
          LaurentPolynomial.C g * genX K ^ i * genYB K p ^ j
        rw [hg', map_mul, map_pow, genX, genYB, mul_pow, LaurentPolynomial.T_pow, LaurentPolynomial.T_pow]
        have hT : (LaurentPolynomial.T m : Ambient K) =
            LaurentPolynomial.T ((i : ℤ) * 1) * LaurentPolynomial.T ((j : ℤ) * (-2)) := by
          rw [← LaurentPolynomial.T_add]; congr 1; linarith
        rw [hT]; ring
      have h1_ne : h₁ ≠ 0 := fun h0 => (grX K).topComp_ne_zero ha_ne (congrArg Subtype.val h0)
      rw [hfac] at hh₁_inv h1_ne
      have hcgx_ne : bC K p g * bX K p ^ i ≠ 0 := left_ne_zero_of_mul h1_ne
      have hcgx_inv : bC K p g * bX K p ^ i ∈ φ₁.invSubalg :=
        (φ₁.mem_invSubalg_of_mul hcgx_ne (right_ne_zero_of_mul h1_ne) hh₁_inv).1
      have hcg_inv : bC K p g ∈ φ₁.invSubalg :=
        (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul hcgx_ne) (right_ne_zero_of_mul hcgx_ne) hcgx_inv).1
      have hxi_inv : bX K p ^ i ∈ φ₁.invSubalg :=
        (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul hcgx_ne) (right_ne_zero_of_mul hcgx_ne) hcgx_inv).2
      by_cases hi0 : i = 0
      · refine ⟨g, fun c hc => ?_, hcg_inv⟩
        apply ha_top_not
        change h₁ ∈ _
        rw [hfac, hi0, pow_zero, mul_one, hc]
        have hc_eq : bC K p (MvPolynomial.C c) = algebraMap K (HomRing K p) c := rfl
        rw [hc_eq]
        exact mul_mem ((Algebra.adjoin K _).algebraMap_mem c)
          (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) j)
      · have hx_inv : bX K p ∈ φ₁.invSubalg := by
          have hpow : bX K p * bX K p ^ (i - 1) = bX K p ^ i := by
            rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hi0)]
          rw [← hpow] at hxi_inv
          have hne_p : bX K p * bX K p ^ (i - 1) ≠ 0 := by rw [hpow]; exact right_ne_zero_of_mul hcgx_ne
          exact (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul hne_p) (right_ne_zero_of_mul hne_p) hxi_inv).1
        exact hX_imp hx_inv
    · have hfac : h₁ = bC K p f * bX K p ^ m.toNat := by
        apply Subtype.ext
        rw [hh₁_eq, singleT_eq_C_mul_T]
        change LaurentPolynomial.C f * LaurentPolynomial.T m = LaurentPolynomial.C f * genX K ^ m.toNat
        rw [genX, LaurentPolynomial.T_pow]; congr 2; omega
      have h1_ne : h₁ ≠ 0 := fun h0 => (grX K).topComp_ne_zero ha_ne (congrArg Subtype.val h0)
      rw [hfac] at hh₁_inv h1_ne
      have hcf_inv : bC K p f ∈ φ₁.invSubalg :=
        (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul h1_ne) (right_ne_zero_of_mul h1_ne) hh₁_inv).1
      have hxm_inv : bX K p ^ m.toNat ∈ φ₁.invSubalg :=
        (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul h1_ne) (right_ne_zero_of_mul h1_ne) hh₁_inv).2
      by_cases hm0 : m.toNat = 0
      · refine ⟨f, fun c hc => ?_, hcf_inv⟩
        apply ha_top_not
        change h₁ ∈ _
        rw [hfac, hm0, pow_zero, mul_one, hc]
        exact (Algebra.adjoin K _).algebraMap_mem c
      · have hx_inv : bX K p ∈ φ₁.invSubalg := by
          have hpow : bX K p * bX K p ^ (m.toNat - 1) = bX K p ^ m.toNat := by
            rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
          rw [← hpow] at hxm_inv
          have hne_p : bX K p * bX K p ^ (m.toNat - 1) ≠ 0 := by rw [hpow]; exact right_ne_zero_of_mul h1_ne
          exact (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul hne_p) (right_ne_zero_of_mul hne_p) hxm_inv).1
        exact hX_imp hx_inv
  obtain ⟨h, hh_nc, hh_inv⟩ := hex_h
  -- Step 4: Homogenize `φ₁` wrt `grZT` to get `φ₂` with `bY ∈ φ₂.invSubalg` and `bC hbar ∈ φ₂.invSubalg`!
  obtain ⟨φ₂, hnt₂, hinv₂⟩ := homogenize_homSubalg_grZT K p hp φ₁ hnt₁
  have hy₂ : bY K p ∈ φ₂.invSubalg := by
    have h1 := hinv₂ (bY K p) hy₁
    have htopY : (grZT K p).topComp (genYB K p) = genYB K p := by
      have hne : genYB K p ≠ 0 := fun h0 => by
        have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
        rw [genYB, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl] at this
        exact gHomPoly_ne_zero K p hp (neg_eq_zero.mp this)
      have hhom : (grZT K p).proj (p ^ 2 * (p + 1) : ℤ) (genYB K p) = genYB K p := by
        ext m : 1
        change (∑ j ∈ suppA K (genYB K p), singleT K j (projP2 K p _ ((genYB K p).coeff j))).coeff m = _
        rw [coeff_sum_projP2, genYB, ← singleT_eq_C_mul_T, coeff_singleT]
        split_ifs
        · rw [projP2_neg, gHomPoly_hom]
        · ext d; simp [coeff_projP2]
      rw [ZGrading.topComp, dif_neg hne]
      have hdeg : (grZT K p).topDeg (genYB K p) hne = (p ^ 2 * (p + 1) : ℤ) := by
        apply le_antisymm
        · exact (grZT K p).topDeg_le_of_degLe hne (fun m hm => by rw [← hhom, (grZT K p).proj_proj, if_neg (by omega)])
        · apply Finset.le_max'; rw [(grZT K p).mem_supp, hhom]; exact hne
      rw [hdeg, hhom]
    have heq : (bY K p : HomRing K p) = ⟨(grZT K p).topComp (genYB K p), by rw [htopY]; exact (bY K p).2⟩ :=
      Subtype.ext htopY.symm
    rw [heq]; exact h1
  have hh_ne : (bC K p h : Ambient K) ≠ 0 := by
    intro h0
    have := congrArg (fun r : Ambient K => r.coeff 0) h0
    change (LaurentPolynomial.C h : Ambient K).coeff 0 = 0 at this
    have h1 : (LaurentPolynomial.C h : Ambient K).coeff 0 = h := by
      change (singleT K 0 h).coeff 0 = h; simp [coeff_singleT]
    rw [h1] at this; exact hh_nc 0 (by simp [this])
  let d_h : ℤ := (grZT K p).topDeg (bC K p h : Ambient K) hh_ne
  let hbar : P2 K := projP2 K p d_h h
  have htop_h : (grZT K p).topComp (bC K p h : Ambient K) = (bC K p hbar : Ambient K) := by
    rw [ZGrading.topComp, dif_neg hh_ne]
    ext m : 1
    change (∑ j ∈ suppA K (LaurentPolynomial.C h), singleT K j (projP2 K p d_h ((LaurentPolynomial.C h).coeff j))).coeff m =
      (LaurentPolynomial.C hbar).coeff m
    rw [coeff_sum_projP2]
    have hC0 : ∀ g : P2 K, (LaurentPolynomial.C g : Ambient K) = singleT K 0 g := fun g => by
      rw [singleT_eq_C_mul_T, LaurentPolynomial.T_zero, mul_one]
    rw [hC0 h, hC0 hbar, coeff_singleT, coeff_singleT]
    split_ifs
    · rfl
    · ext d; simp [coeff_projP2]
  have hhbar_inv : bC K p hbar ∈ φ₂.invSubalg := by
    have h1 := hinv₂ (bC K p h) hh_inv
    have heq : bC K p hbar = ⟨(grZT K p).topComp (bC K p h : Ambient K), by rw [htop_h]; exact (bC K p hbar).2⟩ :=
      Subtype.ext htop_h.symm
    rw [heq]; exact h1
  have hhbar_hom : projP2 K p d_h hbar = hbar := by
    ext d; simp only [hbar, coeff_projP2]; split_ifs <;> rfl
  have hhbar_nc : ∀ c : K, hbar ≠ MvPolynomial.C c := by
    intro c hc
    have hd_pos : 0 < d_h := by
      have hex_d : ∃ d ∈ h.support, d ≠ 0 := by
        by_contra hall; push Not at hall
        apply hh_nc (h.coeff 0)
        ext d; rw [MvPolynomial.coeff_C]
        split_ifs with hd0
        · subst hd0; rfl
        · by_contra hne; exact hd0 (hall d (MvPolynomial.mem_support_iff.mpr hne)).symm
      obtain ⟨d, hd_mem, hd_ne0⟩ := hex_d
      have hwt_pos : 0 < ((p + 1) * d 0 + p * d 1 : ℤ) := by
        have h01 : 0 < d 0 ∨ 0 < d 1 := by
          by_contra hno; push Not at hno
          apply hd_ne0; ext i; fin_cases i
          · change d 0 = 0; omega
          · change d 1 = 0; omega
        rcases h01 with h0 | h1 <;> nlinarith
      have hmem_supp : ((p + 1) * d 0 + p * d 1 : ℤ) ∈ (grZT K p).supp (bC K p h : Ambient K) := by
        rw [(grZT K p).mem_supp]
        intro h0
        have hc0 := congrArg (fun r : Ambient K => (r.coeff 0).coeff d) h0
        change ((∑ j ∈ suppA K (LaurentPolynomial.C h), singleT K j
          (projP2 K p _ ((LaurentPolynomial.C h).coeff j))).coeff 0).coeff d = 0 at hc0
        rw [coeff_sum_projP2] at hc0
        have hC0 : (LaurentPolynomial.C h : Ambient K).coeff 0 = h := by
          change (singleT K 0 h).coeff 0 = h; simp [coeff_singleT]
        rw [hC0, coeff_projP2, if_pos rfl] at hc0
        exact MvPolynomial.mem_support_iff.mp hd_mem hc0
      have hle : ((p + 1) * d 0 + p * d 1 : ℤ) ≤ d_h := Finset.le_max' _ _ hmem_supp
      linarith
    have hhbar_ne : hbar ≠ 0 := fun h0 => by
      have htop0 : (grZT K p).topComp (bC K p h : Ambient K) = 0 := by
        rw [htop_h, h0]; change LaurentPolynomial.C (0 : P2 K) = 0; exact map_zero _
      exact (grZT K p).topComp_ne_zero hh_ne htop0
    have h0 := congrArg (fun r : P2 K => r.coeff 0) hhbar_hom
    rw [hc, coeff_projP2, MvPolynomial.coeff_C, if_pos rfl, if_neg (by simp; omega)] at h0
    rw [hc, ← h0, map_zero] at hhbar_ne
    exact hhbar_ne rfl
  -- Step 5: Factor `hbar` via `hom_P2_factor` and use factorial closure (`mem_invSubalg_of_mul`)!
  have hhbar_ne_B : bC K p hbar ≠ 0 := fun h0 => by
    have h1 := congrArg (fun r : HomRing K p => (r : Ambient K).coeff 0) h0
    have hC0 : (bC K p hbar : Ambient K).coeff 0 = hbar := by
      change (singleT K 0 hbar).coeff 0 = hbar; simp [coeff_singleT]
    rw [hC0] at h1; exact hhbar_nc 0 (by simp [h1])
  rcases hom_P2_factor K p hp d_h hbar hhbar_hom hhbar_nc with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨μ, hμ, q, hq⟩
  · refine ⟨φ₂, MvPolynomial.X 0, hnt₂, hy₂, ?_, Or.inl rfl⟩
    have hmul : bC K p hbar = bC K p (MvPolynomial.X 0) * bC K p q := by
      apply Subtype.ext; change LaurentPolynomial.C hbar = LaurentPolynomial.C _ * LaurentPolynomial.C _
      rw [← map_mul, hq]
    rw [hmul] at hhbar_inv hhbar_ne_B
    exact (φ₂.mem_invSubalg_of_mul (left_ne_zero_of_mul hhbar_ne_B) (right_ne_zero_of_mul hhbar_ne_B) hhbar_inv).1
  · refine ⟨φ₂, MvPolynomial.X 1, hnt₂, hy₂, ?_, Or.inr (Or.inl rfl)⟩
    have hmul : bC K p hbar = bC K p (MvPolynomial.X 1) * bC K p q := by
      apply Subtype.ext; change LaurentPolynomial.C hbar = LaurentPolynomial.C _ * LaurentPolynomial.C _
      rw [← map_mul, hq]
    rw [hmul] at hhbar_inv hhbar_ne_B
    exact (φ₂.mem_invSubalg_of_mul (left_ne_zero_of_mul hhbar_ne_B) (right_ne_zero_of_mul hhbar_ne_B) hhbar_inv).1
  · refine ⟨φ₂, MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1),
      hnt₂, hy₂, ?_, Or.inr (Or.inr ⟨μ, hμ, rfl⟩)⟩
    have hmul : bC K p hbar =
        bC K p (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1)) * bC K p q := by
      apply Subtype.ext; change LaurentPolynomial.C hbar = LaurentPolynomial.C _ * LaurentPolynomial.C _
      rw [← map_mul, hq]
    rw [hmul] at hhbar_inv hhbar_ne_B
    exact (φ₂.mem_invSubalg_of_mul (left_ne_zero_of_mul hhbar_ne_B) (right_ne_zero_of_mul hhbar_ne_B) hhbar_inv).1

/-- Base change of an `ExpMap L D` along a field extension `L →+* L'` to `L' ⊗[L] D`. -/
noncomputable def ExpMap.baseChange {L L' D : Type*} [Field L] [Field L'] [CommRing D]
    [Algebra L L'] [Algebra L D] (φ : ExpMap L D) :
    ExpMap L' (TensorProduct L L' D) := by
  let fL : TensorProduct L L' D →ₐ[L] Polynomial (TensorProduct L L' D) :=
    Algebra.TensorProduct.lift
      ((Polynomial.CAlgHom (R := L) (A := TensorProduct L L' D)).comp
        (Algebra.TensorProduct.includeLeft))
      ((Polynomial.mapAlgHom Algebra.TensorProduct.includeRight).comp φ.toAlgHom)
      (fun _ _ => Commute.all _ _)
  let fL' : TensorProduct L L' D →ₐ[L'] Polynomial (TensorProduct L L' D) :=
    { toRingHom := fL.toRingHom
      commutes' := fun c => by
        change fL (c ⊗ₜ[L] (1 : D)) = Polynomial.C (c ⊗ₜ[L] (1 : D))
        simp [fL] }
  refine
    { toAlgHom := fL'
      eval_zero := fun x => ?_
      coassoc := fun x => ?_ }
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      change (Polynomial.eval 0) (fL (c ⊗ₜ[L] d)) = c ⊗ₜ[L] d
      simp only [fL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Polynomial.CAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
        Polynomial.eval_mul, Polynomial.eval_C]
      change (c ⊗ₜ[L] (1 : D)) *
        Polynomial.eval 0 (Polynomial.map (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom (φ d)) =
        c ⊗ₜ[L] d
      rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, φ.coeff_zero d]
      change (c ⊗ₜ[L] (1 : D)) * ((1 : L') ⊗ₜ[L] d) = c ⊗ₜ[L] d
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp [map_add, hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      change Polynomial.map (fL'.toRingHom) (fL (c ⊗ₜ[L] d)) =
        Polynomial.eval₂ (Polynomial.C.comp Polynomial.C)
          (Polynomial.C Polynomial.X + Polynomial.X) (fL (c ⊗ₜ[L] d))
      simp only [fL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Polynomial.CAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
        Polynomial.map_mul, Polynomial.map_C]
      change Polynomial.C (fL'.toRingHom (c ⊗ₜ[L] 1)) *
          Polynomial.map fL'.toRingHom ((Polynomial.mapAlgHom Algebra.TensorProduct.includeRight) (φ.toAlgHom d)) =
        (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) (Polynomial.C Polynomial.X + Polynomial.X))
          (Polynomial.C (c ⊗ₜ[L] 1) * (Polynomial.mapAlgHom Algebra.TensorProduct.includeRight) (φ.toAlgHom d))
      rw [map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      congr 1
      · change Polynomial.C (fL (c ⊗ₜ[L] (1 : D))) = Polynomial.C (Polynomial.C (c ⊗ₜ[L] (1 : D)))
        simp [fL]
      · have hcomp : (fL'.toRingHom).comp (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom =
            (Polynomial.mapRingHom (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom).comp
              φ.toAlgHom.toRingHom := by
          apply RingHom.ext; intro r
          change fL ((1 : L') ⊗ₜ[L] r) = _
          simp only [fL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
            Polynomial.CAlgHom_apply, Algebra.TensorProduct.includeLeft_apply]
          have h1 : Polynomial.C ((1 : L') ⊗ₜ[L] (1 : D)) = (1 : Polynomial (TensorProduct L L' D)) :=
            map_one Polynomial.C
          rw [h1, one_mul]; rfl
        change Polynomial.map fL'.toRingHom
            (Polynomial.map (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom (φ d)) =
          Polynomial.eval₂ (Polynomial.C.comp Polynomial.C) (Polynomial.C Polynomial.X + Polynomial.X)
            (Polynomial.map (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom (φ d))
        rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, φ.coassoc d]
        generalize φ d = P
        induction P using Polynomial.induction_on' with
        | add p₁ p₂ h₁ h₂ =>
          simp only [Polynomial.coe_eval₂RingHom] at h₁ h₂
          simp only [Polynomial.map_add, map_add, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, h₁, h₂]
        | monomial n r =>
          simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
            Polynomial.map_monomial, RingHom.comp_apply, Polynomial.map_mul,
            Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
            Polynomial.coe_mapRingHom]
    | add x y hx hy =>
      change Polynomial.map fL'.toRingHom (fL' (x + y)) =
        Polynomial.eval₂ (Polynomial.C.comp Polynomial.C) (Polynomial.C Polynomial.X + Polynomial.X) (fL' (x + y))
      rw [map_add, Polynomial.map_add, Polynomial.eval₂_add]
      exact congrArg₂ (· + ·) hx hy

lemma ExpMap.baseChange_isNontrivial {L L' D : Type*} [Field L] [Field L'] [CommRing D]
    [Algebra L L'] [Algebra L D] (φ : ExpMap L D) (hnt : φ.IsNontrivial) :
    (φ.baseChange (L' := L')).IsNontrivial := by
  classical
  obtain ⟨d, hd⟩ := hnt
  refine ⟨(1 : L') ⊗ₜ[L] d, fun hinv => hd ?_⟩
  -- Build an `L`-linear functional `π : L' →ₗ[L] L` with `π 1 = 1` via complement of `span L {1}`
  let S1 : Submodule L L' := Submodule.span L {(1 : L')}
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S1
  let proj1 : L' →ₗ[L] S1 := S1.linearProjOfIsCompl W hW
  let toL : S1 →ₗ[L] L :=
    { toFun := fun x => (Submodule.mem_span_singleton.mp x.2).choose
      map_add' := fun x y => by
        have hx := (Submodule.mem_span_singleton.mp x.2).choose_spec
        have hy := (Submodule.mem_span_singleton.mp y.2).choose_spec
        have hxy := (Submodule.mem_span_singleton.mp (x + y).2).choose_spec
        have h1 : ((Submodule.mem_span_singleton.mp (x + y).2).choose : L) • (1 : L') =
            ((Submodule.mem_span_singleton.mp x.2).choose + (Submodule.mem_span_singleton.mp y.2).choose) • (1 : L') := by
          rw [add_smul, hx, hy, hxy]; rfl
        apply (algebraMap L L').injective
        simpa [Algebra.smul_def] using h1
      map_smul' := fun r x => by
        have hx := (Submodule.mem_span_singleton.mp x.2).choose_spec
        have hrx := (Submodule.mem_span_singleton.mp (r • x).2).choose_spec
        have h1 : ((Submodule.mem_span_singleton.mp (r • x).2).choose : L) • (1 : L') =
            (r * (Submodule.mem_span_singleton.mp x.2).choose) • (1 : L') := by
          rw [mul_smul, hx, hrx]; rfl
        apply (algebraMap L L').injective
        simpa [Algebra.smul_def] using h1 }
  let π : L' →ₗ[L] L := toL.comp proj1
  have hπ1 : π (1 : L') = 1 := by
    have hmem : (1 : L') ∈ S1 := Submodule.subset_span (Set.mem_singleton _)
    have hp : proj1 (1 : L') = ⟨1, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hW ⟨1, hmem⟩
    change toL (proj1 (1 : L')) = 1
    rw [hp]
    have hspec := (Submodule.mem_span_singleton.mp hmem).choose_spec
    apply (algebraMap L L').injective
    simpa [toL, Algebra.smul_def] using hspec
  let retract : TensorProduct L L' D →ₗ[L] D :=
    TensorProduct.lift
      { toFun := fun c => (π c) • LinearMap.id
        map_add' := fun c₁ c₂ => by ext x; simp [add_smul]
        map_smul' := fun r c => by ext x; simp [mul_smul] }
  have hret_tmul : ∀ (c : L') (x : D), retract (c ⊗ₜ[L] x) = (π c) • x := fun _ _ => rfl
  change (φ.baseChange (L' := L')) ((1 : L') ⊗ₜ[L] d) = Polynomial.C ((1 : L') ⊗ₜ[L] d) at hinv
  change φ d = Polynomial.C d
  ext n
  have hn := congrArg (fun P : Polynomial (TensorProduct L L' D) => retract (P.coeff n)) hinv
  have hlhs : ((φ.baseChange (L' := L')) ((1 : L') ⊗ₜ[L] d)).coeff n =
      (1 : L') ⊗ₜ[L] ((φ d).coeff n) := by
    have hbc : (φ.baseChange (L' := L')) ((1 : L') ⊗ₜ[L] d) =
        Polynomial.map (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D)).toRingHom (φ d) := by
      change (Algebra.TensorProduct.lift
        ((Polynomial.CAlgHom (R := L) (A := TensorProduct L L' D)).comp Algebra.TensorProduct.includeLeft)
        ((Polynomial.mapAlgHom (Algebra.TensorProduct.includeRight (R := L) (A := L') (B := D))).comp φ.toAlgHom)
        (fun _ _ => Commute.all _ _)) ((1 : L') ⊗ₜ[L] d) = _
      rw [Algebra.TensorProduct.lift_tmul]
      simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Algebra.TensorProduct.includeLeft_apply]
      have h1 : Polynomial.C ((1 : L') ⊗ₜ[L] (1 : D)) = (1 : Polynomial (TensorProduct L L' D)) :=
        map_one Polynomial.C
      rw [h1, one_mul]; rfl
    rw [hbc, Polynomial.coeff_map]; rfl
  rw [hlhs, hret_tmul, hπ1, one_smul] at hn
  rw [Polynomial.coeff_C] at hn ⊢
  split_ifs at hn ⊢
  · rw [hret_tmul, hπ1, one_smul] at hn; exact hn
  · rw [map_zero] at hn; exact hn

/-- Irreducibility of `Z^p + μ * T^(p+1)` in `P2 F` over any field `F` when `1 < p` and `μ ≠ 0`. -/
lemma irreducible_Zp_add_mu_Tp1 {F : Type*} [Field F] (hp : 1 < p) {μ : F} (hμ : μ ≠ 0) :
    Irreducible (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1) : P2 F) := by
  set f : P2 F := MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1) with hf_def
  have hf_hom : projP2 F p (p * (p + 1) : ℤ) f = f := by
    ext d; rw [coeff_projP2]
    simp only [hf_def, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C_mul]
    by_cases h0 : Finsupp.single (0 : Fin 2) p = d
    · subst h0; simp [mul_comm]
    · by_cases h1 : Finsupp.single (1 : Fin 2) (p + 1) = d
      · subst h1; simp
      · rw [if_neg h0, if_neg h1, mul_zero, add_zero, ite_self]
  have hf_ne : f ≠ 0 := by
    intro h0
    have hc := congrArg (fun r : P2 F => r.coeff (Finsupp.single 0 p)) h0
    simp only [hf_def, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_zero] at hc
    have hne : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 0 p := by
      intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; omega
    rw [if_neg hne] at hc; simp at hc
  have hf_not_unit : ¬ IsUnit f := by
    intro hu
    obtain ⟨g, hfg⟩ := hu.exists_right_inv
    have hdeg0 : DegLeP2 F p 0 (f * g) := by
      rw [hfg]; intro d hd
      have hne := MvPolynomial.mem_support_iff.mp hd
      rw [MvPolynomial.coeff_one] at hne
      by_cases hd0 : (0 : Fin 2 →₀ ℕ) = d
      · subst hd0; simp
      · rw [if_neg hd0] at hne; exact absurd rfl hne
    have hf_deg : DegLeP2 F p (p * (p + 1) : ℤ) f := by
      rw [degLeP2_iff_projP2]; intro k hk
      rw [← hf_hom]; ext d; rw [coeff_projP2, coeff_projP2, MvPolynomial.coeff_zero]
      by_cases h1 : ((p + 1) * d 0 + p * d 1 : ℤ) = k
      · rw [if_pos h1, if_neg (by linarith)]
      · rw [if_neg h1]
    have hg_deg : DegLeP2 F p (0 - (p * (p + 1) : ℤ)) g :=
      degLeP2_of_mul F p hf_deg (by rw [hf_hom]; exact hf_ne) hdeg0
    have hg0 : g = 0 := by
      ext d; rw [MvPolynomial.coeff_zero]; by_contra hne
      have hle := hg_deg d (MvPolynomial.mem_support_iff.mpr hne)
      have hnn : (0 : ℤ) ≤ ((p + 1) * d 0 + p * d 1 : ℤ) := by positivity
      nlinarith
    rw [hg0, mul_zero] at hfg; exact zero_ne_one hfg
  refine ⟨hf_not_unit, fun a b hab => ?_⟩
  have ha_ne : a ≠ 0 := fun h0 => hf_ne (by rw [hab, h0, zero_mul])
  have hb_ne : b ≠ 0 := fun h0 => hf_ne (by rw [hab, h0, mul_zero])
  let waSet : Finset ℤ := a.support.image fun d => ((p + 1) * d 0 + p * d 1 : ℤ)
  let wbSet : Finset ℤ := b.support.image fun d => ((p + 1) * d 0 + p * d 1 : ℤ)
  set wa : ℤ := waSet.max' ((MvPolynomial.support_nonempty.mpr ha_ne).image _) with hwa_def
  set wb : ℤ := wbSet.max' ((MvPolynomial.support_nonempty.mpr hb_ne).image _) with hwb_def
  have hwa_deg : DegLeP2 F p wa a := fun d hd => Finset.le_max' waSet _ (Finset.mem_image_of_mem _ hd)
  have hwb_deg : DegLeP2 F p wb b := fun d hd => Finset.le_max' wbSet _ (Finset.mem_image_of_mem _ hd)
  have hwa_top : projP2 F p wa a ≠ 0 := by
    obtain ⟨d, hd, hwd⟩ := Finset.mem_image.mp (Finset.max'_mem waSet ((MvPolynomial.support_nonempty.mpr ha_ne).image _))
    intro h0; have hc := congrArg (fun r : P2 F => r.coeff d) h0
    rw [coeff_projP2, if_pos (hwd.trans hwa_def.symm), MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  have hwb_top : projP2 F p wb b ≠ 0 := by
    obtain ⟨d, hd, hwd⟩ := Finset.mem_image.mp (Finset.max'_mem wbSet ((MvPolynomial.support_nonempty.mpr hb_ne).image _))
    intro h0; have hc := congrArg (fun r : P2 F => r.coeff d) h0
    rw [coeff_projP2, if_pos (hwd.trans hwb_def.symm), MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
  have hwa_nn : 0 ≤ wa := by
    obtain ⟨d, _, hwd⟩ := Finset.mem_image.mp (Finset.max'_mem waSet ((MvPolynomial.support_nonempty.mpr ha_ne).image _))
    rw [hwa_def, ← hwd]; positivity
  have hwb_nn : 0 ≤ wb := by
    obtain ⟨d, _, hwd⟩ := Finset.mem_image.mp (Finset.max'_mem wbSet ((MvPolynomial.support_nonempty.mpr hb_ne).image _))
    rw [hwb_def, ← hwd]; positivity
  have hsum_w : wa + wb = (p * (p + 1) : ℤ) := by
    have hprod_top : projP2 F p (wa + wb) f ≠ 0 := by
      rw [hab, projP2_mul_top F p hwa_deg hwb_deg]; exact mul_ne_zero hwa_top hwb_top
    by_contra hne
    apply hprod_top
    rw [← hf_hom]; ext d; rw [coeff_projP2, coeff_projP2, MvPolynomial.coeff_zero]
    by_cases h1 : ((p + 1) * d 0 + p * d 1 : ℤ) = wa + wb
    · rw [if_pos h1, if_neg (fun h2 => hne (h1.symm.trans h2))]
    · rw [if_neg h1]
  by_cases hwa0 : wa = 0
  · left
    have ha_const : a = MvPolynomial.C (a.coeff 0) := by
      ext d; rw [MvPolynomial.coeff_C]; split_ifs with hd0
      · subst hd0; rfl
      · by_contra hne
        have hle := hwa_deg d (MvPolynomial.mem_support_iff.mpr hne)
        rw [hwa0] at hle
        have h0 : d 0 = 0 := by nlinarith
        have h1 : d 1 = 0 := by nlinarith
        apply hd0; ext i; fin_cases i
        · change 0 = d 0; omega
        · change 0 = d 1; omega
    have hc0 : a.coeff 0 ≠ 0 := fun h0 => ha_ne (by rw [ha_const, h0, map_zero])
    rw [ha_const]; exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C
  · by_cases hwb0 : wb = 0
    · right
      have hb_const : b = MvPolynomial.C (b.coeff 0) := by
        ext d; rw [MvPolynomial.coeff_C]; split_ifs with hd0
        · subst hd0; rfl
        · by_contra hne
          have hle := hwb_deg d (MvPolynomial.mem_support_iff.mpr hne)
          rw [hwb0] at hle
          have h0 : d 0 = 0 := by nlinarith
          have h1 : d 1 = 0 := by nlinarith
          apply hd0; ext i; fin_cases i
          · change 0 = d 0; omega
          · change 0 = d 1; omega
      have hc0 : b.coeff 0 ≠ 0 := fun h0 => hb_ne (by rw [hb_const, h0, map_zero])
      rw [hb_const]; exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C
    · exfalso
      have hprod_eq : f = projP2 F p wa a * projP2 F p wb b := by
        rw [← hf_hom, ← hsum_w, hab, projP2_mul_top F p hwa_deg hwb_deg]
      have hno_both : ∀ g : P2 F, ∀ w : ℤ, 0 < w → w < (p * (p + 1) : ℤ) →
          projP2 F p w g = g →
          (∀ d ∈ g.support, 1 ≤ d 0) ∨ (∀ d ∈ g.support, 1 ≤ d 1) := by
        intro g w hw0 hwlt hg_hom
        by_contra hno; push Not at hno
        obtain ⟨⟨dT, hdT, hdT0⟩, ⟨dZ, hdZ, hdZ1⟩⟩ := hno
        have hwtT : ((p + 1) * dT 0 + p * dT 1 : ℤ) = w := by
          have h1 := congrArg (fun r : P2 F => r.coeff dT) hg_hom
          rw [coeff_projP2] at h1
          by_cases h : ((p + 1) * dT 0 + p * dT 1 : ℤ) = w
          · exact h
          · rw [if_neg h] at h1; exact absurd h1.symm (MvPolynomial.mem_support_iff.mp hdT)
        have hwtZ : ((p + 1) * dZ 0 + p * dZ 1 : ℤ) = w := by
          have h1 := congrArg (fun r : P2 F => r.coeff dZ) hg_hom
          rw [coeff_projP2] at h1
          by_cases h : ((p + 1) * dZ 0 + p * dZ 1 : ℤ) = w
          · exact h
          · rw [if_neg h] at h1; exact absurd h1.symm (MvPolynomial.mem_support_iff.mp hdZ)
        have hT0 : dT 0 = 0 := by omega
        have hZ1 : dZ 1 = 0 := by omega
        rw [hT0] at hwtT; rw [hZ1] at hwtZ; simp at hwtT hwtZ
        have hrel : (p + 1) * dZ 0 = p * dT 1 := by
          have : ((p + 1) * dZ 0 : ℤ) = (p * dT 1 : ℤ) := hwtZ.trans hwtT.symm
          exact_mod_cast this
        have hcop : Nat.Coprime p (p + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
        obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left ⟨dT 1, hrel⟩
        have hkpos : 1 ≤ k := by
          by_contra hk0; have : k = 0 := by omega
          rw [this, mul_zero] at hk; rw [hk] at hwtZ; simp at hwtZ; omega
        rw [hk] at hwtZ; push_cast at hwtZ; nlinarith
      have hpp_a : projP2 F p wa (projP2 F p wa a) = projP2 F p wa a := by
        ext d; rw [coeff_projP2, coeff_projP2]; split_ifs <;> rfl
      rcases hno_both (projP2 F p wa a) wa (by omega) (by omega) hpp_a with hdivZ | hdivT
      · have hev0 : MvPolynomial.aeval ![(0 : F), (1 : F)] (projP2 F p wa a) = 0 := by
          rw [MvPolynomial.as_sum (projP2 F p wa a), map_sum]
          apply Finset.sum_eq_zero; intro d hd
          rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
          have hd0 : d 0 ≠ 0 := by have := hdivZ d hd; omega
          simp [zero_pow hd0]
        have hf0 := congrArg (MvPolynomial.aeval ![(0 : F), (1 : F)]) hprod_eq
        rw [map_mul, hev0, zero_mul] at hf0
        simp [hf_def, zero_pow (by omega : p ≠ 0)] at hf0
        exact hμ hf0
      · have hev0 : MvPolynomial.aeval ![(1 : F), (0 : F)] (projP2 F p wa a) = 0 := by
          rw [MvPolynomial.as_sum (projP2 F p wa a), map_sum]
          apply Finset.sum_eq_zero; intro d hd
          rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
          have hd1 : d 1 ≠ 0 := by have := hdivT d hd; omega
          simp [zero_pow hd1]
        have hf0 := congrArg (MvPolynomial.aeval ![(1 : F), (0 : F)]) hprod_eq
        rw [map_mul, hev0, zero_mul] at hf0
        simp [hf_def, zero_pow (by omega : p + 1 ≠ 0)] at hf0

end FactorAndBaseChange


/- ## Section 7b3: Presentation of `HomRing`, Cases A & B, Lemma 3.5, Proposition 3.6, Theorem 3.8 -/

section Lemma35AndMain

variable (K : Type*) [Field K] (p : ℕ)

/-- Helper: lift a `PointDeriv` along a quotient by an ideal `I` when `ev` and `D` vanish on `I`. -/
def PointDeriv.quotient {L R : Type*} [Field L] [CommRing R] [Algebra L R]
    (I : Ideal R) (ev : R →ₐ[L] L) (hev : ∀ x ∈ I, ev x = 0)
    (D : PointDeriv L R ev) (hD : ∀ x ∈ I, D.toLinearMap x = 0) :
    PointDeriv L (R ⧸ I) (Ideal.Quotient.liftₐ I ev hev) where
  toLinearMap :=
    { toFun := fun x => Quotient.liftOn' x D.toLinearMap (fun a b hab => by
        have hsub : a - b ∈ I := (Submodule.quotientRel_def I).mp hab
        have h0 := hD (a - b) hsub
        rw [map_sub] at h0; exact sub_eq_zero.mp h0)
      map_add' := fun x y => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact map_add D.toLinearMap a b
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact map_smul D.toLinearMap c a }
  leibniz a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change D.toLinearMap (a * b) = ev a * D.toLinearMap b + ev b * D.toLinearMap a
    exact D.leibniz a b

/-- Helper: lift a `K`-linear Leibniz derivation `D : R →ₗ[K] L` (relative to `ev : R →ₐ[K] L`)
    to a `PointDeriv L (Localization M) ev_L` when `M = (nonZeroDivisors (Polynomial K)).map ι`,
    `L = FractionRing (Polynomial K)`, `ev ∘ ι = algebraMap`, and `D ∘ ι = 0`. -/
noncomputable def PointDeriv.localizePoly {K₀ R : Type*} [Field K₀] [CommRing R] [Algebra K₀ R]
    (ι : Polynomial K₀ →ₐ[K₀] R)
    (M : Submonoid R)
    (hM : M = (nonZeroDivisors (Polynomial K₀)).map ι.toRingHom.toMonoidHom)
    (ev : R →ₐ[K₀] FractionRing (Polynomial K₀))
    (hev_ι : ∀ q : Polynomial K₀, ev (ι q) = algebraMap (Polynomial K₀) (FractionRing (Polynomial K₀)) q)
    (D : R →ₗ[K₀] FractionRing (Polynomial K₀))
    (hD_leib : ∀ a b : R, D (a * b) = ev a * D b + ev b * D a)
    (hD_ι : ∀ q : Polynomial K₀, D (ι q) = 0) :
    let L := FractionRing (Polynomial K₀)
    let iR : Polynomial K₀ →+* Localization M := (algebraMap R (Localization M)).comp ι.toRingHom
    let hiR_unit : ∀ y : nonZeroDivisors (Polynomial K₀), IsUnit (iR y) := fun y =>
      IsLocalization.map_units (Localization M) (⟨ι y.1, by rw [hM]; exact ⟨y.1, y.2, rfl⟩⟩ : M)
    letI : Algebra L (Localization M) := RingHom.toAlgebra (IsLocalization.lift hiR_unit)
    let hev_M : ∀ m : M, ev m.1 ≠ 0 := fun m => by
      obtain ⟨q, hq, hqeq⟩ := (SetLike.ext_iff.mp hM m.1).mp m.2
      have h1 : ev m.1 = algebraMap (Polynomial K₀) L q := by
        rw [← hqeq]; exact hev_ι q
      rw [h1, ← map_zero (algebraMap (Polynomial K₀) L)]
      exact (IsFractionRing.injective (Polynomial K₀) L).ne (nonZeroDivisors.ne_zero hq)
    let ev_L : Localization M →ₐ[L] L :=
      { toRingHom := IsLocalization.lift (M := M) (g := ev.toRingHom)
          (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
        commutes' := fun c => by
          obtain ⟨⟨q₁, q₂⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K₀)) c
          have hq2_ne : algebraMap (Polynomial K₀) L q₂.1 ≠ 0 := by
            rw [← map_zero (algebraMap (Polynomial K₀) L)]
            exact (IsFractionRing.injective (Polynomial K₀) L).ne (nonZeroDivisors.ne_zero q₂.2)
          apply mul_right_cancel₀ hq2_ne
          have hpoly : ∀ q : Polynomial K₀,
              IsLocalization.lift (M := M) (g := ev.toRingHom)
                (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
                (algebraMap L (Localization M) (algebraMap (Polynomial K₀) L q)) =
              algebraMap (Polynomial K₀) L q := fun q => by
            change IsLocalization.lift _ (IsLocalization.lift hiR_unit (algebraMap (Polynomial K₀) L q)) = _
            rw [IsLocalization.lift_eq]
            change IsLocalization.lift _ (algebraMap R (Localization M) (ι q)) = _
            rw [IsLocalization.lift_eq]; exact hev_ι q
          calc IsLocalization.lift (M := M) (g := ev.toRingHom)
                (fun m => isUnit_iff_ne_zero.mpr (hev_M m)) (algebraMap L (Localization M) c) *
                algebraMap (Polynomial K₀) L q₂.1
              = IsLocalization.lift (M := M) (g := ev.toRingHom)
                (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
                (algebraMap L (Localization M) (c * algebraMap (Polynomial K₀) L q₂.1)) := by
                rw [map_mul, map_mul, hpoly q₂.1]
            _ = algebraMap (Polynomial K₀) L q₁ := by rw [hq, hpoly q₁]
            _ = c * algebraMap (Polynomial K₀) L q₂.1 := hq.symm }
    PointDeriv L (Localization M) ev_L := by
  dsimp only
  let L := FractionRing (Polynomial K₀)
  let iR : Polynomial K₀ →+* Localization M := (algebraMap R (Localization M)).comp ι.toRingHom
  let hiR_unit : ∀ y : nonZeroDivisors (Polynomial K₀), IsUnit (iR y) := fun y =>
    IsLocalization.map_units (Localization M) (⟨ι y.1, by rw [hM]; exact ⟨y.1, y.2, rfl⟩⟩ : M)
  letI : Algebra L (Localization M) := RingHom.toAlgebra (IsLocalization.lift hiR_unit)
  have hev_M : ∀ m : M, ev m.1 ≠ 0 := fun m => by
    obtain ⟨q, hq, hqeq⟩ := (SetLike.ext_iff.mp hM m.1).mp m.2
    have h1 : ev m.1 = algebraMap (Polynomial K₀) L q := by
      rw [← hqeq]; exact hev_ι q
    rw [h1, ← map_zero (algebraMap (Polynomial K₀) L)]
    exact (IsFractionRing.injective (Polynomial K₀) L).ne (nonZeroDivisors.ne_zero hq)
  let ev_L : Localization M →ₐ[L] L :=
    { toRingHom := IsLocalization.lift (M := M) (g := ev.toRingHom)
        (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
      commutes' := fun c => by
        obtain ⟨⟨q₁, q₂⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K₀)) c
        have hq2_ne : algebraMap (Polynomial K₀) L q₂.1 ≠ 0 := by
          rw [← map_zero (algebraMap (Polynomial K₀) L)]
          exact (IsFractionRing.injective (Polynomial K₀) L).ne (nonZeroDivisors.ne_zero q₂.2)
        apply mul_right_cancel₀ hq2_ne
        have hpoly : ∀ q : Polynomial K₀,
            IsLocalization.lift (M := M) (g := ev.toRingHom)
              (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
              (algebraMap L (Localization M) (algebraMap (Polynomial K₀) L q)) =
            algebraMap (Polynomial K₀) L q := fun q => by
          change IsLocalization.lift _ (IsLocalization.lift hiR_unit (algebraMap (Polynomial K₀) L q)) = _
          rw [IsLocalization.lift_eq]
          change IsLocalization.lift _ (algebraMap R (Localization M) (ι q)) = _
          rw [IsLocalization.lift_eq]; exact hev_ι q
        calc IsLocalization.lift (M := M) (g := ev.toRingHom)
              (fun m => isUnit_iff_ne_zero.mpr (hev_M m)) (algebraMap L (Localization M) c) *
              algebraMap (Polynomial K₀) L q₂.1
            = IsLocalization.lift (M := M) (g := ev.toRingHom)
              (fun m => isUnit_iff_ne_zero.mpr (hev_M m))
              (algebraMap L (Localization M) (c * algebraMap (Polynomial K₀) L q₂.1)) := by
              rw [map_mul, map_mul, hpoly q₂.1]
          _ = algebraMap (Polynomial K₀) L q₁ := by rw [hq, hpoly q₁]
          _ = c * algebraMap (Polynomial K₀) L q₂.1 := hq.symm }
  have hD_M : ∀ m : M, D m.1 = 0 := fun m => by
    obtain ⟨q, _, hqeq⟩ := (SetLike.ext_iff.mp hM m.1).mp m.2
    rw [← hqeq]; exact hD_ι q
  have hfn_wd : ∀ (r₁ r₂ : R) (m₁ m₂ : M), Localization.r M (r₁, m₁) (r₂, m₂) →
      D r₁ * (ev m₁.1)⁻¹ = D r₂ * (ev m₂.1)⁻¹ := by
    intro r₁ r₂ m₁ m₂ h
    rw [Localization.r_iff_exists] at h
    obtain ⟨t, ht⟩ := h
    have hD_eq := congrArg D ht
    simp only [hD_leib, hD_M, mul_zero, add_zero] at hD_eq
    have ht_ne : ev t.1 ≠ 0 := hev_M t
    have hm1_ne : ev m₁.1 ≠ 0 := hev_M m₁
    have hm2_ne : ev m₂.1 ≠ 0 := hev_M m₂
    have hcancel : ev m₂.1 * D r₁ = ev m₁.1 * D r₂ := mul_left_cancel₀ ht_ne hD_eq
    field_simp [hm1_ne, hm2_ne]
    linear_combination hcancel
  let D_fun : Localization M → L := fun x =>
    Localization.liftOn x (fun r m => D r * (ev m.1)⁻¹) (fun h => hfn_wd _ _ _ _ h)
  have hD_mk : ∀ (r : R) (m : M), D_fun (Localization.mk r m) = D r * (ev m.1)⁻¹ :=
    fun r m => Localization.liftOn_mk _ _ _ _
  have hev_mk : ∀ (r : R) (m : M), ev_L (Localization.mk r m) = ev r * (ev m.1)⁻¹ := fun r m => by
    have hm_ne : ev m.1 ≠ 0 := hev_M m
    apply mul_right_cancel₀ hm_ne
    rw [mul_assoc, inv_mul_cancel₀ hm_ne, mul_one]
    have hm_eq : ev_L (algebraMap R (Localization M) m.1) = ev m.1 := IsLocalization.lift_eq _ m.1
    rw [← hm_eq, ← map_mul, mul_comm (Localization.mk r m), Localization.mk_eq_mk',
      IsLocalization.mk'_spec' (Localization M) r m]
    exact IsLocalization.lift_eq _ r
  have hD_add : ∀ x y : Localization M, D_fun (x + y) = D_fun x + D_fun y := by
    intro x y
    induction x using Localization.induction_on with | H p₁ =>
    induction y using Localization.induction_on with | H p₂ =>
    obtain ⟨r₁, m₁⟩ := p₁; obtain ⟨r₂, m₂⟩ := p₂
    rw [Localization.add_mk, hD_mk, hD_mk, hD_mk, map_add, hD_leib, hD_leib,
      hD_M m₁, hD_M m₂, mul_zero, add_zero, mul_zero, add_zero, Submonoid.coe_mul, map_mul]
    have hm1 : ev m₁.1 ≠ 0 := hev_M m₁
    have hm2 : ev m₂.1 ≠ 0 := hev_M m₂
    field_simp [hm1, hm2]; ring
  have hD_leib_L : ∀ x y : Localization M, D_fun (x * y) = ev_L x * D_fun y + ev_L y * D_fun x := by
    intro x y
    induction x using Localization.induction_on with | H p₁ =>
    induction y using Localization.induction_on with | H p₂ =>
    obtain ⟨r₁, m₁⟩ := p₁; obtain ⟨r₂, m₂⟩ := p₂
    rw [Localization.mk_mul, hD_mk, hD_mk, hD_mk, hev_mk, hev_mk, hD_leib, Submonoid.coe_mul, map_mul]
    have hm1 : ev m₁.1 ≠ 0 := hev_M m₁
    have hm2 : ev m₂.1 ≠ 0 := hev_M m₂
    field_simp [hm1, hm2]
  have hD_algMap : ∀ c : L, D_fun (algebraMap L (Localization M) c) = 0 := by
    intro c
    obtain ⟨⟨q₁, q₂⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K₀)) c
    have hq2_ne : algebraMap (Polynomial K₀) L q₂.1 ≠ 0 := by
      rw [← map_zero (algebraMap (Polynomial K₀) L)]
      exact (IsFractionRing.injective (Polynomial K₀) L).ne (nonZeroDivisors.ne_zero q₂.2)
    have h1 := hD_leib_L (algebraMap L (Localization M) c)
      (algebraMap L (Localization M) (algebraMap (Polynomial K₀) L q₂.1))
    rw [← map_mul, hq] at h1
    have hD_poly : ∀ q : Polynomial K₀,
        D_fun (algebraMap L (Localization M) (algebraMap (Polynomial K₀) L q)) = 0 := by
      intro q
      have h2 : algebraMap L (Localization M) (algebraMap (Polynomial K₀) L q) =
          Localization.mk (ι q) (1 : M) := by
        change IsLocalization.lift hiR_unit (algebraMap (Polynomial K₀) L q) = _
        rw [IsLocalization.lift_eq]; exact (Localization.mk_one_eq_algebraMap (ι q)).symm
      rw [h2, hD_mk, hD_ι q, zero_mul]
    rw [hD_poly q₁, hD_poly q₂.1, mul_zero, zero_add, AlgHom.commutes] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hq2_ne
  exact
    { toLinearMap :=
        { toFun := D_fun
          map_add' := hD_add
          map_smul' := fun c x => by
            rw [Algebra.smul_def, hD_leib_L, hD_algMap, mul_zero, add_zero, AlgHom.commutes]
            change c * D_fun x = c • D_fun x; rfl }
      leibniz := hD_leib_L }

set_option maxHeartbeats 400000 in
/-- Explicit presentation of `HomRing K p`:
    `K[X, Y, Z, T] / (X^2 * Y + gHomPoly(Z, T)) ≃ₐ[K] HomRing K p`. -/
noncomputable def homRing_quotEquiv (hp : 1 < p) :
    (MvPolynomial (Fin 4) K ⧸
      Ideal.span {(MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
        MvPolynomial.X 2 ^ (p ^ 2) + MvPolynomial.X 3 ^ (p * (p + 1)) : MvPolynomial (Fin 4) K)}) ≃ₐ[K]
    HomRing K p := by
  let rel : MvPolynomial (Fin 4) K :=
    MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
      MvPolynomial.X 2 ^ (p ^ 2) + MvPolynomial.X 3 ^ (p * (p + 1))
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {rel}
  let φ0 : MvPolynomial (Fin 4) K →ₐ[K] HomRing K p :=
    MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p]
  have hrel0 : φ0 rel = 0 := by
    apply Subtype.ext
    simp only [φ0, rel, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_zero]
    change genX K ^ 2 * genYB K p + genZ K ^ (p ^ 2) + genT K ^ (p * (p + 1)) = 0
    rw [genX, genYB, genZ, genT, LaurentPolynomial.T_pow, ← map_pow, ← map_pow]
    have hT0 : (LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) : Ambient K) * LaurentPolynomial.T (-2) = 1 := by
      rw [← LaurentPolynomial.T_add]; norm_num
    calc LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) * (LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2)) +
          LaurentPolynomial.C (MvPolynomial.X 0 ^ (p ^ 2)) +
          LaurentPolynomial.C (MvPolynomial.X 1 ^ (p * (p + 1)))
        = LaurentPolynomial.C (-gHomPoly K p) *
            (LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) * LaurentPolynomial.T (-2)) +
          LaurentPolynomial.C (MvPolynomial.X 0 ^ (p ^ 2) + MvPolynomial.X 1 ^ (p * (p + 1))) := by
          rw [map_add]; ring
      _ = LaurentPolynomial.C (-gHomPoly K p) * 1 + LaurentPolynomial.C (gHomPoly K p) := by
          rw [hT0]; rfl
      _ = 0 := by rw [mul_one, map_neg, neg_add_cancel]
  let fwd : (MvPolynomial (Fin 4) K ⧸ I) →ₐ[K] HomRing K p :=
    Ideal.Quotient.liftₐ I φ0 (fun x hx => by
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨q, rfl⟩ := hx; rw [map_mul, hrel0, zero_mul])
  have hfwd_surj : Function.Surjective fwd := by
    intro y
    have hy_mem : (y : Ambient K) ∈ Algebra.adjoin K ({genX K, genYB K p, genZ K, genT K} : Set (Ambient K)) := y.2
    have hrange : HomSubalg K p ≤ ((HomSubalg K p).val.comp fwd).range := by
      unfold HomSubalg
      rw [Algebra.adjoin_le_iff]
      rintro g (rfl | rfl | rfl | rfl)
      · exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 0), by
          change (φ0 (MvPolynomial.X 0) : Ambient K) = genX K; simp [φ0, bX]⟩
      · exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 1), by
          change (φ0 (MvPolynomial.X 1) : Ambient K) = genYB K p; simp [φ0, bY]⟩
      · exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 2), by
          change (φ0 (MvPolynomial.X 2) : Ambient K) = genZ K; simp [φ0, bZ]⟩
      · exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 3), by
          change (φ0 (MvPolynomial.X 3) : Ambient K) = genT K; simp [φ0, bT]⟩
    obtain ⟨q, hq⟩ := hrange hy_mem
    exact ⟨q, Subtype.ext hq⟩
  have hfwd_inj : Function.Injective fwd := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    change φ0 P = 0 at hq
    rw [Ideal.Quotient.eq_zero_iff_mem]
    -- Every `P ∈ K[X, Y, Z, T]` is congruent mod `I` to a sum of monomials with `min(e 0 / 2, e 1) = 0`!
    have hreduce : ∀ P : MvPolynomial (Fin 4) K, ∃ Q : MvPolynomial (Fin 4) K,
        P - Q ∈ I ∧ ∀ e ∈ Q.support, e 0 < 2 ∨ e 1 = 0 := by
      intro P0
      -- Induct on `N := ∑ e ∈ P0.support, e 1`? Better: on `max_{e ∈ P0.support} e 1`!
      suffices ∀ M : ℕ, ∀ P : MvPolynomial (Fin 4) K,
          (∀ e ∈ P.support, e 1 ≤ M) →
          ∃ Q : MvPolynomial (Fin 4) K, P - Q ∈ I ∧ ∀ e ∈ Q.support, e 0 < 2 ∨ e 1 = 0 by
        exact this (P0.support.sup fun e => e 1) P0 (fun e he => Finset.le_sup (f := fun e : Fin 4 →₀ ℕ => e 1) he)
      intro M
      induction M with
      | zero =>
        intro P hP
        exact ⟨P, by simp, fun e he => Or.inr (Nat.eq_zero_of_le_zero (hP e he))⟩
      | succ M ih =>
        intro P hP
        -- For each monomial `e ∈ P.support`, if `2 ≤ e 0` and `1 ≤ e 1`, replace `X 0^2 * X 1` by `-(X 2^(p^2) + X 3^(p*(p+1)))`
        let stepMon (e : Fin 4 →₀ ℕ) : MvPolynomial (Fin 4) K :=
          if 2 ≤ e 0 ∧ 1 ≤ e 1 then
            -(MvPolynomial.monomial (e - Finsupp.single 0 2 - Finsupp.single 1 1) (P.coeff e) *
              (MvPolynomial.X 2 ^ (p ^ 2) + MvPolynomial.X 3 ^ (p * (p + 1))))
          else MvPolynomial.monomial e (P.coeff e)
        -- Actually apply the step iteratively: each step reduces `e 1` by 1 for all `e` with `2 ≤ e 0 ∧ 1 ≤ e 1`!
        let P_good : MvPolynomial (Fin 4) K :=
          ∑ e ∈ P.support.filter (fun e => e 0 < 2 ∨ e 1 = 0), MvPolynomial.monomial e (P.coeff e)
        let P_bad : MvPolynomial (Fin 4) K :=
          ∑ e ∈ P.support.filter (fun e => ¬(e 0 < 2 ∨ e 1 = 0)),
            -(MvPolynomial.monomial (e - Finsupp.single 0 2 - Finsupp.single 1 1) (P.coeff e) *
              (MvPolynomial.X 2 ^ (p ^ 2) + MvPolynomial.X 3 ^ (p * (p + 1))))
        have hdiff : P - (P_good + P_bad) ∈ I := by
          have hP_split : P =
              (∑ e ∈ P.support.filter (fun e => e 0 < 2 ∨ e 1 = 0), MvPolynomial.monomial e (P.coeff e)) +
              (∑ e ∈ P.support.filter (fun e => ¬(e 0 < 2 ∨ e 1 = 0)), MvPolynomial.monomial e (P.coeff e)) := by
            rw [Finset.sum_filter_add_sum_filter_not]; exact MvPolynomial.as_sum P
          have hsub : P - (P_good + P_bad) =
              ∑ e ∈ P.support.filter (fun e => ¬(e 0 < 2 ∨ e 1 = 0)),
                MvPolynomial.monomial (e - Finsupp.single 0 2 - Finsupp.single 1 1) (P.coeff e) * rel := by
            conv_lhs => rw [hP_split]
            simp only [P_good, P_bad]
            rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun e he => ?_
            have hbad : 2 ≤ e 0 ∧ 1 ≤ e 1 := by
              have := (Finset.mem_filter.mp he).2; omega
            have hmon_split : MvPolynomial.monomial e (P.coeff e) =
                MvPolynomial.monomial (e - Finsupp.single 0 2 - Finsupp.single 1 1) (P.coeff e) *
                  (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) := by
              have hX : (MvPolynomial.X (0 : Fin 4) ^ 2 * MvPolynomial.X 1 : MvPolynomial (Fin 4) K) =
                  MvPolynomial.monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 := by
                rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                  Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]; simp
              rw [hX, MvPolynomial.monomial_mul, mul_one]
              refine congrArg (fun s => MvPolynomial.monomial s (P.coeff e)) ?_
              ext i; fin_cases i
              · simp; omega
              · simp; omega
              · simp
              · simp
            rw [hmon_split]; simp only [rel]; ring
          rw [hsub]
          exact Ideal.sum_mem I fun e _ => Ideal.mul_mem_left I _ (Ideal.subset_span rfl)
        have hP_bad_deg : ∀ e ∈ P_bad.support, e 1 ≤ M := by
          intro e he
          have hne := MvPolynomial.mem_support_iff.mp he
          simp only [P_bad, MvPolynomial.coeff_sum] at hne
          obtain ⟨d, hd, hterm_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
          have hd_mem := (Finset.mem_filter.mp hd).1
          have hd_bad : 2 ≤ d 0 ∧ 1 ≤ d 1 := by have := (Finset.mem_filter.mp hd).2; omega
          have hd_le : d 1 ≤ M + 1 := hP d hd_mem
          rw [MvPolynomial.coeff_neg, neg_ne_zero, MvPolynomial.coeff_mul] at hterm_ne
          obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hterm_ne
          have has : a₁ + a₂ = e := by simpa using ha12
          have ha1 : a₁ = d - Finsupp.single 0 2 - Finsupp.single 1 1 := by
            have h1 := left_ne_zero_of_mul hpr
            rw [MvPolynomial.coeff_monomial] at h1
            split_ifs at h1 with h
            · exact h.symm
            · exact absurd rfl h1
          have ha2_1 : a₂ 1 = 0 := by
            have h2 := right_ne_zero_of_mul hpr
            simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow] at h2
            by_cases hc1 : Finsupp.single (2 : Fin 4) (p ^ 2) = a₂
            · subst hc1; simp
            · by_cases hc2 : Finsupp.single (3 : Fin 4) (p * (p + 1)) = a₂
              · subst hc2; simp
              · rw [if_neg hc1, if_neg hc2, add_zero] at h2; exact absurd rfl h2
          have he1 : e 1 = a₁ 1 + a₂ 1 := by rw [← has]; rfl
          rw [he1, ha1, ha2_1]; simp; omega
        obtain ⟨Q_bad, hQ_bad_I, hQ_bad_good⟩ := ih P_bad hP_bad_deg
        refine ⟨P_good + Q_bad, ?_, ?_⟩
        · have : P - (P_good + Q_bad) = (P - (P_good + P_bad)) + (P_bad - Q_bad) := by ring
          rw [this]; exact add_mem hdiff hQ_bad_I
        · intro e he
          have hne := MvPolynomial.mem_support_iff.mp he
          rw [MvPolynomial.coeff_add] at hne
          by_cases h1 : P_good.coeff e = 0
          · rw [h1, zero_add] at hne
            exact hQ_bad_good e (MvPolynomial.mem_support_iff.mpr hne)
          · simp only [P_good, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at h1
            obtain ⟨d, hd, hdn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
            split_ifs at hdn with hde
            · subst hde; exact (Finset.mem_filter.mp hd).2
            · exact absurd rfl hdn
    obtain ⟨Q, hPQ_I, hQ_good⟩ := hreduce P
    -- Since `φ0 P = 0` and `P - Q ∈ I`, `φ0 Q = 0`, which forces `Q = 0`!
    have hQ0 : φ0 Q = 0 := by
      have hdiff0 : φ0 (P - Q) = 0 := by
        rw [Ideal.mem_span_singleton] at hPQ_I
        obtain ⟨r, hr⟩ := hPQ_I; rw [hr, map_mul, hrel0, zero_mul]
      rw [map_sub, hq, zero_sub, neg_eq_zero] at hdiff0
      exact hdiff0
    suffices hQ_zero : Q = 0 by rwa [hQ_zero, sub_zero] at hPQ_I
    by_contra hQ_ne
    -- Pick a monomial `e₀ ∈ Q.support`, look at `((φ0 Q : Ambient K).coeff m₀)` where `m₀ = e₀ 0 - 2 * e₀ 1`!
    obtain ⟨e₀, he₀⟩ := MvPolynomial.support_nonempty.mpr hQ_ne
    let m₀ : ℤ := (e₀ 0 : ℤ) - 2 * (e₀ 1 : ℤ)
    have hcoeff_m0 : ((φ0 Q : HomRing K p) : Ambient K).coeff m₀ = 0 := by rw [hQ0]; rfl
    have hφ0_coe : ((φ0 Q : HomRing K p) : Ambient K) = MvPolynomial.aeval ![genX K, genYB K p, genZ K, genT K] Q := by
      have hcomp : (HomSubalg K p).val.comp φ0 = MvPolynomial.aeval ![genX K, genYB K p, genZ K, genT K] := by
        apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [φ0, bX, bY, bZ, bT]
      exact AlgHom.congr_fun hcomp Q
    rw [hφ0_coe, MvPolynomial.as_sum Q, map_sum, coeff_sum_A] at hcoeff_m0
    -- Every `e ∈ Q.support` with `e 0 - 2 * e 1 = m₀` MUST have `e 0 = e₀ 0` and `e 1 = e₀ 1` (by `hQ_good`!)
    have huniq01 : ∀ e ∈ Q.support, (e 0 : ℤ) - 2 * (e 1 : ℤ) = m₀ → e 0 = e₀ 0 ∧ e 1 = e₀ 1 := by
      intro e he hm
      have h1 := hQ_good e he
      have h2 := hQ_good e₀ he₀
      rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b <;> omega
    have hsum_eq : (∑ e ∈ Q.support,
        (MvPolynomial.aeval ![genX K, genYB K p, genZ K, genT K] (MvPolynomial.monomial e (Q.coeff e))).coeff m₀) =
        (-gHomPoly K p) ^ (e₀ 1) *
          ∑ e ∈ Q.support.filter (fun e => e 0 = e₀ 0 ∧ e 1 = e₀ 1),
            MvPolynomial.monomial (Finsupp.single 0 (e 2) + Finsupp.single 1 (e 3)) (Q.coeff e) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e he => ?_
      have hmon : MvPolynomial.aeval ![genX K, genYB K p, genZ K, genT K] (MvPolynomial.monomial e (Q.coeff e)) =
          singleT K ((e 0 : ℤ) - 2 * (e 1 : ℤ))
            ((-gHomPoly K p) ^ (e 1) *
              MvPolynomial.monomial (Finsupp.single 0 (e 2) + Finsupp.single 1 (e 3)) (Q.coeff e)) := by
        rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.aeval_C,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
        simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          genX, genYB, genZ, genT, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
        have hC : (algebraMap K (Ambient K)) (Q.coeff e) = LaurentPolynomial.C (MvPolynomial.C (Q.coeff e)) := rfl
        have hmon2 : MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 2) + Finsupp.single 1 (e 3)) (Q.coeff e) =
            MvPolynomial.C (Q.coeff e) * MvPolynomial.X 0 ^ e 2 * MvPolynomial.X 1 ^ e 3 := by
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
          simp [mul_assoc]
        have hTadd : (LaurentPolynomial.T ((e 0 : ℤ) - 2 * (e 1 : ℤ)) : Ambient K) =
            LaurentPolynomial.T ((e 0 : ℤ) * 1) * LaurentPolynomial.T ((e 1 : ℤ) * (-2)) := by
          rw [← LaurentPolynomial.T_add]; congr 1; ring
        rw [hC, hmon2, map_mul, map_mul, map_pow, map_pow, hTadd]; ring
      rw [hmon, coeff_singleT]
      by_cases hm : (e 0 : ℤ) - 2 * (e 1 : ℤ) = m₀
      · obtain ⟨he0, he1⟩ := huniq01 e he hm
        rw [if_pos hm, if_pos ⟨he0, he1⟩, he1]
      · rw [if_neg hm, if_neg]
        rintro ⟨he0, he1⟩; apply hm; simp [m₀, he0, he1]
    rw [hsum_eq] at hcoeff_m0
    have hsum0 : (∑ e ∈ Q.support.filter (fun e => e 0 = e₀ 0 ∧ e 1 = e₀ 1),
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 2) + Finsupp.single 1 (e 3)) (Q.coeff e)) = 0 :=
      (mul_eq_zero.mp hcoeff_m0).resolve_left
        (pow_ne_zero (e₀ 1) (neg_ne_zero.mpr (gHomPoly_ne_zero K p hp)))
    let d₂ : Fin 2 →₀ ℕ := Finsupp.single 0 (e₀ 2) + Finsupp.single 1 (e₀ 3)
    have hc := congrArg (fun r : P2 K => r.coeff d₂) hsum0
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hc
    rw [Finset.sum_eq_single e₀] at hc
    · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hc
      exact MvPolynomial.mem_support_iff.mp he₀ hc
    · intro e he hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hdeq; apply hne
      have h01 := (Finset.mem_filter.mp he).2
      have h2 := congrArg (fun u : Fin 2 →₀ ℕ => u 0) hdeq
      have h3 := congrArg (fun u : Fin 2 →₀ ℕ => u 1) hdeq
      simp [d₂] at h2 h3
      ext i; fin_cases i
      · exact h01.1
      · exact h01.2
      · exact h2
      · exact h3
    · intro hnm; exfalso; exact hnm (Finset.mem_filter.mpr ⟨he₀, rfl, rfl⟩)
  exact AlgEquiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩

lemma homRing_quotEquiv_mk_C (hp : 1 < p) (c : K) :
    (homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.C c)) = algebraMap K (HomRing K p) c := by
  change MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p] (MvPolynomial.C c) = _
  simp

lemma homRing_quotEquiv_mk_X0 (hp : 1 < p) :
    (homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 0)) = bX K p := by
  change MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p] (MvPolynomial.X 0) = _
  simp

lemma homRing_quotEquiv_mk_X1 (hp : 1 < p) :
    (homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 1)) = bY K p := by
  change MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p] (MvPolynomial.X 1) = _
  simp

lemma homRing_quotEquiv_mk_X2 (hp : 1 < p) :
    (homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 2)) = bZ K p := by
  change MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p] (MvPolynomial.X 2) = _
  simp

lemma homRing_quotEquiv_mk_X3 (hp : 1 < p) :
    (homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 3)) = bT K p := by
  change MvPolynomial.aeval ![bX K p, bY K p, bZ K p, bT K p] (MvPolynomial.X 3) = _
  simp

set_option maxHeartbeats 600000 in
/-- Helper: Over an algebraically closed field `L'` of prime characteristic `p`, the singular curve
    `L'[Z, T] / (Z^p + T^(p+1) - w)` admits no non-trivial `ExpMap`. -/
lemma no_expMap_singular_Zp_Tp1 {L' : Type*} [Field L'] [CharP L' p] [IsAlgClosed L']
    [hp_prime : Fact p.Prime] (w_L' : L')
    (φQ : ExpMap L' (P2 L' ⧸ Ideal.span {(MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L' : P2 L')}))
    (hφQ_nt : φQ.IsNontrivial) : False := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  have : CharP (P2 L') p := charP_of_injective_algebraMap (MvPolynomial.C_injective (Fin 2) L') p
  let relL' : P2 L' := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L'
  let IL' : Ideal (P2 L') := Ideal.span {relL'}
  let Q' := P2 L' ⧸ IL'
  obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C w_L') (by
    rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < p)]; exact_mod_cast (by omega : p ≠ 0))
  have hα_pow : α ^ p = w_L' := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hα_root
    exact sub_eq_zero.mp hα_root
  have hrelL'_irred : Irreducible relL' := by
    let shift : P2 L' ≃ₐ[L'] P2 L' :=
      AlgEquiv.ofAlgHom
        (MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C α, MvPolynomial.X 1])
        (MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C α, MvPolynomial.X 1])
        (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)
        (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)
    have hsh : shift (MvPolynomial.X 0 ^ p + MvPolynomial.C (1 : L') * MvPolynomial.X 1 ^ (p + 1)) = relL' := by
      simp only [shift, AlgEquiv.ofAlgHom_apply, map_add, map_pow, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, map_one, one_mul]
      rw [sub_pow_char, ← map_pow, hα_pow]
      simp only [relL']; ring
    rw [← hsh]
    exact (irreducible_Zp_add_mu_Tp1 p hp (one_ne_zero : (1 : L') ≠ 0)).map shift.toMulEquiv
  have : IL'.IsPrime := by
    rw [Ideal.span_singleton_prime (hrelL'_irred.ne_zero)]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hrelL'_irred
  have : IsDomain Q' := Ideal.Quotient.isDomain IL'
  let zQ : Q' := Ideal.Quotient.mk IL' (MvPolynomial.X 0)
  let tQ : Q' := Ideal.Quotient.mk IL' (MvPolynomial.X 1)
  let B_Q : Finset Q' := (Finset.range p).image fun i => zQ ^ i
  have hspan_Q : ∀ a : Q', ∃ g : Q' → Polynomial L', a = ∑ b ∈ B_Q, Polynomial.aeval tQ (g b) * b := by
    intro a
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hred' : ∀ P0 : P2 L', ∃ Q0 : P2 L', P0 - Q0 ∈ IL' ∧ ∀ e ∈ Q0.support, e 0 < p := by
      intro P0
      suffices ∀ M : ℕ, ∀ P1 : P2 L', (∀ e ∈ P1.support, e 0 ≤ M) →
          ∃ Q0 : P2 L', P1 - Q0 ∈ IL' ∧ ∀ e ∈ Q0.support, e 0 < p by
        exact this (P0.support.sup fun e => e 0) P0 (fun e he => Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 0) he)
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro P1 hP1
        by_cases hMp : M < p
        · exact ⟨P1, by simp, fun e he => lt_of_le_of_lt (hP1 e he) hMp⟩
        · let P_good : P2 L' := ∑ e ∈ P1.support.filter (fun e => e 0 < p), MvPolynomial.monomial e (P1.coeff e)
          let P_bad : P2 L' := ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p),
            MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) * (MvPolynomial.C w_L' - MvPolynomial.X 1 ^ (p + 1))
          have hdiff : P1 - (P_good + P_bad) ∈ IL' := by
            have hP1s : P1 = P_good + ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p), MvPolynomial.monomial e (P1.coeff e) := by
              simp only [P_good]; rw [Finset.sum_filter_add_sum_filter_not]; exact MvPolynomial.as_sum P1
            have hsub : P1 - (P_good + P_bad) = ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p),
                MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) * relL' := by
              conv_lhs => rw [hP1s]
              simp only [P_bad]; rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun e he => ?_
              have hge : p ≤ e 0 := by have := (Finset.mem_filter.mp he).2; omega
              have hms : MvPolynomial.monomial e (P1.coeff e) =
                  MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) * MvPolynomial.X 0 ^ p := by
                have hX : (MvPolynomial.X (0 : Fin 2) ^ p : P2 L') = MvPolynomial.monomial (Finsupp.single 0 p) 1 := by
                  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; simp
                rw [hX, MvPolynomial.monomial_mul, mul_one]
                refine congrArg (fun s => MvPolynomial.monomial s (P1.coeff e)) ?_
                ext j; fin_cases j
                · simp; omega
                · simp
              rw [hms]; simp only [relL']; ring
            rw [hsub]; exact Ideal.sum_mem IL' fun _ _ => Ideal.mul_mem_left IL' _ (Ideal.subset_span rfl)
          have hP_bad_deg : ∀ e ∈ P_bad.support, e 0 ≤ M - p := by
            intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            simp only [P_bad, MvPolynomial.coeff_sum] at hne
            obtain ⟨d, hd, htn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            have hd_ge : p ≤ d 0 := by have := (Finset.mem_filter.mp hd).2; omega
            have hd_le : d 0 ≤ M := hP1 d (Finset.mem_filter.mp hd).1
            rw [MvPolynomial.coeff_mul] at htn
            obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero htn
            have has : a₁ + a₂ = e := by simpa using ha12
            have ha1 : a₁ = d - Finsupp.single 0 p := by
              have h1 := left_ne_zero_of_mul hpr; rw [MvPolynomial.coeff_monomial] at h1
              split_ifs at h1 with h
              · exact h.symm
              · exact absurd rfl h1
            have ha2_0 : a₂ 0 = 0 := by
              have h2 := right_ne_zero_of_mul hpr
              rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, MvPolynomial.coeff_X_pow] at h2
              by_cases hc1 : (0 : Fin 2 →₀ ℕ) = a₂
              · subst hc1; simp
              · by_cases hc2 : Finsupp.single (1 : Fin 2) (p + 1) = a₂
                · subst hc2; simp
                · rw [if_neg hc1, if_neg hc2, sub_self] at h2; exact absurd rfl h2
            have he0 : e 0 = a₁ 0 + a₂ 0 := by rw [← has]; rfl
            rw [he0, ha1, ha2_0]; simp; omega
          obtain ⟨Q_bad, hQ_bad_I, hQ_bad_good⟩ := ih (M - p) (by omega) P_bad hP_bad_deg
          refine ⟨P_good + Q_bad, ?_, ?_⟩
          · have : P1 - (P_good + Q_bad) = (P1 - (P_good + P_bad)) + (P_bad - Q_bad) := by ring
            rw [this]; exact add_mem hdiff hQ_bad_I
          · intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            rw [MvPolynomial.coeff_add] at hne
            by_cases h1 : P_good.coeff e = 0
            · rw [h1, zero_add] at hne; exact hQ_bad_good e (MvPolynomial.mem_support_iff.mpr hne)
            · simp only [P_good, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at h1
              obtain ⟨d, hd, hdn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
              split_ifs at hdn with hde
              · subst hde; exact (Finset.mem_filter.mp hd).2
              · exact absurd rfl hdn
    obtain ⟨Q0, hPQ, hQ0_lt⟩ := hred' P
    have hmk_eq : Ideal.Quotient.mk IL' P = Ideal.Quotient.mk IL' Q0 :=
      Ideal.Quotient.eq.mpr hPQ
    let g_i (i : ℕ) : Polynomial L' :=
      ∑ e ∈ Q0.support.filter (fun e => e 0 = i), Polynomial.monomial (e 1) (Q0.coeff e)
    refine ⟨fun b => ∑ i ∈ (Finset.range p).filter (fun i => zQ ^ i = b), g_i i, ?_⟩
    rw [hmk_eq, MvPolynomial.as_sum Q0, map_sum]
    have hsum_part : ∑ e ∈ Q0.support, Ideal.Quotient.mk IL' (MvPolynomial.monomial e (Q0.coeff e)) =
        ∑ i ∈ Finset.range p, Polynomial.aeval tQ (g_i i) * zQ ^ i := by
      have h1 : ∑ e ∈ Q0.support, Ideal.Quotient.mk IL' (MvPolynomial.monomial e (Q0.coeff e)) =
          ∑ i ∈ Finset.range p, ∑ e ∈ Q0.support.filter (fun e => e 0 = i),
            Ideal.Quotient.mk IL' (MvPolynomial.monomial e (Q0.coeff e)) := by
        simp_rw [Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Finset.sum_eq_single (e 0)]
        · simp
        · intro i _ hne; rw [if_neg (Ne.symm hne)]
        · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr (hQ0_lt e he))
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [g_i, map_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e he => ?_
      have he0 : e 0 = i := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
        Polynomial.aeval_monomial, he0, map_mul, map_mul, map_pow, map_pow]
      change algebraMap L' Q' (Q0.coeff e) * (zQ ^ i * tQ ^ (e 1)) =
        algebraMap L' Q' (Q0.coeff e) * tQ ^ (e 1) * zQ ^ i
      ring
    rw [hsum_part]
    have hreidx : ∑ b ∈ B_Q, Polynomial.aeval tQ (∑ i ∈ (Finset.range p).filter (fun i => zQ ^ i = b), g_i i) * b =
        ∑ i ∈ Finset.range p, Polynomial.aeval tQ (g_i i) * zQ ^ i := by
      simp only [map_sum]
      simp_rw [Finset.sum_mul, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single (zQ ^ i)]
      · simp
      · intro b _ hne; rw [if_neg (Ne.symm hne)]
      · intro hnm; exfalso; exact hnm (Finset.mem_image_of_mem _ hi)
    exact hreidx.symm
  let ev0 : P2 L' →ₐ[L'] L' := MvPolynomial.aeval ![α, (0 : L')]
  have hev0_IL' : ∀ x ∈ IL', ev0 x = 0 := by
    intro x hx; rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
    rw [map_mul]; convert zero_mul _
    simp [ev0, relL', hα_pow, zero_pow (by omega : p + 1 ≠ 0)]
  let evQ : Q' →ₐ[L'] L' := Ideal.Quotient.liftₐ IL' ev0 hev0_IL'
  let mkPD (j : Fin 2) : PointDeriv L' (P2 L') ev0 :=
    { toLinearMap := ev0.toLinearMap.comp (MvPolynomial.pderiv j).toLinearMap
      leibniz := fun a b => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Derivation.coeFn_coe,
          Derivation.leibniz, map_add, map_mul, smul_eq_mul] }
  have hPD_IL' : ∀ (j : Fin 2), ∀ x ∈ IL', (mkPD j).toLinearMap x = 0 := by
    intro j x hx; rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
    rw [(mkPD j).leibniz, hev0_IL' relL' (Ideal.subset_span rfl), zero_mul, zero_add]
    suffices h0 : (mkPD j).toLinearMap relL' = 0 by rw [h0, mul_zero]
    simp only [mkPD, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Derivation.coeFn_coe,
      relL', map_sub, map_add, MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X]
    match j with
    | 0 =>
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        mul_one, mul_zero, add_zero, sub_zero, map_zero, CharP.cast_eq_zero, zero_mul]
    | 1 =>
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        mul_one, mul_zero, zero_add, sub_zero, map_zero, map_mul, map_pow,
        MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, ev0,
        zero_pow (by omega : p + 1 - 1 ≠ 0)]
  have : CharP Q' p := charP_of_injective_algebraMap (algebraMap L' Q').injective p
  have : Fact (Nat.Prime (ringChar Q')) := by rw [ringChar.eq Q' p]; exact hp_prime
  let D1 : PointDeriv L' Q' evQ := PointDeriv.quotient IL' ev0 hev0_IL' (mkPD 0) (hPD_IL' 0)
  let D2 : PointDeriv L' Q' evQ := PointDeriv.quotient IL' ev0 hev0_IL' (mkPD 1) (hPD_IL' 1)
  exact no_expMap_of_singular_curve tQ B_Q hspan_Q evQ D1 D2 zQ tQ
    (by change ev0 (MvPolynomial.pderiv 0 (MvPolynomial.X 0)) = 1; simp)
    (by change ev0 (MvPolynomial.pderiv 0 (MvPolynomial.X 1)) = 0; simp)
    (by change ev0 (MvPolynomial.pderiv 1 (MvPolynomial.X 0)) = 0; simp)
    (by change ev0 (MvPolynomial.pderiv 1 (MvPolynomial.X 1)) = 1; simp)
    φQ hφQ_nt

/-- Helper: Base change of a principal quotient `P2 L ⧸ ⟨f⟩ ≃ₐ[L] D` along `L → L'`. -/
noncomputable def quot_baseChange_equiv {L L' : Type*} [Field L] [Field L'] [Algebra L L']
    {D : Type*} [CommRing D] [Algebra L D] (f : P2 L) (f' : P2 L')
    (hf' : MvPolynomial.map (algebraMap L L') f = f')
    (e0 : (P2 L ⧸ Ideal.span ({f} : Set (P2 L))) ≃ₐ[L] D) :
    TensorProduct L L' D ≃ₐ[L'] (P2 L' ⧸ Ideal.span ({f'} : Set (P2 L'))) := by
  let IL : Ideal (P2 L) := Ideal.span {f}
  let IL' : Ideal (P2 L') := Ideal.span {f'}
  let Q' := P2 L' ⧸ IL'
  let z_D : D := e0 (Ideal.Quotient.mk IL (MvPolynomial.X 0))
  let t_D : D := e0 (Ideal.Quotient.mk IL (MvPolynomial.X 1))
  have hmap_aeval : ∀ P : P2 L,
      MvPolynomial.aeval ![(1 : L') ⊗ₜ[L] z_D, (1 : L') ⊗ₜ[L] t_D] (MvPolynomial.map (algebraMap L L') P) =
      (1 : L') ⊗ₜ[L] e0 (Ideal.Quotient.mk IL P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
      have hC2 : e0 (Ideal.Quotient.mk IL (MvPolynomial.C r)) = algebraMap L D r := by
        change e0 (algebraMap L (P2 L ⧸ IL) r) = _; exact e0.commutes r
      rw [hC2]
      change (algebraMap L L' r) ⊗ₜ[L] (1 : D) = (1 : L') ⊗ₜ[L] (algebraMap L D r)
      rw [← mul_one (algebraMap L L' r), ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
    | add p₁ p₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add] at h₁ h₂ ⊢; rw [h₁, h₂]
    | mul_X p₁ j h₁ =>
      simp only [map_mul, MvPolynomial.map_X] at h₁ ⊢
      rw [h₁]
      match j with
      | 0 =>
        rw [MvPolynomial.aeval_X, Matrix.cons_val_zero, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      | 1 =>
        rw [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  let toTP : Q' →ₐ[L'] TensorProduct L L' D :=
    Ideal.Quotient.liftₐ IL'
      (MvPolynomial.aeval ![(1 : L') ⊗ₜ[L] z_D, (1 : L') ⊗ₜ[L] t_D])
      (fun x hx => by
        rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
        rw [map_mul, ← hf', hmap_aeval f]
        have hf0 : Ideal.Quotient.mk IL f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
        rw [hf0, map_zero, TensorProduct.tmul_zero, zero_mul])
  let mapQ : (P2 L ⧸ IL) →ₐ[L] Q' :=
    Ideal.Quotient.liftₐ IL
      ((Ideal.Quotient.mkₐ L' IL' |>.restrictScalars L).comp
        ((MvPolynomial.mapAlgHom (Algebra.ofId L L')).restrictScalars L))
      (fun x hx => by
        rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
        rw [map_mul]; convert zero_mul _
        change Ideal.Quotient.mk IL' (MvPolynomial.map (algebraMap L L') f) = 0
        rw [hf', Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl)
  let fromTP_L : TensorProduct L L' D →ₐ[L] Q' :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId L' Q').restrictScalars L)
      (mapQ.comp e0.symm.toAlgHom)
      (fun _ _ => Commute.all _ _)
  let fromTP : TensorProduct L L' D →ₐ[L'] Q' :=
    { toRingHom := fromTP_L.toRingHom
      commutes' := fun c => by
        change fromTP_L (c ⊗ₜ[L] (1 : D)) = algebraMap L' Q' c
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl }
  have hcomp_lr : ∀ x : Q', fromTP (toTP x) = x := by
    intro x; obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction P using MvPolynomial.induction_on with
    | C c =>
      change fromTP (toTP (algebraMap L' Q' c)) = algebraMap L' Q' c
      rw [AlgHom.commutes, AlgHom.commutes]
    | add p₁ p₂ h₁ h₂ => simp only [map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
    | mul_X p₁ j h₁ =>
      simp only [map_mul] at h₁ ⊢; rw [h₁]; congr 1
      match j with
      | 0 =>
        have hX0 : toTP (Ideal.Quotient.mk IL' (MvPolynomial.X 0)) = (1 : L') ⊗ₜ[L] z_D := by
          change MvPolynomial.aeval ![(1 : L') ⊗ₜ[L] z_D, (1 : L') ⊗ₜ[L] t_D] (MvPolynomial.X 0) = _; simp
        rw [hX0]
        change fromTP_L ((1 : L') ⊗ₜ[L] z_D) = _
        rw [Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, map_one, one_mul,
          AlgHom.comp_apply, AlgEquiv.coe_algHom, e0.symm_apply_apply]
        change Ideal.Quotient.mk IL' (MvPolynomial.map (algebraMap L L') (MvPolynomial.X 0)) = _
        rw [MvPolynomial.map_X]
      | 1 =>
        have hX1 : toTP (Ideal.Quotient.mk IL' (MvPolynomial.X 1)) = (1 : L') ⊗ₜ[L] t_D := by
          change MvPolynomial.aeval ![(1 : L') ⊗ₜ[L] z_D, (1 : L') ⊗ₜ[L] t_D] (MvPolynomial.X 1) = _; simp
        rw [hX1]
        change fromTP_L ((1 : L') ⊗ₜ[L] t_D) = _
        rw [Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, map_one, one_mul,
          AlgHom.comp_apply, AlgEquiv.coe_algHom, e0.symm_apply_apply]
        change Ideal.Quotient.mk IL' (MvPolynomial.map (algebraMap L L') (MvPolynomial.X 1)) = _
        rw [MvPolynomial.map_X]
  have hcomp_rl : ∀ y : TensorProduct L L' D, toTP (fromTP y) = y := by
    intro y; induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      obtain ⟨q, rfl⟩ := e0.surjective d
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
      have h1 : fromTP (c ⊗ₜ[L] e0 (Ideal.Quotient.mk IL P)) =
          algebraMap L' Q' c * Ideal.Quotient.mk IL' (MvPolynomial.map (algebraMap L L') P) := by
        change fromTP_L (c ⊗ₜ[L] e0 (Ideal.Quotient.mk IL P)) = _
        rw [Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, AlgHom.comp_apply,
          AlgEquiv.coe_algHom, e0.symm_apply_apply]
        rfl
      rw [h1, map_mul, AlgHom.commutes]
      have h2 : toTP (Ideal.Quotient.mk IL' (MvPolynomial.map (algebraMap L L') P)) =
          (1 : L') ⊗ₜ[L] e0 (Ideal.Quotient.mk IL P) := hmap_aeval P
      rw [h2]
      change (c ⊗ₜ[L] (1 : D)) * ((1 : L') ⊗ₜ[L] e0 (Ideal.Quotient.mk IL P)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact AlgEquiv.ofAlgHom fromTP toTP (AlgHom.ext hcomp_lr) (AlgHom.ext hcomp_rl)

/-- Helper for Case A: 1, bZ, ..., bZ^(p-1) are linearly independent over K[bX, bC(Z^p+T^(p+1)), bT]. -/
lemma homRing_bZ_algIndep_caseA (hp : 1 < p)
    (f : Fin p → MvPolynomial (Fin 3) K)
    (hsum : (∑ i : Fin p,
      MvPolynomial.aeval ![bX K p, bC K p (MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1)), bT K p] (f i) *
        bZ K p ^ (i : ℕ)) = 0) :
    ∀ i : Fin p, f i = 0 := by
  classical
  let w0 : P2 K := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1)
  let bW : HomRing K p := bC K p w0
  change (∑ i : Fin p, MvPolynomial.aeval ![bX K p, bW, bT K p] (f i) * bZ K p ^ (i : ℕ)) = 0 at hsum
  -- Pass to `Ambient K`: look at `X`-coefficient `k`, where `bX = T 1` and `bW, bT, bZ` have `X`-degree `0`!
  have hval := congrArg Subtype.val hsum
  rw [Subalgebra.coe_zero, AddSubmonoidClass.coe_finsetSum] at hval
  have hcomp_i : ∀ i : Fin p,
      ((MvPolynomial.aeval ![bX K p, bW, bT K p] (f i) * bZ K p ^ (i : ℕ) : HomRing K p) : Ambient K) =
      MvPolynomial.aeval ![genX K, LaurentPolynomial.C w0, genT K] (f i) * genZ K ^ (i : ℕ) := by
    intro i
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    congr 1
    have hc : (HomSubalg K p).val.comp (MvPolynomial.aeval ![bX K p, bW, bT K p]) =
        MvPolynomial.aeval ![genX K, LaurentPolynomial.C w0, genT K] := by
      apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp [bX, bW, bC, bT]
    exact AlgHom.congr_fun hc (f i)
  simp_rw [hcomp_i] at hval
  -- For each `k : ℕ`, the `X`-degree `k` coefficient of `hval` in `P2 K` is
  -- `∑ i : Fin p, (∑_{e 0 = k} C (f i).coeff e * w0^(e 1) * T^(e 2)) * Z^i = 0`!
  intro i₀
  by_contra hfi_ne
  obtain ⟨e₀, he₀⟩ := MvPolynomial.support_nonempty.mpr hfi_ne
  let k₀ : ℕ := e₀ 0
  have hck := congrArg (fun r : Ambient K => r.coeff (k₀ : ℤ)) hval
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, coeff_sum_A] at hck
  -- Define `g i ∈ P2 K` = coefficient of `T k₀` in `aeval ![genX, C w0, genT] (f i)`
  let g (i : Fin p) : P2 K :=
    ∑ e ∈ (f i).support.filter (fun e => e 0 = k₀),
      MvPolynomial.C ((f i).coeff e) * w0 ^ (e 1) * MvPolynomial.X 1 ^ (e 2)
  have hck_eq : ∀ i : Fin p,
      (MvPolynomial.aeval ![genX K, LaurentPolynomial.C w0, genT K] (f i) * genZ K ^ (i : ℕ)).coeff (k₀ : ℤ) =
      g i * MvPolynomial.X 0 ^ (i : ℕ) := by
    intro i
    rw [MvPolynomial.as_sum (f i), map_sum, Finset.sum_mul, coeff_sum_A, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hmon : MvPolynomial.aeval ![genX K, LaurentPolynomial.C w0, genT K] (MvPolynomial.monomial e ((f i).coeff e)) *
          genZ K ^ (i : ℕ) =
        singleT K (e 0 : ℤ) (MvPolynomial.C ((f i).coeff e) * w0 ^ (e 1) * MvPolynomial.X 1 ^ (e 2) *
          MvPolynomial.X 0 ^ (i : ℕ)) := by
      rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.aeval_C,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        genX, genZ, genT, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
      have hC : (algebraMap K (Ambient K)) ((f i).coeff e) = LaurentPolynomial.C (MvPolynomial.C ((f i).coeff e)) := rfl
      have hT1 : (LaurentPolynomial.T ((e 0 : ℤ) * 1) : Ambient K) = LaurentPolynomial.T (e 0 : ℤ) := by rw [mul_one]
      rw [hC, hT1]; ring
    rw [hmon, coeff_singleT]
    by_cases he0 : e 0 = k₀
    · rw [if_pos (by exact_mod_cast he0), if_pos he0]
    · rw [if_neg (by intro h; exact he0 (by exact_mod_cast h)), if_neg he0]
  simp_rw [hck_eq] at hck
  -- Notice every monomial in `g i` has `Z`-degree divisible by `p` (since `w0 = Z^p + T^(p+1)`)!
  have hg_mod : ∀ (i : Fin p) (d : Fin 2 →₀ ℕ), (g i).coeff d ≠ 0 → p ∣ d 0 := by
    intro i d hd
    have hw0_pow_mod : ∀ n : ℕ, ∀ d' : Fin 2 →₀ ℕ, (w0 ^ n).coeff d' ≠ 0 → p ∣ d' 0 := by
      intro n
      induction n with
      | zero =>
        intro d' hd'; rw [pow_zero, MvPolynomial.coeff_one] at hd'
        by_cases h0 : (0 : Fin 2 →₀ ℕ) = d'
        · subst h0; simp
        · rw [if_neg h0] at hd'; exact absurd rfl hd'
      | succ n ihn =>
        intro d' hd'; rw [pow_succ', MvPolynomial.coeff_mul] at hd'
        obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd'
        have has : a₁ + a₂ = d' := by simpa using ha12
        have h2 := ihn a₂ (right_ne_zero_of_mul hpr)
        have h1 : p ∣ a₁ 0 := by
          have hne1 := left_ne_zero_of_mul hpr
          simp only [w0, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow] at hne1
          by_cases hc1 : Finsupp.single (0 : Fin 2) p = a₁
          · subst hc1; simp
          · by_cases hc2 : Finsupp.single (1 : Fin 2) (p + 1) = a₁
            · subst hc2; simp
            · rw [if_neg hc1, if_neg hc2, add_zero] at hne1; exact absurd rfl hne1
        have : d' 0 = a₁ 0 + a₂ 0 := by rw [← has]; rfl
        rw [this]; exact dvd_add h1 h2
    simp only [g, MvPolynomial.coeff_sum] at hd
    obtain ⟨e, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    rw [mul_assoc, MvPolynomial.coeff_C_mul] at hne
    have hne' := right_ne_zero_of_mul hne
    rw [MvPolynomial.coeff_mul] at hne'
    obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have has : a₁ + a₂ = d := by simpa using ha12
    have h1 := hw0_pow_mod (e 1) a₁ (left_ne_zero_of_mul hpr)
    have h2 : a₂ 0 = 0 := by
      have hne2 := right_ne_zero_of_mul hpr
      rw [MvPolynomial.coeff_X_pow] at hne2
      split_ifs at hne2 with h
      · subst h; simp
      · exact absurd rfl hne2
    have : d 0 = a₁ 0 + a₂ 0 := by rw [← has]; rfl
    rw [this, h2, add_zero]; exact h1
  -- Therefore `g i₀ = 0`!
  have hgi0_zero : g i₀ = 0 := by
    ext d
    rw [MvPolynomial.coeff_zero]
    by_contra hd_ne
    have hp_dvd_d0 : p ∣ d 0 := hg_mod i₀ d hd_ne
    let d' : Fin 2 →₀ ℕ := d + Finsupp.single 0 (i₀ : ℕ)
    have hcd := congrArg (fun r : P2 K => r.coeff d') hck
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcd
    have hterm_d : ∀ i : Fin p,
        (g i * MvPolynomial.X 0 ^ (i : ℕ)).coeff d' =
        if i = i₀ then (g i₀).coeff d else 0 := by
      intro i
      have hX : (MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) : P2 K) = MvPolynomial.monomial (Finsupp.single 0 (i : ℕ)) 1 := by
        rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; simp
      rw [mul_comm, hX, MvPolynomial.coeff_monomial_mul']
      by_cases hi : i = i₀
      · subst hi
        have hle : Finsupp.single (0 : Fin 2) (i : ℕ) ≤ d' := by
          intro j; fin_cases j <;> simp [d']
        rw [if_pos hle, if_pos rfl, one_mul, show d' - Finsupp.single 0 (i : ℕ) = d by
          simp [d']]
      · rw [if_neg hi]
        split_ifs with hle
        · rw [one_mul]; by_contra hne
          have hp_dvd := hg_mod i (d' - Finsupp.single (0 : Fin 2) (i : ℕ)) hne
          have h0_eq : (d' - Finsupp.single (0 : Fin 2) (i : ℕ)) 0 + (i : ℕ) = d 0 + (i₀ : ℕ) := by
            have hle0 : (i : ℕ) ≤ d' 0 := by simpa using hle 0
            simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, d', Finsupp.coe_add, Pi.add_apply] at hle0 ⊢
            omega
          have hmod : (i : ℕ) % p = (i₀ : ℕ) % p := by
            obtain ⟨a, ha⟩ := hp_dvd
            obtain ⟨b, hb⟩ := hp_dvd_d0
            rw [ha, hb] at h0_eq
            have := congrArg (· % p) h0_eq
            simp [Nat.add_mod] at this
            exact this
          rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i₀.isLt] at hmod
          exact hi (Fin.ext hmod)
        · rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm_d i), Finset.sum_eq_single i₀] at hcd
    · rw [if_pos rfl] at hcd; exact hd_ne hcd
    · intro i _ hne; rw [if_neg hne]
    · intro hnm; exact absurd (Finset.mem_univ i₀) hnm
  -- Now `g i₀ = 0` contradicts `e₀ ∈ (f i₀).support` with `e₀ 0 = k₀`!
  -- Look at the max `e 1` among `e ∈ (f i₀).support` with `e 0 = k₀`, and look at `Z`-degree `jmax * p`!
  let S0 : Finset (Fin 3 →₀ ℕ) := (f i₀).support.filter (fun e => e 0 = k₀)
  have hS0_ne : S0.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨he₀, rfl⟩⟩
  let jset : Finset ℕ := S0.image fun e => e 1
  let jmax : ℕ := jset.max' (hS0_ne.image _)
  obtain ⟨e₁, he₁_mem, he₁_1⟩ := Finset.mem_image.mp (Finset.max'_mem jset (hS0_ne.image _))
  let d₁ : Fin 2 →₀ ℕ := Finsupp.single 0 (jmax * p) + Finsupp.single 1 (e₁ 2)
  have hcd1 := congrArg (fun r : P2 K => r.coeff d₁) hgi0_zero
  rw [MvPolynomial.coeff_zero] at hcd1
  simp only [g, MvPolynomial.coeff_sum] at hcd1
  -- For any `n`, every monomial in `w0^n` has `Z`-degree `≤ n * p`, with unique max-`Z`-degree term `Z^(n * p)`!
  have hw0_Zdeg : ∀ n : ℕ, ∀ d : Fin 2 →₀ ℕ, (w0 ^ n).coeff d ≠ 0 → d 0 ≤ n * p := by
    intro n; induction n with
    | zero =>
      intro d hd; rw [pow_zero, MvPolynomial.coeff_one] at hd
      by_cases h0 : (0 : Fin 2 →₀ ℕ) = d
      · subst h0; simp
      · rw [if_neg h0] at hd; exact absurd rfl hd
    | succ n ih =>
      intro d hd; rw [pow_succ', MvPolynomial.coeff_mul] at hd
      obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
      have has : a₁ + a₂ = d := by simpa using ha12
      have h2 := ih a₂ (right_ne_zero_of_mul hpr)
      have h1 : a₁ 0 ≤ p := by
        have hne1 := left_ne_zero_of_mul hpr
        simp only [w0, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow] at hne1
        by_cases hc1 : Finsupp.single (0 : Fin 2) p = a₁; · subst hc1; simp
        · by_cases hc2 : Finsupp.single (1 : Fin 2) (p + 1) = a₁; · subst hc2; simp
          · rw [if_neg hc1, if_neg hc2, add_zero] at hne1; exact absurd rfl hne1
      have : d 0 = a₁ 0 + a₂ 0 := by rw [← has]; rfl
      rw [this]; nlinarith
  have hw0_Ztop : ∀ n : ℕ, ∀ d : Fin 2 →₀ ℕ, d 0 = n * p →
      (w0 ^ n).coeff d = if d = Finsupp.single 0 (n * p) then 1 else 0 := by
    intro n; induction n with
    | zero =>
      intro d _; simp only [pow_zero, zero_mul, Finsupp.single_zero, MvPolynomial.coeff_one]
      by_cases h0 : (0 : Fin 2 →₀ ℕ) = d
      · subst h0; simp
      · rw [if_neg h0, if_neg (Ne.symm h0)]
    | succ n ih =>
      intro d hd0
      rw [pow_succ', MvPolynomial.coeff_mul]
      have hsub : Finsupp.single (0 : Fin 2) p ≤ d := by
        intro j; fin_cases j
        · simp [hd0]; nlinarith
        · simp
      have hmem : (Finsupp.single (0 : Fin 2) p, d - Finsupp.single 0 p) ∈ Finset.HasAntidiagonal.antidiagonal d :=
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_tsub_cancel_of_le hsub)
      rw [Finset.sum_eq_single (Finsupp.single (0 : Fin 2) p, d - Finsupp.single 0 p)]
      · have hw1 : w0.coeff (Finsupp.single 0 p) = 1 := by
          simp only [w0, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow]
          have hne : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 0 p := by
            intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; omega
          rw [if_neg hne]; simp
        have hd2 : (d - Finsupp.single (0 : Fin 2) p) 0 = n * p := by
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, hd0]
          have : (n + 1) * p = n * p + p := by ring
          omega
        rw [hw1, one_mul, ih _ hd2]
        by_cases hdeq : d = Finsupp.single 0 ((n + 1) * p)
        · subst hdeq
          have hse : Finsupp.single (0 : Fin 2) ((n + 1) * p) - Finsupp.single 0 p = Finsupp.single 0 (n * p) := by
            ext j; fin_cases j
            · simp; ring_nf; omega
            · simp
          rw [if_pos hse, if_pos rfl]
        · rw [if_neg hdeq, if_neg]
          intro hse; apply hdeq
          have hadd := congrArg (fun u => Finsupp.single (0 : Fin 2) p + u) hse
          rw [add_tsub_cancel_of_le hsub] at hadd
          rw [hadd]; ext j; fin_cases j
          · simp; ring
          · simp
      · rintro ⟨a₁, a₂⟩ ha12 hne
        have has : a₁ + a₂ = d := by simpa using ha12
        by_cases h1 : w0.coeff a₁ = 0; · rw [h1, zero_mul]
        · by_cases h2 : (w0 ^ n).coeff a₂ = 0; · rw [h2, mul_zero]
          · exfalso
            have ha2 := hw0_Zdeg n a₂ h2
            have ha1_cases : a₁ = Finsupp.single 0 p ∨ a₁ = Finsupp.single 1 (p + 1) := by
              simp only [w0, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow] at h1
              by_cases hc1 : Finsupp.single (0 : Fin 2) p = a₁; · exact Or.inl hc1.symm
              · by_cases hc2 : Finsupp.single (1 : Fin 2) (p + 1) = a₁; · exact Or.inr hc2.symm
                · rw [if_neg hc1, if_neg hc2, add_zero] at h1; exact absurd rfl h1
            have hs0 : a₁ 0 + a₂ 0 = d 0 := by rw [← has]; rfl
            rcases ha1_cases with rfl | rfl
            · apply hne; exact Prod.ext rfl (by rw [← has, add_tsub_cancel_left])
            · simp at hs0; nlinarith
      · intro hnm; exact absurd hmem hnm
  have hterm_e : ∀ e ∈ S0,
      (MvPolynomial.C ((f i₀).coeff e) * w0 ^ (e 1) * MvPolynomial.X 1 ^ (e 2)).coeff d₁ =
      if e = e₁ then (f i₀).coeff e₁ else 0 := by
    intro e he
    have he1_le : e 1 ≤ jmax := Finset.le_max' jset (e 1) (Finset.mem_image_of_mem _ he)
    rw [mul_assoc, MvPolynomial.coeff_C_mul]
    have hX1 : (MvPolynomial.X (1 : Fin 2) ^ (e 2) : P2 K) = MvPolynomial.monomial (Finsupp.single 1 (e 2)) 1 := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; simp
    rw [mul_comm (w0 ^ (e 1)), hX1, MvPolynomial.coeff_monomial_mul']
    by_cases heq : e = e₁
    · subst heq
      have hle : Finsupp.single (1 : Fin 2) (e 2) ≤ d₁ := by
        intro j; fin_cases j <;> simp [d₁]
      rw [if_pos hle, if_pos rfl, one_mul, he₁_1,
        show d₁ - Finsupp.single 1 (e 2) = Finsupp.single 0 (jmax * p) by ext j; fin_cases j <;> simp [d₁],
        hw0_Ztop jmax _ (by simp), if_pos rfl, mul_one]
    · rw [if_neg heq]
      split_ifs with hle
      · rw [one_mul]
        by_cases he1_eq : e 1 = jmax
        · rw [he1_eq, hw0_Ztop jmax _ (by simp [d₁]), if_neg]
          · simp
          · intro hsub_eq
            apply heq
            have he2_eq : e 2 = e₁ 2 := by
              have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) hsub_eq
              have hle1 : e 2 ≤ d₁ 1 := by simpa using hle 1
              simp [d₁] at this hle1; omega
            have he0_eq : e 0 = e₁ 0 := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he₁_mem).2.symm
            ext j; fin_cases j
            · exact he0_eq
            · exact he1_eq.trans he₁_1.symm
            · exact he2_eq
        · have hlt : e 1 < jmax := by omega
          have hc0 : (w0 ^ (e 1)).coeff (d₁ - Finsupp.single 1 (e 2)) = 0 := by
            by_contra hne
            have := hw0_Zdeg (e 1) _ hne
            simp [d₁] at this; nlinarith
          rw [hc0, mul_zero]
      · rw [mul_zero]
  change ∑ e ∈ S0, _ = 0 at hcd1
  rw [Finset.sum_congr rfl hterm_e, Finset.sum_eq_single e₁] at hcd1
  · rw [if_pos rfl] at hcd1
    exact MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp he₁_mem).1 hcd1
  · intro e _ hne; rw [if_neg hne]
  · intro hnm; exact absurd he₁_mem hnm

/-- Helper: coefficient of `MvPolynomial.rename ![0, 1] g0` in `MvPolynomial (Fin 3) K`. -/
lemma mvPoly_rename01_coeff (g0 : P2 K) (m : Fin 3 →₀ ℕ) :
    (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) g0).coeff m =
    if m 2 = 0 then g0.coeff (Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)) else 0 := by
  induction g0 using MvPolynomial.induction_on' with
  | add a b ha hb => simp [map_add, ha, hb]; split_ifs <;> simp
  | monomial u c =>
    rw [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hm2 : m 2 = 0
    · rw [if_pos hm2]
      have hiff : Finsupp.mapDomain (![0, 1] : Fin 2 → Fin 3) u = m ↔
          u = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
        constructor
        · intro h; ext j; fin_cases j
          · have := congrArg (fun v : Fin 3 →₀ ℕ => v ((![0, 1] : Fin 2 → Fin 3) 0)) h
            rw [Finsupp.mapDomain_apply (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)] at this
            simpa using this
          · have := congrArg (fun v : Fin 3 →₀ ℕ => v ((![0, 1] : Fin 2 → Fin 3) 1)) h
            rw [Finsupp.mapDomain_apply (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)] at this
            simpa using this
        · intro h; subst h; ext j; fin_cases j
          · simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
          · simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
          · simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single, hm2]
      by_cases hu : u = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)
      · rw [if_pos (hiff.mpr hu), if_pos hu]
      · rw [if_neg (fun h => hu (hiff.mp h)), if_neg hu]
    · rw [if_neg hm2, if_neg]
      intro h; apply hm2
      have := congrArg (fun v : Fin 3 →₀ ℕ => v 2) h
      rw [← this]; simp [Finsupp.mapDomain, Finsupp.sum]

set_option maxHeartbeats 400000 in
/-- Final base-change step of Case A, abstracted over `L, D, e0_equiv` so `whnf` never unfolds `Localization`. -/
lemma no_expMap_caseA_finish {L : Type*} [Field L] (p : ℕ) [CharP L p] [hp_prime : Fact p.Prime]
    {D : Type*} [CommRing D] [Algebra L D] (w_L : L)
    (e0_equiv : (P2 L ⧸ Ideal.span ({MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L} : Set (P2 L))) ≃ₐ[L] D)
    (φ_L : ExpMap L D) (hφ_L_nt : φ_L.IsNontrivial) : False := by
  let L' := AlgebraicClosure L
  have : CharP L' p := charP_of_injective_algebraMap (algebraMap L L').injective p
  have : CharP (P2 L') p := charP_of_injective_algebraMap (MvPolynomial.C_injective (Fin 2) L') p
  let w_L' : L' := algebraMap L L' w_L
  let relL : P2 L := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L
  let relL' : P2 L' := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L'
  let IL' : Ideal (P2 L') := Ideal.span {relL'}
  let Q' := P2 L' ⧸ IL'
  have hrel_map : MvPolynomial.map (algebraMap L L') relL = relL' := by
    simp only [relL, relL', w_L', map_sub, map_add, map_pow, MvPolynomial.map_X, MvPolynomial.map_C]
  let e' : TensorProduct L L' D ≃ₐ[L'] Q' :=
    quot_baseChange_equiv (L' := L') relL relL' hrel_map e0_equiv
  let φQ : ExpMap L' Q' := (φ_L.baseChange (L' := L')).compAlgEquiv e'
  have hφQ_nt : φQ.IsNontrivial := by
    obtain ⟨x, hx⟩ := φ_L.baseChange_isNontrivial (L' := L') hφ_L_nt
    refine ⟨e' x, fun hinv => hx ?_⟩
    change Polynomial.map e'.toRingHom ((φ_L.baseChange (L' := L')) (e'.symm (e' x))) =
      Polynomial.C (e' x) at hinv
    rw [e'.symm_apply_apply] at hinv
    change (φ_L.baseChange (L' := L')) x = Polynomial.C x
    ext n
    have hn := congrArg (fun P => P.coeff n) hinv
    rw [Polynomial.coeff_map, Polynomial.coeff_C] at hn
    rw [Polynomial.coeff_C]
    apply e'.injective
    split_ifs at hn ⊢
    · exact hn
    · rw [map_zero]; exact hn
  exact no_expMap_singular_Zp_Tp1 p w_L' φQ hφQ_nt

set_option maxHeartbeats 600000 in
/-- Helper: Case A of Lemma 3.5 — no non-trivial `ExpMap` on `B_K` fixes `bY` and `bC (Z^p + T^(p+1))`. -/
lemma no_expMap_caseA [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (HomRing K p)) (hnt : φ.IsNontrivial)
    (hy : bY K p ∈ φ.invSubalg)
    (hw : bC K p (MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1)) ∈ φ.invSubalg) : False := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  let w0 : P2 K := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1)
  let bW : HomRing K p := bC K p w0
  -- Step 1: `bX ∈ φ.invSubalg` since `bX^2 * bY = -bW^p`
  have hw0_pow : w0 ^ p = gHomPoly K p := by
    simp only [w0, gHomPoly, add_pow_char, ← pow_mul, sq, mul_comm (p + 1) p]
  have hrel : bX K p ^ 2 * bY K p = -(bW ^ p) := by
    apply Subtype.ext
    change genX K ^ 2 * genYB K p = -(LaurentPolynomial.C w0 ^ p)
    rw [← map_pow, hw0_pow, genX, genYB, LaurentPolynomial.T_pow]
    have hT0 : (LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) : Ambient K) * LaurentPolynomial.T (-2) = 1 := by
      rw [← LaurentPolynomial.T_add]; norm_num
    calc LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) * (LaurentPolynomial.C (-gHomPoly K p) * LaurentPolynomial.T (-2))
        = LaurentPolynomial.C (-gHomPoly K p) * (LaurentPolynomial.T ((2 : ℕ) * (1 : ℤ)) * LaurentPolynomial.T (-2)) := by ring
      _ = -LaurentPolynomial.C (gHomPoly K p) := by rw [hT0, mul_one, map_neg]
  have hx_inv : bX K p ∈ φ.invSubalg := by
    have h1 : bX K p * (bX K p * bY K p) ∈ φ.invSubalg := by
      rw [← mul_assoc, ← sq, hrel]; exact neg_mem (pow_mem hw p)
    have hne : bX K p * (bX K p * bY K p) ≠ 0 := by
      rw [← mul_assoc, ← sq, hrel]; intro h0
      have h2 := congrArg (fun r : HomRing K p => (r : Ambient K).coeff 0) h0
      change -(LaurentPolynomial.C w0 ^ p).coeff 0 = 0 at h2
      rw [← map_pow, hw0_pow] at h2
      have hC0 : (LaurentPolynomial.C (gHomPoly K p) : Ambient K).coeff 0 = gHomPoly K p := by
        change (singleT K 0 (gHomPoly K p)).coeff 0 = _; simp [coeff_singleT]
      rw [hC0] at h2; exact gHomPoly_ne_zero K p hp (neg_eq_zero.mp h2)
    exact (φ.mem_invSubalg_of_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne) h1).1
  -- Step 2: `ι_xw : P2 K →ₐ[K] HomRing K p` (`0 ↦ bX, 1 ↦ bW`) is injective and lands in `φ.invSubalg`
  let ι_xw : P2 K →ₐ[K] HomRing K p := MvPolynomial.aeval ![bX K p, bW]
  have hι_inv : ∀ r : P2 K, ι_xw r ∈ φ.invSubalg := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact φ.invSubalg.algebraMap_mem c
    | add r₁ r₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X r₁ j h₁ =>
      rw [map_mul, MvPolynomial.aeval_X]
      fin_cases j
      · exact mul_mem h₁ hx_inv
      · exact mul_mem h₁ hw
  have hZ_indep : ∀ (f : Fin p → MvPolynomial (Fin 3) K),
      (∑ i : Fin p, MvPolynomial.aeval ![bX K p, bW, bT K p] (f i) * bZ K p ^ (i : ℕ)) = 0 →
      ∀ i : Fin p, f i = 0 := homRing_bZ_algIndep_caseA K p hp
  -- From `hZ_indep`, `ι_xw : P2 K →ₐ[K] HomRing K p` is injective!
  have hι_inj : Function.Injective ι_xw := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    let f0 : Fin p → MvPolynomial (Fin 3) K := fun i =>
      if (i : ℕ) = 0 then MvPolynomial.rename ![0, 1] r else 0
    have hsum : (∑ i : Fin p, MvPolynomial.aeval ![bX K p, bW, bT K p] (f0 i) * bZ K p ^ (i : ℕ)) = 0 := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp only [f0, ↓reduceIte, pow_zero, mul_one, MvPolynomial.aeval_rename]
        have hcomp : (![bX K p, bW, bT K p] ∘ ![0, 1]) = ![bX K p, bW] := by
          ext j; fin_cases j <;> rfl
        rw [hcomp]; exact hr
      · intro i _ hne
        have hne' : i ≠ 0 := fun h => hne (by subst h; rfl)
        simp [f0, hne']
      · intro hnm; exact absurd (Finset.mem_univ _) hnm
    have hf0 := hZ_indep f0 hsum ⟨0, by omega⟩
    simp only [f0, ↓reduceIte] at hf0
    have hinj_ren : Function.Injective (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) : P2 K → MvPolynomial (Fin 3) K) :=
      MvPolynomial.rename_injective _ (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    exact hinj_ren (by rw [hf0, map_zero])
  -- Step 3: Localize `φ` at `M = (nonZeroDivisors (P2 K)).map ι_xw` to get a non-trivial `ExpMap L D`,
  -- then base-change to `L' = AlgebraicClosure L`, and apply `no_expMap_of_singular_curve`!
  let M : Submonoid (HomRing K p) := (nonZeroDivisors (P2 K)).map ι_xw.toRingHom.toMonoidHom
  have hM_inv : ∀ m ∈ M, m ∈ φ.invSubalg := by
    rintro m ⟨r, _, rfl⟩; exact hι_inv r
  have hM_nz : ∀ m ∈ M, m ≠ 0 := by
    rintro m ⟨r, hr, rfl⟩ h0
    exact nonZeroDivisors.ne_zero hr (hι_inj (by rw [map_zero]; exact h0))
  let D := Localization M
  let L := FractionRing (P2 K)
  let iR : P2 K →+* D := (algebraMap (HomRing K p) D).comp ι_xw.toRingHom
  have hiR_unit : ∀ y : nonZeroDivisors (P2 K), IsUnit (iR y) := fun y =>
    IsLocalization.map_units D (⟨ι_xw y.1, y.1, y.2, rfl⟩ : M)
  let iL : L →+* D := IsLocalization.lift hiR_unit
  letI : Algebra L D := RingHom.toAlgebra iL
  -- Localize `φ` to `φ_K : ExpMap K D`, then upgrade to `φ_L : ExpMap L D`!
  let φ_K : ExpMap K D := φ.localize M hM_inv
  have hφ_K_nt : φ_K.IsNontrivial := by
    obtain ⟨b, hb⟩ := hnt
    refine ⟨algebraMap (HomRing K p) D b, fun hinv => hb ?_⟩
    have hinj : Function.Injective (algebraMap (HomRing K p) D) :=
      IsLocalization.injective D (fun m hm => mem_nonZeroDivisors_of_ne_zero (hM_nz m hm))
    have h1 : φ_K (algebraMap (HomRing K p) D b) = Polynomial.map (algebraMap (HomRing K p) D) (φ b) :=
      φ.localizeAlgHom_algebraMap M hM_inv b
    change φ_K (algebraMap (HomRing K p) D b) = Polynomial.C (algebraMap (HomRing K p) D b) at hinv
    rw [h1] at hinv
    change φ b = Polynomial.C b
    refine Polynomial.ext fun n => ?_
    have hn := congrArg (fun P => P.coeff n) hinv
    rw [Polynomial.coeff_map, Polynomial.coeff_C] at hn
    rw [Polynomial.coeff_C]
    apply hinj
    split_ifs at hn ⊢
    · exact hn
    · rw [map_zero]; exact hn
  have hφ_K_L : ∀ c : L, φ_K (algebraMap L D c) = Polynomial.C (algebraMap L D c) := by
    intro c
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := IsLocalization.surj (nonZeroDivisors (P2 K)) c
    have hr2_unit : IsUnit (Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₂.1))) :=
      (isUnit_iff_ne_zero.mpr (by
        rw [← map_zero (algebraMap (P2 K) L)]
        exact (IsFractionRing.injective (P2 K) L).ne (nonZeroDivisors.ne_zero r₂.2))).map
        (Polynomial.C.comp (algebraMap L D))
    have hpoly : ∀ r : P2 K, φ_K (algebraMap L D (algebraMap (P2 K) L r)) =
        Polynomial.C (algebraMap L D (algebraMap (P2 K) L r)) := by
      intro r
      have heq : algebraMap L D (algebraMap (P2 K) L r) = algebraMap (HomRing K p) D (ι_xw r) := by
        change iL (algebraMap (P2 K) L r) = _; exact IsLocalization.lift_eq hiR_unit r
      rw [heq]
      have h1 : φ_K (algebraMap (HomRing K p) D (ι_xw r)) =
          Polynomial.map (algebraMap (HomRing K p) D) (φ (ι_xw r)) :=
        φ.localizeAlgHom_algebraMap M hM_inv (ι_xw r)
      rw [h1, show φ (ι_xw r) = Polynomial.C (ι_xw r) from hι_inv r, Polynomial.map_C]
    have hmul : φ_K (algebraMap L D c) * Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₂.1)) =
        Polynomial.C (algebraMap L D c) * Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₂.1)) := by
      calc φ_K (algebraMap L D c) * Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₂.1))
          = φ_K (algebraMap L D (c * algebraMap (P2 K) L r₂.1)) := by rw [← hpoly r₂.1, ← map_mul, ← map_mul]
        _ = Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₁)) := by rw [hr, hpoly r₁]
        _ = Polynomial.C (algebraMap L D c) * Polynomial.C (algebraMap L D (algebraMap (P2 K) L r₂.1)) := by
            rw [← hr, map_mul, map_mul]
    exact hr2_unit.mul_right_cancel hmul
  let φ_L : ExpMap L D :=
    { toAlgHom := { toRingHom := φ_K.toAlgHom.toRingHom, commutes' := hφ_K_L }
      eval_zero := φ_K.eval_zero
      coassoc := φ_K.coassoc }
  have hφ_L_nt : φ_L.IsNontrivial := by
    obtain ⟨d, hd⟩ := hφ_K_nt; exact ⟨d, hd⟩
  -- Step 4: Present `D` as `P2 L ⧸ Ideal.span {Z^p + T^(p+1) - C w_L}`!
  let w_L : L := algebraMap (P2 K) L (MvPolynomial.X 1)
  let x_L : L := algebraMap (P2 K) L (MvPolynomial.X 0)
  have hx_L_ne : x_L ≠ 0 := by
    dsimp only [x_L]; rw [← map_zero (algebraMap (P2 K) L)]
    exact (IsFractionRing.injective (P2 K) L).ne (MvPolynomial.X_ne_zero 0)
  let z_D : D := algebraMap (HomRing K p) D (bZ K p)
  let t_D : D := algebraMap (HomRing K p) D (bT K p)
  let relL : P2 L := MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C w_L
  let IL : Ideal (P2 L) := Ideal.span {relL}
  let ψ0 : P2 L →ₐ[L] D := MvPolynomial.aeval ![z_D, t_D]
  have hrelL0 : ψ0 relL = 0 := by
    simp only [ψ0, relL, map_sub, map_add, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hw_eq : algebraMap L D w_L = algebraMap (HomRing K p) D bW := by
      change iL (algebraMap (P2 K) L (MvPolynomial.X 1)) = _
      rw [IsLocalization.lift_eq]; simp [iR, ι_xw]
    rw [hw_eq, ← map_pow, ← map_pow, ← map_add, ← map_sub]
    have hbw_eq : bZ K p ^ p + bT K p ^ (p + 1) - bW = 0 := by
      apply Subtype.ext
      change genZ K ^ p + genT K ^ (p + 1) - LaurentPolynomial.C w0 = 0
      rw [genZ, genT, ← map_pow, ← map_pow, ← map_add, ← map_sub]; simp [w0]
    rw [hbw_eq, map_zero]
  let e0 : (P2 L ⧸ IL) →ₐ[L] D :=
    Ideal.Quotient.liftₐ IL ψ0 (fun x hx => by
      rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx; rw [map_mul, hrelL0, zero_mul])
  -- Surjectivity of `e0`: `z_D, t_D, x_D, y_D` are all in the range of `e0`!
  have he0_surj : Function.Surjective e0 := by
    have hB_in : ∀ b : HomRing K p, algebraMap (HomRing K p) D b ∈ e0.range := by
      intro b
      obtain ⟨q, rfl⟩ := (homRing_quotEquiv K p hp).surjective b
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
      induction P using MvPolynomial.induction_on with
      | C c =>
        have hc : algebraMap (HomRing K p) D ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.C c))) =
            algebraMap L D (algebraMap (P2 K) L (MvPolynomial.C c)) := by
          rw [homRing_quotEquiv_mk_C]
          change algebraMap (HomRing K p) D (algebraMap K (HomRing K p) c) =
            iL (algebraMap (P2 K) L (MvPolynomial.C c))
          rw [IsLocalization.lift_eq]; simp [iR, ι_xw]
        rw [hc]; exact ⟨algebraMap L _ (algebraMap (P2 K) L (MvPolynomial.C c)), AlgHom.commutes e0 _⟩
      | add p₁ p₂ h₁ h₂ =>
        rw [map_add, map_add, map_add]; exact add_mem h₁ h₂
      | mul_X p₁ j h₁ =>
        rw [map_mul, map_mul, map_mul]
        refine mul_mem h₁ ?_
        match j with
        | 0 =>
          -- `bX = ι_xw (X 0)` is in `L`!
          have hx_eq : algebraMap (HomRing K p) D
              ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 0))) =
              algebraMap L D x_L := by
            rw [homRing_quotEquiv_mk_X0]
            change algebraMap (HomRing K p) D (bX K p) = iL (algebraMap (P2 K) L (MvPolynomial.X 0))
            rw [IsLocalization.lift_eq]; simp [iR, ι_xw]
          rw [hx_eq]; exact ⟨algebraMap L _ x_L, AlgHom.commutes e0 x_L⟩
        | 1 =>
          -- `bY = -bW^p / bX^2` is in `L`!
          have hy_eq : algebraMap (HomRing K p) D
              ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk _ (MvPolynomial.X 1))) =
              algebraMap L D (-(w_L ^ p) * (x_L ^ 2)⁻¹) := by
            rw [homRing_quotEquiv_mk_X1]
            have hx2_u : IsUnit (algebraMap L D (x_L ^ 2)) :=
              (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hx_L_ne)).map (algebraMap L D)
            apply hx2_u.mul_left_cancel
            rw [← map_mul, mul_comm (x_L ^ 2), mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hx_L_ne), mul_one]
            have hx_eq : algebraMap L D x_L = algebraMap (HomRing K p) D (bX K p) := by
              change iL (algebraMap (P2 K) L (MvPolynomial.X 0)) = _; rw [IsLocalization.lift_eq]; simp [iR, ι_xw]
            have hw_eq : algebraMap L D w_L = algebraMap (HomRing K p) D bW := by
              change iL (algebraMap (P2 K) L (MvPolynomial.X 1)) = _; rw [IsLocalization.lift_eq]; simp [iR, ι_xw]
            rw [map_pow, map_neg, map_pow, hx_eq, hw_eq, ← map_pow, ← map_mul, hrel, map_neg, map_pow]
          rw [hy_eq]; exact ⟨algebraMap L _ (-(w_L ^ p) * (x_L ^ 2)⁻¹), AlgHom.commutes e0 _⟩
        | 2 =>
          exact ⟨Ideal.Quotient.mk IL (MvPolynomial.X 0), by
            rw [homRing_quotEquiv_mk_X2]
            change MvPolynomial.aeval ![z_D, t_D] (MvPolynomial.X 0) = z_D; simp⟩
        | 3 =>
          exact ⟨Ideal.Quotient.mk IL (MvPolynomial.X 1), by
            rw [homRing_quotEquiv_mk_X3]
            change MvPolynomial.aeval ![z_D, t_D] (MvPolynomial.X 1) = t_D; simp⟩
    intro d
    induction d using Localization.induction_on with | H p_pair =>
    obtain ⟨r, m⟩ := p_pair
    obtain ⟨q, hq_nzd, hq_eq⟩ := m.2
    obtain ⟨u, hu⟩ := hB_in r
    let q_L : L := algebraMap (P2 K) L q
    have hq_L_ne : q_L ≠ 0 := by
      dsimp only [q_L]; rw [← map_zero (algebraMap (P2 K) L)]
      exact (IsFractionRing.injective (P2 K) L).ne (nonZeroDivisors.ne_zero hq_nzd)
    refine ⟨q_L⁻¹ • u, ?_⟩
    rw [map_smul, show e0 u = algebraMap (HomRing K p) D r from hu, Algebra.smul_def]
    have hm_eq : algebraMap L D q_L = algebraMap (HomRing K p) D m.1 := by
      change iL (algebraMap (P2 K) L q) = _; rw [IsLocalization.lift_eq]
      simp only [iR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact congrArg (algebraMap (HomRing K p) D) hq_eq
    have hq_u : IsUnit (algebraMap L D q_L) := (isUnit_iff_ne_zero.mpr hq_L_ne).map (algebraMap L D)
    apply hq_u.mul_left_cancel
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq_L_ne, map_one, one_mul, hm_eq,
      Localization.mk_eq_mk', IsLocalization.mk'_spec' D r m]
  -- Injectivity of `e0`: reduce mod `Z^p = w_L - T^(p+1)` and apply `hZ_indep`!
  have he0_inj : Function.Injective e0 := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    change ψ0 P = 0 at hq
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hred : ∀ P0 : P2 L, ∃ Q : P2 L, P0 - Q ∈ IL ∧ ∀ e ∈ Q.support, e 0 < p := by
      intro P0
      suffices ∀ M : ℕ, ∀ P1 : P2 L, (∀ e ∈ P1.support, e 0 ≤ M) →
          ∃ Q : P2 L, P1 - Q ∈ IL ∧ ∀ e ∈ Q.support, e 0 < p by
        exact this (P0.support.sup fun e => e 0) P0 (fun e he => Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 0) he)
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro P1 hP1
        by_cases hMp : M < p
        · exact ⟨P1, by simp, fun e he => lt_of_le_of_lt (hP1 e he) hMp⟩
        · let P_good : P2 L :=
            ∑ e ∈ P1.support.filter (fun e => e 0 < p), MvPolynomial.monomial e (P1.coeff e)
          let P_bad : P2 L :=
            ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p),
              MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) *
                (MvPolynomial.C w_L - MvPolynomial.X 1 ^ (p + 1))
          have hdiff : P1 - (P_good + P_bad) ∈ IL := by
            have hP1_split : P1 = P_good +
                ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p), MvPolynomial.monomial e (P1.coeff e) := by
              simp only [P_good]; rw [Finset.sum_filter_add_sum_filter_not]; exact MvPolynomial.as_sum P1
            have hsub : P1 - (P_good + P_bad) =
                ∑ e ∈ P1.support.filter (fun e => ¬ e 0 < p),
                  MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) * relL := by
              conv_lhs => rw [hP1_split]
              simp only [P_bad]; rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun e he => ?_
              have hge : p ≤ e 0 := by have := (Finset.mem_filter.mp he).2; omega
              have hms : MvPolynomial.monomial e (P1.coeff e) =
                  MvPolynomial.monomial (e - Finsupp.single 0 p) (P1.coeff e) * MvPolynomial.X 0 ^ p := by
                have hX : (MvPolynomial.X (0 : Fin 2) ^ p : P2 L) = MvPolynomial.monomial (Finsupp.single 0 p) 1 := by
                  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
                    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]; simp
                rw [hX, MvPolynomial.monomial_mul, mul_one]
                refine congrArg (fun s => MvPolynomial.monomial s (P1.coeff e)) ?_
                ext j; fin_cases j
                · simp; omega
                · simp
              rw [hms]; simp only [relL]; ring
            rw [hsub]; exact Ideal.sum_mem IL fun _ _ => Ideal.mul_mem_left IL _ (Ideal.subset_span rfl)
          have hP_bad_deg : ∀ e ∈ P_bad.support, e 0 ≤ M - p := by
            intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            simp only [P_bad, MvPolynomial.coeff_sum] at hne
            obtain ⟨d, hd, htn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            have hd_mem := (Finset.mem_filter.mp hd).1
            have hd_ge : p ≤ d 0 := by have := (Finset.mem_filter.mp hd).2; omega
            have hd_le : d 0 ≤ M := hP1 d hd_mem
            rw [MvPolynomial.coeff_mul] at htn
            obtain ⟨⟨a₁, a₂⟩, ha12, hpr⟩ := Finset.exists_ne_zero_of_sum_ne_zero htn
            have has : a₁ + a₂ = e := by simpa using ha12
            have ha1 : a₁ = d - Finsupp.single 0 p := by
              have h1 := left_ne_zero_of_mul hpr; rw [MvPolynomial.coeff_monomial] at h1
              split_ifs at h1 with h
              · exact h.symm
              · exact absurd rfl h1
            have ha2_0 : a₂ 0 = 0 := by
              have h2 := right_ne_zero_of_mul hpr
              rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, MvPolynomial.coeff_X_pow] at h2
              by_cases hc1 : (0 : Fin 2 →₀ ℕ) = a₂
              · subst hc1; simp
              · by_cases hc2 : Finsupp.single (1 : Fin 2) (p + 1) = a₂
                · subst hc2; simp
                · rw [if_neg hc1, if_neg hc2, sub_self] at h2; exact absurd rfl h2
            have he0 : e 0 = a₁ 0 + a₂ 0 := by rw [← has]; rfl
            rw [he0, ha1, ha2_0]; simp; omega
          obtain ⟨Q_bad, hQ_bad_I, hQ_bad_good⟩ := ih (M - p) (by omega) P_bad hP_bad_deg
          refine ⟨P_good + Q_bad, ?_, ?_⟩
          · have : P1 - (P_good + Q_bad) = (P1 - (P_good + P_bad)) + (P_bad - Q_bad) := by ring
            rw [this]; exact add_mem hdiff hQ_bad_I
          · intro e he
            have hne := MvPolynomial.mem_support_iff.mp he
            rw [MvPolynomial.coeff_add] at hne
            by_cases h1 : P_good.coeff e = 0
            · rw [h1, zero_add] at hne; exact hQ_bad_good e (MvPolynomial.mem_support_iff.mpr hne)
            · simp only [P_good, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at h1
              obtain ⟨d, hd, hdn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
              split_ifs at hdn with hde
              · subst hde; exact (Finset.mem_filter.mp hd).2
              · exact absurd rfl hdn
    obtain ⟨Q, hPQ_I, hQ_lt⟩ := hred P
    have hQ0 : ψ0 Q = 0 := by
      have hdiff0 : ψ0 (P - Q) = 0 := by
        rw [Ideal.mem_span_singleton] at hPQ_I
        obtain ⟨r, hr⟩ := hPQ_I; rw [hr, map_mul, hrelL0, zero_mul]
      rw [map_sub, hq, zero_sub, neg_eq_zero] at hdiff0; exact hdiff0
    suffices hQz : Q = 0 by rwa [hQz, sub_zero] at hPQ_I
    -- Clear denominators of `Q : P2 L` to get `Q_R : P2 (P2 K)` with `ψ0_R Q_R = 0` in `HomRing K p`, then apply `hZ_indep`!
    choose pair hpair using fun e : Fin 2 →₀ ℕ => IsLocalization.surj (nonZeroDivisors (P2 K)) (Q.coeff e)
    let num := fun e => (pair e).1
    let den := fun e => (pair e).2
    have hden_eq : ∀ e, Q.coeff e * algebraMap (P2 K) L (den e).1 = algebraMap (P2 K) L (num e) := fun e => hpair e
    let d_all : P2 K := ∏ e ∈ Q.support, (den e).1
    have hd_all_ne : d_all ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => nonZeroDivisors.ne_zero (den e).2
    let Q_R : P2 (P2 K) := ∑ e ∈ Q.support,
      MvPolynomial.monomial e (num e * ∏ e' ∈ Q.support.erase e, (den e').1)
    have hQR_map : Q_R.map (algebraMap (P2 K) L) = MvPolynomial.C (algebraMap (P2 K) L d_all) * Q := by
      ext e; rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
      simp only [Q_R, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      by_cases he : e ∈ Q.support
      · rw [Finset.sum_eq_single e]
        · rw [if_pos rfl, map_mul, map_prod]
          have hd_sp : d_all = (den e).1 * ∏ e' ∈ Q.support.erase e, (den e').1 :=
            (Finset.mul_prod_erase Q.support (fun e' => (den e').1) he).symm
          rw [hd_sp, map_mul, map_prod, mul_comm (algebraMap (P2 K) L (den e).1), mul_assoc,
            mul_comm (algebraMap (P2 K) L (den e).1), hden_eq e, mul_comm]
        · intro e' _ hne; rw [if_neg hne]
        · intro hnm; exact absurd he hnm
      · rw [Finset.sum_eq_zero (fun e' he' => if_neg (fun h : e' = e => he (h ▸ he'))), map_zero,
          MvPolynomial.notMem_support_iff.mp he, mul_zero]
    -- Group `Q_R` by `i = e 0 < p` into `f : Fin p → MvPolynomial (Fin 3) K`!
    let f : Fin p → MvPolynomial (Fin 3) K := fun i =>
      ∑ e ∈ Q.support.filter (fun e => e 0 = (i : ℕ)),
        MvPolynomial.rename ![0, 1] (Q_R.coeff e) * MvPolynomial.X 2 ^ (e 1)
    have hf_eval : (∑ i : Fin p, MvPolynomial.aeval ![bX K p, bW, bT K p] (f i) * bZ K p ^ (i : ℕ)) = 0 := by
      have hinj_D : Function.Injective (algebraMap (HomRing K p) D) :=
        IsLocalization.injective (M := M) D (fun x hx => mem_nonZeroDivisors_of_ne_zero (hM_nz x hx))
      apply hinj_D; rw [map_zero]
      have h1 : algebraMap (HomRing K p) D
          (∑ i : Fin p, MvPolynomial.aeval ![bX K p, bW, bT K p] (f i) * bZ K p ^ (i : ℕ)) =
          ψ0 (Q_R.map (algebraMap (P2 K) L)) := by
        rw [map_sum]
        have hQR_supp : Q_R.support ⊆ Q.support := by
          intro e he; by_contra hnm
          have h0 : Q_R.coeff e = 0 := by
            simp only [Q_R, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
            exact Finset.sum_eq_zero fun e' he' => if_neg (fun h : e' = e => hnm (h ▸ he'))
          exact MvPolynomial.mem_support_iff.mp he h0
        have hQR_sum : Q_R.map (algebraMap (P2 K) L) =
            ∑ e ∈ Q.support, MvPolynomial.monomial e (algebraMap (P2 K) L (Q_R.coeff e)) := by
          refine MvPolynomial.ext _ _ fun e => ?_
          rw [MvPolynomial.coeff_map]; symm; rw [MvPolynomial.coeff_sum]
          by_cases he : e ∈ Q.support
          · rw [Finset.sum_eq_single e]
            · simp
            · intro e' _ hne; simp [MvPolynomial.coeff_monomial, hne]
            · intro hnm; exact absurd he hnm
          · rw [Finset.sum_eq_zero (fun e' he' => by
              simp [MvPolynomial.coeff_monomial, show e' ≠ e from fun h => he (h ▸ he')])]
            have h0 : Q_R.coeff e = 0 := by
              by_contra hne; exact he (hQR_supp (MvPolynomial.mem_support_iff.mpr hne))
            rw [h0, map_zero]
        rw [hQR_sum, map_sum]
        have hpart : ∑ e ∈ Q.support, ψ0 (MvPolynomial.monomial e (algebraMap (P2 K) L (Q_R.coeff e))) =
            ∑ i : Fin p, ∑ e ∈ Q.support.filter (fun e => e 0 = (i : ℕ)),
              ψ0 (MvPolynomial.monomial e (algebraMap (P2 K) L (Q_R.coeff e))) := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e he => ?_
          rw [Finset.sum_eq_single ⟨e 0, hQ_lt e he⟩]
          · simp
          · intro i _ hne; rw [if_neg (fun h => hne (Fin.ext h.symm))]
          · intro hnm; exact absurd (Finset.mem_univ _) hnm
        rw [hpart]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [f, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun e he => ?_
        have he0 : e 0 = (i : ℕ) := (Finset.mem_filter.mp he).2
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, he0, map_mul, map_pow, MvPolynomial.aeval_X,
          MvPolynomial.aeval_rename]
        have hcomp : (![bX K p, bW, bT K p] ∘ ![0, 1]) = ![bX K p, bW] := by
          ext j; fin_cases j <;> rfl
        rw [hcomp]
        have hι_D : algebraMap (HomRing K p) D (ι_xw (Q_R.coeff e)) =
            algebraMap L D (algebraMap (P2 K) L (Q_R.coeff e)) := by
          change iR (Q_R.coeff e) = iL (algebraMap (P2 K) L (Q_R.coeff e))
          exact (IsLocalization.lift_eq hiR_unit _).symm
        change algebraMap (HomRing K p) D (ι_xw (Q_R.coeff e)) * t_D ^ (e 1) * z_D ^ (i : ℕ) =
          algebraMap L D (algebraMap (P2 K) L (Q_R.coeff e)) * (z_D ^ (i : ℕ) * t_D ^ (e 1))
        rw [hι_D]; ring
      rw [h1, hQR_map, map_mul, hQ0, mul_zero]
    have hf0 := hZ_indep f hf_eval
    have hQR0 : Q_R = 0 := by
      refine MvPolynomial.ext _ _ fun e => ?_
      rw [MvPolynomial.coeff_zero]
      by_cases he : e ∈ Q.support
      · let i0 : Fin p := ⟨e 0, hQ_lt e he⟩
        have hfi0 : f i0 = 0 := hf0 i0
        -- Extract `Q_R.coeff e` from `f i0 = 0` by comparing `X 2`-degree `e 1`!
        ext d
        have hc := congrArg (fun r : MvPolynomial (Fin 3) K =>
          r.coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) + Finsupp.single 2 (e 1))) hfi0
        rw [MvPolynomial.coeff_zero] at hc
        simp only [f, MvPolynomial.coeff_sum] at hc
        have hterm_c : ∀ e' ∈ Q.support.filter (fun e' => e' 0 = (i0 : ℕ)),
            (MvPolynomial.rename (![0, 1] : Fin 2 → Fin 3) (Q_R.coeff e') *
              (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ^ (e' 1)).coeff
              (Finsupp.single (0 : Fin 3) (d 0) + Finsupp.single 1 (d 1) + Finsupp.single 2 (e 1)) =
            if e' = e then (Q_R.coeff e).coeff d else 0 := by
          intro e' he'
          have hX2 : (MvPolynomial.X (2 : Fin 3) ^ (e' 1) : MvPolynomial (Fin 3) K) =
              MvPolynomial.monomial (Finsupp.single 2 (e' 1)) 1 := by
            rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
              Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]; simp
          rw [mul_comm, hX2, MvPolynomial.coeff_monomial_mul']
          by_cases heq : e' = e
          · subst e'
            have hle : Finsupp.single (2 : Fin 3) (e 1) ≤
                Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) + Finsupp.single 2 (e 1) := by
              intro j; fin_cases j <;> simp
            rw [if_pos hle, if_pos rfl, one_mul, mvPoly_rename01_coeff, if_pos (by simp)]
            congr 1; ext j; fin_cases j <;> simp
          · rw [if_neg heq]
            split_ifs with hle
            · rw [one_mul, mvPoly_rename01_coeff, if_neg]
              intro h20
              have hle2 : e' 1 ≤ e 1 := by simpa using hle 2
              simp at h20
              have he1_eq : e' 1 = e 1 := by omega
              have he0_eq : e' 0 = e 0 := (Finset.mem_filter.mp he').2
              apply heq; ext j; fin_cases j <;> assumption
            · rfl
        rw [Finset.sum_congr rfl hterm_c, Finset.sum_eq_single e] at hc
        · rw [if_pos rfl] at hc; exact hc
        · intro e' _ hne; rw [if_neg hne]
        · intro hnm; exfalso; exact hnm (Finset.mem_filter.mpr ⟨he, rfl⟩)
      · simp only [Q_R, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        exact Finset.sum_eq_zero fun e' he' => if_neg (fun h : e' = e => he (h ▸ he'))
    rw [hQR0, map_zero] at hQR_map
    have hdL : MvPolynomial.C (algebraMap (P2 K) L d_all) ≠ (0 : P2 L) := by
      intro h0
      have := MvPolynomial.C_eq_zero.mp h0
      rw [← map_zero (algebraMap (P2 K) L)] at this
      exact hd_all_ne (IsFractionRing.injective (P2 K) L this)
    exact (mul_eq_zero.mp hQR_map.symm).resolve_left hdL
  -- Step 5 & 6: Base change to `L' := AlgebraicClosure L` and apply `no_expMap_singular_Zp_Tp1`!
  have : CharP L p :=
    (RingHom.charP_iff_charP ((algebraMap (P2 K) L).comp MvPolynomial.C) p).mp ‹CharP K p›
  exact no_expMap_caseA_finish p w_L (AlgEquiv.ofBijective e0 ⟨he0_inj, he0_surj⟩) φ_L hφ_L_nt

/-- Helper: Over an infinite field `K`, any non-zero `F ∈ P2 K` takes a non-zero value at some `(z, t) ∈ K × K`. -/
lemma exists_aeval_ne_zero_P2 [Infinite K] (F : P2 K) (hF : F ≠ 0) :
    ∃ z t : K, MvPolynomial.aeval ![z, t] F ≠ 0 := by
  classical
  obtain ⟨e₀, he₀⟩ := MvPolynomial.support_nonempty.mpr hF
  let k : ℕ := e₀ 0
  let q1 : Polynomial K :=
    ∑ e ∈ F.support.filter (fun e => e 0 = k), Polynomial.C (F.coeff e) * Polynomial.X ^ (e 1)
  have hq1_ne : q1 ≠ 0 := by
    intro h0
    have hc := congrArg (fun r : Polynomial K => r.coeff (e₀ 1)) h0
    rw [Polynomial.coeff_zero] at hc
    simp only [q1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    rw [Finset.sum_eq_single e₀] at hc
    · rw [if_pos rfl, mul_one] at hc
      exact MvPolynomial.mem_support_iff.mp he₀ hc
    · intro e he hne
      have he0 : e 0 = e₀ 0 := (Finset.mem_filter.mp he).2
      have he1 : e 1 ≠ e₀ 1 := by
        intro h1; apply hne; ext j; fin_cases j <;> assumption
      rw [if_neg (Ne.symm he1), mul_zero]
    · intro hnm; exfalso; exact hnm (Finset.mem_filter.mpr ⟨he₀, rfl⟩)
  obtain ⟨t, ht⟩ : ∃ t : K, q1.eval t ≠ 0 := by
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset q1.roots.toFinset
    exact ⟨t, fun h0 => ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq1_ne).mpr h0))⟩
  let q2 : Polynomial K := MvPolynomial.aeval ![Polynomial.X, Polynomial.C t] F
  have hq2_ne : q2 ≠ 0 := by
    intro h0
    have hc := congrArg (fun r : Polynomial K => r.coeff k) h0
    rw [Polynomial.coeff_zero] at hc
    have hq2_k : q2.coeff k = q1.eval t := by
      have hFsum : q2 = ∑ e ∈ F.support,
          MvPolynomial.aeval ![Polynomial.X, Polynomial.C t] (MvPolynomial.monomial e (F.coeff e)) := by
        dsimp only [q2]; conv_lhs => rw [MvPolynomial.as_sum F]
        rw [map_sum]
      rw [hFsum, Polynomial.finsetSum_coeff]
      simp only [q1, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_eq_smul_one,
        Polynomial.smul_eq_C_mul, mul_one, ← Polynomial.C_pow]
      have hmul : Polynomial.C (F.coeff e) * (Polynomial.X ^ e 0 * Polynomial.C (t ^ e 1)) =
          Polynomial.C (F.coeff e * t ^ e 1) * Polynomial.X ^ e 0 := by rw [map_mul]; ring
      rw [hmul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases he0 : e 0 = k
      · rw [if_pos he0.symm, if_pos he0, mul_one]; simp
      · rw [if_neg (Ne.symm he0), if_neg he0, mul_zero, Polynomial.eval_zero]
    rw [hq2_k] at hc; exact ht hc
  obtain ⟨z, hz⟩ : ∃ z : K, q2.eval z ≠ 0 := by
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset q2.roots.toFinset
    exact ⟨z, fun h0 => hz (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq2_ne).mpr h0))⟩
  refine ⟨z, t, ?_⟩
  have hev : (Polynomial.aeval z).comp (MvPolynomial.aeval ![Polynomial.X, Polynomial.C t]) =
      MvPolynomial.aeval ![z, t] := by
    apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp
  have hval : MvPolynomial.aeval ![z, t] F = q2.eval z := by
    rw [← hev]; rfl
  rw [hval]; exact hz

/-- Helper: Irreducibility of `X j - C β` in `P2 K` for `j : Fin 2`, `β : K`. -/
lemma irreducible_X_sub_C_P2 (j : Fin 2) (β : K) :
    Irreducible (MvPolynomial.X j - MvPolynomial.C β : P2 K) := by
  have hirred0 : Irreducible (MvPolynomial.X 0 : P2 K) := by
    let e : P2 K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) := MvPolynomial.finSuccEquiv K 1
    have hX0 : e.symm Polynomial.X = MvPolynomial.X 0 :=
      e.symm_apply_eq.mpr (MvPolynomial.finSuccEquiv_X_zero).symm
    rw [← hX0]
    exact (Polynomial.prime_X (R := MvPolynomial (Fin 1) K)).irreducible.map e.symm.toMulEquiv
  match j with
  | 0 =>
    let shift : P2 K ≃ₐ[K] P2 K :=
      AlgEquiv.ofAlgHom
        (MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C β, MvPolynomial.X 1])
        (MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C β, MvPolynomial.X 1])
        (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
        (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
    have hsh : shift (MvPolynomial.X 0) = MvPolynomial.X 0 - MvPolynomial.C β := by simp [shift]
    rw [← hsh]
    exact hirred0.map shift.toMulEquiv
  | 1 =>
    let swap : P2 K ≃ₐ[K] P2 K := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)
    have hirred1 : Irreducible (MvPolynomial.X 1 : P2 K) := by
      have h1 : swap (MvPolynomial.X 0) = MvPolynomial.X 1 := by simp [swap]
      rw [← h1]; exact hirred0.map swap.toMulEquiv
    let shift : P2 K ≃ₐ[K] P2 K :=
      AlgEquiv.ofAlgHom
        (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.C β])
        (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C β])
        (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
        (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp)
    have hsh : shift (MvPolynomial.X 1) = MvPolynomial.X 1 - MvPolynomial.C β := by simp [shift]
    rw [← hsh]
    exact hirred1.map shift.toMulEquiv

set_option maxHeartbeats 800000 in
/-- Core of Case B of Lemma 3.5: given an abstract domain `Bbar ≃ₐ[K] HomRing K p ⧸ ⟨bC (w - β)⟩`
    with a non-trivial `ExpMap` fixing `ybar` (and `K[ybar] ↪ Bbar`), derive `False`. -/
lemma no_expMap_caseB_core [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (w : P2 K) (β : K) (hβ_ne : β ≠ 0)
    (hw_cases : w = MvPolynomial.X 0 ∨ w = MvPolynomial.X 1 ∨
      ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 ∧ w = MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1))
    {Bbar : Type*} [CommRing Bbar] [Algebra K Bbar] [IsDomain Bbar]
    (eQ : (HomRing K p ⧸ Ideal.span ({bC K p (w - MvPolynomial.C β)} : Set (HomRing K p))) ≃ₐ[K] Bbar)
    (φbar : ExpMap K Bbar) (hφbar_nt : φbar.IsNontrivial)
    (hybar_inv : eQ (Ideal.Quotient.mk (Ideal.span ({bC K p (w - MvPolynomial.C β)} : Set (HomRing K p))) (bY K p)) ∈ φbar.invSubalg)
    (haeval_ybar_inj : Function.Injective
      (Polynomial.aeval (eQ (Ideal.Quotient.mk (Ideal.span ({bC K p (w - MvPolynomial.C β)} : Set (HomRing K p))) (bY K p))) :
        Polynomial K →ₐ[K] Bbar)) : False := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  let f : P2 K := w - MvPolynomial.C β
  let bf : HomRing K p := bC K p f
  let IB : Ideal (HomRing K p) := Ideal.span {bf}
  let qB : HomRing K p →ₐ[K] Bbar := eQ.toAlgHom.comp (Ideal.Quotient.mkₐ K IB)
  have hqB_surj : Function.Surjective qB := eQ.surjective.comp Ideal.Quotient.mk_surjective
  have hqB_bf : qB bf = 0 := by
    change eQ (Ideal.Quotient.mk IB bf) = 0
    have h0 : Ideal.Quotient.mk IB bf = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [h0, map_zero]
  let ybar : Bbar := qB (bY K p)
  let M : Submonoid Bbar := (nonZeroDivisors (Polynomial K)).map (Polynomial.aeval ybar).toRingHom.toMonoidHom
  have hpoly_ybar_inv : ∀ q : Polynomial K, Polynomial.aeval ybar q ∈ φbar.invSubalg := fun q => by
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | monomial k c =>
      rw [Polynomial.aeval_monomial]
      exact mul_mem (φbar.invSubalg.algebraMap_mem c) (pow_mem hybar_inv k)
  have hM_inv : ∀ m ∈ M, m ∈ φbar.invSubalg := by
    rintro m ⟨q, _, rfl⟩
    exact hpoly_ybar_inv q
  have hM_nz : ∀ m ∈ M, m ≠ 0 := by
    rintro m ⟨q, hq, rfl⟩ h0
    exact nonZeroDivisors.ne_zero hq (haeval_ybar_inj (by rw [map_zero]; exact h0))
  let D_L := Localization M
  let L := FractionRing (Polynomial K)
  let iR : Polynomial K →+* D_L := (algebraMap Bbar D_L).comp (Polynomial.aeval ybar).toRingHom
  have hiR_unit : ∀ y : nonZeroDivisors (Polynomial K), IsUnit (iR y) := fun y =>
    IsLocalization.map_units D_L (⟨Polynomial.aeval ybar y.1, y.1, y.2, rfl⟩ : M)
  let iL : L →+* D_L := IsLocalization.lift (M := nonZeroDivisors (Polynomial K)) hiR_unit
  letI : Algebra L D_L := RingHom.toAlgebra iL
  have : IsDomain D_L :=
    IsLocalization.isDomain_of_le_nonZeroDivisors D_L (fun m hm => mem_nonZeroDivisors_of_ne_zero (hM_nz m hm))
  have : CharP L p := (RingHom.charP_iff_charP ((algebraMap (Polynomial K) L).comp Polynomial.C) p).mp ‹CharP K p›
  have : CharP D_L p := charP_of_injective_algebraMap (algebraMap L D_L).injective p
  have : Fact (Nat.Prime (ringChar D_L)) := by rw [ringChar.eq D_L p]; exact hp_prime
  -- Localize `φbar` to `φ_K : ExpMap K D_L`, then upgrade to `φ_L : ExpMap L D_L`!
  let φ_K : ExpMap K D_L := φbar.localize M hM_inv
  have hφ_K_nt : φ_K.IsNontrivial := by
    obtain ⟨b, hb⟩ := hφbar_nt
    refine ⟨algebraMap Bbar D_L b, fun hinv => hb ?_⟩
    have hinj : Function.Injective (algebraMap Bbar D_L) :=
      IsLocalization.injective D_L (fun m hm => mem_nonZeroDivisors_of_ne_zero (hM_nz m hm))
    have h1 : φ_K (algebraMap Bbar D_L b) = Polynomial.map (algebraMap Bbar D_L) (φbar b) :=
      φbar.localizeAlgHom_algebraMap M hM_inv b
    change φ_K (algebraMap Bbar D_L b) = Polynomial.C (algebraMap Bbar D_L b) at hinv
    rw [h1] at hinv
    change φbar b = Polynomial.C b
    refine Polynomial.ext fun n => ?_
    have hn := congrArg (fun P => P.coeff n) hinv
    rw [Polynomial.coeff_map, Polynomial.coeff_C] at hn
    rw [Polynomial.coeff_C]
    apply hinj; split_ifs at hn ⊢
    · exact hn
    · rw [map_zero]; exact hn
  have hφ_K_L : ∀ c : L, φ_K (algebraMap L D_L c) = Polynomial.C (algebraMap L D_L c) := by
    intro c
    obtain ⟨⟨q₁, q₂⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial K)) c
    have hq2_unit : IsUnit (Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₂.1))) :=
      (isUnit_iff_ne_zero.mpr (by
        rw [← map_zero (algebraMap (Polynomial K) L)]
        exact (IsFractionRing.injective (Polynomial K) L).ne (nonZeroDivisors.ne_zero q₂.2))).map
        (Polynomial.C.comp (algebraMap L D_L))
    have hpoly : ∀ q : Polynomial K, φ_K (algebraMap L D_L (algebraMap (Polynomial K) L q)) =
        Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q)) := by
      intro q
      have heq : algebraMap L D_L (algebraMap (Polynomial K) L q) = algebraMap Bbar D_L (Polynomial.aeval ybar q) := by
        change iL (algebraMap (Polynomial K) L q) = _; exact IsLocalization.lift_eq hiR_unit q
      rw [heq]
      have h1 : φ_K (algebraMap Bbar D_L (Polynomial.aeval ybar q)) =
          Polynomial.map (algebraMap Bbar D_L) (φbar (Polynomial.aeval ybar q)) :=
        φbar.localizeAlgHom_algebraMap M hM_inv _
      have hq_inv : Polynomial.aeval ybar q ∈ φbar.invSubalg := hpoly_ybar_inv q
      rw [h1, show φbar (Polynomial.aeval ybar q) = Polynomial.C (Polynomial.aeval ybar q) from hq_inv, Polynomial.map_C]
    have hmul : φ_K (algebraMap L D_L c) * Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₂.1)) =
        Polynomial.C (algebraMap L D_L c) * Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₂.1)) := by
      calc φ_K (algebraMap L D_L c) * Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₂.1))
          = φ_K (algebraMap L D_L (c * algebraMap (Polynomial K) L q₂.1)) := by rw [← hpoly q₂.1, ← map_mul, ← map_mul]
        _ = Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₁)) := by rw [hq, hpoly q₁]
        _ = Polynomial.C (algebraMap L D_L c) * Polynomial.C (algebraMap L D_L (algebraMap (Polynomial K) L q₂.1)) := by
            rw [← hq, map_mul, map_mul]
    exact hq2_unit.mul_right_cancel hmul
  let φ_L : ExpMap L D_L :=
    { toAlgHom := { toRingHom := φ_K.toAlgHom.toRingHom, commutes' := hφ_K_L }
      eval_zero := φ_K.eval_zero
      coassoc := φ_K.coassoc }
  have hφ_L_nt : φ_L.IsNontrivial := by obtain ⟨d, hd⟩ := hφ_K_nt; exact ⟨d, hd⟩
  -- Step 5: Construct singular `L`-rational point `(0, y_L, z₀, t₀)` and two linearly independent `PointDeriv L D_L ev_L`!
  let y_L : L := algebraMap (Polynomial K) L Polynomial.X
  have hy_L_ne : y_L ≠ 0 := by
    dsimp only [y_L]; rw [← map_zero (algebraMap (Polynomial K) L)]
    exact (IsFractionRing.injective (Polynomial K) L).ne Polynomial.X_ne_zero
  obtain ⟨z₀, t₀, hzt_f, hzt_g⟩ : ∃ z₀ t₀ : K,
      MvPolynomial.aeval ![z₀, t₀] f = 0 ∧ z₀ ^ (p ^ 2) + t₀ ^ (p * (p + 1)) = 0 := by
    rcases hw_cases with rfl | rfl | ⟨μ, _, hμ1, rfl⟩
    · obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (Polynomial.X ^ (p + 1) + Polynomial.C (β ^ p)) (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt]
        · rw [Polynomial.degree_X_pow]; exact_mod_cast (by omega : p + 1 ≠ 0)
        · rw [Polynomial.degree_X_pow]; exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by omega : 0 < p + 1)))
      have ht₀_eq : t₀ ^ (p + 1) + β ^ p = 0 := by
        simpa [Polynomial.IsRoot] using ht₀
      refine ⟨β, t₀, by simp [f], ?_⟩
      have hpow : (β ^ p + t₀ ^ (p + 1)) ^ p = 0 := by rw [add_comm, ht₀_eq, zero_pow (by omega)]
      rw [add_pow_char, ← pow_mul, ← pow_mul, ← sq, mul_comm (p + 1) p] at hpow
      exact hpow
    · obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p + Polynomial.C (β ^ (p + 1))) (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt]
        · rw [Polynomial.degree_X_pow]; exact_mod_cast (by omega : p ≠ 0)
        · rw [Polynomial.degree_X_pow]; exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by omega : 0 < p)))
      have hz₀_eq : z₀ ^ p + β ^ (p + 1) = 0 := by
        simpa [Polynomial.IsRoot] using hz₀
      refine ⟨z₀, β, by simp [f], ?_⟩
      have hpow : (z₀ ^ p + β ^ (p + 1)) ^ p = 0 := by rw [hz₀_eq, zero_pow (by omega)]
      rw [add_pow_char, ← pow_mul, ← pow_mul, ← sq, mul_comm (p + 1) p] at hpow
      exact hpow
    · have hμ_sub : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ1
      obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (Polynomial.X ^ (p + 1) - Polynomial.C (β * (μ - 1)⁻¹)) (by
        rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < p + 1)]; exact_mod_cast (by omega : p + 1 ≠ 0))
      have ht₀_eq : t₀ ^ (p + 1) = β * (μ - 1)⁻¹ := sub_eq_zero.mp (by simpa [Polynomial.IsRoot] using ht₀)
      obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p + Polynomial.C (t₀ ^ (p + 1))) (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt]
        · rw [Polynomial.degree_X_pow]; exact_mod_cast (by omega : p ≠ 0)
        · rw [Polynomial.degree_X_pow]; exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by omega : 0 < p)))
      have hz₀_eq : z₀ ^ p + t₀ ^ (p + 1) = 0 := by simpa [Polynomial.IsRoot] using hz₀
      refine ⟨z₀, t₀, ?_, ?_⟩
      · simp only [f, map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
          Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_self, RingHom.id_apply]
        have hz0p : z₀ ^ p = -(t₀ ^ (p + 1)) := eq_neg_of_add_eq_zero_left hz₀_eq
        rw [hz0p, show -(t₀ ^ (p + 1)) + μ * t₀ ^ (p + 1) = (μ - 1) * t₀ ^ (p + 1) by ring,
          ht₀_eq, mul_comm (μ - 1), mul_assoc, inv_mul_cancel₀ hμ_sub, mul_one, sub_self]
      · have hpow : (z₀ ^ p + t₀ ^ (p + 1)) ^ p = 0 := by rw [hz₀_eq, zero_pow (by omega)]
        rw [add_pow_char, ← pow_mul, ← pow_mul, ← sq, mul_comm (p + 1) p] at hpow
        exact hpow
  -- Lift `ev4 : K[X,Y,Z,T] →ₐ[K] L` at `(0, y_L, z₀, t₀)` to `ev_Bbar : Bbar →ₐ[K] L`!
  let iKL : K →+* L := algebraMap K L
  let rel4 : MvPolynomial (Fin 4) K :=
    MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 + MvPolynomial.X 2 ^ (p ^ 2) + MvPolynomial.X 3 ^ (p * (p + 1))
  let I4 : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {rel4}
  let f4 : MvPolynomial (Fin 4) K := MvPolynomial.rename ![2, 3] f
  have hhom_f4 : (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 f4) = bf := by
    suffices ∀ g : P2 K, (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.rename (![2, 3] : Fin 2 → Fin 4) g)) = bC K p g from this f
    intro g
    induction g using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.rename_C, homRing_quotEquiv_mk_C]
      apply Subtype.ext; rfl
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]
      apply Subtype.ext; change LaurentPolynomial.C a + LaurentPolynomial.C b = LaurentPolynomial.C (a + b)
      rw [map_add]
    | mul_X a j ha =>
      rw [map_mul, map_mul, map_mul, ha, MvPolynomial.rename_X]
      match j with
      | 0 =>
        dsimp only [I4, rel4]
        rw [show (![2, 3] : Fin 2 → Fin 4) 0 = 2 from rfl, homRing_quotEquiv_mk_X2]
        apply Subtype.ext; change LaurentPolynomial.C a * genZ K = LaurentPolynomial.C (a * MvPolynomial.X 0)
        rw [genZ, map_mul]
      | 1 =>
        dsimp only [I4, rel4]
        rw [show (![2, 3] : Fin 2 → Fin 4) 1 = 3 from rfl, homRing_quotEquiv_mk_X3]
        apply Subtype.ext; change LaurentPolynomial.C a * genT K = LaurentPolynomial.C (a * MvPolynomial.X 1)
        rw [genT, map_mul]
  let ev4 : MvPolynomial (Fin 4) K →ₐ[K] L := MvPolynomial.aeval ![(0 : L), y_L, iKL z₀, iKL t₀]
  have hev4_rel4 : ev4 rel4 = 0 := by
    simp only [ev4, rel4, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
    rw [← map_pow, ← map_pow, ← map_add, hzt_g, map_zero]
  have hev4_f4 : ev4 f4 = 0 := by
    simp only [ev4, f4, MvPolynomial.aeval_rename]
    have hcomp : (![(0 : L), y_L, iKL z₀, iKL t₀] ∘ ![2, 3]) = (iKL ∘ ![z₀, t₀]) := by
      ext j; fin_cases j <;> rfl
    rw [hcomp]
    have h1 : MvPolynomial.aeval (iKL ∘ ![z₀, t₀]) f = iKL (MvPolynomial.aeval ![z₀, t₀] f) := by
      induction f using MvPolynomial.induction_on with
      | C c => simp [iKL]
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a j ha => simp [map_mul, ha]
    rw [h1, hzt_f, map_zero]
  let ev_Q4 : (MvPolynomial (Fin 4) K ⧸ I4) →ₐ[K] L :=
    Ideal.Quotient.liftₐ I4 ev4 (fun x hx => by
      rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx; rw [map_mul, hev4_rel4, zero_mul])
  let ev_B : HomRing K p →ₐ[K] L := ev_Q4.comp (homRing_quotEquiv K p hp).symm.toAlgHom
  have hev_B_bf : ev_B bf = 0 := by
    rw [← hhom_f4]
    change ev_Q4 ((homRing_quotEquiv K p hp).symm ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 f4))) = 0
    rw [(homRing_quotEquiv K p hp).symm_apply_apply]
    exact hev4_f4
  let ev_Q : (HomRing K p ⧸ IB) →ₐ[K] L :=
    Ideal.Quotient.liftₐ IB ev_B (fun x hx => by
      rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx; rw [map_mul, hev_B_bf, zero_mul])
  let ev_Bbar : Bbar →ₐ[K] L := ev_Q.comp eQ.symm.toAlgHom
  have hev_qB : ∀ b : HomRing K p, ev_Bbar (qB b) = ev_B b := fun b => by
    change ev_Q (eQ.symm (eQ (Ideal.Quotient.mk IB b))) = ev_B b
    rw [eQ.symm_apply_apply]; rfl
  have hev_ybar : ev_Bbar ybar = y_L := by
    rw [show ybar = qB (bY K p) from rfl, hev_qB]
    have hy_symm : (homRing_quotEquiv K p hp).symm (bY K p) = Ideal.Quotient.mk I4 (MvPolynomial.X 1) :=
      (homRing_quotEquiv K p hp).symm_apply_eq.mpr (homRing_quotEquiv_mk_X1 K p hp).symm
    change ev_Q4 ((homRing_quotEquiv K p hp).symm (bY K p)) = y_L
    rw [hy_symm]; change ev4 (MvPolynomial.X 1) = y_L; simp [ev4]
  have hev_ι : ∀ q : Polynomial K, ev_Bbar (Polynomial.aeval ybar q) = algebraMap (Polynomial K) L q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
    | monomial k c =>
      rw [Polynomial.aeval_monomial, map_mul, map_pow, AlgHom.commutes, hev_ybar,
        ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      rfl
  -- Two `K`-linear Leibniz derivations `D1_B, D2_B : Bbar →ₗ[K] L` via `pderiv 0` and `pderiv j₂`!
  let j₂ : Fin 4 := if w = MvPolynomial.X 0 then 3 else 2
  have hmkD4 : ∀ j : Fin 4, (ev4 (MvPolynomial.pderiv j rel4) = 0) →
      (ev4 (MvPolynomial.pderiv j f4) = 0) → (j ≠ 1) →
      ∃ D : Bbar →ₗ[K] L,
        (∀ a b : Bbar, D (a * b) = ev_Bbar a * D b + ev_Bbar b * D a) ∧
        (∀ q : Polynomial K, D (Polynomial.aeval ybar q) = 0) ∧
        (∀ i : Fin 4, D (qB ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.X i)))) =
          if i = j then 1 else 0) := by
    intro j hj_rel hj_f hj_ne1
    let D4 : MvPolynomial (Fin 4) K →ₗ[K] L := ev4.toLinearMap.comp (MvPolynomial.pderiv j).toLinearMap
    have hD4_leib : ∀ a b : MvPolynomial (Fin 4) K, D4 (a * b) = ev4 a * D4 b + ev4 b * D4 a := fun a b => by
      simp only [D4, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Derivation.coeFn_coe,
        Derivation.leibniz, map_add, map_mul, smul_eq_mul]
    have hD4_I4 : ∀ x ∈ I4, D4 x = 0 := by
      intro x hx; rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
      rw [hD4_leib, hev4_rel4, zero_mul, zero_add]
      change ev4 q * ev4 (MvPolynomial.pderiv j rel4) = 0
      rw [hj_rel, mul_zero]
    let D_Q4 : (MvPolynomial (Fin 4) K ⧸ I4) →ₗ[K] L :=
      { toFun := fun x => Quotient.liftOn' x D4 (fun a b hab => by
          have h0 := hD4_I4 (a - b) ((Submodule.quotientRel_def I4).mp hab)
          rw [map_sub] at h0; exact sub_eq_zero.mp h0)
        map_add' := fun x y => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
          exact map_add D4 a b
        map_smul' := fun c x => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact map_smul D4 c a }
    let D_B : HomRing K p →ₗ[K] L := D_Q4.comp (homRing_quotEquiv K p hp).symm.toLinearEquiv.toLinearMap
    have hD_B_leib : ∀ a b : HomRing K p, D_B (a * b) = ev_B a * D_B b + ev_B b * D_B a := by
      intro a b
      obtain ⟨q1, rfl⟩ := (homRing_quotEquiv K p hp).surjective a
      obtain ⟨q2, rfl⟩ := (homRing_quotEquiv K p hp).surjective b
      obtain ⟨P1, rfl⟩ := Ideal.Quotient.mk_surjective q1
      obtain ⟨P2, rfl⟩ := Ideal.Quotient.mk_surjective q2
      have hmul : (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 P1) *
          (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 P2) =
          (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (P1 * P2)) := by
        rw [← map_mul, ← map_mul]
      rw [hmul]
      simp only [D_B, ev_B, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearMap.comp_apply,
        LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, AlgEquiv.symm_apply_apply]
      exact hD4_leib P1 P2
    have hD_B_IB : ∀ x ∈ IB, D_B x = 0 := by
      intro x hx; rw [Ideal.mem_span_singleton] at hx; obtain ⟨q, rfl⟩ := hx
      rw [hD_B_leib, hev_B_bf, zero_mul, zero_add]
      have hbf0 : D_B bf = 0 := by
        rw [← hhom_f4]
        simp only [D_B, LinearMap.comp_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
          AlgEquiv.symm_apply_apply]
        exact hj_f
      rw [hbf0, mul_zero]
    let D_Q : (HomRing K p ⧸ IB) →ₗ[K] L :=
      { toFun := fun x => Quotient.liftOn' x D_B (fun a b hab => by
          have h0 := hD_B_IB (a - b) ((Submodule.quotientRel_def IB).mp hab)
          rw [map_sub] at h0; exact sub_eq_zero.mp h0)
        map_add' := fun x y => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
          exact map_add D_B a b
        map_smul' := fun c x => by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact map_smul D_B c a }
    let D_Bbar : Bbar →ₗ[K] L := D_Q.comp eQ.symm.toLinearEquiv.toLinearMap
    have hD_qB : ∀ a : HomRing K p, D_Bbar (qB a) = D_B a := fun a => by
      change D_Q (eQ.symm (eQ (Ideal.Quotient.mk IB a))) = D_B a
      rw [eQ.symm_apply_apply]; rfl
    have hD_Bbar_leib : ∀ a b : Bbar, D_Bbar (a * b) = ev_Bbar a * D_Bbar b + ev_Bbar b * D_Bbar a := by
      intro a b
      obtain ⟨a, rfl⟩ := hqB_surj a
      obtain ⟨b, rfl⟩ := hqB_surj b
      rw [← map_mul, hD_qB, hD_qB, hD_qB, hev_qB, hev_qB]
      exact hD_B_leib a b
    have hD_Bbar_X : ∀ i : Fin 4,
        D_Bbar (qB ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.X i)))) =
        if i = j then 1 else 0 := by
      intro i
      rw [hD_qB]
      simp only [D_B, LinearMap.comp_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
        AlgEquiv.symm_apply_apply]
      change ev4 (MvPolynomial.pderiv j (MvPolynomial.X i)) = _
      rw [MvPolynomial.pderiv_X]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij, hij]
    have hD_ybar : D_Bbar ybar = 0 := by
      have : ybar = qB ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.X 1))) := by
        rw [homRing_quotEquiv_mk_X1]
      rw [this, hD_Bbar_X 1, if_neg hj_ne1.symm]
    have hD_poly : ∀ q : Polynomial K, D_Bbar (Polynomial.aeval ybar q) = 0 := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
      | monomial k c =>
        rw [Polynomial.aeval_monomial, hD_Bbar_leib]
        have hC0 : D_Bbar (algebraMap K Bbar c) = 0 := by
          have : algebraMap K Bbar c = c • (1 : Bbar) := Algebra.algebraMap_eq_smul_one c
          rw [this, map_smul]
          have h10 : D_Bbar 1 = 0 := by
            have h := hD_Bbar_leib 1 1
            have hev1 : ev_Bbar 1 = 1 := map_one ev_Bbar
            rw [mul_one, hev1, one_mul] at h
            linear_combination -h
          rw [h10, smul_zero]
        have hpow0 : ∀ n : ℕ, D_Bbar (ybar ^ n) = 0 := fun n => by
          induction n with
          | zero =>
            rw [pow_zero]
            have h := hD_Bbar_leib 1 1
            have hev1 : ev_Bbar 1 = 1 := map_one ev_Bbar
            rw [mul_one, hev1, one_mul] at h
            linear_combination -h
          | succ n ih => rw [pow_succ, hD_Bbar_leib, ih, hD_ybar, mul_zero, mul_zero, add_zero]
        rw [hC0, hpow0 k, mul_zero, mul_zero, add_zero]
    exact ⟨D_Bbar, hD_Bbar_leib, hD_poly, hD_Bbar_X⟩
  have : CharP (MvPolynomial (Fin 4) K) p := charP_of_injective_algebraMap (MvPolynomial.C_injective (Fin 4) K) p
  have hrel4_d0 : ev4 (MvPolynomial.pderiv 0 rel4) = 0 := by
    simp only [rel4, map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
      Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 0 by decide),
      mul_one, mul_zero, add_zero, zero_mul, smul_eq_mul, map_mul, map_pow, ev4,
      MvPolynomial.aeval_X, Matrix.cons_val_zero, zero_pow (by decide : 2 - 1 ≠ 0)]
  have hf4_d0 : ev4 (MvPolynomial.pderiv 0 f4) = 0 := by
    have h0 : ∀ g : P2 K, MvPolynomial.pderiv (0 : Fin 4) (MvPolynomial.rename (![2, 3] : Fin 2 → Fin 4) g) = 0 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C c => simp
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a i ha =>
        rw [map_mul, MvPolynomial.rename_X, MvPolynomial.pderiv_mul, ha, zero_mul, zero_add,
          MvPolynomial.pderiv_X]
        match i with
        | 0 => simp [Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 0 by decide)]
        | 1 => simp [Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 0 by decide)]
    rw [h0 f, map_zero]
  have hrel4_dj2 : ev4 (MvPolynomial.pderiv j₂ rel4) = 0 := by
    have hj2_ne0 : j₂ ≠ 0 := by dsimp only [j₂]; split_ifs <;> decide
    have hj2_ne1 : j₂ ≠ 1 := by dsimp only [j₂]; split_ifs <;> decide
    have hp2_0 : ((p ^ 2 : ℕ) : MvPolynomial (Fin 4) K) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by decide)]
    have hpp1_0 : ((p * (p + 1) : ℕ) : MvPolynomial (Fin 4) K) = 0 := by
      rw [Nat.cast_mul, CharP.cast_eq_zero, zero_mul]
    simp only [rel4, map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
      Pi.single_eq_of_ne (Ne.symm hj2_ne0), Pi.single_eq_of_ne (Ne.symm hj2_ne1),
      hp2_0, hpp1_0, mul_zero, zero_mul, add_zero, zero_add, smul_eq_mul, map_zero]
  have hf4_dj2 : ev4 (MvPolynomial.pderiv j₂ f4) = 0 := by
    rcases hw_cases with rfl | rfl | ⟨μ, _, _, rfl⟩
    · have hj2 : j₂ = 3 := if_pos rfl
      rw [hj2]
      simp [f4, f, MvPolynomial.pderiv_X, Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 3 by decide)]
    · have hne : (MvPolynomial.X 1 : P2 K) ≠ MvPolynomial.X 0 := by
        intro h; have := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h; simp at this
      have hj2 : j₂ = 2 := if_neg hne
      rw [hj2]
      simp [f4, f, MvPolynomial.pderiv_X, Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 2 by decide)]
    · have hne : (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1) : P2 K) ≠ MvPolynomial.X 0 := by
        intro h; have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
        simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C_mul,
          MvPolynomial.coeff_X'] at this
        have h1 : Finsupp.single (0 : Fin 2) p ≠ Finsupp.single 0 1 := by
          intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) he; simp at this; omega
        have h2 : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 0 1 := by
          intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) he; simp at this
        rw [if_neg h1, if_neg h2] at this; simp at this
      have hj2 : j₂ = 2 := if_neg hne
      rw [hj2]
      simp only [f4, f, map_sub, map_add, map_mul, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_C,
        Matrix.cons_val_zero, Matrix.cons_val_one, MvPolynomial.pderiv_C, sub_zero,
        MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
        Pi.single_eq_same, Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 2 by decide),
        CharP.cast_eq_zero, zero_mul, mul_zero, add_zero, smul_eq_mul, map_zero]
  obtain ⟨D1_B, hD1_leib, hD1_poly, hD1_X⟩ := hmkD4 0 hrel4_d0 hf4_d0 (by decide)
  obtain ⟨D2_B, hD2_leib, hD2_poly, hD2_X⟩ := hmkD4 j₂ hrel4_dj2 hf4_dj2 (by dsimp only [j₂]; split_ifs <;> decide)
  let PD1 := PointDeriv.localizePoly (Polynomial.aeval ybar) M rfl ev_Bbar hev_ι D1_B hD1_leib hD1_poly
  let PD2 := PointDeriv.localizePoly (Polynomial.aeval ybar) M rfl ev_Bbar hev_ι D2_B hD2_leib hD2_poly
  -- Step 6: Show `D_L` is finitely generated over `L[u_D]` and apply `no_expMap_of_singular_curve`!
  let x_D : D_L := algebraMap Bbar D_L (qB (bX K p))
  let z_D : D_L := algebraMap Bbar D_L (qB (bZ K p))
  let t_D : D_L := algebraMap Bbar D_L (qB (bT K p))
  let v_D : D_L := if w = MvPolynomial.X 0 then t_D else z_D
  let u_D : D_L := if w = MvPolynomial.X 1 then z_D else t_D
  have hx_sq : x_D ^ 2 = -(y_L⁻¹ • (z_D ^ (p ^ 2) + t_D ^ (p * (p + 1)))) := by
    have hrel_B : bX K p ^ 2 * bY K p + bZ K p ^ (p ^ 2) + bT K p ^ (p * (p + 1)) = 0 := by
      have h0 : (homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 rel4) = 0 := by
        have hmem : Ideal.Quotient.mk I4 rel4 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
        rw [hmem, map_zero]
      simp only [rel4, map_add, map_mul, map_pow] at h0
      rw [homRing_quotEquiv_mk_X0, homRing_quotEquiv_mk_X1, homRing_quotEquiv_mk_X2, homRing_quotEquiv_mk_X3] at h0
      exact h0
    have hrel_D : x_D ^ 2 * algebraMap L D_L y_L = -(z_D ^ (p ^ 2) + t_D ^ (p * (p + 1))) := by
      have hy_eq : algebraMap L D_L y_L = algebraMap Bbar D_L ybar := by
        change iL (algebraMap (Polynomial K) L Polynomial.X) = _
        rw [IsLocalization.lift_eq]; simp [iR]
      rw [hy_eq]
      have h0 := congrArg (fun r => algebraMap Bbar D_L (qB r)) hrel_B
      simp only [map_add, map_mul, map_pow, map_zero] at h0
      exact eq_neg_of_add_eq_zero_left (by linear_combination h0)
    have hy_u : IsUnit (algebraMap L D_L y_L) := (isUnit_iff_ne_zero.mpr hy_L_ne).map (algebraMap L D_L)
    apply hy_u.mul_right_cancel
    rw [hrel_D, Algebra.smul_def, neg_mul, mul_right_comm, ← map_mul, inv_mul_cancel₀ hy_L_ne, map_one, one_mul]
  let B_fin : Finset D_L :=
    ((Finset.range 2).product (Finset.range p)).image fun ij => x_D ^ ij.1 * z_D ^ ij.2
  have hspan_D : ∀ a : D_L, ∃ g : D_L → Polynomial L, a = ∑ b ∈ B_fin, Polynomial.aeval u_D (g b) * b := by
    let P_set : Set D_L := {a : D_L | ∃ g : D_L → Polynomial L, a = ∑ b ∈ B_fin, Polynomial.aeval u_D (g b) * b}
    have h0_mem : (0 : D_L) ∈ P_set := ⟨fun _ => 0, by simp⟩
    have hadd_mem : ∀ a b : D_L, a ∈ P_set → b ∈ P_set → a + b ∈ P_set := by
      rintro a b ⟨ga, rfl⟩ ⟨gb, rfl⟩
      refine ⟨fun c => ga c + gb c, ?_⟩
      simp only [map_add, add_mul, Finset.sum_add_distrib]
    have hsmul_mem : ∀ (c : L) (a : D_L), a ∈ P_set → c • a ∈ P_set := by
      rintro c a ⟨ga, rfl⟩
      refine ⟨fun b => Polynomial.C c * ga b, ?_⟩
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, Polynomial.aeval_C, Algebra.smul_def, mul_assoc]
    have h1_mem : (1 : D_L) ∈ P_set := by
      have h1in : (1 : D_L) ∈ B_fin := Finset.mem_image.mpr ⟨(0, 0), by simp; omega, by simp⟩
      refine ⟨fun b => if b = 1 then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single (1 : D_L)]
      · simp
      · intro b _ hne; simp [hne]
      · intro hnm; exact absurd h1in hnm
    have hu_mul : ∀ a : D_L, a ∈ P_set → u_D * a ∈ P_set := by
      rintro a ⟨ga, rfl⟩
      refine ⟨fun b => Polynomial.X * ga b, ?_⟩
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, Polynomial.aeval_X, mul_assoc]
    have hC_D : ∀ c : K, algebraMap Bbar D_L (qB (algebraMap K (HomRing K p) c)) = algebraMap L D_L (iKL c) := fun c => by
      rw [AlgHom.commutes]
      change algebraMap Bbar D_L (algebraMap K Bbar c) = iL (algebraMap (Polynomial K) L (Polynomial.C c))
      rw [IsLocalization.lift_eq]; simp [iR]
    have hz_mul : ∀ a : D_L, a ∈ P_set → z_D * a ∈ P_set := by
      rcases hw_cases with rfl | rfl | ⟨μ, _, _, rfl⟩
      · have hz_eq : z_D = (iKL β) • (1 : D_L) := by
          have h1 : bZ K p - algebraMap K (HomRing K p) β = bf := by
            apply Subtype.ext; change genZ K - LaurentPolynomial.C (MvPolynomial.C β) = LaurentPolynomial.C (MvPolynomial.X 0 - MvPolynomial.C β)
            rw [genZ, map_sub]
          have h2 : qB (bZ K p) = qB (algebraMap K (HomRing K p) β) := by
            apply sub_eq_zero.mp; rw [← map_sub, h1]; exact hqB_bf
          rw [show z_D = algebraMap Bbar D_L (qB (bZ K p)) from rfl, h2, hC_D β, Algebra.smul_def, mul_one]
        intro a ha; rw [hz_eq, smul_mul_assoc, one_mul]; exact hsmul_mem (iKL β) a ha
      · have hu_eq : u_D = z_D := if_pos rfl
        intro a ha; rw [← hu_eq]; exact hu_mul a ha
      · have hu_eq : u_D = t_D := by
          dsimp only [u_D]; rw [if_neg]
          intro h; have := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h
          simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C_mul,
            MvPolynomial.coeff_X'] at this
          have h1 : Finsupp.single (0 : Fin 2) p ≠ Finsupp.single 1 1 := by
            intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) he; simp at this; omega
          have h2 : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 1 1 := by
            intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) he; simp at this; omega
          rw [if_neg h1, if_neg h2] at this; simp at this
        have hz_pow : z_D ^ p = (iKL β) • (1 : D_L) - (iKL μ) • (u_D ^ (p + 1)) := by
          have h1 : bZ K p ^ p + algebraMap K (HomRing K p) μ * bT K p ^ (p + 1) -
              algebraMap K (HomRing K p) β = bf := by
            apply Subtype.ext
            change genZ K ^ p + LaurentPolynomial.C (MvPolynomial.C μ) * genT K ^ (p + 1) -
              LaurentPolynomial.C (MvPolynomial.C β) =
              LaurentPolynomial.C (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.C β)
            simp [genZ, genT]
          have h2 := congrArg (fun r => algebraMap Bbar D_L (qB r)) h1
          rw [hqB_bf, map_zero] at h2
          simp only [map_sub, map_add, map_mul, map_pow] at h2
          rw [hC_D μ, hC_D β] at h2
          rw [hu_eq, Algebra.smul_def, Algebra.smul_def, mul_one]
          exact eq_sub_of_add_eq (sub_eq_zero.mp h2)
        have hbasis : ∀ (i j : ℕ), i < 2 → j < p → x_D ^ i * z_D ^ j ∈ P_set := fun i j hi hj => by
          have hmem : x_D ^ i * z_D ^ j ∈ B_fin :=
            Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, rfl⟩
          refine ⟨fun b => if b = x_D ^ i * z_D ^ j then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single (x_D ^ i * z_D ^ j)]
          · simp
          · intro b _ hne; simp [hne]
          · intro hnm; exact absurd hmem hnm
        have hupow_mul : ∀ (k : ℕ) (a : D_L), a ∈ P_set → u_D ^ k * a ∈ P_set := fun k => by
          induction k with
          | zero => intro a ha; simpa using ha
          | succ k ih => intro a ha; rw [pow_succ', mul_assoc]; exact hu_mul _ (ih a ha)
        intro a ha; rcases ha with ⟨ga, rfl⟩
        rw [Finset.mul_sum]
        have hsum_mem : ∀ (S : Finset D_L) (F : D_L → D_L), (∀ b ∈ S, F b ∈ P_set) → (∑ b ∈ S, F b) ∈ P_set := by
          intro S F hF; induction S using Finset.induction_on with
          | empty => simpa using h0_mem
          | insert x s hxs ih => rw [Finset.sum_insert hxs]; exact hadd_mem _ _ (hF x (Finset.mem_insert_self _ _)) (ih fun y hy => hF y (Finset.mem_insert_of_mem hy))
        refine hsum_mem B_fin _ fun b hb => ?_
        obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
        rw [Finset.mem_range] at hi hj
        have hpoly_mul : ∀ (q : Polynomial L) (x : D_L), x ∈ P_set → Polynomial.aeval u_D q * x ∈ P_set := by
          intro q x hx
          induction q using Polynomial.induction_on' with
          | add q₁ q₂ h₁ h₂ => rw [map_add, add_mul]; exact hadd_mem _ _ h₁ h₂
          | monomial k c =>
            rw [Polynomial.aeval_monomial, mul_assoc, ← Algebra.smul_def]
            exact hsmul_mem c _ (hupow_mul k x hx)
        rw [mul_left_comm]
        apply hpoly_mul
        rw [mul_left_comm, ← pow_succ']
        by_cases hj1 : j + 1 < p
        · exact hbasis i (j + 1) hi hj1
        · have hjp : j + 1 = p := by omega
          rw [hjp, hz_pow, mul_sub, mul_smul_comm, mul_one, mul_smul_comm]
          have hneg : ∀ x : D_L, x ∈ P_set → -x ∈ P_set := fun x hx => by
            rw [← neg_one_smul L x]; exact hsmul_mem (-1) x hx
          rw [sub_eq_add_neg]
          exact hadd_mem _ _ (hsmul_mem _ _ (by simpa using hbasis i 0 hi (by omega)))
            (hneg _ (hsmul_mem _ _ (by rw [mul_comm]; exact hupow_mul (p + 1) _ (by simpa using hbasis i 0 hi (by omega)))))
    have ht_mul : ∀ a : D_L, a ∈ P_set → t_D * a ∈ P_set := by
      rcases hw_cases with rfl | rfl | ⟨μ, _, _, rfl⟩
      · have hu_eq : u_D = t_D := by
          dsimp only [u_D]; rw [if_neg]
          intro h; have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h; simp at this
        intro a ha; rw [← hu_eq]; exact hu_mul a ha
      · have ht_eq : t_D = (iKL β) • (1 : D_L) := by
          have h1 : bT K p - algebraMap K (HomRing K p) β = bf := by
            apply Subtype.ext; change genT K - LaurentPolynomial.C (MvPolynomial.C β) = LaurentPolynomial.C (MvPolynomial.X 1 - MvPolynomial.C β)
            rw [genT, map_sub]
          have h2 : qB (bT K p) = qB (algebraMap K (HomRing K p) β) := by
            apply sub_eq_zero.mp; rw [← map_sub, h1]; exact hqB_bf
          rw [show t_D = algebraMap Bbar D_L (qB (bT K p)) from rfl, h2, hC_D β, Algebra.smul_def, mul_one]
        intro a ha; rw [ht_eq, smul_mul_assoc, one_mul]; exact hsmul_mem (iKL β) a ha
      · have hu_eq : u_D = t_D := by
          dsimp only [u_D]; rw [if_neg]
          intro h; have := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h
          simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C_mul,
            MvPolynomial.coeff_X'] at this
          have h1 : Finsupp.single (0 : Fin 2) p ≠ Finsupp.single 1 1 := by
            intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) he; simp at this; omega
          have h2 : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 1 1 := by
            intro he; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) he; simp at this; omega
          rw [if_neg h1, if_neg h2] at this; simp at this
        intro a ha; rw [← hu_eq]; exact hu_mul a ha
    have hzpow_mul : ∀ (k : ℕ) (a : D_L), a ∈ P_set → z_D ^ k * a ∈ P_set := fun k => by
      induction k with
      | zero => intro a ha; simpa using ha
      | succ k ih => intro a ha; rw [pow_succ', mul_assoc]; exact hz_mul _ (ih a ha)
    have htpow_mul : ∀ (k : ℕ) (a : D_L), a ∈ P_set → t_D ^ k * a ∈ P_set := fun k => by
      induction k with
      | zero => intro a ha; simpa using ha
      | succ k ih => intro a ha; rw [pow_succ', mul_assoc]; exact ht_mul _ (ih a ha)
    have hx_mul : ∀ a : D_L, a ∈ P_set → x_D * a ∈ P_set := by
      intro a ha; rcases ha with ⟨ga, rfl⟩
      rw [Finset.mul_sum]
      have hsum_mem : ∀ (S : Finset D_L) (F : D_L → D_L), (∀ b ∈ S, F b ∈ P_set) → (∑ b ∈ S, F b) ∈ P_set := by
        intro S F hF; induction S using Finset.induction_on with
        | empty => simpa using h0_mem
        | insert x s hxs ih => rw [Finset.sum_insert hxs]; exact hadd_mem _ _ (hF x (Finset.mem_insert_self _ _)) (ih fun y hy => hF y (Finset.mem_insert_of_mem hy))
      have hupow_mul : ∀ (k : ℕ) (x : D_L), x ∈ P_set → u_D ^ k * x ∈ P_set := fun k => by
        induction k with
        | zero => intro x hx; simpa using hx
        | succ k ih => intro x hx; rw [pow_succ', mul_assoc]; exact hu_mul _ (ih x hx)
      have hpoly_mul : ∀ (q : Polynomial L) (x : D_L), x ∈ P_set → Polynomial.aeval u_D q * x ∈ P_set := by
        intro q x hx
        induction q using Polynomial.induction_on' with
        | add q₁ q₂ h₁ h₂ => rw [map_add, add_mul]; exact hadd_mem _ _ h₁ h₂
        | monomial k c =>
          rw [Polynomial.aeval_monomial, mul_assoc, ← Algebra.smul_def]
          exact hsmul_mem c _ (hupow_mul k x hx)
      refine hsum_mem B_fin _ fun b hb => ?_
      obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
      rw [Finset.mem_range] at hi hj
      rw [mul_left_comm]; apply hpoly_mul
      rw [← mul_assoc, ← pow_succ']
      by_cases hi1 : i + 1 < 2
      · have hmem : x_D ^ (i + 1) * z_D ^ j ∈ B_fin :=
          Finset.mem_image.mpr ⟨(i + 1, j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi1, Finset.mem_range.mpr hj⟩, rfl⟩
        refine ⟨fun c => if c = x_D ^ (i + 1) * z_D ^ j then 1 else 0, ?_⟩
        rw [Finset.sum_eq_single (x_D ^ (i + 1) * z_D ^ j)]
        · simp
        · intro c _ hne; simp [hne]
        · intro hnm; exact absurd hmem hnm
      · have hi2 : i + 1 = 2 := by omega
        rw [hi2, hx_sq, neg_mul, smul_mul_assoc, add_mul]
        have hneg : ∀ x : D_L, x ∈ P_set → -x ∈ P_set := fun x hx => by
          rw [← neg_one_smul L x]; exact hsmul_mem (-1) x hx
        exact hneg _ (hsmul_mem _ _ (hadd_mem _ _
          (hzpow_mul (p ^ 2) _ (by simpa using hzpow_mul j 1 h1_mem))
          (htpow_mul (p * (p + 1)) _ (by simpa using hzpow_mul j 1 h1_mem))))
    have hB_mem : ∀ b : Bbar, algebraMap Bbar D_L b ∈ P_set := by
      intro b; obtain ⟨r, rfl⟩ := hqB_surj b
      obtain ⟨q, rfl⟩ := (homRing_quotEquiv K p hp).surjective r
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [homRing_quotEquiv_mk_C, hC_D c]
        have : algebraMap L D_L (iKL c) = (iKL c) • (1 : D_L) := by rw [Algebra.smul_def, mul_one]
        rw [this]; exact hsmul_mem (iKL c) 1 h1_mem
      | add p₁ p₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add]; exact hadd_mem _ _ h₁ h₂
      | mul_X p₁ j h₁ =>
        rw [map_mul, map_mul, map_mul, map_mul, mul_comm]
        match j with
        | 0 => rw [homRing_quotEquiv_mk_X0]; exact hx_mul _ h₁
        | 1 =>
          rw [homRing_quotEquiv_mk_X1]
          have : algebraMap Bbar D_L (qB (bY K p)) = y_L • (1 : D_L) := by
            rw [Algebra.smul_def, mul_one]
            change algebraMap Bbar D_L ybar = iL (algebraMap (Polynomial K) L Polynomial.X)
            rw [IsLocalization.lift_eq]; simp [iR]
          rw [this, smul_mul_assoc, one_mul]; exact hsmul_mem y_L _ h₁
        | 2 => rw [homRing_quotEquiv_mk_X2]; exact hz_mul _ h₁
        | 3 => rw [homRing_quotEquiv_mk_X3]; exact ht_mul _ h₁
    intro a
    induction a using Localization.induction_on with | H p_pair =>
    obtain ⟨b, m⟩ := p_pair
    obtain ⟨q, hq_nzd, hq_eq⟩ := m.2
    let q_L : L := algebraMap (Polynomial K) L q
    have hq_L_ne : q_L ≠ 0 := by
      dsimp only [q_L]; rw [← map_zero (algebraMap (Polynomial K) L)]
      exact (IsFractionRing.injective (Polynomial K) L).ne (nonZeroDivisors.ne_zero hq_nzd)
    have hmk : Localization.mk b m = q_L⁻¹ • algebraMap Bbar D_L b := by
      have hm_eq : algebraMap L D_L q_L = algebraMap Bbar D_L m.1 := by
        change iL (algebraMap (Polynomial K) L q) = _; rw [IsLocalization.lift_eq]
        simp only [iR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        exact congrArg (algebraMap Bbar D_L) hq_eq
      have hq_u : IsUnit (algebraMap L D_L q_L) := (isUnit_iff_ne_zero.mpr hq_L_ne).map (algebraMap L D_L)
      apply hq_u.mul_left_cancel
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq_L_ne, map_one, one_mul, hm_eq,
        Localization.mk_eq_mk', IsLocalization.mk'_spec' D_L b m]
    rw [hmk]; exact hsmul_mem q_L⁻¹ _ (hB_mem b)
  have hPD1_alg : ∀ b : Bbar, PD1.toLinearMap (algebraMap Bbar D_L b) = D1_B b := fun b => by
    have : algebraMap Bbar D_L b = Localization.mk b (1 : M) := (Localization.mk_one_eq_algebraMap b).symm
    rw [this]; change D1_B b * (ev_Bbar 1)⁻¹ = D1_B b; simp
  have hPD2_alg : ∀ b : Bbar, PD2.toLinearMap (algebraMap Bbar D_L b) = D2_B b := fun b => by
    have : algebraMap Bbar D_L b = Localization.mk b (1 : M) := (Localization.mk_one_eq_algebraMap b).symm
    rw [this]; change D2_B b * (ev_Bbar 1)⁻¹ = D2_B b; simp
  have hv_eq : v_D = algebraMap Bbar D_L
      (qB ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.X j₂)))) := by
    dsimp only [v_D, j₂]
    split_ifs
    · rw [homRing_quotEquiv_mk_X3]
    · rw [homRing_quotEquiv_mk_X2]
  have hx_eq : x_D = algebraMap Bbar D_L
      (qB ((homRing_quotEquiv K p hp) (Ideal.Quotient.mk I4 (MvPolynomial.X 0)))) := by
    rw [homRing_quotEquiv_mk_X0]
  have hj2_ne0 : j₂ ≠ 0 := by dsimp only [j₂]; split_ifs <;> decide
  exact no_expMap_of_singular_curve u_D B_fin hspan_D _ PD1 PD2 x_D v_D
    (by rw [hx_eq, hPD1_alg, hD1_X 0, if_pos rfl])
    (by rw [hv_eq, hPD1_alg, hD1_X j₂, if_neg hj2_ne0])
    (by rw [hx_eq, hPD2_alg, hD2_X 0, if_neg hj2_ne0.symm])
    (by rw [hv_eq, hPD2_alg, hD2_X j₂, if_pos rfl])
    φ_L hφ_L_nt

/-- Helper: Case B of Lemma 3.5 — no non-trivial `ExpMap` on `B_K` fixes `bY` and `bC w`
    for `w ∈ {Z, T} ∪ {Z^p + μ T^(p+1) | μ ≠ 0, μ ≠ 1}`. -/
lemma no_expMap_caseB [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (HomRing K p)) (hnt : φ.IsNontrivial)
    (hy : bY K p ∈ φ.invSubalg) (w : P2 K) (hw : bC K p w ∈ φ.invSubalg)
    (hw_cases : w = MvPolynomial.X 0 ∨ w = MvPolynomial.X 1 ∨
      ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 ∧ w = MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1)) :
    False := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  have : CharP (P2 K) p := charP_of_injective_algebraMap (MvPolynomial.C_injective (Fin 2) K) p
  -- Step 1: Pick `a ∉ φ.invSubalg`, some `n ≥ 1` with `c_n := (φ a).coeff n ≠ 0`,
  -- and `m₀ : ℤ` with `r₀ := (c_n : Ambient K).coeff m₀ ≠ 0`.
  obtain ⟨a_nt, ha_nt⟩ := hnt
  obtain ⟨n_nt, hn_pos, hcn_ne⟩ : ∃ n : ℕ, 0 < n ∧ (φ a_nt).coeff n ≠ 0 := by
    by_contra hall; push Not at hall
    apply ha_nt
    change φ a_nt = Polynomial.C a_nt
    refine Polynomial.ext fun n => ?_
    rw [Polynomial.coeff_C]
    by_cases hn0 : n = 0
    · subst hn0; rw [if_pos rfl, φ.coeff_zero]
    · rw [if_neg hn0]; exact hall n (Nat.pos_of_ne_zero hn0)
  let c_nt : HomRing K p := (φ a_nt).coeff n_nt
  obtain ⟨m₀, hr₀_ne⟩ : ∃ m₀ : ℤ, ((c_nt : Ambient K).coeff m₀) ≠ 0 := by
    by_contra hall; push Not at hall
    apply hcn_ne; apply Subtype.ext; exact AddMonoidAlgebra.ext (Finsupp.ext fun m => hall m)
  let r₀ : P2 K := (c_nt : Ambient K).coeff m₀
  have hw_ne : w ≠ 0 := by
    rcases hw_cases with rfl | rfl | ⟨μ, _, _, rfl⟩
    · exact MvPolynomial.X_ne_zero 0
    · exact MvPolynomial.X_ne_zero 1
    · intro h0
      have hc := congrArg (fun r : P2 K => r.coeff (Finsupp.single 0 p)) h0
      simp only [MvPolynomial.coeff_zero, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow,
        MvPolynomial.coeff_C_mul] at hc
      have hne : Finsupp.single (1 : Fin 2) (p + 1) ≠ Finsupp.single 0 p := by
        intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; omega
      rw [if_neg hne] at hc; simp at hc
  -- Pick `(z₁, t₁) ∈ K × K` where `(w * r₀)(z₁, t₁) ≠ 0`, and set `β := w(z₁, t₁) ≠ 0`!
  obtain ⟨z₁, t₁, hwr1⟩ := exists_aeval_ne_zero_P2 K (w * r₀) (mul_ne_zero hw_ne hr₀_ne)
  rw [map_mul] at hwr1
  let β : K := MvPolynomial.aeval ![z₁, t₁] w
  have hβ_ne : β ≠ 0 := left_ne_zero_of_mul hwr1
  have hr₀_eval_ne : MvPolynomial.aeval ![z₁, t₁] r₀ ≠ 0 := right_ne_zero_of_mul hwr1
  let f : P2 K := w - MvPolynomial.C β
  have hf_not_dvd_r₀ : ¬ (f ∣ r₀) := by
    rintro ⟨q, hq⟩
    have := congrArg (MvPolynomial.aeval ![z₁, t₁]) hq
    simp only [f, map_mul, map_sub, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      β, sub_self, zero_mul] at this
    exact hr₀_eval_ne this
  -- Step 2: `f` is irreducible (hence prime) in `P2 K`, and `¬ (f ∣ gHomPoly K p)`.
  have hf_irred : Irreducible f := by
    rcases hw_cases with rfl | rfl | ⟨μ, hμ0, _, rfl⟩
    · exact irreducible_X_sub_C_P2 K 0 β
    · exact irreducible_X_sub_C_P2 K 1 β
    · obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C β) (by
        rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < p)]; exact_mod_cast (by omega : p ≠ 0))
      have hα_pow : α ^ p = β := by
        rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hα_root
        exact sub_eq_zero.mp hα_root
      let shift : P2 K ≃ₐ[K] P2 K :=
        AlgEquiv.ofAlgHom
          (MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C α, MvPolynomial.X 1])
          (MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C α, MvPolynomial.X 1])
          (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)
          (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)
      have hsh : shift (MvPolynomial.X 0 ^ p + MvPolynomial.C μ * MvPolynomial.X 1 ^ (p + 1)) = f := by
        simp only [shift, AlgEquiv.ofAlgHom_apply, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
          MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [sub_pow_char, ← map_pow, hα_pow, MvPolynomial.algebraMap_eq]
        simp only [f]; ring
      rw [← hsh]
      exact (irreducible_Zp_add_mu_Tp1 p hp hμ0).map shift.toMulEquiv
  have hf_prime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf_irred
  have hf_not_dvd_g : ¬ (f ∣ gHomPoly K p) := by
    rintro ⟨q, hq⟩
    rcases hw_cases with rfl | rfl | ⟨μ, _, _, rfl⟩
    · have := congrArg (MvPolynomial.aeval ![β, (0 : K)]) hq
      simp only [f, gHomPoly, map_add, map_mul, map_sub, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_mul,
        zero_pow (by nlinarith : p * (p + 1) ≠ 0), add_zero] at this
      exact pow_ne_zero (p ^ 2) hβ_ne this
    · have := congrArg (MvPolynomial.aeval ![(0 : K), β]) hq
      simp only [f, gHomPoly, map_add, map_mul, map_sub, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_mul,
        zero_pow (by nlinarith : p ^ 2 ≠ 0), zero_add] at this
      exact pow_ne_zero (p * (p + 1)) hβ_ne this
    · obtain ⟨α, hα_root⟩ := IsAlgClosed.exists_root (Polynomial.X ^ p - Polynomial.C β) (by
        rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < p)]; exact_mod_cast (by omega : p ≠ 0))
      have hα_pow : α ^ p = β := by
        rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hα_root
        exact sub_eq_zero.mp hα_root
      have := congrArg (MvPolynomial.aeval ![α, (0 : K)]) hq
      simp only [f, gHomPoly, map_add, map_mul, map_sub, map_pow, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_pow (by omega : p + 1 ≠ 0), mul_zero, add_zero, hα_pow, sub_self, zero_mul,
        zero_pow (by nlinarith : p * (p + 1) ≠ 0)] at this
      have hα_ne : α ≠ 0 := fun h0 => hβ_ne (by rw [← hα_pow, h0, zero_pow (by omega)])
      exact pow_ne_zero (p ^ 2) hα_ne this
  -- Step 3: Quotient `Bbar := HomRing K p ⧸ Ideal.span {bC K p f}` embeds into `LaurentPolynomial (P2 K ⧸ Ideal.span {f})`!
  let If : Ideal (P2 K) := Ideal.span {f}
  have : If.IsPrime := (Ideal.span_singleton_prime hf_prime.ne_zero).mpr hf_prime
  let Pbar := P2 K ⧸ If
  have : IsDomain Pbar := Ideal.Quotient.isDomain If
  let bf : HomRing K p := bC K p f
  have hbf_inv : bf ∈ φ.invSubalg := by
    have h1 : bf = bC K p w - algebraMap K (HomRing K p) β := by
      apply Subtype.ext; change LaurentPolynomial.C (w - MvPolynomial.C β) =
        LaurentPolynomial.C w - LaurentPolynomial.C (MvPolynomial.C β)
      rw [map_sub]
    rw [h1]; exact sub_mem hw (φ.invSubalg.algebraMap_mem β)
  let IB : Ideal (HomRing K p) := Ideal.span {bf}
  let Bbar := HomRing K p ⧸ IB
  -- Map `π_amb : Ambient K →ₐ[K] LaurentPolynomial Pbar` and restrict to `HomRing K p`
  let mkP : P2 K →ₐ[K] Pbar := Ideal.Quotient.mkₐ K If
  let π_amb : Ambient K →ₐ[K] LaurentPolynomial Pbar :=
    { toRingHom := AddMonoidAlgebra.mapRingHom ℤ mkP.toRingHom
      commutes' := fun c => by
        change AddMonoidAlgebra.mapRingHom ℤ mkP.toRingHom
          (AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.C c)) =
          AddMonoidAlgebra.single (0 : ℤ) (Ideal.Quotient.mk If (MvPolynomial.C c))
        rw [AddMonoidAlgebra.mapRingHom_single]; rfl }
  let π : HomRing K p →ₐ[K] LaurentPolynomial Pbar := π_amb.comp (HomSubalg K p).val
  have hπ_coeff : ∀ (b : HomRing K p) (m : ℤ),
      (π b).coeff m = Ideal.Quotient.mk If ((b : Ambient K).coeff m) := by
    intro b m
    change (AddMonoidAlgebra.mapRingHom ℤ mkP.toRingHom (b : Ambient K)).coeff m = _
    simp [AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.map, mkP]; rfl
  have hπ_ker : ∀ b : HomRing K p, π b = 0 ↔ b ∈ IB := by
    intro b; constructor
    · intro hb0
      have hdvd : ∀ m : ℤ, f ∣ (b : Ambient K).coeff m := by
        intro m
        have hm := congrArg (fun r : LaurentPolynomial Pbar => r.coeff m) hb0
        rw [hπ_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hm
        exact hm
      choose qm hqm using hdvd
      let u : Ambient K :=
        AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (suppA K (b : Ambient K)) (fun m => qm m) (fun m hm => by
          by_contra hnm
          have h0 : (b : Ambient K).coeff m = 0 := Finsupp.notMem_support_iff.mp hnm
          rw [hqm m] at h0
          exact hm ((mul_eq_zero.mp h0).resolve_left hf_prime.ne_zero)))
      have hu_coeff : ∀ m : ℤ, u.coeff m = qm m := fun m => by simp [u]
      have hbu : (b : Ambient K) = LaurentPolynomial.C f * u := by
        refine AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
        have hCmul : ((LaurentPolynomial.C f : Ambient K) * u).coeff m = f * u.coeff m := by
          have h1 : (LaurentPolynomial.C f : Ambient K) = singleT K 0 f := rfl
          rw [h1, coeff_mul_A]
          have h0_mem : (0 : ℤ) ∈ suppA K (singleT K 0 f) := by
            rw [mem_suppA_iff, coeff_singleT, if_pos rfl]; exact hf_prime.ne_zero
          rw [Finset.sum_eq_single 0]
          · rw [coeff_singleT, if_pos rfl]
            by_cases hum : m ∈ suppA K u
            · rw [Finset.sum_eq_single m]
              · simp
              · intro j _ hj; rw [if_neg (by omega)]
              · intro hnm; exact absurd hum hnm
            · have hu0 : u.coeff m = 0 := by simpa [mem_suppA_iff] using hum
              rw [hu0, mul_zero]
              apply Finset.sum_eq_zero; intro j hj
              have hne : j ≠ m := fun h => hum (h ▸ hj)
              rw [if_neg (by omega)]
          · intro i _ hi
            apply Finset.sum_eq_zero; intro j _
            rw [coeff_singleT, if_neg (Ne.symm hi), zero_mul, ite_self]
          · intro hnm; exact absurd h0_mem hnm
        change (b : Ambient K).coeff m = ((LaurentPolynomial.C f : Ambient K) * u).coeff m
        rw [hqm m, hCmul, hu_coeff]
      have hu_mem : u ∈ HomSubalg K p := by
        change u ∈ SubalgOfPoly K (gHomPoly K p)
        rw [mem_subalgOfPoly_iff]
        intro m hm
        have hbm := (mem_subalgOfPoly_iff K (gHomPoly K p) _).mp b.2 m hm
        rw [hqm m] at hbm
        obtain ⟨r, hr⟩ := hbm
        have hf_not_pow : ¬ (f ∣ (-gHomPoly K p) ^ ((-m + 1) / 2).toNat) := by
          intro h; have h1 := hf_prime.dvd_of_dvd_pow h
          exact hf_not_dvd_g (dvd_neg.mp h1)
        have hf_dvd_r : f ∣ r := by
          have : f ∣ (-gHomPoly K p) ^ ((-m + 1) / 2).toNat * r := ⟨qm m, hr.symm⟩
          exact (hf_prime.dvd_or_dvd this).resolve_left hf_not_pow
        obtain ⟨r', rfl⟩ := hf_dvd_r
        have hcancel : qm m = (-gHomPoly K p) ^ ((-m + 1) / 2).toNat * r' :=
          mul_left_cancel₀ hf_prime.ne_zero (by rw [hr]; ring)
        exact ⟨r', hcancel⟩
      rw [Ideal.mem_span_singleton]
      exact ⟨⟨u, hu_mem⟩, Subtype.ext hbu⟩
    · intro hbI
      rw [Ideal.mem_span_singleton] at hbI
      obtain ⟨q, rfl⟩ := hbI
      rw [map_mul]; convert zero_mul _
      ext m; rw [hπ_coeff]
      change Ideal.Quotient.mk If ((LaurentPolynomial.C f : Ambient K).coeff m) = 0
      by_cases hm : m = 0
      · subst hm
        have hC0 : (LaurentPolynomial.C f : Ambient K).coeff 0 = f := by
          change (singleT K 0 f).coeff 0 = f; simp [coeff_singleT]
        rw [hC0, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      · have hCm : (LaurentPolynomial.C f : Ambient K).coeff m = 0 := by
          change (singleT K 0 f).coeff m = 0; simp [coeff_singleT, Ne.symm hm]
        rw [hCm, map_zero]
  let πbar : Bbar →ₐ[K] LaurentPolynomial Pbar :=
    Ideal.Quotient.liftₐ IB π (fun b hb => (hπ_ker b).mpr hb)
  have hπbar_inj : Function.Injective πbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx; obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hπ_ker b).mp hx
  have : IsDomain Bbar := Function.Injective.isDomain πbar.toRingHom hπbar_inj
  -- `φbar := φ.quotient bf hbf_inv` is non-trivial on `Bbar`!
  let φbar : ExpMap K Bbar := φ.quotient bf hbf_inv
  have hφbar_nt : φbar.IsNontrivial := by
    refine ⟨Ideal.Quotient.mk IB a_nt, fun hinv => ?_⟩
    change Polynomial.map (Ideal.Quotient.mk IB) (φ a_nt) = Polynomial.C (Ideal.Quotient.mk IB a_nt) at hinv
    have hn := congrArg (fun P => P.coeff n_nt) hinv
    rw [Polynomial.coeff_map, Polynomial.coeff_C, if_neg (by omega : n_nt ≠ 0),
      Ideal.Quotient.eq_zero_iff_mem] at hn
    have hπ0 := (hπ_ker c_nt).mpr hn
    have hm0 := congrArg (fun r : LaurentPolynomial Pbar => r.coeff m₀) hπ0
    rw [hπ_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hm0
    exact hf_not_dvd_r₀ hm0
  -- Step 4: `Polynomial.aeval ybar : Polynomial K →ₐ[K] Bbar` is injective, so we localize `Bbar` at `M`!
  let ybar : Bbar := Ideal.Quotient.mk IB (bY K p)
  have hybar_inv : ybar ∈ φbar.invSubalg := by
    change Polynomial.map (Ideal.Quotient.mk IB) (φ (bY K p)) = Polynomial.C ybar
    rw [show φ (bY K p) = Polynomial.C (bY K p) from hy, Polynomial.map_C]
  have haeval_ybar_inj : Function.Injective (Polynomial.aeval ybar : Polynomial K →ₐ[K] Bbar) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have hπq : π (Polynomial.aeval (bY K p) q) = 0 := by
      have h1 : πbar (Polynomial.aeval ybar q) = 0 := by rw [hq, map_zero]
      have h2 : Polynomial.aeval ybar q = Ideal.Quotient.mk IB (Polynomial.aeval (bY K p) q) :=
        Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K IB) (bY K p) q
      rw [h2] at h1; exact h1
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    have hcoeff_m : ((Polynomial.aeval (bY K p) q : HomRing K p) : Ambient K).coeff (-2 * (k : ℤ)) =
        MvPolynomial.C (q.coeff k) * (-gHomPoly K p) ^ k := by
      have haev : ((Polynomial.aeval (bY K p) q : HomRing K p) : Ambient K) =
          Polynomial.aeval (genYB K p) q :=
        (Polynomial.aeval_algHom_apply (HomSubalg K p).val (bY K p) q).symm
      rw [haev, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, coeff_sum_A]
      by_cases hk : k < q.natDegree + 1
      · rw [Finset.sum_eq_single k]
        · have hterm : (algebraMap K (Ambient K)) (q.coeff k) * genYB K p ^ k =
              singleT K (-2 * (k : ℤ)) (MvPolynomial.C (q.coeff k) * (-gHomPoly K p) ^ k) := by
            simp only [genYB, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
            have hC : (algebraMap K (Ambient K)) (q.coeff k) = LaurentPolynomial.C (MvPolynomial.C (q.coeff k)) := rfl
            rw [hC, mul_comm (k : ℤ) (-2)]; ring
          rw [hterm, coeff_singleT, if_pos rfl]
        · intro j _ hjk
          have hterm : (algebraMap K (Ambient K)) (q.coeff j) * genYB K p ^ j =
              singleT K (-2 * (j : ℤ)) (MvPolynomial.C (q.coeff j) * (-gHomPoly K p) ^ j) := by
            simp only [genYB, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
            have hC : (algebraMap K (Ambient K)) (q.coeff j) = LaurentPolynomial.C (MvPolynomial.C (q.coeff j)) := rfl
            rw [hC, mul_comm (j : ℤ) (-2)]; ring
          rw [hterm, coeff_singleT, if_neg (by omega)]
        · intro hnm; exfalso; exact hnm (Finset.mem_range.mpr hk)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]
        apply Finset.sum_eq_zero; intro j hj
        have hlt : j < q.natDegree + 1 := Finset.mem_range.mp hj
        have hterm : (algebraMap K (Ambient K)) (q.coeff j) * genYB K p ^ j =
            singleT K (-2 * (j : ℤ)) (MvPolynomial.C (q.coeff j) * (-gHomPoly K p) ^ j) := by
          simp only [genYB, mul_pow, LaurentPolynomial.T_pow, singleT_eq_C_mul_T, map_mul, map_pow]
          have hC : (algebraMap K (Ambient K)) (q.coeff j) = LaurentPolynomial.C (MvPolynomial.C (q.coeff j)) := rfl
          rw [hC, mul_comm (j : ℤ) (-2)]; ring
        rw [hterm, coeff_singleT, if_neg (by omega)]
    have h0 := congrArg (fun r : LaurentPolynomial Pbar => r.coeff (-2 * (k : ℤ))) hπq
    rw [hπ_coeff, hcoeff_m, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      map_mul, map_pow] at h0
    have hg_ne : Ideal.Quotient.mk If (-gHomPoly K p) ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      intro h; exact hf_not_dvd_g (dvd_neg.mp h)
    have hC0 : Ideal.Quotient.mk If (MvPolynomial.C (q.coeff k)) = 0 :=
      (mul_eq_zero.mp h0).resolve_right (pow_ne_zero k hg_ne)
    by_contra hqk
    have hunit : IsUnit (MvPolynomial.C (q.coeff k) : P2 K) := (isUnit_iff_ne_zero.mpr hqk).map MvPolynomial.C
    have hmem : MvPolynomial.C (q.coeff k) ∈ If := Ideal.Quotient.eq_zero_iff_mem.mp hC0
    rw [Ideal.mem_span_singleton] at hmem
    exact hf_irred.not_isUnit (isUnit_of_dvd_unit hmem hunit)
  exact no_expMap_caseB_core K p w β hβ_ne hw_cases (Bbar := Bbar) AlgEquiv.refl φbar hφbar_nt hybar_inv haeval_ybar_inj

/-- **Lemma 3.5 (Gupta 2014):** Over an algebraically closed field `K` of prime characteristic `p`,
    no non-trivial `ExpMap` on `B_K = HomRing K p` fixes `bY`. -/
lemma no_expMap_B_with_y_inv [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (HomRing K p)) (hnt : φ.IsNontrivial) (hy : bY K p ∈ φ.invSubalg) : False := by
  obtain ⟨φ₂, w, hnt₂, hy₂, hw₂, hw_cases⟩ := exists_factor_inv_of_bY_inv K p φ hnt hy
  rcases hw_cases with rfl | rfl | ⟨μ, hμ0, rfl⟩
  · exact no_expMap_caseB K p φ₂ hnt₂ hy₂ (MvPolynomial.X 0) hw₂ (Or.inl rfl)
  · exact no_expMap_caseB K p φ₂ hnt₂ hy₂ (MvPolynomial.X 1) hw₂ (Or.inr (Or.inl rfl))
  · by_cases hμ1 : μ = 1
    · subst hμ1
      have hw' : bC K p (MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ (p + 1)) ∈ φ₂.invSubalg := by
        simpa using hw₂
      exact no_expMap_caseA K p φ₂ hnt₂ hy₂ hw'
    · exact no_expMap_caseB K p φ₂ hnt₂ hy₂ _ hw₂ (Or.inr (Or.inr ⟨μ, hμ0, hμ1, rfl⟩))

set_option maxHeartbeats 400000 in
/-- **Proposition 3.6 (Gupta 2014):** Over an algebraically closed field `K` of prime characteristic `p`,
    every non-trivial exponential map `φ` on `AsanumaRing K p` satisfies
    `φ.invSubalg ≤ K[aX, aZ, aT]`. -/
lemma invSubalg_asanuma_le [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime]
    (φ : ExpMap K (AsanumaRing K p)) (hnt : φ.IsNontrivial) :
    φ.invSubalg ≤ Algebra.adjoin K ({aX K p, aZ K p, aT K p} : Set (AsanumaRing K p)) := by
  classical
  have hp : 1 < p := hp_prime.out.one_lt
  let S : Subalgebra K (AsanumaRing K p) := Algebra.adjoin K ({aX K p, aZ K p, aT K p} : Set (AsanumaRing K p))
  -- Helper: any `q : P2 K` embeds into `S` as `⟨LaurentPolynomial.C q, _⟩`.
  have hC_mem_A : ∀ q : P2 K, LaurentPolynomial.C q ∈ AsanumaSubalg K p := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => exact (AsanumaSubalg K p).algebraMap_mem c
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul]
      match j with
      | 0 => exact mul_mem ha (aZ K p).2
      | 1 => exact mul_mem ha (aT K p).2
  have hC_mem_S : ∀ q : P2 K, (⟨LaurentPolynomial.C q, hC_mem_A q⟩ : AsanumaRing K p) ∈ S := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have : (⟨LaurentPolynomial.C (MvPolynomial.C c), hC_mem_A _⟩ : AsanumaRing K p) =
          algebraMap K (AsanumaRing K p) c := Subtype.ext rfl
      rw [this]; exact S.algebraMap_mem c
    | add a b ha hb =>
      have : (⟨LaurentPolynomial.C (a + b), hC_mem_A _⟩ : AsanumaRing K p) =
          ⟨LaurentPolynomial.C a, hC_mem_A a⟩ + ⟨LaurentPolynomial.C b, hC_mem_A b⟩ :=
        Subtype.ext (map_add _ a b)
      rw [this]; exact add_mem ha hb
    | mul_X a j ha =>
      match j with
      | 0 =>
        have : (⟨LaurentPolynomial.C (a * MvPolynomial.X 0), hC_mem_A _⟩ : AsanumaRing K p) =
            ⟨LaurentPolynomial.C a, hC_mem_A a⟩ * aZ K p := Subtype.ext (map_mul _ a _)
        rw [this]; exact mul_mem ha (Algebra.subset_adjoin (by simp))
      | 1 =>
        have : (⟨LaurentPolynomial.C (a * MvPolynomial.X 1), hC_mem_A _⟩ : AsanumaRing K p) =
            ⟨LaurentPolynomial.C a, hC_mem_A a⟩ * aT K p := Subtype.ext (map_mul _ a _)
        rw [this]; exact mul_mem ha (Algebra.subset_adjoin (by simp))
  -- Helper: if `(a : Ambient K).coeff m = 0` for all `m < 0`, then `a ∈ S`.
  have hnonneg_mem_S : ∀ a : AsanumaRing K p, (∀ m : ℤ, m < 0 → (a : Ambient K).coeff m = 0) → a ∈ S := by
    intro a ha_nn
    have hsum : (a : Ambient K) = ∑ m ∈ suppA K (a : Ambient K), singleT K m ((a : Ambient K).coeff m) := by
      apply AddMonoidAlgebra.ext; apply Finsupp.ext; intro m
      change (a : Ambient K).coeff m = (∑ j ∈ suppA K (a : Ambient K), singleT K j ((a : Ambient K).coeff j)).coeff m
      rw [coeff_sum_A]
      by_cases hm : m ∈ suppA K (a : Ambient K)
      · rw [Finset.sum_eq_single m]
        · rw [coeff_singleT, if_pos rfl]
        · intro j _ hne; rw [coeff_singleT, if_neg hne]
        · intro hnm; exact absurd hm hnm
      · have h0 : (a : Ambient K).coeff m = 0 := by simpa [mem_suppA_iff] using hm
        rw [h0]; symm; apply Finset.sum_eq_zero; intro j hj
        have hne : j ≠ m := fun h => hm (h ▸ hj)
        rw [coeff_singleT, if_neg hne]
    have ha_eq : a = ∑ m ∈ suppA K (a : Ambient K),
        aX K p ^ m.toNat * ⟨LaurentPolynomial.C ((a : Ambient K).coeff m), hC_mem_A _⟩ := by
      apply Subtype.ext
      nth_rw 1 [hsum]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_nn : 0 ≤ m := by
        by_contra hlt; push Not at hlt
        exact (mem_suppA_iff K _ m).mp hm (ha_nn m hlt)
      have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nn
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, aX, genX, singleT_eq_C_mul_T,
        LaurentPolynomial.T_pow, mul_one, hmn, mul_comm]
    rw [ha_eq]
    refine sum_mem fun m _ => mul_mem (pow_mem (Algebra.subset_adjoin (by simp)) _) (hC_mem_S _)
  -- Now prove `φ.invSubalg ≤ S` by contradiction!
  intro a ha_inv
  by_contra ha_notS
  obtain ⟨m₀, hm₀_neg, hm₀_ne⟩ : ∃ m₀ : ℤ, m₀ < 0 ∧ (a : Ambient K).coeff m₀ ≠ 0 := by
    by_contra hall; push Not at hall
    exact ha_notS (hnonneg_mem_S a hall)
  have ha_ne : (a : Ambient K) ≠ 0 := fun h0 => hm₀_ne (by rw [h0]; rfl)
  -- Homogenize `φ` by `grX` via `homogenize_subalgOfPoly_grX`!
  obtain ⟨φ₁, hφ₁_nt, hφ₁_inv⟩ :=
    homogenize_subalgOfPoly_grX K (fPoly K p) (fPoly_ne_zero K p hp) φ hnt
  let a_top : AsanumaRing K p := ⟨(grX K).topComp (a : Ambient K), by
    by_cases h0 : (a : Ambient K) = 0
    · simp [ZGrading.topComp, h0, (AsanumaSubalg K p).zero_mem]
    · rw [ZGrading.topComp, dif_neg h0]
      change _ ∈ SubalgOfPoly K (fPoly K p)
      rw [mem_subalgOfPoly_iff]
      intro m hm
      change (-fPoly K p) ^ ((-m + 1) / 2).toNat ∣
        (singleT K (-((grX K).topDeg (a : Ambient K) h0))
          ((a : Ambient K).coeff (-((grX K).topDeg (a : Ambient K) h0)))).coeff m
      rw [coeff_singleT]
      split_ifs with hmeq
      · subst hmeq; exact (mem_subalgOfPoly_iff K (fPoly K p) _).mp a.2 _ hm
      · exact dvd_zero _⟩
  have ha_top_inv : a_top ∈ φ₁.invSubalg := hφ₁_inv a ha_inv
  let d : ℤ := (grX K).topDeg (a : Ambient K) ha_ne
  have hd_pos : 0 < d := by
    have hle : (grX K).DegLe (a : Ambient K) d := (grX K).degLe_topDeg ha_ne
    have hle' : -m₀ ≤ d := by
      by_contra hgt; push Not at hgt
      have h0 : (grX K).proj (-m₀) (a : Ambient K) = 0 := hle (-m₀) hgt
      have hc0 := congrArg (fun r : Ambient K => r.coeff m₀) h0
      change (singleT K (-(-m₀)) ((a : Ambient K).coeff (-(-m₀)))).coeff m₀ = 0 at hc0
      rw [neg_neg, coeff_singleT, if_pos rfl] at hc0
      exact hm₀_ne hc0
    omega
  have ha_top_val : (a_top : Ambient K) = singleT K (-d) ((a : Ambient K).coeff (-d)) := by
    change (grX K).topComp (a : Ambient K) = _
    rw [ZGrading.topComp, dif_neg ha_ne]; rfl
  have hc_ne : (a : Ambient K).coeff (-d) ≠ 0 := by
    intro hc0
    have htop0 : (grX K).topComp (a : Ambient K) = 0 := by
      rw [ZGrading.topComp, dif_neg ha_ne]
      change singleT K (-d) ((a : Ambient K).coeff (-d)) = 0
      rw [hc0, singleT_eq_C_mul_T, map_zero, zero_mul]
    exact (grX K).topComp_ne_zero ha_ne htop0
  -- Factor `a_top = aY * rest` in `AsanumaRing K p`!
  have hdvd : (-fPoly K p) ^ ((-(-d) + 1) / 2).toNat ∣ (a : Ambient K).coeff (-d) :=
    (mem_subalgOfPoly_iff K (fPoly K p) _).mp a.2 (-d) (by omega)
  let k : ℕ := d.toNat
  have hk_eq : (k : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hk_pos : 0 < k := by omega
  let s : ℕ := (k + 1) / 2
  let r : ℕ := k % 2
  have hs_pos : 0 < s := by omega
  have hs_eq : ((-(-d) + 1) / 2).toNat = s := by omega
  rw [hs_eq] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  let rest : AsanumaRing K p :=
    aX K p ^ r * aY K p ^ (s - 1) * ⟨LaurentPolynomial.C q, hC_mem_A q⟩
  have hfac : a_top = aY K p * rest := by
    apply Subtype.ext
    rw [ha_top_val, hq]
    simp only [rest, Subalgebra.coe_mul, Subalgebra.coe_pow, aX, aY, genX, genY,
      singleT_eq_C_mul_T, mul_pow, LaurentPolynomial.T_pow, map_mul, map_pow]
    have hT : (LaurentPolynomial.T (-2 : ℤ) : Ambient K) * (LaurentPolynomial.T ((r : ℤ) * 1) *
        LaurentPolynomial.T (((s - 1 : ℕ) : ℤ) * -2)) = LaurentPolynomial.T (-d) := by
      rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
      congr 1; omega
    have hC : LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.C (-fPoly K p) ^ (s - 1) =
        LaurentPolynomial.C (-fPoly K p) ^ s := by
      rw [← pow_succ', show s - 1 + 1 = s by omega]
    calc LaurentPolynomial.C (-fPoly K p) ^ s * LaurentPolynomial.C q * LaurentPolynomial.T (-d)
        = (LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.C (-fPoly K p) ^ (s - 1)) *
            LaurentPolynomial.C q *
            (LaurentPolynomial.T (-2 : ℤ) * (LaurentPolynomial.T ((r : ℤ) * 1) *
              LaurentPolynomial.T (((s - 1 : ℕ) : ℤ) * -2))) := by rw [hC, hT]
      _ = LaurentPolynomial.C (-fPoly K p) * LaurentPolynomial.T (-2 : ℤ) *
            (LaurentPolynomial.T ((r : ℤ) * 1) *
              (LaurentPolynomial.C (-fPoly K p) ^ (s - 1) *
                LaurentPolynomial.T (((s - 1 : ℕ) : ℤ) * -2)) * LaurentPolynomial.C q) := by ring
  have ha_top_ne : a_top ≠ 0 := fun h0 => by
    have := congrArg (fun x : AsanumaRing K p => (x : Ambient K).coeff (-d)) h0
    rw [ha_top_val, coeff_singleT, if_pos rfl] at this
    exact hc_ne this
  rw [hfac] at ha_top_inv ha_top_ne
  have haY_inv : aY K p ∈ φ₁.invSubalg :=
    (φ₁.mem_invSubalg_of_mul (left_ne_zero_of_mul ha_top_ne) (right_ne_zero_of_mul ha_top_ne) ha_top_inv).1
  -- Homogenize `φ₁` by `grZT` to `HomRing K p` via `homogenize_asanuma_to_hom_grZT`!
  obtain ⟨φ₂, hφ₂_nt, hφ₂_inv⟩ := homogenize_asanuma_to_hom_grZT K p hp φ₁ hφ₁_nt
  have htop_genY : (grZT K p).topComp (genY K p) = genYB K p := by
    have hgenY_ne : genY K p ≠ 0 := by
      intro h0
      have := congrArg (fun r : Ambient K => r.coeff (-2)) h0
      rw [genY, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl] at this
      exact fPoly_ne_zero K p hp (neg_eq_zero.mp this)
    -- Show `topDeg (genY K p) = p^2 * (p + 1)` and `proj (p^2 * (p + 1)) (genY K p) = genYB K p`!
    let D0 : ℤ := (p : ℤ) ^ 2 * ((p : ℤ) + 1)
    have hpZ : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    have hD0_gt_p : (p : ℤ) < D0 := by dsimp only [D0]; nlinarith
    have hproj_fPoly : ∀ d' : ℤ, projP2 K p d' (-fPoly K p) =
        if d' = D0 then -gHomPoly K p else if d' = (p : ℤ) then -MvPolynomial.X 1 else 0 := by
      intro d'
      ext e
      rw [coeff_projP2]
      have hneg_f : (-fPoly K p).coeff e =
          -(MvPolynomial.X (0 : Fin 2) ^ (p ^ 2) : P2 K).coeff e -
          (MvPolynomial.X (1 : Fin 2) : P2 K).coeff e -
          (MvPolynomial.X (1 : Fin 2) ^ (p * (p + 1)) : P2 K).coeff e := by
        simp only [fPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add]; ring
      have hneg_g : (-gHomPoly K p).coeff e =
          -(MvPolynomial.X (0 : Fin 2) ^ (p ^ 2) : P2 K).coeff e -
          (MvPolynomial.X (1 : Fin 2) ^ (p * (p + 1)) : P2 K).coeff e := by
        simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add]; ring
      have hD0_ne_p : D0 ≠ (p : ℤ) := ne_of_gt hD0_gt_p
      by_cases he1 : e = Finsupp.single 0 (p ^ 2)
      · subst he1
        have hne2 : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 0 (p ^ 2) := by
          intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) h; simp at this
        have hne3 : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ Finsupp.single 0 (p ^ 2) := by
          intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; nlinarith
        have hwt : ((p : ℤ) + 1) * ↑((Finsupp.single (0 : Fin 2) (p ^ 2) : Fin 2 →₀ ℕ) 0) +
            (p : ℤ) * ↑((Finsupp.single (0 : Fin 2) (p ^ 2) : Fin 2 →₀ ℕ) 1) = D0 := by
          simp [D0]; ring
        have hcf : (-fPoly K p).coeff (Finsupp.single 0 (p ^ 2)) = -1 := by
          rw [hneg_f, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X',
            if_pos rfl, if_neg hne2, if_neg hne3]; ring
        have hcg : (-gHomPoly K p).coeff (Finsupp.single 0 (p ^ 2)) = -1 := by
          rw [hneg_g, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, if_pos rfl, if_neg hne3]; ring
        have hcX1 : (-MvPolynomial.X (1 : Fin 2) : P2 K).coeff (Finsupp.single 0 (p ^ 2)) = 0 := by
          rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X', if_neg hne2, neg_zero]
        rw [hwt, hcf]
        by_cases hd1 : d' = D0
        · subst hd1; rw [if_pos rfl, if_pos rfl, hcg]
        · rw [if_neg (Ne.symm hd1), if_neg hd1]
          split_ifs
          · exact hcX1.symm
          · rfl
      · by_cases he2 : e = Finsupp.single 1 1
        · subst he2
          have hne1 : Finsupp.single (0 : Fin 2) (p ^ 2) ≠ Finsupp.single 1 1 := by
            intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) h; simp at this
          have hne3 : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ Finsupp.single 1 1 := by
            intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) h; simp at this; nlinarith
          have hwt : ((p : ℤ) + 1) * ↑((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) +
              (p : ℤ) * ↑((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1) = (p : ℤ) := by
            simp
          have hcf : (-fPoly K p).coeff (Finsupp.single 1 1) = -1 := by
            rw [hneg_f, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X',
              if_neg hne1, if_pos rfl, if_neg hne3]; ring
          have hcg : (-gHomPoly K p).coeff (Finsupp.single 1 1) = 0 := by
            rw [hneg_g, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, if_neg hne1, if_neg hne3]; ring
          have hcX1 : (-MvPolynomial.X (1 : Fin 2) : P2 K).coeff (Finsupp.single 1 1) = -1 := by
            rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X', if_pos rfl]
          rw [hwt, hcf]
          by_cases hd1 : d' = D0
          · subst hd1; rw [if_neg (Ne.symm hD0_ne_p), if_pos rfl, hcg]
          · rw [if_neg hd1]
            by_cases hd2 : d' = (p : ℤ)
            · subst hd2; rw [if_pos rfl, if_pos rfl, hcX1]
            · rw [if_neg (Ne.symm hd2), if_neg hd2]; rfl
        · by_cases he3 : e = Finsupp.single 1 (p * (p + 1))
          · subst he3
            have hne1 : Finsupp.single (0 : Fin 2) (p ^ 2) ≠ Finsupp.single 1 (p * (p + 1)) := by
              intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; nlinarith
            have hne2 : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 1 (p * (p + 1)) := by
              intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 1) h; simp at this; nlinarith
            have hwt : ((p : ℤ) + 1) * ↑((Finsupp.single (1 : Fin 2) (p * (p + 1)) : Fin 2 →₀ ℕ) 0) +
                (p : ℤ) * ↑((Finsupp.single (1 : Fin 2) (p * (p + 1)) : Fin 2 →₀ ℕ) 1) = D0 := by
              simp [D0]; ring
            have hcf : (-fPoly K p).coeff (Finsupp.single 1 (p * (p + 1))) = -1 := by
              rw [hneg_f, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X',
                if_neg hne1, if_neg hne2, if_pos rfl]; ring
            have hcg : (-gHomPoly K p).coeff (Finsupp.single 1 (p * (p + 1))) = -1 := by
              rw [hneg_g, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, if_neg hne1, if_pos rfl]; ring
            have hcX1 : (-MvPolynomial.X (1 : Fin 2) : P2 K).coeff (Finsupp.single 1 (p * (p + 1))) = 0 := by
              rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X', if_neg hne2, neg_zero]
            rw [hwt, hcf]
            by_cases hd1 : d' = D0
            · subst hd1; rw [if_pos rfl, if_pos rfl, hcg]
            · rw [if_neg (Ne.symm hd1), if_neg hd1]
              split_ifs
              · exact hcX1.symm
              · rfl
          · have hcf : (-fPoly K p).coeff e = 0 := by
              rw [hneg_f, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X',
                if_neg (Ne.symm he1), if_neg (Ne.symm he2), if_neg (Ne.symm he3)]; ring
            have hcg : (-gHomPoly K p).coeff e = 0 := by
              rw [hneg_g, MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow,
                if_neg (Ne.symm he1), if_neg (Ne.symm he3)]; ring
            have hcX1 : (-MvPolynomial.X (1 : Fin 2) : P2 K).coeff e = 0 := by
              rw [MvPolynomial.coeff_neg, MvPolynomial.coeff_X', if_neg (Ne.symm he2), neg_zero]
            rw [hcf, ite_self]
            split_ifs
            · exact hcg.symm
            · exact hcX1.symm
            · rfl
    have hproj_genY : ∀ d' : ℤ, (grZT K p).proj d' (genY K p) =
        singleT K (-2) (projP2 K p d' (-fPoly K p)) := by
      intro d'
      apply AddMonoidAlgebra.ext; apply Finsupp.ext; intro m
      change (∑ j ∈ suppA K (genY K p), singleT K j (projP2 K p d' ((genY K p).coeff j))).coeff m = _
      rw [coeff_sum_projP2, coeff_singleT]
      have hcoeff_m : (genY K p).coeff m = if (-2 : ℤ) = m then -fPoly K p else 0 := by
        rw [genY, ← singleT_eq_C_mul_T, coeff_singleT]
      rw [hcoeff_m]
      split_ifs with hm
      · rfl
      · ext e; simp [coeff_projP2]
    have hD0_proj : (grZT K p).proj D0 (genY K p) = genYB K p := by
      rw [hproj_genY D0, hproj_fPoly D0, if_pos rfl, genYB, singleT_eq_C_mul_T]
    have hD0_ne : (grZT K p).proj D0 (genY K p) ≠ 0 := by
      rw [hD0_proj]
      intro h0
      have hc := congrArg (fun r : Ambient K => (r.coeff (-2)).coeff (Finsupp.single 0 (p ^ 2))) h0
      rw [genYB, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl] at hc
      simp only [gHomPoly, MvPolynomial.coeff_neg, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow] at hc
      have hne : Finsupp.single (1 : Fin 2) (p * (p + 1)) ≠ Finsupp.single 0 (p ^ 2) := by
        intro h; have := congrArg (fun u : Fin 2 →₀ ℕ => u 0) h; simp at this; nlinarith
      rw [if_neg hne, add_zero] at hc
      exact neg_ne_zero.mpr one_ne_zero hc
    have hle_D0 : (grZT K p).DegLe (genY K p) D0 := by
      intro d' hd'
      rw [hproj_genY d', hproj_fPoly d', if_neg (by omega), if_neg (by omega),
        singleT_eq_C_mul_T, map_zero, zero_mul]
    have htop_eq : (grZT K p).topDeg (genY K p) hgenY_ne = D0 := by
      apply le_antisymm
      · by_contra hgt; push Not at hgt
        exact (grZT K p).topComp_ne_zero hgenY_ne
          (by rw [ZGrading.topComp, dif_neg hgenY_ne]; exact hle_D0 _ hgt)
      · by_contra hlt; push Not at hlt
        exact hD0_ne ((grZT K p).degLe_topDeg hgenY_ne D0 hlt)
    rw [ZGrading.topComp, dif_neg hgenY_ne, htop_eq, hD0_proj]
  have hbY_inv : bY K p ∈ φ₂.invSubalg := by
    have h1 := hφ₂_inv (aY K p) haY_inv
    convert h1 using 1
    apply Subtype.ext; exact htop_genY.symm
  exact no_expMap_B_with_y_inv K p φ₂ hφ₂_nt hbY_inv

/-- **Theorem 3.8 (Gupta 2014):** Over an algebraically closed field `K` of prime characteristic `p`,
    the Asanuma–Gupta ring `AsanumaRing K p` is not isomorphic as a `K`-algebra to `K[X_0, X_1, X_2]`. -/
theorem asanuma_not_algEquiv_mvPoly3 [CharP K p] [IsAlgClosed K] [hp_prime : Fact p.Prime] :
    ¬ Nonempty (AsanumaRing K p ≃ₐ[K] MvPolynomial (Fin 3) K) := by
  have hp : 1 < p := hp_prime.out.one_lt
  let S : Subalgebra K (AsanumaRing K p) := Algebra.adjoin K ({aX K p, aZ K p, aT K p} : Set (AsanumaRing K p))
  have hS_ne_top : S ≠ ⊤ := by
    intro htop
    have haY_mem : aY K p ∈ S := htop ▸ trivial
    have hS_nn : ∀ x ∈ S, ∀ m : ℤ, m < 0 → (x : Ambient K).coeff m = 0 := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · intro m hm; change (singleT K 1 1).coeff m = 0; simp [coeff_singleT]; omega
        · intro m hm; change (singleT K 0 (MvPolynomial.X 0)).coeff m = 0; simp [coeff_singleT]; omega
        · intro m hm; change (singleT K 0 (MvPolynomial.X 1)).coeff m = 0; simp [coeff_singleT]; omega
      | algebraMap c =>
        intro m hm; change (singleT K 0 (MvPolynomial.C c)).coeff m = 0; simp [coeff_singleT]; omega
      | add a b _ _ ha hb =>
        intro m hm; rw [Subalgebra.coe_add, coeff_add_A, ha m hm, hb m hm, add_zero]
      | mul a b _ _ ha hb =>
        intro m hm
        rw [Subalgebra.coe_mul, coeff_mul_A]
        apply Finset.sum_eq_zero; intro i _
        apply Finset.sum_eq_zero; intro j _
        split_ifs with hij
        · by_cases hi : i < 0
          · rw [ha i hi, zero_mul]
          · rw [hb j (by omega), mul_zero]
        · rfl
    have h0 := hS_nn (aY K p) haY_mem (-2) (by decide)
    change (genY K p).coeff (-2) = 0 at h0
    rw [genY, ← singleT_eq_C_mul_T, coeff_singleT, if_pos rfl] at h0
    exact fPoly_ne_zero K p hp (neg_eq_zero.mp h0)
  exact ExpMap.not_algEquiv_mvPoly3_of_invSubalg_le S hS_ne_top (invSubalg_asanuma_le K p)

end Lemma35AndMain

/- ## Section 8: Base change `ZMod p → AlgebraicClosure (ZMod p)` and main theorem -/

section BaseChangeAndMain

/-- Base change of `AsanumaRing` along a field extension `k → K`:
    `K ⊗[k] AsanumaRing k p ≃ₐ[K] AsanumaRing K p`. -/
noncomputable def asanuma_baseChange_equiv (k K : Type*) [Field k] [Field K] [Algebra k K] (p : ℕ) :
    TensorProduct k K (AsanumaRing k p) ≃ₐ[K] AsanumaRing K p := by
  classical
  let mapP2 : P2 k →ₐ[k] P2 K := MvPolynomial.mapAlgHom (Algebra.ofId k K)
  let mapAmb : Ambient k →ₐ[k] Ambient K :=
    { toRingHom := AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom
      commutes' := fun c => by
        change AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom (AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.C c)) =
          AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.C (algebraMap k K c))
        rw [AddMonoidAlgebra.mapRingHom_single]; simp [mapP2] }
  have hmapAmb_coeff : ∀ (x : Ambient k) (m : ℤ), (mapAmb x).coeff m = mapP2 (x.coeff m) := by
    intro x m
    change (AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom x).coeff m = _
    simp [AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.map, mapP2]
  have hmapAmb_genX : mapAmb (genX k) = genX K := by
    change AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom (AddMonoidAlgebra.single (1 : ℤ) 1) =
      AddMonoidAlgebra.single (1 : ℤ) 1
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hmapAmb_genZ : mapAmb (genZ k) = genZ K := by
    change AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom (AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.X 0)) =
      AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.X 0)
    rw [AddMonoidAlgebra.mapRingHom_single]; simp [mapP2]
  have hmapAmb_genT : mapAmb (genT k) = genT K := by
    change AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom (AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.X 1)) =
      AddMonoidAlgebra.single (0 : ℤ) (MvPolynomial.X 1)
    rw [AddMonoidAlgebra.mapRingHom_single]; simp [mapP2]
  have hmapAmb_genY : mapAmb (genY k p) = genY K p := by
    rw [genY, genY, ← singleT_eq_C_mul_T, ← singleT_eq_C_mul_T]
    change AddMonoidAlgebra.mapRingHom ℤ mapP2.toRingHom (AddMonoidAlgebra.single (-2 : ℤ) (-fPoly k p)) =
      AddMonoidAlgebra.single (-2 : ℤ) (-fPoly K p)
    rw [AddMonoidAlgebra.mapRingHom_single]
    congr 1; simp [mapP2, fPoly]
  have hmap_mem : ∀ a : AsanumaRing k p, mapAmb (a : Ambient k) ∈ AsanumaSubalg K p := by
    have haux : ∀ x ∈ AsanumaSubalg k p, mapAmb x ∈ AsanumaSubalg K p := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [hmapAmb_genX]; exact (aX K p).2
        · rw [hmapAmb_genY]; exact (aY K p).2
        · rw [hmapAmb_genZ]; exact (aZ K p).2
        · rw [hmapAmb_genT]; exact (aT K p).2
      | algebraMap c =>
        rw [AlgHom.commutes]; exact (AsanumaSubalg K p).algebraMap_mem (algebraMap k K c)
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    intro a; exact haux a.1 a.2
  let iA : AsanumaRing k p →ₐ[k] AsanumaRing K p :=
    { toFun := fun a => ⟨mapAmb (a : Ambient k), hmap_mem a⟩
      map_one' := Subtype.ext (map_one mapAmb)
      map_mul' := fun a b => Subtype.ext (map_mul mapAmb _ _)
      map_zero' := Subtype.ext (map_zero mapAmb)
      map_add' := fun a b => Subtype.ext (map_add mapAmb _ _)
      commutes' := fun c => Subtype.ext (mapAmb.commutes c) }
  let φ_k : TensorProduct k K (AsanumaRing k p) →ₐ[k] AsanumaRing K p :=
    Algebra.TensorProduct.lift ((Algebra.ofId K (AsanumaRing K p)).restrictScalars k) iA
      (fun _ _ => Commute.all _ _)
  let φ : TensorProduct k K (AsanumaRing k p) →ₐ[K] AsanumaRing K p :=
    { toRingHom := φ_k.toRingHom
      commutes' := fun c => by
        change φ_k (c ⊗ₜ[k] 1) = algebraMap K (AsanumaRing K p) c
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl }
  have hsurj : Function.Surjective φ := by
    have haux : ∀ y ∈ AsanumaSubalg K p, y ∈ Subalgebra.map (AsanumaSubalg K p).val φ.range := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨aX K p, ⟨(1 : K) ⊗ₜ[k] aX k p, by
            change φ_k ((1 : K) ⊗ₜ[k] aX k p) = aX K p
            rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; exact Subtype.ext hmapAmb_genX⟩, rfl⟩
        · exact ⟨aY K p, ⟨(1 : K) ⊗ₜ[k] aY k p, by
            change φ_k ((1 : K) ⊗ₜ[k] aY k p) = aY K p
            rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; exact Subtype.ext hmapAmb_genY⟩, rfl⟩
        · exact ⟨aZ K p, ⟨(1 : K) ⊗ₜ[k] aZ k p, by
            change φ_k ((1 : K) ⊗ₜ[k] aZ k p) = aZ K p
            rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; exact Subtype.ext hmapAmb_genZ⟩, rfl⟩
        · exact ⟨aT K p, ⟨(1 : K) ⊗ₜ[k] aT k p, by
            change φ_k ((1 : K) ⊗ₜ[k] aT k p) = aT K p
            rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; exact Subtype.ext hmapAmb_genT⟩, rfl⟩
      | algebraMap c =>
        exact ⟨algebraMap K (AsanumaRing K p) c, ⟨c ⊗ₜ[k] 1, φ.commutes c⟩, rfl⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb
        exact ⟨a' + b', add_mem ha' hb', rfl⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb
        exact ⟨a' * b', mul_mem ha' hb', rfl⟩
    intro y
    obtain ⟨y', ⟨x, hx⟩, hy'⟩ := haux y.1 y.2
    exact ⟨x, hx.trans (Subtype.ext hy')⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- Expand `x` in a `k`-basis `B` of `K`!
    let B := Module.Free.chooseBasis k K
    obtain ⟨S_B, f, hx_sum⟩ : ∃ (S_B : Finset (Module.Free.ChooseBasisIndex k K))
        (f : Module.Free.ChooseBasisIndex k K → AsanumaRing k p),
        x = ∑ i ∈ S_B, (B i) ⊗ₜ[k] (f i) := by
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨∅, fun _ => 0, by simp⟩
      | tmul c a =>
        refine ⟨(B.repr c).support, fun i => (B.repr c i) • a, ?_⟩
        have hc : c = ∑ i ∈ (B.repr c).support, (B.repr c i) • B i := by
          simpa [Finsupp.linearCombination_apply, Finsupp.sum] using (B.linearCombination_repr c).symm
        conv_lhs => rw [hc]
        rw [TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
      | add x₁ x₂ h₁ h₂ =>
        obtain ⟨S₁, f₁, rfl⟩ := h₁
        obtain ⟨S₂, f₂, rfl⟩ := h₂
        refine ⟨S₁ ∪ S₂, fun i => (if i ∈ S₁ then f₁ i else 0) + (if i ∈ S₂ then f₂ i else 0), ?_⟩
        simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_subset Finset.subset_union_left (fun i _ hi => by simp [hi])]
          exact Finset.sum_congr rfl fun i hi => by simp [hi]
        · rw [← Finset.sum_subset Finset.subset_union_right (fun i _ hi => by simp [hi])]
          exact Finset.sum_congr rfl fun i hi => by simp [hi]
    -- Show `f i = 0` for every `i ∈ S_B` by checking each `(m, d)` coefficient!
    have hf_zero : ∀ i ∈ S_B, f i = 0 := by
      intro i hi
      apply Subtype.ext; apply AddMonoidAlgebra.ext; apply Finsupp.ext; intro m
      ext d
      have h0 : (((φ x : AsanumaRing K p) : Ambient K).coeff m).coeff d = 0 := by
        rw [hx]; rfl
      rw [hx_sum, map_sum, AddSubmonoidClass.coe_finsetSum, coeff_sum_A, MvPolynomial.coeff_sum] at h0
      have hterm : ∀ j ∈ S_B,
          (((φ ((B j) ⊗ₜ[k] f j) : AsanumaRing K p) : Ambient K).coeff m).coeff d =
          (((f j : Ambient k).coeff m).coeff d) • (B j) := by
        intro j _
        have hφj : (φ ((B j) ⊗ₜ[k] f j) : Ambient K) = algebraMap K (Ambient K) (B j) * mapAmb (f j : Ambient k) := by
          change (φ_k ((B j) ⊗ₜ[k] f j) : Ambient K) = _
          rw [Algebra.TensorProduct.lift_tmul]; rfl
        rw [hφj]
        have hCmul : (algebraMap K (Ambient K) (B j) * mapAmb (f j : Ambient k)).coeff m =
            MvPolynomial.C (B j) * (mapAmb (f j : Ambient k)).coeff m := by
          change (LaurentPolynomial.C (MvPolynomial.C (B j)) * mapAmb (f j : Ambient k)).coeff m = _
          have h1 : (LaurentPolynomial.C (MvPolynomial.C (B j)) : Ambient K) = singleT K 0 (MvPolynomial.C (B j)) := rfl
          rw [h1, coeff_mul_A]
          by_cases hBj : B j = 0
          · rw [hBj, map_zero, zero_mul]
            apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _
            rw [coeff_singleT]; split_ifs <;> simp
          · have h0m : (0 : ℤ) ∈ suppA K (singleT K 0 (MvPolynomial.C (B j))) := by
              rw [mem_suppA_iff, coeff_singleT, if_pos rfl]; exact MvPolynomial.C_ne_zero.mpr hBj
            rw [Finset.sum_eq_single 0]
            · rw [coeff_singleT, if_pos rfl]
              by_cases hum : m ∈ suppA K (mapAmb (f j : Ambient k))
              · rw [Finset.sum_eq_single m]
                · simp
                · intro b _ hb; rw [if_neg (by omega)]
                · intro hnm; exact absurd hum hnm
              · have hu0 : (mapAmb (f j : Ambient k)).coeff m = 0 := by simpa [mem_suppA_iff] using hum
                rw [hu0, mul_zero]
                apply Finset.sum_eq_zero; intro b hb
                have hne : b ≠ m := fun h => hum (h ▸ hb)
                rw [if_neg (by omega)]
            · intro a _ ha; apply Finset.sum_eq_zero; intro b _
              rw [coeff_singleT, if_neg (Ne.symm ha), zero_mul, ite_self]
            · intro hnm; exact absurd h0m hnm
        rw [hCmul, hmapAmb_coeff, MvPolynomial.coeff_C_mul]
        change B j * (MvPolynomial.map (algebraMap k K) ((f j : Ambient k).coeff m)).coeff d = _
        rw [MvPolynomial.coeff_map, mul_comm, ← Algebra.smul_def]
      rw [Finset.sum_congr rfl hterm] at h0
      exact (linearIndependent_iff'.mp B.linearIndependent) S_B
        (fun j => ((f j : Ambient k).coeff m).coeff d) h0 i hi
    rw [hx_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [hf_zero i hi, TensorProduct.tmul_zero]
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- Base change of `MvPolynomial (Fin 3) k` along a field extension `k → K`:
    `K ⊗[k] MvPolynomial (Fin 3) k ≃ₐ[K] MvPolynomial (Fin 3) K`. -/
noncomputable def mvPoly3_baseChange_equiv (k K : Type*) [Field k] [Field K] [Algebra k K] :
    TensorProduct k K (MvPolynomial (Fin 3) k) ≃ₐ[K] MvPolynomial (Fin 3) K := by
  let toP_k : TensorProduct k K (MvPolynomial (Fin 3) k) →ₐ[k] MvPolynomial (Fin 3) K :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId K (MvPolynomial (Fin 3) K)).restrictScalars k)
      (MvPolynomial.mapAlgHom (Algebra.ofId k K))
      (fun _ _ => Commute.all _ _)
  let toP : TensorProduct k K (MvPolynomial (Fin 3) k) →ₐ[K] MvPolynomial (Fin 3) K :=
    { toRingHom := toP_k.toRingHom
      commutes' := fun c => by
        change toP_k (c ⊗ₜ[k] 1) = algebraMap K _ c
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl }
  let fromP : MvPolynomial (Fin 3) K →ₐ[K] TensorProduct k K (MvPolynomial (Fin 3) k) :=
    MvPolynomial.aeval fun j => (1 : K) ⊗ₜ[k] (MvPolynomial.X j : MvPolynomial (Fin 3) k)
  refine AlgEquiv.ofAlgHom toP fromP ?_ ?_
  · apply MvPolynomial.algHom_ext; intro j
    simp only [AlgHom.comp_apply, AlgHom.id_apply, fromP, MvPolynomial.aeval_X]
    change toP_k ((1 : K) ⊗ₜ[k] MvPolynomial.X j) = MvPolynomial.X j
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; simp
  · have hmap : ∀ P : MvPolynomial (Fin 3) k,
        fromP (MvPolynomial.map (algebraMap k K) P) = (1 : K) ⊗ₜ[k] P := fun P => by
      induction P using MvPolynomial.induction_on with
      | C r =>
        rw [MvPolynomial.map_C]
        change fromP (algebraMap K _ (algebraMap k K r)) = _
        rw [fromP.commutes]
        change (algebraMap k K r) ⊗ₜ[k] (1 : MvPolynomial (Fin 3) k) =
          (1 : K) ⊗ₜ[k] (algebraMap k _ r)
        rw [← mul_one (algebraMap k K r), ← Algebra.smul_def, TensorProduct.smul_tmul,
          ← Algebra.algebraMap_eq_smul_one]
      | add a b ha hb => rw [map_add, map_add, ha, hb, TensorProduct.tmul_add]
      | mul_X a j ha =>
        rw [map_mul, MvPolynomial.map_X, map_mul, ha]
        simp only [fromP, MvPolynomial.aeval_X, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    apply Algebra.TensorProduct.ext'
    intro c P
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have h1 : toP (c ⊗ₜ[k] P) = MvPolynomial.C c * MvPolynomial.map (algebraMap k K) P := by
      change toP_k (c ⊗ₜ[k] P) = _; rw [Algebra.TensorProduct.lift_tmul]; rfl
    rw [h1, map_mul]
    have hC : fromP (MvPolynomial.C c) = c ⊗ₜ[k] (1 : MvPolynomial (Fin 3) k) := by
      change fromP (algebraMap K _ c) = _; exact fromP.commutes c
    rw [hC, hmap P, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Over `ZMod p`, `AsanumaRing (ZMod p) p ≇ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p)`. -/
theorem asanuma_not_algEquiv_mvPoly3_zmod (p : ℕ) [hp : Fact p.Prime] :
    ¬ Nonempty (AsanumaRing (ZMod p) p ≃ₐ[ZMod p] MvPolynomial (Fin 3) (ZMod p)) := by
  rintro ⟨e⟩
  let K := AlgebraicClosure (ZMod p)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let eTP_k : TensorProduct (ZMod p) K (AsanumaRing (ZMod p) p) ≃ₐ[ZMod p]
      TensorProduct (ZMod p) K (MvPolynomial (Fin 3) (ZMod p)) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  let eTP : TensorProduct (ZMod p) K (AsanumaRing (ZMod p) p) ≃ₐ[K]
      TensorProduct (ZMod p) K (MvPolynomial (Fin 3) (ZMod p)) :=
    { toRingEquiv := eTP_k.toRingEquiv
      commutes' := fun c => by
        change eTP_k (c ⊗ₜ[ZMod p] 1) = c ⊗ₜ[ZMod p] 1
        simp [eTP_k] }
  have eK : AsanumaRing K p ≃ₐ[K] MvPolynomial (Fin 3) K :=
    (asanuma_baseChange_equiv (ZMod p) K p).symm.trans
      (eTP.trans (mvPoly3_baseChange_equiv (ZMod p) K))
  exact asanuma_not_algEquiv_mvPoly3 K p ⟨eK⟩

end BaseChangeAndMain

end ZariskiCancelPosChar

theorem OMA.solution :
    type_of% @Arxiv.«2208.14736».zariski_cancellation_problem.variants.false_pos_card := by
  intro p hp ι _ hι hcancel
  have eι : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hι
  obtain ⟨eA4⟩ := ZariskiCancelPosChar.asanuma_poly_algEquiv (ZMod p) p
  let A_up := ULift.{_} (ZariskiCancelPosChar.AsanumaRing (ZMod p) p)
  let eUL : A_up ≃ₐ[ZMod p] ZariskiCancelPosChar.AsanumaRing (ZMod p) p :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have : Algebra.FiniteType (ZMod p) A_up :=
    Algebra.FiniteType.of_surjective eUL.symm.toAlgHom eUL.symm.surjective
  have ePoly : Polynomial (MvPolynomial ι (ZMod p)) ≃ₐ[ZMod p] Polynomial A_up :=
    (((Polynomial.mapAlgEquiv (MvPolynomial.renameEquiv (ZMod p) eι)).trans
      (MvPolynomial.finSuccEquiv (ZMod p) 3).symm).trans eA4.symm).trans
      (Polynomial.mapAlgEquiv eUL.symm)
  obtain ⟨eIso⟩ := hcancel (B := A_up) ⟨ePoly⟩
  exact ZariskiCancelPosChar.asanuma_not_algEquiv_mvPoly3_zmod p
    ⟨(eUL.symm.trans eIso.symm).trans (MvPolynomial.renameEquiv (ZMod p) eι)⟩


