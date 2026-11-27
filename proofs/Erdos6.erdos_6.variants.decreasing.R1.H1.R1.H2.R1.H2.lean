import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1
import Mathlib

/-!
# Vaughan's dyadic mean-value estimate

Adapted from @nil-commits, Arithmetica4, commit
023f6441c22a9ca0db1670e351e8ac44f00555ea, used under Apache-2.0.
The multiplicative large sieve, Vaughan's identity and the dyadic
Type I and Type II estimates are from RHDirect/Stage2BehrendSieve,
Stage2DirichletAP, Stage3BombieriVinogradov, Stage10ZeroDensity and
Stage11BombieriVinogradov. Arithmetica4 builds on Mathlib4 under Apache-2.0.
Credit: @marcusbuffett.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace RHDirect
namespace Stage2BehrendSieve

private lemma norm_sum_sq_eq_re {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 = (∑ x ∈ s, ∑ y ∈ s, f x * starRingEnd ℂ (f y)).re := by
  set z : ℂ := ∑ x ∈ s, f x
  rw [show ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]]
  congr 1; simp only [z, map_sum, Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_comm

/-! ## 1. Discrete Duality Principle & Abstract Large-Sieve / Bessel Inequality -/

/-- Complex Finset Cauchy–Schwarz inequality. -/
theorem cauchy_schwarz_complex {ι : Type*} (I : Finset ι) (u v : ι → ℂ) :
    ‖∑ i ∈ I, u i * v i‖ ^ 2 ≤ (∑ i ∈ I, ‖u i‖ ^ 2) * (∑ i ∈ I, ‖v i‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sum_le I _).trans_eq (Finset.sum_congr rfl fun i _ => norm_mul (u i) (v i))) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq I (fun i => ‖u i‖) (fun i => ‖v i‖))

/-- Cardinality form of complex Finset Cauchy–Schwarz: `‖∑_{i ∈ I} a_i‖² ≤ |I| ∑ ‖a_i‖²`. -/
theorem cauchy_schwarz_complex_card {ι : Type*} (I : Finset ι) (a : ι → ℂ) :
    ‖∑ i ∈ I, a i‖ ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  simpa using cauchy_schwarz_complex I (fun _ => (1 : ℂ)) a

/-- Discrete duality principle for finite complex bilinear forms. -/
theorem duality_principle {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdual : ∀ b : κ → ℂ, ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2)
    (a : ι → ℂ) : ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  set b : κ → ℂ := fun j => ∑ i ∈ I, K j i * a i
  set S : ℝ := ∑ j ∈ J, ‖b j‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hzero : S = 0
  · rw [hzero]; exact mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hSeq : S = (∑ i ∈ I, a i * starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j)).re := by
      have h1 : S = (∑ j ∈ J, b j * starRingEnd ℂ (b j)).re := by
        rw [Complex.re_sum]; exact Finset.sum_congr rfl fun j _ => by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [h1]; congr 1
      calc ∑ j ∈ J, b j * starRingEnd ℂ (b j) = ∑ j ∈ J, ∑ i ∈ I, K j i * a i * starRingEnd ℂ (b j) := Finset.sum_congr rfl fun j _ => Finset.sum_mul I _ _
        _ = ∑ i ∈ I, ∑ j ∈ J, K j i * a i * starRingEnd ℂ (b j) := Finset.sum_comm
        _ = ∑ i ∈ I, a i * starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j) := Finset.sum_congr rfl fun i _ => by
            rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]; ring
    have hneq : ∑ i ∈ I, ‖starRingEnd ℂ (∑ j ∈ J, starRingEnd ℂ (K j i) * b j)‖ ^ 2 =
        ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 := Finset.sum_congr rfl fun i _ => by rw [RCLike.norm_conj]
    have hCS : S ^ 2 ≤ (∑ i ∈ I, ‖a i‖ ^ 2) * (Δ * S) :=
      (pow_le_pow_left₀ hS0 (hSeq ▸ Complex.re_le_norm _) 2).trans <| (cauchy_schwarz_complex I a _).trans <| by
        rw [hneq]; exact mul_le_mul_of_nonneg_left (hdual b) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact le_of_mul_le_mul_right (by rw [← sq]; linarith : S * S ≤ (Δ * ∑ i ∈ I, ‖a i‖ ^ 2) * S) (lt_of_le_of_ne hS0 (Ne.symm hzero))

/-- Full primal/dual equivalence of the discrete duality principle. -/
theorem duality_principle_iff {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (∀ a : ι → ℂ, ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2) ↔
    (∀ b : κ → ℂ, ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2) :=
  ⟨fun hp b => duality_principle J I (fun i j => starRingEnd ℂ (K j i)) hΔ
      (fun a => by simpa [RingHomCompTriple.comp_apply, RingHom.id_apply] using hp a) b, duality_principle I J K hΔ⟩

/-- Dual Schur-test / Gram-matrix large-sieve bound. -/
theorem gram_large_sieve_dual {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ) {Δ : ℝ}
    (hGram : ∀ j ∈ J, ∑ j' ∈ J, ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖ ≤ Δ) (b : κ → ℂ) :
    ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 ≤ Δ * ∑ j ∈ J, ‖b j‖ ^ 2 := by
  set G : κ → κ → ℝ := fun j j' => ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖
  have hGsym : ∀ j j', G j j' = G j' j := fun j j' => by
    have hc : starRingEnd ℂ (∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)) = ∑ i ∈ I, K j' i * starRingEnd ℂ (K j i) := by
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
    dsimp only [G]; rw [← hc, RCLike.norm_conj]
  have hexp : ∑ i ∈ I, ‖∑ j ∈ J, starRingEnd ℂ (K j i) * b j‖ ^ 2 =
      (∑ j ∈ J, ∑ j' ∈ J, b j * starRingEnd ℂ (b j') * ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i).re := by
    simp_rw [norm_sum_sq_eq_re]; rw [← Complex.re_sum]; congr 1
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]; ring
  rw [hexp, Complex.re_sum]
  have h1 : ∑ j ∈ J, (∑ j' ∈ J, b j * starRingEnd ℂ (b j') * ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i).re ≤
      ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' := by
    refine Finset.sum_le_sum fun j _ => ?_; rw [Complex.re_sum]
    refine Finset.sum_le_sum fun j' _ => (Complex.re_le_norm _).trans_eq ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]; congr 1
    have hr : starRingEnd ℂ (∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)) = ∑ i ∈ I, starRingEnd ℂ (K j i) * K j' i := by
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    dsimp only [G]; rw [← hr, RCLike.norm_conj]
  have h2 : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' ≤ ∑ j ∈ J, ‖b j‖ ^ 2 * ∑ j' ∈ J, G j j' := by
    have ham : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * G j j' ≤ ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * G j j' :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖b j‖ - ‖b j'‖)]) (norm_nonneg _)
    refine ham.trans_eq ?_
    have hsp : ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * G j j' =
        (1 / 2) * (∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * G j j') + (1 / 2) * (∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * G j j') := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have hsw : ∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * G j j' = ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * G j j' := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by rw [hGsym]
    rw [hsp, hsw, Finset.sum_congr rfl fun j _ => (Finset.mul_sum J _ _).symm]; ring
  refine h1.trans (h2.trans ?_); rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => by rw [mul_comm Δ]; exact mul_le_mul_of_nonneg_left (hGram j hj) (sq_nonneg _)

/-- Bombieri / Gram-matrix Large Sieve Inequality via discrete duality. -/
theorem gram_large_sieve {ι κ : Type*} (I : Finset ι) (J : Finset κ) (K : κ → ι → ℂ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hGram : ∀ j ∈ J, ∑ j' ∈ J, ‖∑ i ∈ I, K j i * starRingEnd ℂ (K j' i)‖ ≤ Δ) (a : ι → ℂ) :
    ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 :=
  duality_principle I J K hΔ (gram_large_sieve_dual I J K hGram) a

/-- Discrete Hilbert / Bessel inequality for an orthogonal family on `I`. -/
theorem bessel_inequality_of_orthogonal {ι κ : Type*} [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (K : κ → ι → ℂ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (horth : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∑ i ∈ I, K j i * starRingEnd ℂ (K j' i) = 0)
    (hnorm : ∀ j ∈ J, ∑ i ∈ I, ‖K j i‖ ^ 2 ≤ Δ) (a : ι → ℂ) :
    ∑ j ∈ J, ‖∑ i ∈ I, K j i * a i‖ ^ 2 ≤ Δ * ∑ i ∈ I, ‖a i‖ ^ 2 := by
  refine gram_large_sieve I J K hΔ (fun j hj => ?_) a
  rw [Finset.sum_eq_single j]
  · have hd : ∑ i ∈ I, K j i * starRingEnd ℂ (K j i) = ((∑ i ∈ I, ‖K j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hd, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]; exact hnorm j hj
  · intro j' hj' hne; rw [horth j hj j' hj' hne.symm, norm_zero]
  · exact fun h => absurd hj h

/-! ## 2. Dirichlet Character Orthogonality & Multiplicative Mean-Square Inequality -/

section DirichletMeanSquare

/-- On units of `ZMod q`, every complex Dirichlet character has unit modulus and `conj(χ a) = χ(a⁻¹)`. -/
theorem dirichlet_norm_eq_one_and_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    ‖χ a‖ = 1 ∧ starRingEnd ℂ (χ a) = χ a⁻¹ := by
  obtain ⟨u, rfl⟩ := ha
  have hnp : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, norm_one]
  have hnorm : ‖χ (u : ZMod q)‖ = 1 := by
    by_contra hne; rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := pow_lt_pow_left₀ hlt (norm_nonneg _) (Fintype.card_pos (α := (ZMod q)ˣ)).ne'
      rw [hnp, one_pow] at h; exact lt_irrefl _ h
    · have h := pow_lt_pow_left₀ hgt zero_le_one (Fintype.card_pos (α := (ZMod q)ˣ)).ne'
      rw [hnp, one_pow] at h; exact lt_irrefl _ h
  refine ⟨hnorm, ?_⟩
  have h1 : χ (u : ZMod q) * starRingEnd ℂ (χ (u : ZMod q)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have h2 : χ (u : ZMod q) * χ (u : ZMod q)⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit (u : ZMod q) u.isUnit, map_one]
  exact mul_left_cancel₀ (fun h0 => zero_ne_one (by rw [h0, zero_mul] at h1; exact h1)) (h1.trans h2.symm)

/-- Conjugate orthogonality for Dirichlet characters mod `q`. -/
theorem dirichlet_orthogonality_conj {q : ℕ} [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * starRingEnd ℂ (χ b) = if IsUnit a ∧ a = b then (Nat.totient q : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · rw [Finset.sum_congr rfl fun χ _ => by rw [(dirichlet_norm_eq_one_and_conj χ hb).2, mul_comm],
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1 ▸ hb, h1.symm⟩ h2
    · exact absurd h2.2.symm h1
    · rfl
  · rw [Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit χ hb, map_zero, mul_zero],
      if_neg (fun h : IsUnit a ∧ a = b => hb (h.2 ▸ h.1))]

/-- Exact character Parseval / Plancherel identity on `ZMod q`. -/
theorem dirichlet_parseval_residue_classes {q : ℕ} [NeZero q] (I : Finset ℕ) (a : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, a n * χ (n : ZMod q)‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ r : (ZMod q)ˣ, ‖∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)), a n‖ ^ 2 := by
  simp_rw [norm_sum_sq_eq_re]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]; congr 1
  have hL : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ I, ∑ m ∈ I, a n * χ (n : ZMod q) * starRingEnd ℂ (a m * χ (m : ZMod q)) =
      ∑ n ∈ I, ∑ m ∈ I, if IsUnit (n : ZMod q) ∧ (n : ZMod q) = (m : ZMod q) then a n * starRingEnd ℂ (a m) * (Nat.totient q : ℂ) else 0 := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m _ => ?_
    have hm : ∑ χ : DirichletCharacter ℂ q, a n * χ (n : ZMod q) * starRingEnd ℂ (a m * χ (m : ZMod q)) =
        a n * starRingEnd ℂ (a m) * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * starRingEnd ℂ (χ (m : ZMod q)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by rw [map_mul]; ring
    rw [hm, dirichlet_orthogonality_conj]; split_ifs <;> ring
  rw [hL, Finset.mul_sum]
  have hs : ∀ r : (ZMod q)ˣ, (Nat.totient q : ℂ) *
      ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = (r : ZMod q)),
        ∑ m ∈ I.filter (fun m : ℕ => (m : ZMod q) = (r : ZMod q)), a n * starRingEnd ℂ (a m) =
      ∑ n ∈ I, ∑ m ∈ I, if (n : ZMod q) = (r : ZMod q) ∧ (m : ZMod q) = (r : ZMod q) then
        a n * starRingEnd ℂ (a m) * (Nat.totient q : ℂ) else 0 := fun r => by
    rw [Finset.mul_sum]; simp_rw [Finset.mul_sum, Finset.sum_filter]; refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : (n : ZMod q) = (r : ZMod q)
    · rw [if_pos hn]; refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : (m : ZMod q) = (r : ZMod q)
      · rw [if_pos hm, if_pos ⟨hn, hm⟩]; ring
      · rw [if_neg hm, if_neg fun h => hm h.2]
    · rw [if_neg hn]; exact (Finset.sum_eq_zero fun m _ => if_neg fun h => hn h.1).symm
  rw [Finset.sum_congr rfl fun r _ => hs r, Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)ˣ)) (t := I)]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)ˣ)) (t := I)]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases h : IsUnit (n : ZMod q) ∧ (n : ZMod q) = (m : ZMod q)
  · obtain ⟨⟨r₀, hr₀⟩, hnm⟩ := h; rw [if_pos ⟨⟨r₀, hr₀⟩, hnm⟩]; symm; rw [Finset.sum_eq_single r₀]
    · rw [if_pos ⟨hr₀.symm, hnm.symm.trans hr₀.symm⟩]
    · intro r _ hne; exact if_neg fun ⟨h1, _⟩ => hne (Units.ext (h1.symm.trans hr₀.symm))
    · intro hm; exact absurd (Finset.mem_univ r₀) hm
  · rw [if_neg h]; symm; exact Finset.sum_eq_zero fun r _ => if_neg fun ⟨h1, h2⟩ => h ⟨h1 ▸ r.isUnit, h1.trans h2.symm⟩

/-- Exact residue-class counting bound in an interval `Finset.Ico M (M + N)`. -/
theorem card_filter_zmod_Ico_le {q : ℕ} [NeZero q] (M N : ℕ) (r : ZMod q) :
    (((Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤ (N : ℝ) / (q : ℝ) + 1 ∧
    (Nat.totient q : ℝ) * (((Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤
      (Nat.totient q : ℝ) + ((Nat.totient q : ℝ) / (q : ℝ)) * (N : ℝ) := by
  set S : Finset ℕ := (Finset.Ico M (M + N)).filter (fun n : ℕ => (n : ZMod q) = r)
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (S.card : ℝ) ≤ (N : ℝ) / (q : ℝ) + 1 := by
    by_cases hne : S.Nonempty
    · set m₀ : ℕ := S.min' hne
      have hm₀_I := Finset.mem_Ico.1 (Finset.mem_filter.1 (S.min'_mem hne)).1
      have hm₀_r : (m₀ : ZMod q) = r := (Finset.mem_filter.1 (S.min'_mem hne)).2
      have hsub : S.image (fun n => (n - m₀) / q) ⊆ Finset.range ((N - 1) / q + 1) := fun k hk => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk; have hn_I := Finset.mem_Ico.1 (Finset.mem_filter.1 hn).1
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
      have hinj : Set.InjOn (fun n => (n - m₀) / q) (S : Set ℕ) := fun a ha b hb hab => by
        dsimp only at hab; have hma := S.min'_le a ha; have hmb := S.min'_le b hb
        have hda : q ∣ a - m₀ := (ZMod.natCast_eq_zero_iff (a - m₀) q).1 <| by rw [Nat.cast_sub hma, (Finset.mem_filter.1 ha).2, hm₀_r, sub_self]
        have hdb : q ∣ b - m₀ := (ZMod.natCast_eq_zero_iff (b - m₀) q).1 <| by rw [Nat.cast_sub hmb, (Finset.mem_filter.1 hb).2, hm₀_r, sub_self]
        have : a - m₀ = b - m₀ := by rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
        omega
      have hnat : (S.card : ℝ) ≤ (((N - 1) / q : ℕ) : ℝ) + 1 := by exact_mod_cast (Finset.card_image_of_injOn hinj).symm.trans_le ((Finset.card_le_card hsub).trans_eq (Finset.card_range _))
      have hdiv : (((N - 1) / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) := (le_div_iff₀ hqR).2 (by exact_mod_cast (Nat.div_mul_le_self (N - 1) q).trans (Nat.sub_le N 1))
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]; positivity
  exact ⟨hcard, (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)).trans_eq (by ring)⟩


end DirichletMeanSquare
end Stage2BehrendSieve
end RHDirect
end

noncomputable section

open Complex DirichletCharacter Finset RHDirect
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage2DirichletAP

def chebyshevPsiChar {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ (n : ZMod q) * (Λ n : ℂ)

end RHDirect.Stage2DirichletAP
end

noncomputable section

open Complex Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage3BombieriVinogradov

def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

def fracSym (x : ℝ) : ℝ := x - (round x : ℝ)

def distZ (x : ℝ) : ℝ := |fracSym x|

def WellSpaced {κ : Type*} (J : Finset κ) (α : κ → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ J, ∀ s ∈ J, r ≠ s → δ ≤ distZ (α r - α s)

theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_sub (x y : ℝ) : e (x - y) = e x * e (-y) := by
  rw [sub_eq_add_neg, e_add]

theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  unfold e
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : (2 * Real.pi * Complex.I * (x : ℂ)) = (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem conj_e (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := by
  have h1 : e x * starRingEnd ℂ (e x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]; norm_num
  have h2 : e x * e (-x) = 1 := by
    rw [← e_add, add_neg_cancel, e_zero]
  have hne : e x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem e_int_eq_one (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have h : (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

theorem e_sub_int (x : ℝ) (k : ℤ) : e (x - (k : ℝ)) = e x := by
  rw [e_sub, e_neg, e_int_eq_one, inv_one, mul_one]

theorem e_fracSym (x : ℝ) : e (fracSym x) = e x :=
  e_sub_int x (round x)

theorem distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

theorem distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := abs_sub_round x

theorem distZ_le_abs_sub_int (x : ℝ) (k : ℤ) : distZ x ≤ |x - (k : ℝ)| := by
  unfold distZ fracSym
  by_cases hk : k = round x
  · subst hk; exact le_rfl
  · have h1 : (1 : ℝ) ≤ |(k : ℝ) - (round x : ℝ)| := by
      have hne : k - round x ≠ 0 := sub_ne_zero.mpr hk
      have hnat : (1 : ℤ) ≤ |k - round x| := Int.one_le_abs hne
      exact_mod_cast hnat
    have htri : |(k : ℝ) - (round x : ℝ)| ≤ |x - (round x : ℝ)| + |x - (k : ℝ)| := by
      calc |(k : ℝ) - (round x : ℝ)|
          = |(x - (round x : ℝ)) - (x - (k : ℝ))| := by ring_nf
        _ ≤ |x - (round x : ℝ)| + |x - (k : ℝ)| := abs_sub _ _
    have hhalf : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    linarith

theorem distZ_neg (x : ℝ) : distZ (-x) = distZ x := by
  have h1 : distZ (-x) ≤ distZ x := by
    have h := distZ_le_abs_sub_int (-x) (-round x)
    refine h.trans_eq ?_
    unfold distZ fracSym
    push_cast
    rw [show -x - -(round x : ℝ) = -(x - (round x : ℝ)) by ring, abs_neg]
  have h2 : distZ x ≤ distZ (-x) := by
    have h := distZ_le_abs_sub_int x (-round (-x))
    refine h.trans_eq ?_
    unfold distZ fracSym
    push_cast
    rw [show x - -(round (-x) : ℝ) = -(-x - (round (-x) : ℝ)) by ring, abs_neg]
  exact le_antisymm h1 h2

theorem distZ_sub_comm (x y : ℝ) : distZ (x - y) = distZ (y - x) := by
  rw [← distZ_neg (x - y), neg_sub]

theorem norm_e_sub_one_eq (x : ℝ) : ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hfac : e x - 1 = e (x / 2) * (e (x / 2) - e (-(x / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : x / 2 + x / 2 = x := by ring
    have h2 : x / 2 + -(x / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  have hdiff : e (x / 2) - e (-(x / 2)) = ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    unfold e
    have hpos : 2 * Real.pi * Complex.I * ((x / 2 : ℝ) : ℂ) = (((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    have hneg : 2 * Real.pi * Complex.I * ((-(x / 2) : ℝ) : ℂ) = (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hfac, norm_mul, norm_e, one_mul, hdiff, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem four_mul_distZ_le_norm_e_sub_one (θ : ℝ) : 4 * distZ θ ≤ ‖e θ - 1‖ := by
  rw [← e_fracSym θ, norm_e_sub_one_eq]
  have hhalf : |fracSym θ| ≤ 1 / 2 := abs_sub_round θ
  have habs : |Real.sin (Real.pi * fracSym θ)| = Real.sin (Real.pi * distZ θ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    rcases le_total 0 (fracSym θ) with h | h
    · have hd : distZ θ = fracSym θ := by unfold distZ; exact abs_of_nonneg h
      rw [hd]
      have hle : fracSym θ ≤ 1 / 2 := by rwa [abs_of_nonneg h] at hhalf
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hpi.le h) (by nlinarith))
    · have hd : distZ θ = -fracSym θ := by unfold distZ; exact abs_of_nonpos h
      rw [hd, mul_neg, Real.sin_neg]
      have hnn : 0 ≤ -fracSym θ := by linarith
      have hle : -fracSym θ ≤ 1 / 2 := by rwa [abs_of_nonpos h] at hhalf
      have hsin_nn : 0 ≤ Real.sin (Real.pi * (-fracSym θ)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hpi.le hnn) (by nlinarith)
      rw [mul_neg, Real.sin_neg] at hsin_nn
      rw [abs_of_nonpos (by linarith)]
  rw [habs]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hle : Real.pi * distZ θ ≤ Real.pi / 2 := by
    have := distZ_le_half θ
    nlinarith
  have hsin := Real.mul_le_sin (mul_nonneg hpi.le (distZ_nonneg θ)) hle
  have halg : 2 / Real.pi * (Real.pi * distZ θ) = 2 * distZ θ := by
    field_simp [hpi.ne']
  linarith

private theorem e_sub_one_mul_geom_sum (M : ℤ) (A : ℕ) (θ : ℝ) :
    (e θ - 1) * ∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ) =
      e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hstep : (e θ - 1) * e (((M + (A : ℤ)) : ℤ) * θ) =
        e (((M + ((A + 1 : ℕ) : ℤ)) : ℤ) * θ) - e (((M + (A : ℤ)) : ℤ) * θ) := by
      rw [sub_mul, one_mul, ← e_add]
      congr 1
      congr 1
      push_cast
      ring
    rw [hstep]
    ring

theorem norm_geom_sum_e_le (M : ℤ) (A : ℕ) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ (2 * distZ θ)⁻¹ := by
  have h4 : 4 * distZ θ ≤ ‖e θ - 1‖ := four_mul_distZ_le_norm_e_sub_one θ
  have hmul : 4 * distZ θ * ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ 2 := by
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    rw [← norm_mul, e_sub_one_mul_geom_sum]
    calc ‖e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ)‖
        ≤ ‖e (((M + (A : ℤ)) : ℤ) * θ)‖ + ‖e ((M : ℝ) * θ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_e, norm_e]
      _ = 2 := by norm_num
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  linarith

theorem norm_geom_sum_e_Ico_le (M : ℤ) (A : ℕ) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ n ∈ Finset.Ico M (M + (A : ℤ)), e ((n : ℝ) * θ)‖ ≤ (2 * distZ θ)⁻¹ := by
  have heq : ∑ n ∈ Finset.Ico M (M + (A : ℤ)), e ((n : ℝ) * θ) =
      ∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ) := by
    refine Finset.sum_bij (fun n _ => (n - M).toNat) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_range]
      omega
    · intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_Ico] at hn₁ hn₂
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨M + (k : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      congr 1
      have hsub : M + ((n - M).toNat : ℤ) = n := by omega
      rw [hsub]
  rw [heq]
  have h4 : 4 * distZ θ ≤ ‖e θ - 1‖ := four_mul_distZ_le_norm_e_sub_one θ
  have hmul : 4 * distZ θ * ‖∑ k ∈ Finset.range A, e (((M + (k : ℤ)) : ℤ) * θ)‖ ≤ 2 := by
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    rw [← norm_mul, e_sub_one_mul_geom_sum]
    calc ‖e (((M + (A : ℤ)) : ℤ) * θ) - e ((M : ℝ) * θ)‖
        ≤ ‖e (((M + (A : ℤ)) : ℤ) * θ)‖ + ‖e ((M : ℝ) * θ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_e, norm_e]
      _ = 2 := by norm_num
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  linarith

def fejerWeight (M : ℤ) (N L : ℕ) (n : ℤ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ v ∈ Finset.range L,
    if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0

theorem fejerWeight_nonneg (M : ℤ) (N L : ℕ) (n : ℤ) : 0 ≤ fejerWeight M N L n := by
  unfold fejerWeight
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem fejerWeight_eq_one_of_mem {M : ℤ} {N L : ℕ} (hL : 0 < L)
    {n : ℤ} (hn : n ∈ Finset.Ico M (M + (N : ℤ))) :
    fejerWeight M N L n = 1 := by
  simp only [Finset.mem_Ico] at hn
  unfold fejerWeight
  have hsum : ∑ v ∈ Finset.range L,
      (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0) = (L : ℝ) := by
    have hcongr : ∑ v ∈ Finset.range L,
        (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ) then (1 : ℝ) else 0) =
        ∑ _v ∈ Finset.range L, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_range] at hv
      rw [if_pos ⟨by omega, by omega⟩]
    rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL.ne')]

theorem fejerTransform_eq (M : ℤ) (N L : ℕ) (θ : ℝ) :
    ∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
      ((L : ℝ)⁻¹ : ℂ) *
        (∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)) *
        (∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))) := by
  set I' : Finset ℤ := Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ))
  have hexp :
      ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
        ((L : ℝ)⁻¹ : ℂ) * ∑ v ∈ Finset.range L,
          ∑ n ∈ I', (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
            then e ((n : ℝ) * θ) else 0) := by
    have h1 :
        ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ) =
          ((L : ℝ)⁻¹ : ℂ) * ∑ n ∈ I', ∑ v ∈ Finset.range L,
            (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
              then e ((n : ℝ) * θ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold fejerWeight
      rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum, mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
      · rw [if_pos hv, if_pos hv, Complex.ofReal_one, one_mul]
      · rw [if_neg hv, if_neg hv, Complex.ofReal_zero, zero_mul]
    rw [h1, Finset.sum_comm]
  rw [hexp]
  have hinner : ∀ v ∈ Finset.range L,
      ∑ n ∈ I', (if M ≤ n + (v : ℤ) ∧ n + (v : ℤ) < M + (N : ℤ) + (L : ℤ)
          then e ((n : ℝ) * θ) else 0) =
        (∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)) * e (-((v : ℝ) * θ)) := by
    intro v hv
    rw [Finset.mem_range] at hv
    rw [← Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_bij (fun n _ => n + (v : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
      push_cast
      omega
    · intro n₁ _ n₂ _ h
      omega
    · intro u hu
      simp only [Finset.mem_Ico] at hu
      refine ⟨u - (v : ℤ), ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ico, I']
      push_cast at hu
      omega
    · intro n _
      rw [← e_add]
      congr 1
      push_cast
      ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, mul_assoc]

theorem fejerTransform_zero (M : ℤ) (N L : ℕ) (hL : 0 < L) :
    ∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * 0) = ((N + L : ℕ) : ℂ) := by
  rw [fejerTransform_eq]
  have h1 : ∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * 0) = ((N + L : ℕ) : ℂ) := by
    simp only [mul_zero, e_zero, Finset.sum_const, Int.card_Ico, add_sub_cancel_left,
      Int.toNat_natCast, nsmul_eq_mul, mul_one]
  have h2 : ∑ v ∈ Finset.range L, e (-((v : ℝ) * 0)) = (L : ℂ) := by
    simp only [mul_zero, neg_zero, e_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [h1, h2]
  have hLne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  push_cast
  field_simp [hLne]

theorem norm_fejerTransform_le (M : ℤ) (N L : ℕ) (hL : 0 < L) {θ : ℝ} (hθ : 0 < distZ θ) :
    ‖∑ n ∈ Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ)),
        ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * θ)‖ ≤
      (4 * (L : ℝ) * distZ θ ^ 2)⁻¹ := by
  rw [fejerTransform_eq, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h1 : ‖∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)‖ ≤ (2 * distZ θ)⁻¹ :=
    norm_geom_sum_e_Ico_le M (N + L) hθ
  have h2 : ‖∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))‖ ≤ (2 * distZ θ)⁻¹ := by
    have hrewrite : ∑ v ∈ Finset.range L, e (-((v : ℝ) * θ)) =
        ∑ k ∈ Finset.range L, e (((0 + (k : ℤ)) : ℤ) * (-θ)) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      congr 1; push_cast; ring
    rw [hrewrite]
    have hneg : 0 < distZ (-θ) := by rwa [distZ_neg]
    have hb := norm_geom_sum_e_le 0 L hneg
    rwa [distZ_neg] at hb
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  calc (L : ℝ)⁻¹ * ‖∑ u ∈ Finset.Ico M (M + ((N + L : ℕ) : ℤ)), e ((u : ℝ) * θ)‖ *
        ‖∑ v ∈ Finset.range L, e (-((v : ℝ) * θ))‖
      ≤ (L : ℝ)⁻¹ * (2 * distZ θ)⁻¹ * (2 * distZ θ)⁻¹ := by
        gcongr
    _ = (4 * (L : ℝ) * distZ θ ^ 2)⁻¹ := by
        field_simp [hLpos.ne', hθ.ne']
        ring

private theorem sum_inv_sq_Icc_le_two (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m → ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ ≤ 2 - (m : ℝ)⁻¹ := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hmpos
      · norm_num
      · have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
        rw [hIcc, Finset.sum_insert hnotmem]
        have ihm := ih hmpos
        have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmpos
        have hm1R : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hstep : (((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ (m : ℝ)⁻¹ - ((m + 1 : ℕ) : ℝ)⁻¹ := by
          push_cast
          have hdiff : (m : ℝ)⁻¹ - ((m : ℝ) + 1)⁻¹ = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
            field_simp [hmR.ne', (by positivity : (m : ℝ) + 1 ≠ 0)]
            ring
          rw [hdiff, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
        linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · have h := hstrong K hK
    have hinv : (0 : ℝ) ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    linarith

theorem sum_inv_distZ_sq_le {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hws : WellSpaced J α δ) {r : κ} (hr : r ∈ J) :
    ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ ≤ 4 / δ ^ 2 := by
  let bin : κ → Bool × ℕ := fun s =>
    (decide (0 ≤ fracSym (α s - α r)), ⌊distZ (α s - α r) / δ⌋₊)
  let K : ℕ := ⌊(1 / 2 : ℝ) / δ⌋₊
  have hinj : Set.InjOn bin (J.erase r : Set κ) := by
    intro s₁ hs₁ s₂ hs₂ hbin
    simp only [Finset.mem_coe, Finset.mem_erase] at hs₁ hs₂
    have hsign : decide (0 ≤ fracSym (α s₁ - α r)) = decide (0 ≤ fracSym (α s₂ - α r)) :=
      congrArg Prod.fst hbin
    have hfl : ⌊distZ (α s₁ - α r) / δ⌋₊ = ⌊distZ (α s₂ - α r) / δ⌋₊ :=
      congrArg Prod.snd hbin
    set k : ℕ := ⌊distZ (α s₁ - α r) / δ⌋₊
    have h1lo : (k : ℝ) ≤ distZ (α s₁ - α r) / δ := Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le)
    have h1hi : distZ (α s₁ - α r) / δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2lo : (k : ℝ) ≤ distZ (α s₂ - α r) / δ := hfl ▸ Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le)
    have h2hi : distZ (α s₂ - α r) / δ < (k : ℝ) + 1 := hfl ▸ Nat.lt_floor_add_one _
    have habs_diff : |distZ (α s₁ - α r) - distZ (α s₂ - α r)| < δ := by
      have h1a : (k : ℝ) * δ ≤ distZ (α s₁ - α r) := (le_div_iff₀ hδ).mp h1lo
      have h1b : distZ (α s₁ - α r) < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1hi
      have h2a : (k : ℝ) * δ ≤ distZ (α s₂ - α r) := (le_div_iff₀ hδ).mp h2lo
      have h2b : distZ (α s₂ - α r) < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h2hi
      rw [abs_lt]; constructor <;> nlinarith
    have hfrac_diff : |fracSym (α s₁ - α r) - fracSym (α s₂ - α r)| < δ := by
      unfold distZ at habs_diff
      by_cases hp1 : 0 ≤ fracSym (α s₁ - α r)
      · have hp2 : 0 ≤ fracSym (α s₂ - α r) := by
          have : decide (0 ≤ fracSym (α s₂ - α r)) = true := by rw [← hsign, decide_eq_true_eq]; exact hp1
          exact decide_eq_true_eq.mp this
        rwa [abs_of_nonneg hp1, abs_of_nonneg hp2] at habs_diff
      · have hp2 : ¬ 0 ≤ fracSym (α s₂ - α r) := by
          intro h2
          have : decide (0 ≤ fracSym (α s₁ - α r)) = true := by rw [hsign, decide_eq_true_eq]; exact h2
          exact hp1 (decide_eq_true_eq.mp this)
        have hn1 : fracSym (α s₁ - α r) ≤ 0 := le_of_not_ge hp1
        have hn2 : fracSym (α s₂ - α r) ≤ 0 := le_of_not_ge hp2
        rw [abs_of_nonpos hn1, abs_of_nonpos hn2] at habs_diff
        have heq : -(fracSym (α s₁ - α r) - fracSym (α s₂ - α r)) =
            -fracSym (α s₁ - α r) - -fracSym (α s₂ - α r) := by ring
        rw [← abs_neg, heq]
        exact habs_diff
    have hdist_lt : distZ (α s₁ - α s₂) < δ := by
      let m : ℤ := round (α s₁ - α r) - round (α s₂ - α r)
      have hle := distZ_le_abs_sub_int (α s₁ - α s₂) m
      have heq : α s₁ - α s₂ - (m : ℝ) = fracSym (α s₁ - α r) - fracSym (α s₂ - α r) := by
        unfold fracSym; simp only [m]; push_cast; ring
      rw [heq] at hle
      exact lt_of_le_of_lt hle hfrac_diff
    by_contra hne
    have hge := hws s₁ hs₁.2 s₂ hs₂.2 hne
    linarith
  have hmaps : ∀ s ∈ J.erase r, bin s ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K := by
    intro s hs
    simp only [Finset.mem_erase] at hs
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc, bin]
    have hge : δ ≤ distZ (α s - α r) := hws s hs.2 r hr hs.1
    have h1 : 1 ≤ distZ (α s - α r) / δ := (one_le_div hδ).mpr hge
    have h2 : distZ (α s - α r) / δ ≤ (1 / 2 : ℝ) / δ :=
      div_le_div_of_nonneg_right (distZ_le_half _) hδ.le
    exact ⟨Nat.le_floor (by exact_mod_cast h1), Nat.floor_mono h2⟩
  have hterm : ∀ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ ≤ ((((bin s).2 : ℝ) * δ) ^ 2)⁻¹ := by
    intro s hs
    have hk_ge1 : 1 ≤ (bin s).2 := by
      have hmem := hmaps s hs
      simp only [Finset.mem_product, Finset.mem_Icc] at hmem
      exact hmem.2.1
    have hk_pos : (0 : ℝ) < ((bin s).2 : ℝ) * δ := by
      have : (0 : ℝ) < ((bin s).2 : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have hle : ((bin s).2 : ℝ) * δ ≤ distZ (α r - α s) := by
      rw [distZ_sub_comm]
      exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (distZ_nonneg _) hδ.le))
    have hsq : (((bin s).2 : ℝ) * δ) ^ 2 ≤ distZ (α r - α s) ^ 2 :=
      pow_le_pow_left₀ hk_pos.le hle 2
    exact inv_anti₀ (pow_pos hk_pos 2) hsq
  calc ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹
      ≤ ∑ s ∈ J.erase r, ((((bin s).2 : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun s hs => hterm s hs
    _ = ∑ p ∈ (J.erase r).image bin, (((p.2 : ℝ) * δ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun p : Bool × ℕ => (((p.2 : ℝ) * δ) ^ 2)⁻¹) hinj).symm
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K, (((p.2 : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          fun _ _ _ => inv_nonneg.mpr (sq_nonneg _)
    _ = ∑ _b : Bool, ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) * δ) ^ 2)⁻¹ :=
        Finset.sum_product _ _ _
    _ = 2 * (δ ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, mul_inv, mul_comm ((k : ℝ) ^ 2)⁻¹]
    _ ≤ 2 * (δ ^ 2)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le_two K) (by positivity)
    _ = 4 / δ ^ 2 := by ring

theorem additive_large_sieve_Ico_int {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hws : WellSpaced J α δ) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
      ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
  by_cases hδ_half : 1 / 2 < δ
  · 
    have hcard : J.card ≤ 1 := by
      refine Finset.card_le_one.mpr fun r hr s hs => ?_
      by_contra hne
      linarith [hws r hr s hs hne, distZ_le_half (α r - α s)]
    have hterm : ∀ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
        (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
      intro r _
      have hcs := Stage2BehrendSieve.cauchy_schwarz_complex_card
        (Finset.Ico M (M + (N : ℤ))) (fun n => a n * e ((n : ℝ) * α r))
      have hcardI : ((Finset.Ico M (M + (N : ℤ))).card : ℝ) = (N : ℝ) := by
        simp [Int.card_Ico]
      have hnorm : ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n * e ((n : ℝ) * α r)‖ ^ 2 =
          ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, norm_e, mul_one]
      rw [hcardI, hnorm] at hcs
      exact hcs
    calc ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + (N : ℤ)), a n * e ((n : ℝ) * α r)‖ ^ 2
        ≤ ∑ _r ∈ J, (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (J.card : ℝ) * ((N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * ((N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ?_
          exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (N : ℝ) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 := one_mul _
      _ ≤ ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + (N : ℤ)), ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith [inv_pos.mpr hδ])
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · 
    
    have hδ_le : δ ≤ 1 / 2 := le_of_not_gt hδ_half
    set L : ℕ := ⌈δ⁻¹⌉₊
    have hinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hL_ge : δ⁻¹ ≤ (L : ℝ) := Nat.le_ceil δ⁻¹
    have hL_pos : 0 < L := by
      have : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le hinv_pos hL_ge
      exact Nat.cast_pos.mp this
    have hL_le : (L : ℝ) ≤ 2 * δ⁻¹ := by
      have hlt := Nat.ceil_lt_add_one hinv_pos.le
      have h1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
      linarith
    set I : Finset ℤ := Finset.Ico M (M + (N : ℤ))
    set I' : Finset ℤ := Finset.Ico (M - (L : ℤ) + 1) (M + (N : ℤ) + (L : ℤ))
    have hI_sub : I ⊆ I' := fun n hn => by
      simp only [Finset.mem_Ico, I, I'] at hn ⊢
      omega
    let K : κ → ℤ → ℂ := fun r n => ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e ((n : ℝ) * α r)
    let a' : ℤ → ℂ := fun n => if n ∈ I then a n else 0
    have hΔ0 : 0 ≤ (N : ℝ) + 3 * δ⁻¹ := by positivity
    have hGram : ∀ r ∈ J, ∑ s ∈ J, ‖∑ n ∈ I', K r n * starRingEnd ℂ (K s n)‖ ≤ (N : ℝ) + 3 * δ⁻¹ := by
      intro r hr
      have hGeq : ∀ s : κ, ∑ n ∈ I', K r n * starRingEnd ℂ (K s n) =
          ∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s)) := by
        intro s
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [K]
        rw [map_mul, Complex.conj_ofReal, conj_e]
        have hsq : ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) *
            ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) = ((fejerWeight M N L n : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (fejerWeight_nonneg M N L n)]
        calc ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e ((n : ℝ) * α r) *
              (((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) * e (-((n : ℝ) * α s)))
            = (((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ) *
                ((Real.sqrt (fejerWeight M N L n) : ℝ) : ℂ)) *
                (e ((n : ℝ) * α r) * e (-((n : ℝ) * α s))) := by ring
          _ = ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s)) := by
              rw [hsq, ← e_add]; congr 2; ring
      simp_rw [hGeq]
      rw [← Finset.add_sum_erase J _ hr]
      have hdiag : ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α r))‖ =
          (N : ℝ) + (L : ℝ) := by
        rw [sub_self, fejerTransform_zero M N L hL_pos]
        rw [show ((N + L : ℕ) : ℂ) = (((N : ℝ) + (L : ℝ) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hoff : ∑ s ∈ J.erase r,
          ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s))‖ ≤ δ⁻¹ := by
        have hLposR : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
        calc ∑ s ∈ J.erase r,
              ‖∑ n ∈ I', ((fejerWeight M N L n : ℝ) : ℂ) * e ((n : ℝ) * (α r - α s))‖
            ≤ ∑ s ∈ J.erase r, (4 * (L : ℝ) * distZ (α r - α s) ^ 2)⁻¹ := by
              refine Finset.sum_le_sum fun s hs => ?_
              have hne : r ≠ s := (Finset.mem_erase.mp hs).1.symm
              have hds : 0 < distZ (α r - α s) := lt_of_lt_of_le hδ (hws r hr s (Finset.mem_erase.mp hs).2 hne)
              exact norm_fejerTransform_le M N L hL_pos hds
          _ = (4 * (L : ℝ))⁻¹ * ∑ s ∈ J.erase r, (distZ (α r - α s) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [mul_inv]
          _ ≤ (4 * (L : ℝ))⁻¹ * (4 / δ ^ 2) :=
              mul_le_mul_of_nonneg_left (sum_inv_distZ_sq_le J α hδ hws hr) (by positivity)
          _ = ((L : ℝ) * δ ^ 2)⁻¹ := by
              field_simp [hLposR.ne', hδ.ne']
          _ ≤ δ⁻¹ := by
              rw [inv_le_inv₀ (by positivity) hδ]
              have h1 : 1 ≤ (L : ℝ) * δ := by
                have := mul_le_mul_of_nonneg_right hL_ge hδ.le
                rwa [inv_mul_cancel₀ hδ.ne'] at this
              nlinarith
      rw [hdiag]
      linarith
    have hLS := Stage2BehrendSieve.gram_large_sieve I' J K hΔ0 hGram a'
    have hLHS : ∑ r ∈ J, ‖∑ n ∈ I', K r n * a' n‖ ^ 2 =
        ∑ r ∈ J, ‖∑ n ∈ I, a n * e ((n : ℝ) * α r)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 2
      rw [← Finset.sum_subset hI_sub]
      · refine Finset.sum_congr rfl fun n hn => ?_
        dsimp only [K, a']
        rw [if_pos hn, fejerWeight_eq_one_of_mem hL_pos hn, Real.sqrt_one, Complex.ofReal_one, one_mul, mul_comm]
      · intro n _ hn
        dsimp only [a']
        rw [if_neg hn, mul_zero]
    have hRHS : ∑ n ∈ I', ‖a' n‖ ^ 2 = ∑ n ∈ I, ‖a n‖ ^ 2 := by
      rw [← Finset.sum_subset hI_sub]
      · refine Finset.sum_congr rfl fun n hn => ?_
        dsimp only [a']; rw [if_pos hn]
      · intro n _ hn
        dsimp only [a']; rw [if_neg hn, norm_zero, zero_pow (by norm_num)]
    rw [hLHS, hRHS] at hLS
    exact hLS

theorem additive_large_sieve_Ico_nat {κ : Type*} [DecidableEq κ] (J : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hws : WellSpaced J α δ) (M N : ℕ) (a : ℕ → ℂ) :
    ∑ r ∈ J, ‖∑ n ∈ Finset.Ico M (M + N), a n * e ((n : ℝ) * α r)‖ ^ 2 ≤
      ((N : ℝ) + 3 * δ⁻¹) * ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by
  let aZ : ℤ → ℂ := fun z => if 0 ≤ z then a z.toNat else 0
  have h := additive_large_sieve_Ico_int J α hδ hws (M : ℤ) N aZ
  have hL : ∀ r : κ,
      ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + (N : ℤ)), aZ n * e ((n : ℝ) * α r) =
        ∑ n ∈ Finset.Ico M (M + N), a n * e ((n : ℝ) * α r) := by
    intro r
    refine Finset.sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_Ico] at hz ⊢; omega
    · intro z₁ hz₁ z₂ hz₂ heq; simp only [Finset.mem_Ico] at hz₁ hz₂; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn
      exact ⟨(n : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro z hz
      simp only [Finset.mem_Ico] at hz
      have hz0 : 0 ≤ z := by omega
      dsimp only [aZ]
      rw [if_pos hz0]
      have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hz0
      rw [hcast]
  have hR : ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + (N : ℤ)), ‖aZ n‖ ^ 2 =
      ∑ n ∈ Finset.Ico M (M + N), ‖a n‖ ^ 2 := by
    refine Finset.sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_Ico] at hz ⊢; omega
    · intro z₁ hz₁ z₂ hz₂ heq; simp only [Finset.mem_Ico] at hz₁ hz₂; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn
      exact ⟨(n : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro z hz
      simp only [Finset.mem_Ico] at hz
      dsimp only [aZ]; rw [if_pos (by omega)]
  simp_rw [hL] at h
  rw [hR] at h
  exact h

def fareyPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => (q, a))

theorem farey_distZ_ge {Q : ℕ} (hQ : 0 < Q) :
    WellSpaced (fareyPairs Q) (fun p => (p.2 : ℝ) / (p.1 : ℝ)) (((Q : ℝ) ^ 2)⁻¹) := by
  intro p₁ hp₁ p₂ hp₂ hne
  simp only [fareyPairs, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range] at hp₁ hp₂
  obtain ⟨q₁, ⟨hq1_lo, hq1_hi⟩, a₁, ⟨ha1_lt, hcop1⟩, rfl⟩ := hp₁
  obtain ⟨q₂, ⟨hq2_lo, hq2_hi⟩, a₂, ⟨ha2_lt, hcop2⟩, rfl⟩ := hp₂
  have hq1_pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq2_pos : (0 : ℝ) < (q₂ : ℝ) := Nat.cast_pos.mpr (by omega)
  let k : ℤ := round ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ))
  let m : ℤ := (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) - k * (q₁ : ℤ) * (q₂ : ℤ)
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hdiv1 : (q₁ : ℤ) ∣ (a₁ : ℤ) * (q₂ : ℤ) := by
      refine ⟨(a₂ : ℤ) + k * (q₂ : ℤ), ?_⟩
      dsimp only [m] at hm0
      linarith
    have hdiv2 : (q₂ : ℤ) ∣ (a₂ : ℤ) * (q₁ : ℤ) := by
      refine ⟨(a₁ : ℤ) - k * (q₁ : ℤ), ?_⟩
      dsimp only [m] at hm0
      linarith
    have hnat1 : q₁ ∣ a₁ * q₂ := Int.natCast_dvd_natCast.mp (by simpa using hdiv1)
    have hnat2 : q₂ ∣ a₂ * q₁ := Int.natCast_dvd_natCast.mp (by simpa using hdiv2)
    have hq12 : q₁ ∣ q₂ := hcop1.symm.dvd_of_dvd_mul_left hnat1
    have hq21 : q₂ ∣ q₁ := hcop2.symm.dvd_of_dvd_mul_left hnat2
    have hqeq : q₁ = q₂ := Nat.dvd_antisymm hq12 hq21
    subst hqeq
    have hdiff : ((a₁ : ℤ) - (a₂ : ℤ) - k * (q₁ : ℤ)) * (q₁ : ℤ) = 0 := by
      dsimp only [m] at hm0
      linarith
    have hsub : (a₁ : ℤ) - (a₂ : ℤ) = k * (q₁ : ℤ) := by
      have hqne : (q₁ : ℤ) ≠ 0 := by omega
      have := (mul_eq_zero.mp hdiff).resolve_right hqne
      linarith
    have hk0 : k = 0 := by
      by_contra hk
      have habs : (q₁ : ℤ) ≤ |k * (q₁ : ℤ)| := by
        rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (q₁ : ℤ))]
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
        nlinarith
      rw [← hsub] at habs
      have : |(a₁ : ℤ) - (a₂ : ℤ)| < (q₁ : ℤ) := by
        rw [abs_lt]; omega
      omega
    have haeq : a₁ = a₂ := by rw [hk0, zero_mul] at hsub; omega
    exact hne (Prod.ext rfl haeq)
  have hm_ge : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    exact_mod_cast this
  have hval : fracSym ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)) = (m : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    unfold fracSym
    dsimp only [m, k]
    push_cast
    field_simp [hq1_pos.ne', hq2_pos.ne']
  have hdist : distZ ((a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ)) = |(m : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    unfold distZ
    rw [hval, abs_div, abs_of_pos (mul_pos hq1_pos hq2_pos)]
  rw [hdist]
  have hqq : (q₁ : ℝ) * (q₂ : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq1_hi
    have h2 : (q₂ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq2_hi
    nlinarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  calc ((Q : ℝ) ^ 2)⁻¹
      = 1 / (Q : ℝ) ^ 2 := by rw [one_div]
    _ ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := one_div_le_one_div_of_le (mul_pos hq1_pos hq2_pos) hqq
    _ ≤ |(m : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := div_le_div_of_nonneg_right hm_ge (mul_pos hq1_pos hq2_pos).le

private theorem sum_fareyPairs_eq (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ fareyPairs Q, f p.1 p.2 =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f q a := by
  unfold fareyPairs
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_image]
    intro a₁ _ a₂ _ h
    exact (Prod.mk.inj h).2
  · intro q₁ _ q₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image] at hp1 hp2
    obtain ⟨a₁, _, rfl⟩ := hp1
    obtain ⟨a₂, _, h2⟩ := hp2
    exact hne (Prod.mk.inj h2).1.symm

theorem farey_large_sieve_Ico (Q M N : ℕ) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + N), ‖c n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hδ : 0 < ((Q : ℝ) ^ 2)⁻¹ := inv_pos.mpr (pow_pos (Nat.cast_pos.mpr hQ) 2)
    have h := additive_large_sieve_Ico_nat (fareyPairs Q) (fun p => (p.2 : ℝ) / (p.1 : ℝ))
      hδ (farey_distZ_ge hQ) M N c
    rw [inv_inv, sum_fareyPairs_eq (f := fun q a =>
      ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2)] at h
    exact h

theorem stdAddChar_eq_e {q : ℕ} [NeZero q] (a : ZMod q) :
    ZMod.stdAddChar a = e ((a.val : ℝ) / (q : ℝ)) := by
  have hcast : (((a.val : ℤ) : ZMod q)) = a := by simp
  conv_lhs => rw [← hcast]
  rw [ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

theorem stdAddChar_natCast_eq_e {q : ℕ} [NeZero q] (m : ℕ) :
    ZMod.stdAddChar (m : ZMod q) = e ((m : ℝ) / (q : ℝ)) := by
  have h := ZMod.stdAddChar_coe (N := q) (m : ℤ)
  push_cast at h
  rw [h]
  unfold e
  congr 1
  push_cast
  ring

theorem norm_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [stdAddChar_eq_e, norm_e]

theorem conj_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  have h1 : ZMod.stdAddChar a * starRingEnd ℂ (ZMod.stdAddChar a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_stdAddChar]; norm_num
  have h2 : ZMod.stdAddChar a * ZMod.stdAddChar (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hne : ZMod.stdAddChar a ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem stdAddChar_ne_one_of_ne_zero {q : ℕ} [NeZero q] {d : ZMod q} (hd : d ≠ 0) :
    ZMod.stdAddChar d ≠ 1 := by
  rw [stdAddChar_eq_e]
  have hval_pos : 0 < d.val := Nat.pos_of_ne_zero fun h0 => hd (by rw [← ZMod.natCast_zmod_val d, h0, Nat.cast_zero])
  have hval_lt : d.val < q := ZMod.val_lt d
  have hdist_pos : 0 < distZ ((d.val : ℝ) / (q : ℝ)) := by
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have h0 : (0 : ℝ) < (d.val : ℝ) / (q : ℝ) := div_pos (Nat.cast_pos.mpr hval_pos) hq_pos
    have h1 : (d.val : ℝ) / (q : ℝ) < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast hval_lt)
    unfold distZ fracSym
    rw [abs_pos]
    intro heq
    have hint : (d.val : ℝ) / (q : ℝ) = (round ((d.val : ℝ) / (q : ℝ)) : ℝ) := sub_eq_zero.mp heq
    have hk0 : (0 : ℤ) < round ((d.val : ℝ) / (q : ℝ)) := by
      have : ((0 : ℤ) : ℝ) < (round ((d.val : ℝ) / (q : ℝ)) : ℝ) := by rw [← hint]; simpa using h0
      exact_mod_cast this
    have hk1 : round ((d.val : ℝ) / (q : ℝ)) < 1 := by
      have : (round ((d.val : ℝ) / (q : ℝ)) : ℝ) < ((1 : ℤ) : ℝ) := by rw [← hint]; simpa using h1
      exact_mod_cast this
    omega
  intro heq
  have h4 := four_mul_distZ_le_norm_e_sub_one ((d.val : ℝ) / (q : ℝ))
  rw [heq, sub_self, norm_zero] at h4
  linarith

theorem sum_stdAddChar_mul {q : ℕ} [NeZero q] (d : ZMod q) :
    ∑ k : ZMod q, ZMod.stdAddChar (k * d) = if d = 0 then (q : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one, ite_true]
  · rw [if_neg hd]
    set S : ℂ := ∑ k : ZMod q, ZMod.stdAddChar (k * d)
    have hshift : ZMod.stdAddChar d * S = S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      calc ∑ k : ZMod q, ZMod.stdAddChar d * ZMod.stdAddChar (k * d)
          = ∑ k : ZMod q, ZMod.stdAddChar ((k + 1) * d) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← AddChar.map_add_eq_mul]; congr 1; ring
        _ = ∑ k : ZMod q, ZMod.stdAddChar (k * d) := by
            exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod q)) _ _ fun k => rfl
    have hmul : (ZMod.stdAddChar d - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (stdAddChar_ne_one_of_ne_zero hd))

theorem zmod_dft_parseval {q : ℕ} [NeZero q] (Φ : ZMod q → ℂ) :
    ∑ k : ZMod q, ‖ZMod.dft Φ k‖ ^ 2 = (q : ℝ) * ∑ j : ZMod q, ‖Φ j‖ ^ 2 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hsq]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]
  congr 1
  have hL : ∑ k : ZMod q, ZMod.dft Φ k * starRingEnd ℂ (ZMod.dft Φ k) =
      ∑ j : ZMod q, ∑ j' : ZMod q,
        Φ j * starRingEnd ℂ (Φ j') * ∑ k : ZMod q, ZMod.stdAddChar (k * (j' - j)) := by
    have hexp : ∀ k : ZMod q,
        ZMod.dft Φ k * starRingEnd ℂ (ZMod.dft Φ k) =
          ∑ j : ZMod q, ∑ j' : ZMod q,
            Φ j * starRingEnd ℂ (Φ j') * ZMod.stdAddChar (k * (j' - j)) := by
      intro k
      rw [ZMod.dft_def]
      simp only [smul_eq_mul, map_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [map_mul, conj_stdAddChar, neg_neg]
      have hadd : ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) =
          ZMod.stdAddChar (k * (j' - j)) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      calc ZMod.stdAddChar (-(j * k)) * Φ j * (ZMod.stdAddChar (j' * k) * starRingEnd ℂ (Φ j'))
          = Φ j * starRingEnd ℂ (Φ j') * (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k)) := by ring
        _ = Φ j * starRingEnd ℂ (Φ j') * ZMod.stdAddChar (k * (j' - j)) := by rw [hadd]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [sum_stdAddChar_mul]
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl]; ring
  · intro j' _ hne
    rw [if_neg (sub_ne_zero.mpr hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem sum_norm_sq_dirichletChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ j : ZMod q, ‖χ j‖ ^ 2 = (Nat.totient q : ℝ) := by
  have hfilt : ∑ j : ZMod q, ‖χ j‖ ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j : ZMod q => IsUnit j), (1 : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : IsUnit j
    · rw [if_pos hj, (Stage2BehrendSieve.dirichlet_norm_eq_one_and_conj χ hj).1, one_pow]
    · rw [if_neg hj, MulChar.map_nonunit χ hj, norm_zero, zero_pow (by norm_num)]
  rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun j : ZMod q => IsUnit j)).card = Fintype.card (ZMod q)ˣ := by
    refine Finset.card_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q)) ?_ ?_ ?_ |>.symm
    · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
    · intro u₁ _ u₂ _ h; exact Units.ext h
    · intro j hj
      obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hj).2
      exact ⟨u, Finset.mem_univ _, rfl⟩
  rw [hcard, ZMod.card_units_eq_totient]

theorem norm_sq_gaussSum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  have hp := zmod_dft_parseval (Φ := (χ : ZMod q → ℂ))
  rw [sum_norm_sq_dirichletChar χ] at hp
  have hL : ∑ k : ZMod q, ‖ZMod.dft (⇑χ) k‖ ^ 2 =
      ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * (Nat.totient q : ℝ) := by
    have h1 : ∀ k : ZMod q, ‖ZMod.dft (⇑χ) k‖ ^ 2 =
        ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * ‖χ⁻¹ (-k)‖ ^ 2 := by
      intro k
      rw [hprim.fourierTransform_eq_inv_mul_gaussSum k, norm_mul, mul_pow, mul_comm]
    simp_rw [h1, ← Finset.mul_sum]
    congr 1
    calc ∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2
        = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
          Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ fun _ => rfl
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletChar χ⁻¹
  rw [hL] at hp
  have hphi : (Nat.totient q : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  exact mul_right_cancel₀ hphi hp

theorem norm_gaussSum_eq_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_gaussSum_eq hprim]

theorem gaussSum_mul_char_sum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (I : Finset ℕ) (c : ℕ → ℂ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ I, c n * χ (n : ZMod q) =
      ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
        ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hpoint : ∀ n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q) =
      ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
    intro n
    have hft := hprim_inv.fourierTransform_eq_inv_mul_gaussSum (-(n : ZMod q))
    rw [inv_inv, neg_neg, mul_comm] at hft
    rw [← hft, ZMod.dft_def]
    simp only [smul_eq_mul]
    have hfilt : ∑ j : ZMod q, ZMod.stdAddChar (-(j * -(n : ZMod q))) * χ⁻¹ j =
        ∑ j ∈ Finset.univ.filter (fun j : ZMod q => IsUnit j),
          ZMod.stdAddChar (j * (n : ZMod q)) * χ⁻¹ j := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : IsUnit j
      · rw [if_pos hj, mul_neg, neg_neg]
      · rw [if_neg hj, MulChar.map_nonunit χ⁻¹ hj, mul_zero]
    rw [hfilt]
    refine Finset.sum_bij (fun j hj => (Finset.mem_filter.mp hj).2.unit) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro j₁ hj₁ j₂ hj₂ h
      have := congrArg Units.val h
      simpa using this
    · intro a _
      exact ⟨(a : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩, Units.ext (by simp)⟩
    · intro j hj
      have hjval : (((Finset.mem_filter.mp hj).2.unit : (ZMod q)ˣ) : ZMod q) = j := by simp
      rw [hjval, mul_comm]
      congr 1
      have hmul : (j : ZMod q) * (n : ZMod q) = ((n * j.val : ℕ) : ZMod q) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]
      rw [hmul, stdAddChar_natCast_eq_e]
      congr 1
      push_cast
      ring
  calc gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ I, c n * χ (n : ZMod q)
      = ∑ n ∈ I, c n * (gaussSum χ⁻¹ ZMod.stdAddChar * χ (n : ZMod q)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = ∑ n ∈ I, c n * ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
        refine Finset.sum_congr rfl fun n _ => by rw [hpoint n]
    _ = ∑ n ∈ I, ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          (c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) *
          ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum I _ _).symm

private theorem sum_all_chars_units_parseval {q : ℕ} [NeZero q] (S : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hsq]
  rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_natCast]
  congr 1
  have hinv : ∑ χ : DirichletCharacter ℂ q,
      (∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a) *
        starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a) =
      ∑ χ : DirichletCharacter ℂ q,
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
        starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) :=
    Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ fun _ => rfl
  rw [hinv]
  have hexp :
      ∑ χ : DirichletCharacter ℂ q,
          (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
            starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) =
        ∑ a : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ,
          S a * starRingEnd ℂ (S b) *
            ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q)) := by
    have h1 : ∀ χ : DirichletCharacter ℂ q,
        (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) *
          starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * S a) =
        ∑ a : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ,
          S a * starRingEnd ℂ (S b) * (χ (a : ZMod q) * starRingEnd ℂ (χ (b : ZMod q))) := by
      intro χ
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Stage2BehrendSieve.dirichlet_orthogonality_conj]
  rw [Finset.sum_eq_single a]
  · rw [if_pos ⟨a.isUnit, rfl⟩]; ring
  · intro b _ hne
    rw [if_neg (fun h => hne (Units.ext h.2.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

open Classical in

theorem primitive_char_sum_le_additive_sum {q : ℕ} [NeZero q] (I : Finset ℕ) (c : ℕ → ℂ) :
    ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ I, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  let S : (ZMod q)ˣ → ℂ := fun a =>
    ∑ n ∈ I, c n * e ((n : ℝ) * (((a : ZMod q).val : ℝ) / (q : ℝ)))
  have hq_lhs :
      (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 =
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ a : (ZMod q)ˣ, χ⁻¹ (a : ZMod q) * S a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
    have hprim_inv : χ⁻¹.IsPrimitive := by
      show χ⁻¹.conductor = q
      rw [DirichletCharacter.conductor_inv, hprim]
    rw [← norm_sq_gaussSum_eq hprim_inv, ← mul_pow, ← norm_mul,
      gaussSum_mul_char_sum_eq hprim I c]
  have hle_all :
      (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          ‖∑ n ∈ I, c n * χ (n : ZMod q)‖ ^ 2 ≤
        (Nat.totient q : ℝ) * ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 := by
    rw [hq_lhs, ← sum_all_chars_units_parseval S]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hbij : ∑ a : (ZMod q)ˣ, ‖S a‖ ^ 2 =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ I, c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
    · intro u _
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      have hu : IsUnit (((u : ZMod q).val : ℕ) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]; exact u.isUnit
      exact (ZMod.isUnit_iff_coprime _ q).mp hu
    · intro u₁ _ u₂ _ h
      exact Units.ext (by rw [← ZMod.natCast_zmod_val (u₁ : ZMod q), ← ZMod.natCast_zmod_val (u₂ : ZMod q), h])
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha.2
      refine ⟨hu.unit, Finset.mem_univ _, ?_⟩
      simp only [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
    · intro u _; rfl
  rw [hbij] at hle_all
  rw [div_mul_eq_mul_div, div_le_iff₀ hphi_pos]
  linarith

open Classical in

theorem multiplicative_large_sieve_Ico (Q M N : ℕ) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + N), ‖c n‖ ^ 2 := by
  have hstep :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ico M (M + N), c n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
        ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 :=
    Finset.sum_le_sum fun k _ =>
      primitive_char_sum_le_additive_sum (q := k + 1) (Finset.Ico M (M + N)) c
  have hshift :
      ∑ k ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (k + 1)).filter (fun a => Nat.Coprime a (k + 1)),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / ((k + 1 : ℕ) : ℝ)))‖ ^ 2 =
        ∑ q ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ‖∑ n ∈ Finset.Ico M (M + N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k₁ _ k₂ _ h; omega
    · intro q hq; rw [Finset.mem_Icc] at hq
      exact ⟨q - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  exact hstep.trans (hshift ▸ farey_large_sieve_Ico Q M N c)

open Classical in

theorem chebyshevPsiChar_eq_sum_Icc {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ (n : ZMod q) := by
  unfold Stage2DirichletAP.chebyshevPsiChar
  have hsplit : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : 0 ∉ Finset.Icc 1 ⌊x⌋₊ := by simp
  rw [hsplit, Finset.sum_insert h0, ArithmeticFunction.map_zero,
    Complex.ofReal_zero, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

end RHDirect.Stage3BombieriVinogradov
end

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Real Matrix

namespace RHDirect.Stage10ZeroDensity

lemma sub_div_le_log_div {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    ((m : ℝ) - (n : ℝ)) / (m : ℝ) ≤ Real.log ((m : ℝ) / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hn0)
  have h2 : 1 - ((m : ℝ) / (n : ℝ))⁻¹ = ((m : ℝ) - (n : ℝ)) / (m : ℝ) := by
    field_simp [hn0.ne', hm0.ne']
  linarith

lemma divisors_card_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    have hdvd : d ∣ a * b := Nat.dvd_of_mem_divisors hd
    set x := Nat.gcd d a
    have hx_dvd_d : x ∣ d := Nat.gcd_dvd_left d a
    have hx_dvd_a : x ∣ a := Nat.gcd_dvd_right d a
    have hx_pos : 0 < x := Nat.gcd_pos_of_pos_right d (by omega)
    set y := d / x
    have hxy : x * y = d := Nat.mul_div_cancel' hx_dvd_d
    have hy_dvd_b : y ∣ b := by
      have hcop : Nat.Coprime (d / x) (a / x) := Nat.coprime_div_gcd_div_gcd hx_pos
      have hdvd' : (d / x) ∣ (a / x) * b := by
        have h1 : x * (d / x) ∣ x * ((a / x) * b) := by
          rw [Nat.mul_div_cancel' hx_dvd_d, ← mul_assoc, Nat.mul_div_cancel' hx_dvd_a]
          exact hdvd
        exact (mul_dvd_mul_iff_left hx_pos.ne').mp h1
      exact hcop.dvd_of_dvd_mul_left hdvd'
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hx_dvd_a, by omega⟩, Nat.mem_divisors.mpr ⟨hy_dvd_b, by omega⟩⟩, hxy⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by rw [Finset.card_product]))

lemma sum_inv_le_one_add_log {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction r with
  | zero => simp
  | succ r ih =>
    have hIcc : Finset.Icc 1 (1 + (r + 1)) = insert (1 + (r + 1)) (Finset.Icc 1 (1 + r)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hstep := sub_div_le_log_div (n := 1 + r) (m := 1 + (r + 1)) (by omega) (by omega)
    have hdiff : ((1 + (r + 1) : ℕ) : ℝ) - ((1 + r : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [hdiff, Real.log_div (Nat.cast_pos.mpr (by omega)).ne' (Nat.cast_pos.mpr (by omega)).ne'] at hstep
    linarith [ih (by omega)]

lemma sum_divisors_card_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hN)
  
  have hsum_d : ∀ M : ℕ, 1 ≤ M →
      ∑ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
    intro M hM
    have hswap : ∑ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) =
        ∑ c ∈ Finset.Icc 1 M, (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ) := by
      have h1 : ∀ b ∈ Finset.Icc 1 M, (b.divisors.card : ℝ) =
          ∑ c ∈ Finset.Icc 1 M, if c ∣ b then (1 : ℝ) else 0 := by
        intro b hb
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
        have hbM : b ≤ M := (Finset.mem_Icc.mp hb).2
        have hdiv_eq : b.divisors = (Finset.Icc 1 M).filter (fun c => c ∣ b) := by
          ext c
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨hcb, _⟩
            have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcb (by omega)
            have hcM : c ≤ M := (Nat.le_of_dvd (by omega) hcb).trans hbM
            exact ⟨⟨hc1, hcM⟩, hcb⟩
          · rintro ⟨_, hcb⟩; exact ⟨hcb, by omega⟩
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hdiv_eq]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hswap]
    have hcard : ∀ c ∈ Finset.Icc 1 M,
        (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ) ≤ (M : ℝ) / (c : ℝ) := by
      intro c hc
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      have hsub : (Finset.Icc 1 M).filter (fun b => c ∣ b) ⊆
          (Finset.Icc 1 (M / c)).image (fun k => c * k) := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_Icc] at hb
        obtain ⟨k, rfl⟩ := hb.2
        rw [Finset.mem_image]
        refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra hk0; push Not at hk0; have hk : k = 0 := by omega
          subst hk; simp at hb
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [hb.1.2])
      have hle : ((Finset.Icc 1 M).filter (fun b => c ∣ b)).card ≤ M / c :=
        (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
      calc (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ)
          ≤ ((M / c : ℕ) : ℝ) := Nat.cast_le.mpr hle
        _ ≤ (M : ℝ) / (c : ℝ) := by
            rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
            exact_mod_cast Nat.div_mul_le_self M c
    calc ∑ c ∈ Finset.Icc 1 M, (((Finset.Icc 1 M).filter (fun b => c ∣ b)).card : ℝ)
        ≤ ∑ c ∈ Finset.Icc 1 M, (M : ℝ) / (c : ℝ) := Finset.sum_le_sum hcard
      _ = (M : ℝ) * ∑ c ∈ Finset.Icc 1 M, (1 : ℝ) / (c : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log hM) (Nat.cast_nonneg M)
  
  have hsum_d_div : ∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    have h1 : ∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ) =
        ∑ a ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N, if c ∣ a then (1 : ℝ) / (a : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
      have hdiv_eq : a.divisors = (Finset.Icc 1 N).filter (fun c => c ∣ a) := by
        ext c
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hca, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hca (by omega), (Nat.le_of_dvd (by omega) hca).trans haN⟩, hca⟩
        · rintro ⟨_, hca⟩; exact ⟨hca, by omega⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div, hdiv_eq]
    rw [h1, Finset.sum_comm]
    have hinner : ∀ c ∈ Finset.Icc 1 N,
        ∑ a ∈ Finset.Icc 1 N, (if c ∣ a then (1 : ℝ) / (a : ℝ) else 0) ≤
        ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) := by
      intro c hc
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      rw [← Finset.sum_filter]
      have hsub : (Finset.Icc 1 N).filter (fun a => c ∣ a) ⊆
          (Finset.Icc 1 N).image (fun e => c * e) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        obtain ⟨e, rfl⟩ := ha.2
        rw [Finset.mem_image]
        refine ⟨e, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra he0; push Not at he0; have he : e = 0 := (by omega); subst he; simp at ha
        · nlinarith [ha.1.2]
      calc ∑ a ∈ (Finset.Icc 1 N).filter (fun a => c ∣ a), (1 : ℝ) / (a : ℝ)
          ≤ ∑ a ∈ (Finset.Icc 1 N).image (fun e => c * e), (1 : ℝ) / (a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / ((c * e : ℕ) : ℝ) := by
            rw [Finset.sum_image]
            intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
        _ = ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => ?_; push_cast; ring
    calc ∑ c ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, (if c ∣ a then (1 : ℝ) / (a : ℝ) else 0)
        ≤ ∑ c ∈ Finset.Icc 1 N, ((1 : ℝ) / (c : ℝ)) * ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) :=
          Finset.sum_le_sum hinner
      _ = (∑ c ∈ Finset.Icc 1 N, (1 : ℝ) / (c : ℝ)) ^ 2 := by rw [← Finset.sum_mul, sq]
      _ ≤ (1 + Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) (sum_inv_le_one_add_log hN) 2
  
  have hdecomp : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 =
        ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, if a ∣ n then (n.divisors.card : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hdiv_eq : n.divisors = (Finset.Icc 1 N).filter (fun a => a ∣ n) := by
        ext a
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨han, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos han (by omega), (Nat.le_of_dvd (by omega) han).trans hnN⟩, han⟩
        · rintro ⟨_, han⟩; exact ⟨han, by omega⟩
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, sq, hdiv_eq]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun n _ => n / a) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨k, rfl⟩ := hn.2
      rw [Nat.mul_div_cancel_left k (by omega)]
      refine ⟨?_, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [hn.1.2])⟩
      by_contra hk0; push Not at hk0; have hk : k = 0 := (by omega); subst hk; simp at hn
    · intro n₁ hn₁ n₂ hn₂ heq
      have h1' := (Finset.mem_filter.mp hn₁).2
      have h2' := (Finset.mem_filter.mp hn₂).2
      calc n₁ = a * (n₁ / a) := (Nat.mul_div_cancel' h1').symm
        _ = a * (n₂ / a) := by rw [heq]
        _ = n₂ := Nat.mul_div_cancel' h2'
    · intro b hb
      rw [Finset.mem_Icc] at hb
      refine ⟨a * b, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a b⟩,
        Nat.mul_div_cancel_left b (by omega)⟩
      · nlinarith [hb.1]
      · exact (Nat.le_div_iff_mul_le (by omega)).mp hb.2 |> fun h => by linarith
    · intro n hn
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
  rw [hdecomp]
  have hinner_le : ∀ a ∈ Finset.Icc 1 N,
      ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ) ≤
      ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    have hM1 : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    have hM_le : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
      exact_mod_cast Nat.div_mul_le_self N a
    have hlog_le : Real.log ((N / a : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (Nat.div_le_self N a))
    calc ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ)
        ≤ ∑ b ∈ Finset.Icc 1 (N / a), (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
          refine Finset.sum_le_sum fun b hb => ?_
          exact_mod_cast divisors_card_mul_le ha1 (Finset.mem_Icc.mp hb).1
      _ = (a.divisors.card : ℝ) * ∑ b ∈ Finset.Icc 1 (N / a), (b.divisors.card : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ (a.divisors.card : ℝ) * (((N / a : ℕ) : ℝ) * (1 + Real.log ((N / a : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hsum_d (N / a) hM1) (Nat.cast_nonneg _)
      _ ≤ (a.divisors.card : ℝ) * (((N : ℝ) / (a : ℝ)) * (1 + Real.log (N : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul hM_le (by linarith) (by linarith [Real.log_nonneg (Nat.one_le_cast.mpr hM1)])
            (by positivity)
      _ = ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by ring
  calc ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b).divisors.card : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 N, ((a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) :=
        Finset.sum_le_sum hinner_le
    _ = (∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ)) * ((N : ℝ) * (1 + Real.log (N : ℝ))) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 * ((N : ℝ) * (1 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hsum_d_div (by positivity)
    _ = (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by ring

end RHDirect.Stage10ZeroDensity
end

noncomputable section

open Complex DirichletCharacter Finset Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage11BombieriVinogradov

def vaughanMollifier (U k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℝ)

def vaughanA0 (V n : ℕ) : ℝ :=
  if n ≤ V then Λ n else 0

def vaughanA1 (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U),
    (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ)

def vaughanA2 (U V n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U),
    (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (· ≤ V), Λ m

def vaughanA3 (U V n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => V < m ∧ U < n / m),
    Λ m * vaughanMollifier U (n / m)

theorem vaughanMollifier_one {U : ℕ} (hU : 1 ≤ U) : vaughanMollifier U 1 = 1 := by
  unfold vaughanMollifier
  have hfilt : (1 : ℕ).divisors.filter (· ≤ U) = {1} := by
    ext d
    simp only [Nat.divisors_one, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hU⟩⟩
  rw [hfilt, Finset.sum_singleton]
  simp

theorem vaughanMollifier_eq_zero_of_le {U k : ℕ} (hk2 : 2 ≤ k) (hkU : k ≤ U) :
    vaughanMollifier U k = 0 := by
  unfold vaughanMollifier
  have hfilt : k.divisors.filter (· ≤ U) = k.divisors :=
    Finset.filter_true_of_mem fun d hd =>
      (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hkU
  rw [hfilt]
  have hZ : ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
    have hmul := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) k
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg (by omega)] at hmul
    rw [← hmul, Nat.sum_divisorsAntidiagonal
      (f := fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hq : k / d ≠ 0 := by
      have hdvd := Nat.dvd_of_mem_divisors hd
      exact Nat.div_ne_zero_iff.mpr ⟨(Nat.pos_of_mem_divisors hd).ne', Nat.le_of_dvd (by omega) hdvd⟩
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq]
  exact_mod_cast hZ

theorem abs_vaughanMollifier_le_divisors (U k : ℕ) :
    |vaughanMollifier U k| ≤ (k.divisors.card : ℝ) := by
  unfold vaughanMollifier
  calc |∑ d ∈ k.divisors.filter (· ≤ U), (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ k.divisors.filter (· ≤ U), |(ArithmeticFunction.moebius d : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ k.divisors.filter (· ≤ U), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        by_cases hsq : Squarefree d
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
          simp [abs_pow]
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          simp
    _ = ((k.divisors.filter (· ≤ U)).card : ℝ) := by simp
    _ ≤ (k.divisors.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)

theorem vaughan_identity {U V n : ℕ} (hU : 1 ≤ U) (hn : 1 ≤ n) :
    Λ n = vaughanA0 V n + vaughanA1 U n - vaughanA2 U V n - vaughanA3 U V n := by
  have hn0 : n ≠ 0 := by omega
  
  have hdiff : vaughanA1 U n - vaughanA2 U V n =
      ∑ d ∈ n.divisors.filter (· ≤ U),
        (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m := by
    unfold vaughanA1 vaughanA2
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← mul_sub]
    congr 1
    have hlog : Real.log ((n / d : ℕ) : ℝ) = ∑ m ∈ (n / d).divisors, Λ m :=
      ArithmeticFunction.vonMangoldt_sum.symm
    rw [hlog, ← Finset.sum_filter_add_sum_filter_not (n / d).divisors (· ≤ V)]
    have hnot : (n / d).divisors.filter (fun m => ¬ m ≤ V) =
        (n / d).divisors.filter (fun m => V < m) := by
      ext m; simp
    rw [hnot]
    ring
  
  have hswap :
      ∑ d ∈ n.divisors.filter (· ≤ U),
          (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m =
        ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) := by
    have hL :
        ∑ d ∈ n.divisors.filter (· ≤ U),
            (ArithmeticFunction.moebius d : ℝ) * ∑ m ∈ (n / d).divisors.filter (fun m => V < m), Λ m =
          ∑ d ∈ n.divisors.filter (· ≤ U), ∑ m ∈ n.divisors.filter (fun m => V < m),
            if d * m ∣ n then (ArithmeticFunction.moebius d : ℝ) * Λ m else 0 := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hm_dvd, hnd_ne⟩, hVm⟩
        have hdm : d * m ∣ n := by
          obtain ⟨r, hr⟩ := hm_dvd
          exact ⟨r, by rw [← Nat.mul_div_cancel' hdvd, hr]; ring⟩
        exact ⟨⟨⟨(dvd_mul_left m d).trans hdm, hn0⟩, hVm⟩, hdm⟩
      · rintro ⟨⟨⟨_, _⟩, hVm⟩, hdm⟩
        have hnd_ne : n / d ≠ 0 :=
          Nat.div_ne_zero_iff.mpr ⟨hdpos.ne', Nat.le_of_dvd hn hdvd⟩
        have hm_dvd : m ∣ n / d := by
          obtain ⟨r, hr⟩ := hdm
          refine ⟨r, ?_⟩
          have h1 : d * (n / d) = d * (m * r) := by
            rw [Nat.mul_div_cancel' hdvd, hr]; ring
          exact Nat.eq_of_mul_eq_mul_left hdpos h1
        exact ⟨⟨hm_dvd, hnd_ne⟩, hVm⟩
    have hR :
        ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) =
          ∑ m ∈ n.divisors.filter (fun m => V < m), ∑ d ∈ n.divisors.filter (· ≤ U),
            if d * m ∣ n then (ArithmeticFunction.moebius d : ℝ) * Λ m else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_dvd : m ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm).1
      have hmpos : 0 < m := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hm).1
      unfold vaughanMollifier
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun d _ => mul_comm _ _
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd_dvd, _⟩, hdU⟩
        have hdm : d * m ∣ n := by
          obtain ⟨r, hr⟩ := hd_dvd
          exact ⟨r, by rw [← Nat.mul_div_cancel' hm_dvd, hr]; ring⟩
        exact ⟨⟨⟨(dvd_mul_right d m).trans hdm, hn0⟩, hdU⟩, hdm⟩
      · rintro ⟨⟨⟨_, _⟩, hdU⟩, hdm⟩
        have hnm_ne : n / m ≠ 0 :=
          Nat.div_ne_zero_iff.mpr ⟨hmpos.ne', Nat.le_of_dvd hn hm_dvd⟩
        have hd_dvd : d ∣ n / m := by
          obtain ⟨r, hr⟩ := hdm
          refine ⟨r, ?_⟩
          have h1 : m * (n / m) = m * (d * r) := by
            rw [Nat.mul_div_cancel' hm_dvd, hr]; ring
          exact Nat.eq_of_mul_eq_mul_left hmpos h1
        exact ⟨⟨hd_dvd, hnm_ne⟩, hdU⟩
    rw [hL, Finset.sum_comm, ← hR]
  
  have hsplit :
      ∑ m ∈ n.divisors.filter (fun m => V < m), Λ m * vaughanMollifier U (n / m) =
        (Λ n - vaughanA0 V n) + vaughanA3 U V n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (n.divisors.filter (fun m => V < m)) (fun m => U < n / m)]
    have hA3 :
        ∑ m ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => U < n / m),
            Λ m * vaughanMollifier U (n / m) = vaughanA3 U V n := by
      unfold vaughanA3
      congr 1; ext m; simp [and_assoc]
    have hsmall :
        ∑ m ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m),
            Λ m * vaughanMollifier U (n / m) = Λ n - vaughanA0 V n := by
      by_cases hVn : V < n
      · have hn_mem : n ∈ (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m) := by
          simp only [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨⟨dvd_rfl, hn0⟩, hVn⟩, by rw [Nat.div_self hn]; omega⟩
        rw [Finset.sum_eq_single n]
        · rw [Nat.div_self hn, vaughanMollifier_one hU, mul_one]
          unfold vaughanA0; rw [if_neg (by omega)]; ring
        · intro m hm hmn
          simp only [Finset.mem_filter, Nat.mem_divisors] at hm
          have hq_ge2 : 2 ≤ n / m := by
            have hm_le : m ≤ n := Nat.le_of_dvd hn hm.1.1.1
            have hm_lt : m < n := lt_of_le_of_ne hm_le hmn
            have hmul := Nat.mul_div_cancel' hm.1.1.1
            have hq0 : n / m ≠ 0 := by intro h0; rw [h0, mul_zero] at hmul; omega
            have hq1 : n / m ≠ 1 := by intro h1; rw [h1, mul_one] at hmul; omega
            rcases Nat.lt_or_ge (n / m) 2 with hlt | hge
            · exfalso
              have hle1 : n / m ≤ 1 := Nat.lt_succ_iff.mp hlt
              rcases Nat.eq_zero_or_pos (n / m) with h0 | hp
              · exact hq0 h0
              · exact hq1 (le_antisymm hle1 hp)
            · exact hge
          rw [vaughanMollifier_eq_zero_of_le hq_ge2 (Nat.not_lt.mp hm.2), mul_zero]
        · intro h; exact absurd hn_mem h
      · have hempty : (n.divisors.filter (fun m => V < m)).filter (fun m => ¬ U < n / m) = ∅ := by
          ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false]
          rintro ⟨⟨⟨hmn, _⟩, hVm⟩, _⟩
          have := Nat.le_of_dvd hn hmn
          omega
        rw [hempty, Finset.sum_empty]
        unfold vaughanA0; rw [if_pos (by omega)]; ring
    rw [hA3, hsmall, add_comm]
  linarith

def vaughanS0 {q : ℕ} (χ : DirichletCharacter ℂ q) (V : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), χ (n : ZMod q) * (Λ n : ℂ)

def vaughanS1 {q : ℕ} (χ : DirichletCharacter ℂ q) (U : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U,
    (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
      ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), χ (m : ZMod q) * (Real.log (m : ℝ) : ℂ)

def vaughanS2 {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 U,
    (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
      ∑ m ∈ Finset.Icc 1 V,
        (Λ m : ℂ) * χ (m : ZMod q) *
          ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (d * m)), χ (r : ZMod q)

def vaughanS3 {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc V (⌊x⌋₊ / U),
    (Λ m : ℂ) * χ (m : ZMod q) *
      ∑ k ∈ Finset.Ioc U (⌊x⌋₊ / m), (vaughanMollifier U k : ℂ) * χ (k : ZMod q)

theorem chebyshevPsiChar_vaughan_decomp {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) {x : ℝ} (_hx : 1 ≤ x) :
    Stage2DirichletAP.chebyshevPsiChar χ x =
      vaughanS0 χ V x + vaughanS1 χ U x - vaughanS2 χ U V x - vaughanS3 χ U V x := by
  set N : ℕ := ⌊x⌋₊
  rw [Stage3BombieriVinogradov.chebyshevPsiChar_eq_sum_Icc]
  have hcomm : ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * χ (n : ZMod q) =
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Λ n : ℂ) :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hcomm]
  have hpoint :
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Λ n : ℂ) =
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA0 V n : ℂ) +
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA1 U n : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA2 U V n : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA3 U V n : ℂ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hv := congrArg (Complex.ofReal : ℝ → ℂ) (vaughan_identity (U := U) (V := V) hU hn1)
    simp only [Complex.ofReal_add, Complex.ofReal_sub] at hv
    rw [hv]; ring
  rw [hpoint]
  
  have hS0 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA0 V n : ℂ) = vaughanS0 χ V x := by
    unfold vaughanA0 vaughanS0
    have hfilt : (Finset.Icc 1 N).filter (· ≤ V) = Finset.Icc 1 (min N V) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]; tauto
    rw [← hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ V <;> simp [h]
  
  have hS1 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA1 U n : ℂ) = vaughanS1 χ U x := by
    unfold vaughanA1 vaughanS1
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U,
            if d ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
                (χ ((n / d : ℕ) : ZMod q) * (Real.log ((n / d : ℕ) : ℝ) : ℂ))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_filter]
      have hset : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hset]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdn : d ∣ n := (Finset.mem_filter.mp hd).2
      have hmul : (n : ZMod q) = (d : ZMod q) * ((n / d : ℕ) : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
      rw [hmul, map_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hm1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hd1
      exact ⟨hm1, (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).mp hm.2
      rwa [mul_comm] at this
    · intro n _; rfl
  
  have hS2 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA2 U V n : ℂ) = vaughanS2 χ U V x := by
    unfold vaughanA2 vaughanS2
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ d ∈ n.divisors.filter (· ≤ U),
              (ArithmeticFunction.moebius d : ℝ) *
                ∑ m ∈ (n / d).divisors.filter (· ≤ V), Λ m : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 U, ∑ m ∈ Finset.Icc 1 V,
            if d * m ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod q) *
                ((Λ m : ℂ) * χ (m : ZMod q) * χ ((n / (d * m) : ℕ) : ZMod q))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [Complex.ofReal_sum, Finset.mul_sum]
      have hsetD : n.divisors.filter (· ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
        ext d; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hdn, _⟩, hdU⟩; exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn1, hdU⟩, hdn⟩
        · rintro ⟨⟨_, hdU⟩, hdn⟩; exact ⟨⟨hdn, by omega⟩, hdU⟩
      rw [hsetD, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      by_cases hdn : d ∣ n
      · rw [if_pos hdn, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_sum,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter]
        have hsetM : (n / d).divisors.filter (· ≤ V) =
            (Finset.Icc 1 V).filter (fun m => d * m ∣ n) := by
          ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hm, _⟩, hmV⟩
            have hdm : d * m ∣ n := by
              obtain ⟨r, hr⟩ := hm
              exact ⟨r, by rw [← Nat.mul_div_cancel' hdn, hr]; ring⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hm (Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd1), hmV⟩, hdm⟩
          · rintro ⟨⟨_, hmV⟩, hdm⟩
            have hnd0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd1).ne'
            have hm : m ∣ n / d := by
              obtain ⟨r, hr⟩ := hdm
              refine ⟨r, Nat.eq_of_mul_eq_mul_left hd1 ?_⟩
              rw [Nat.mul_div_cancel' hdn, hr]; ring
            exact ⟨⟨hm, hnd0⟩, hmV⟩
        rw [hsetM]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hdm : d * m ∣ n := (Finset.mem_filter.mp hm).2
        have hmul : (n : ZMod q) = (d : ZMod q) * (m : ZMod q) * ((n / (d * m) : ℕ) : ZMod q) := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdm]
        rw [hmul, map_mul, map_mul]; ring
      · rw [if_neg hdn]
        symm
        refine Finset.sum_eq_zero fun m _ => if_neg fun hdm => hdn ((dvd_mul_right d m).trans hdm)
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hdm1 : 1 ≤ d * m := Nat.mul_pos hd1 hm1
    rw [← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / (d * m)) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hr1 : 1 ≤ n / (d * m) := Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hdm1
      exact ⟨hr1, (Nat.le_div_iff_mul_le hdm1).mpr (by rw [Nat.div_mul_cancel hn.2]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2, heq]
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      refine ⟨d * m * r, ?_, Nat.mul_div_cancel_left r hdm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hdm1 hr.1, ?_⟩, dvd_mul_right (d * m) r⟩
      have := (Nat.le_div_iff_mul_le hdm1).mp hr.2
      rwa [mul_comm] at this
    · intro n _; ring
  
  have hS3 : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (vaughanA3 U V n : ℂ) = vaughanS3 χ U V x := by
    unfold vaughanA3 vaughanS3
    have h1 :
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) *
            ((∑ m ∈ n.divisors.filter (fun m => V < m ∧ U < n / m),
              Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc V (N / U),
            if m ∣ n ∧ U < n / m then
              (Λ m : ℂ) * χ (m : ZMod q) *
                ((vaughanMollifier U (n / m) : ℂ) * χ ((n / m : ℕ) : ZMod q))
            else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_filter]
      have hset : n.divisors.filter (fun m => V < m ∧ U < n / m) =
          (Finset.Ioc V (N / U)).filter (fun m => m ∣ n ∧ U < n / m) := by
        ext m; simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hmn, _⟩, hVm, hUdiv⟩
          have hmU : m * U ≤ N := by
            have : m * U ≤ m * (n / m) := Nat.mul_le_mul_left m (by omega)
            rw [Nat.mul_div_cancel' hmn] at this
            exact this.trans hnN
          exact ⟨⟨hVm, (Nat.le_div_iff_mul_le hU).mpr hmU⟩, hmn, hUdiv⟩
        · rintro ⟨⟨hVm, _⟩, hmn, hUdiv⟩
          exact ⟨⟨hmn, by omega⟩, hVm, hUdiv⟩
      rw [hset]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmn : m ∣ n := (Finset.mem_filter.mp hm).2.1
      have hmul : (n : ZMod q) = (m : ZMod q) * ((n / m : ℕ) : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]
      rw [hmul, map_mul, Complex.ofReal_mul]; ring
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := by rw [Finset.mem_Ioc] at hm; omega
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.2.2, (Nat.le_div_iff_mul_le hm1).mpr (by rw [Nat.div_mul_cancel hn.2.1]; exact hn.1.2)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
          ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨m * k, ?_, Nat.mul_div_cancel_left k hm1⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hm1 (by omega), ?_⟩, dvd_mul_right m k, ?_⟩
      · have := (Nat.le_div_iff_mul_le hm1).mp hk.2
        rwa [mul_comm] at this
      · rw [Nat.mul_div_cancel_left k hm1]; exact hk.1
    · intro n _; rfl
  rw [hS0, hS1, hS2, hS3]

open Classical in
theorem multiplicative_large_sieve_Ioc (Q M N : ℕ) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hIoc : Finset.Ioc M (M + N) = Finset.Ico (M + 1) ((M + 1) + N) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc]
  exact Stage3BombieriVinogradov.multiplicative_large_sieve_Ico Q (M + 1) N a

open Classical in

theorem multiplicative_large_sieve_Ioc_interval (Q M₁ M₂ : ℕ) (a : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * χ (n : ZMod (k + 1))‖ ^ 2 ≤
      (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M₁ M₂, ‖a n‖ ^ 2 := by
  by_cases hle : M₁ ≤ M₂
  · have hEq : M₁ + (M₂ - M₁) = M₂ := Nat.add_sub_of_le hle
    simpa only [hEq] using multiplicative_large_sieve_Ioc Q M₁ (M₂ - M₁) a
  · have hempty : Finset.Ioc M₁ M₂ = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp

open Classical in

theorem bilinear_multiplicative_large_sieve (Q M₁ M₂ N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖(∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))) *
              (∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1)))‖ ≤
      Real.sqrt (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) *
        Real.sqrt (((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2) := by
  let S : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range Q).sigma fun k =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => ((p.1 + 1 : ℕ) : ℝ) / (Nat.totient (p.1 + 1) : ℝ)
  let A : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => Real.sqrt (w p) * ‖∑ m ∈ Finset.Ioc M₁ M₂, a m * p.2 (m : ZMod (p.1 + 1))‖
  let B : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => Real.sqrt (w p) * ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * p.2 (n : ZMod (p.1 + 1))‖
  have hw_nn : ∀ p : Σ k : ℕ, DirichletCharacter ℂ (k + 1), 0 ≤ w p := fun p => by
    dsimp only [w]; positivity
  have hLHS :
      ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖(∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))) *
                (∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1)))‖ =
        ∑ p ∈ S, A p * B p := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    dsimp only [A, B, w]
    rw [norm_mul]
    have hsq : Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
        Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            (‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ *
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖)
        = (Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            Real.sqrt (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ))) *
            (‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ *
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖) := by rw [hsq]
      _ = _ := by ring
  have hCS : ∑ p ∈ S, A p * B p ≤
      Real.sqrt (∑ p ∈ S, A p ^ 2) * Real.sqrt (∑ p ∈ S, B p ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq S A B
    have hnn : 0 ≤ ∑ p ∈ S, A p * B p :=
      Finset.sum_nonneg fun p _ => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq
  have hA2 : ∑ p ∈ S, A p ^ 2 ≤
      (((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2 := by
    have hEq : ∑ p ∈ S, A p ^ 2 =
        ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ m ∈ Finset.Ioc M₁ M₂, a m * χ (m : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      dsimp only [A, w]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval Q M₁ M₂ a
  have hB2 : ∑ p ∈ S, B p ^ 2 ≤
      (((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2 := by
    have hEq : ∑ p ∈ S, B p ^ 2 =
        ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc N₁ N₂, b n * χ (n : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      dsimp only [B, w]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval Q N₁ N₂ b
  rw [hLHS]
  calc ∑ p ∈ S, A p * B p
      ≤ Real.sqrt (∑ p ∈ S, A p ^ 2) * Real.sqrt (∑ p ∈ S, B p ^ 2) := hCS
    _ ≤ Real.sqrt ((((M₂ - M₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Ioc M₁ M₂, ‖a m‖ ^ 2) *
          Real.sqrt ((((N₂ - N₁ : ℕ) : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc N₁ N₂, ‖b n‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hB2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]; ring

private lemma distZ_div_ge_min {d a : ℕ} (ha1 : 1 ≤ a) (had : a < d) :
    ((min a (d - a) : ℕ) : ℝ) / (d : ℝ) ≤ Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold Stage3BombieriVinogradov.distZ Stage3BombieriVinogradov.fracSym
  set k : ℤ := round ((a : ℝ) / (d : ℝ))
  rcases le_or_gt k 0 with hk0 | hk1
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have ha_pos : (0 : ℝ) ≤ (a : ℝ) / (d : ℝ) := by positivity
    have hmin : ((min a (d - a) : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast Nat.min_le_left a (d - a)
    have h1 : (a : ℝ) / (d : ℝ) ≤ |(a : ℝ) / (d : ℝ) - (k : ℝ)| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    exact (div_le_div_of_nonneg_right hmin hd_pos.le).trans h1
  · have hk1' : (1 : ℤ) ≤ k := hk1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1'
    have hlt1 : (a : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_pos).mpr (by exact_mod_cast had)
    have hmin : ((min a (d - a) : ℕ) : ℝ) ≤ ((d - a : ℕ) : ℝ) := by
      exact_mod_cast Nat.min_le_right a (d - a)
    have hsub : ((d - a : ℕ) : ℝ) / (d : ℝ) = 1 - (a : ℝ) / (d : ℝ) := by
      rw [Nat.cast_sub had.le]; field_simp [hd_pos.ne']
    have h1 : 1 - (a : ℝ) / (d : ℝ) ≤ |(a : ℝ) / (d : ℝ) - (k : ℝ)| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    exact ((div_le_div_of_nonneg_right hmin hd_pos.le).trans_eq hsub).trans h1

theorem polya_vinogradov_primitive {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ ≤ Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = d
    rw [DirichletCharacter.conductor_inv, hprim]
  have hgauss := Stage3BombieriVinogradov.gaussSum_mul_char_sum_eq hprim (Finset.Icc 1 N) (fun _ => (1 : ℂ))
  simp only [one_mul] at hgauss
  have hnorm_lhs : ‖gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ =
      Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ := by
    rw [norm_mul, Stage3BombieriVinogradov.norm_gaussSum_eq_sqrt hprim_inv]
  have hnorm_rhs :
      ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
          ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ ≤
        ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
    calc ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖
        ≤ ∑ a : (ZMod d)ˣ, ‖χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a : (ZMod d)ˣ,
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (χ⁻¹.norm_le_one _) (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ ∑ a ∈ Finset.Icc 1 (d - 1),
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖ := by
          let f : (ZMod d)ˣ → ℕ := fun u => (u : ZMod d).val
          have hinj : Set.InjOn f ((Finset.univ : Finset (ZMod d)ˣ) : Set (ZMod d)ˣ) := by
            intro u₁ _ u₂ _ h
            dsimp only [f] at h
            exact Units.ext (by rw [← ZMod.natCast_zmod_val (u₁ : ZMod d),
              ← ZMod.natCast_zmod_val (u₂ : ZMod d), h])
          have hsub : (Finset.univ : Finset (ZMod d)ˣ).image f ⊆ Finset.Icc 1 (d - 1) := by
            intro a ha
            obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
            rw [Finset.mem_Icc]
            have hlt : (u : ZMod d).val < d := ZMod.val_lt _
            have hne0 : (u : ZMod d).val ≠ 0 := by
              intro h0
              have hu0 : (u : ZMod d) = 0 := by rw [← ZMod.natCast_zmod_val (u : ZMod d), h0, Nat.cast_zero]
              have h10 : (1 : ZMod d) = 0 := by
                have := u.mul_inv; rw [hu0, zero_mul] at this; exact this.symm
              have : Fact (1 < d) := ⟨by omega⟩
              have hlt1 : (1 : ZMod d).val = 1 := ZMod.val_one d
              rw [h10, ZMod.val_zero] at hlt1; omega
            change 1 ≤ (u : ZMod d).val ∧ (u : ZMod d).val ≤ d - 1
            omega
          rw [← Finset.sum_image (f := fun a : ℕ =>
            ‖∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖) hinj]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
      _ ≤ ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have had : a < d := by have := (Finset.mem_Icc.mp ha).2; omega
          have hmin_pos : (0 : ℝ) < ((min a (d - a) : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < min a (d - a) by omega)
          have hdist := distZ_div_ge_min ha1 had
          have hdist_pos : 0 < Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)) :=
            lt_of_lt_of_le (div_pos hmin_pos hd_pos) hdist
          have hIco :
              ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ))) =
                ∑ n ∈ Finset.Ico (1 : ℤ) ((1 : ℤ) + (N : ℤ)),
                  Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ))) := by
            refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
            · intro n hn; simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_Ico]; omega
            · intro n₁ _ n₂ _ h; exact Int.ofNat.inj h
            · intro z hz; simp only [Finset.mem_Ico] at hz
              exact ⟨z.toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro n _; simp
          rw [hIco]
          calc ‖∑ n ∈ Finset.Ico (1 : ℤ) ((1 : ℤ) + (N : ℤ)),
                  Stage3BombieriVinogradov.e ((n : ℝ) * ((a : ℝ) / (d : ℝ)))‖
              ≤ (2 * Stage3BombieriVinogradov.distZ ((a : ℝ) / (d : ℝ)))⁻¹ :=
                Stage3BombieriVinogradov.norm_geom_sum_e_Ico_le 1 N hdist_pos
            _ ≤ (2 * (((min a (d - a) : ℕ) : ℝ) / (d : ℝ)))⁻¹ := by
                exact inv_anti₀ (by positivity) (by linarith)
            _ = (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) := by
                field_simp [hd_pos.ne', hmin_pos.ne']
  
  have hsum_le :
      ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) ≤
        (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have hpair : ∀ a ∈ Finset.Icc 1 (d - 1),
        (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ)) ≤
          ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ) + (1 : ℝ) / ((d - a : ℕ) : ℝ)) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have had : a < d := by have := (Finset.mem_Icc.mp ha).2; omega
      have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
      have hda_pos : (0 : ℝ) < ((d - a : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      rcases le_total a (d - a) with h | h
      · rw [min_eq_left h]
        have hEq : (d : ℝ) / (2 * (a : ℝ)) = ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ)) := by ring
        rw [hEq]
        have hnn : 0 ≤ ((d : ℝ) / 2) * ((1 : ℝ) / ((d - a : ℕ) : ℝ)) := by positivity
        linarith
      · rw [min_eq_right h]
        have hEq : (d : ℝ) / (2 * ((d - a : ℕ) : ℝ)) =
            ((d : ℝ) / 2) * ((1 : ℝ) / ((d - a : ℕ) : ℝ)) := by ring
        rw [hEq]
        have hnn : 0 ≤ ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ)) := by positivity
        linarith
    have hrev :
        ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / ((d - a : ℕ) : ℝ) =
          ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) := by
      refine Finset.sum_bij (fun a _ => d - a) ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Icc] at ha₁ ha₂; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb
        exact ⟨d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro a _; rfl
    have hH : ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) ≤ 1 + Real.log (d : ℝ) := by
      calc ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ)
          ≤ ∑ a ∈ Finset.Icc 1 d, (1 : ℝ) / (a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
              fun _ _ _ => by positivity
        _ ≤ 1 + Real.log (d : ℝ) := Stage10ZeroDensity.sum_inv_le_one_add_log (by omega)
    calc ∑ a ∈ Finset.Icc 1 (d - 1), (d : ℝ) / (2 * ((min a (d - a) : ℕ) : ℝ))
        ≤ ∑ a ∈ Finset.Icc 1 (d - 1),
            ((d : ℝ) / 2) * ((1 : ℝ) / (a : ℝ) + (1 : ℝ) / ((d - a : ℕ) : ℝ)) :=
          Finset.sum_le_sum hpair
      _ = ((d : ℝ) / 2) *
            (∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) +
             ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / ((d - a : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = (d : ℝ) * ∑ a ∈ Finset.Icc 1 (d - 1), (1 : ℝ) / (a : ℝ) := by rw [hrev]; ring
      _ ≤ (d : ℝ) * (1 + Real.log (d : ℝ)) := mul_le_mul_of_nonneg_left hH hd_pos.le
  have hfinal : Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ ≤
      Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
    have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd_pos.le
    calc Real.sqrt (d : ℝ) * ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖
        = ‖gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d)‖ := hnorm_lhs.symm
      _ = ‖∑ a : (ZMod d)ˣ, χ⁻¹ (a : ZMod d) *
            ∑ n ∈ Finset.Icc 1 N, Stage3BombieriVinogradov.e ((n : ℝ) * (((a : ZMod d).val : ℝ) / (d : ℝ)))‖ := by
          rw [hgauss]
      _ ≤ (d : ℝ) * (1 + Real.log (d : ℝ)) := hnorm_rhs.trans hsum_le
      _ = Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
          rw [← mul_assoc, hsq]
  exact le_of_mul_le_mul_left hfinal hsq_pos

theorem polya_vinogradov_log_primitive {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * (Real.log (n : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log ((max 1 N : ℕ) : ℝ) := by
  set M : ℝ := Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))
  have hM_nn : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; linarith)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hmax : max 1 N = N := Nat.max_eq_right hN
    rw [hmax]
    let S : ℕ → ℂ := fun m => ∑ j ∈ Finset.Icc 1 m, χ (j : ZMod d)
    have hS0 : S 0 = 0 := by simp [S]
    have hS_step : ∀ m : ℕ, 1 ≤ m → χ (m : ZMod d) = S m - S (m - 1) := by
      intro m hm
      dsimp only [S]
      have hIcc : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp; omega)]
      ring
    
    have habel : ∀ K : ℕ, 1 ≤ K →
        ∑ n ∈ Finset.Icc 1 K, χ (n : ZMod d) * (Real.log (n : ℝ) : ℂ) =
          S K * (Real.log (K : ℝ) : ℂ) -
            ∑ m ∈ Finset.Icc 1 (K - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ)) := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        have hIcc1 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hIcc2 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc1, Finset.sum_insert (by simp), ih, Nat.add_sub_cancel, hIcc2,
          Finset.sum_insert (by simp; omega), hS_step (k + 1) (by omega), Nat.add_sub_cancel]
        push_cast
        ring
    rw [habel N hN]
    have hS_bd : ∀ m : ℕ, ‖S m‖ ≤ M := fun m => polya_vinogradov_primitive hd2 hprim m
    have htele :
        ∑ m ∈ Finset.Icc 1 (N - 1), (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) =
          Real.log (N : ℝ) := by
      have h1 : ∀ K : ℕ, 1 ≤ K →
          ∑ m ∈ Finset.Icc 1 (K - 1), (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) =
            Real.log (K : ℝ) := by
        intro K hK
        induction K, hK using Nat.le_induction with
        | base => simp
        | succ k hk ih =>
          have hIcc2 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [Nat.add_sub_cancel, hIcc2, Finset.sum_insert (by simp; omega), ih]
          ring
      exact h1 N hN
    calc ‖S N * (Real.log (N : ℝ) : ℂ) -
            ∑ m ∈ Finset.Icc 1 (N - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ))‖
        ≤ ‖S N * (Real.log (N : ℝ) : ℂ)‖ +
            ‖∑ m ∈ Finset.Icc 1 (N - 1),
              S m * (((Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) : ℝ) : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ ‖S N‖ * Real.log (N : ℝ) +
            ∑ m ∈ Finset.Icc 1 (N - 1),
              ‖S m‖ * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
          have hterm1 : ‖S N * (Real.log (N : ℝ) : ℂ)‖ = ‖S N‖ * Real.log (N : ℝ) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg N)]
          rw [hterm1]
          gcongr
          refine (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hdiff_nn : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
            have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
            have := Real.log_le_log (Nat.cast_pos.mpr hm1) hm_le
            linarith
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdiff_nn]
      _ ≤ M * Real.log (N : ℝ) +
            ∑ m ∈ Finset.Icc 1 (N - 1), M * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right (hS_bd N) (Real.log_natCast_nonneg N)) ?_
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
          have hdiff_nn : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
            linarith [Real.log_le_log (Nat.cast_pos.mpr hm1) hm_le]
          exact mul_le_mul_of_nonneg_right (hS_bd m) hdiff_nn
      _ = M * Real.log (N : ℝ) + M * Real.log (N : ℝ) := by
          rw [← Finset.mul_sum, htele]
      _ = 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log (N : ℝ) := by
          dsimp only [M]; ring



open Classical in

private lemma sum_prim_weight_le (Q : ℕ) :
    ∑ k ∈ Finset.range Q,
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
      (Q : ℝ) ^ 2 := by
  calc ∑ k ∈ Finset.range Q,
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
      ≤ ∑ k ∈ Finset.range Q, (Q : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkQ : k + 1 ≤ Q := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
          Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
        have htot : Fintype.card (DirichletCharacter ℂ (k + 1)) = (k + 1).totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (k + 1)
        have hcard :
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) ≤
              (Nat.totient (k + 1) : ℝ) := by
          have hnat : (Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card ≤
              (k + 1).totient := by
            calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).card := Finset.card_filter_le _ _
              _ = (k + 1).totient := by rw [Finset.card_univ, htot]
          exact_mod_cast hnat
        calc (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)
            ≤ (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) * (Nat.totient (k + 1) : ℝ) :=
              mul_le_mul_of_nonneg_left hcard (by positivity)
          _ = ((k + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hphi_pos.ne'
          _ ≤ (Q : ℝ) := by exact_mod_cast hkQ
    _ = (Q : ℝ) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq]

theorem norm_vaughanS0_le {q : ℕ} (χ : DirichletCharacter ℂ q) (V : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖vaughanS0 χ V x‖ ≤ (V : ℝ) * Real.log x := by
  unfold vaughanS0
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ‖∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), χ (n : ZMod q) * (Λ n : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), ‖χ (n : ZMod q) * (Λ n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (min ⌊x⌋₊ V), Real.log x := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnx : (n : ℝ) ≤ x :=
          (by exact_mod_cast ((Finset.mem_Icc.mp hn).2.trans (Nat.min_le_left _ _)) : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
            (Nat.floor_le (by linarith))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc ‖χ (n : ZMod q)‖ * Λ n
            ≤ 1 * Λ n := mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
          _ = Λ n := one_mul _
          _ ≤ Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr hn1) hnx
    _ = ((Finset.Icc 1 (min ⌊x⌋₊ V)).card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (V : ℝ) * Real.log x := by
        refine mul_le_mul_of_nonneg_right ?_ hlogx_nn
        have hcard : (Finset.Icc 1 (min ⌊x⌋₊ V)).card ≤ V := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast hcard

theorem norm_vaughanS1_le {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (U : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖vaughanS1 χ U x‖ ≤ 2 * (U : ℝ) * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
  unfold vaughanS1
  have hM_nn : 0 ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; positivity
  calc ‖∑ k ∈ Finset.Icc 1 U,
          (ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖
      ≤ ∑ k ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 U,
          2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul]
        have hmu : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
          by_cases hsq : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp [norm_pow]
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
        have hfac : ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ ≤ 1 :=
          (mul_le_mul hmu (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
        have hmax_le : ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) ≤ x := by
          rcases le_total 1 (⌊x⌋₊ / k) with h | h
          · rw [Nat.max_eq_right h]
            exact (by exact_mod_cast Nat.div_le_self ⌊x⌋₊ k : ((⌊x⌋₊ / k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
              (Nat.floor_le (by linarith))
          · rw [Nat.max_eq_left h]; exact_mod_cast hx
        have hlog_le : Real.log ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) ≤ Real.log x :=
          Real.log_le_log (by exact_mod_cast (show 0 < max 1 (⌊x⌋₊ / k) by omega)) hmax_le
        calc ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ *
                ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖
            ≤ 1 * ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
          _ = ‖∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / k), χ (m : ZMod d) * (Real.log (m : ℝ) : ℂ)‖ := one_mul _
          _ ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) *
                Real.log ((max 1 (⌊x⌋₊ / k) : ℕ) : ℝ) :=
              polya_vinogradov_log_primitive hd2 hprim (⌊x⌋₊ / k)
          _ ≤ 2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x :=
              mul_le_mul_of_nonneg_left hlog_le hM_nn
    _ = ((Finset.Icc 1 U).card : ℝ) * (2 * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (U : ℝ) * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) * Real.log x := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]; ring

theorem norm_vaughanS2_le {d : ℕ} [NeZero d] (hd2 : 2 ≤ d)
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {U V : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hVx : (V : ℝ) ≤ x) :
    ‖vaughanS2 χ U V x‖ ≤ (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
  unfold vaughanS2
  have hM_nn : 0 ≤ Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d; positivity
  calc ‖∑ k ∈ Finset.Icc 1 U,
          (ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
              ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖
      ≤ ∑ k ∈ Finset.Icc 1 U,
          ‖(ArithmeticFunction.moebius k : ℂ) * χ (k : ZMod d) *
            ∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
              ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 U,
          (V : ℝ) * Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul]
        have hmu : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
          by_cases hsq : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]; simp [norm_pow]
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; simp
        have hfac : ‖(ArithmeticFunction.moebius k : ℂ)‖ * ‖χ (k : ZMod d)‖ ≤ 1 :=
          (mul_le_mul hmu (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
        refine (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans ?_
        rw [one_mul]
        calc ‖∑ m ∈ Finset.Icc 1 V, (Λ m : ℂ) * χ (m : ZMod d) *
                ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖
            ≤ ∑ m ∈ Finset.Icc 1 V, ‖(Λ m : ℂ) * χ (m : ZMod d) *
                ∑ r ∈ Finset.Icc 1 (⌊x⌋₊ / (k * m)), χ (r : ZMod d)‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ Finset.Icc 1 V, Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
              have hmx : (m : ℝ) ≤ x :=
                (by exact_mod_cast (Finset.mem_Icc.mp hm).2 : (m : ℝ) ≤ (V : ℝ)).trans hVx
              rw [norm_mul, norm_mul, Complex.norm_real,
                Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
              have hL : Λ m * ‖χ (m : ZMod d)‖ ≤ Real.log x := by
                calc Λ m * ‖χ (m : ZMod d)‖
                    ≤ Λ m * 1 := mul_le_mul_of_nonneg_left (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
                  _ = Λ m := mul_one _
                  _ ≤ Real.log (m : ℝ) := ArithmeticFunction.vonMangoldt_le_log
                  _ ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr hm1) hmx
              exact mul_le_mul hL (polya_vinogradov_primitive hd2 hprim (⌊x⌋₊ / (k * m)))
                (norm_nonneg _) (Real.log_nonneg hx)
          _ = (V : ℝ) * Real.log x * (Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ))) := by
              rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ = (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt (d : ℝ) * (1 + Real.log (d : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

private def blockLo (V r : ℕ) : ℕ := V * 2 ^ r

private def blockHi (N U V r : ℕ) : ℕ := min (V * 2 ^ (r + 1)) (N / U)

private def blockStep (V : ℕ) (Δ : ℝ) (r : ℕ) : ℕ :=
  max 1 ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊

private def blockCount (N U V : ℕ) (Δ : ℝ) (r : ℕ) : ℕ :=
  (blockHi N U V r - blockLo V r + blockStep V Δ r - 1) / blockStep V Δ r

private def subLo (V : ℕ) (Δ : ℝ) (r j : ℕ) : ℕ :=
  blockLo V r + j * blockStep V Δ r

private def subHi (N U V : ℕ) (Δ : ℝ) (r j : ℕ) : ℕ :=
  min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi N U V r)

private lemma sum_Ioc_split {α : Type*} [AddCommMonoid α] (a b c : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc a b, f m = ∑ m ∈ Finset.Ioc a c, f m + ∑ m ∈ Finset.Ioc c b, f m := by
  have hunion : Finset.Ioc a b = Finset.Ioc a c ∪ Finset.Ioc c b := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ioc a c) (Finset.Ioc c b) := by
    rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Ioc] at h1 h2; omega
  rw [hunion, Finset.sum_union hdisj]

private lemma sum_Ioc_dyadic {α : Type*} [AddCommMonoid α] (N U V : ℕ) (_hU : 1 ≤ U) (hV : 1 ≤ V)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc V (N / U), f m =
      ∑ r ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ Finset.Ioc (blockLo V r) (blockHi N U V r), f m := by
  have hstep : ∀ R : ℕ,
      ∑ m ∈ Finset.Ioc V (min (V * 2 ^ R) (N / U)), f m =
        ∑ r ∈ Finset.range R, ∑ m ∈ Finset.Ioc (blockLo V r) (blockHi N U V r), f m := by
    intro R
    induction R with
    | zero =>
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty]
      have : Finset.Ioc V (min V (N / U)) = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
    | succ R ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases hle : V * 2 ^ R ≤ N / U
      · have hmin1 : min (V * 2 ^ R) (N / U) = V * 2 ^ R := Nat.min_eq_left hle
        rw [hmin1]
        have hVle : V ≤ V * 2 ^ R := Nat.le_mul_of_pos_right V (by positivity)
        have hRle : V * 2 ^ R ≤ min (V * 2 ^ (R + 1)) (N / U) :=
          le_min (Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ R))) hle
        exact sum_Ioc_split V (min (V * 2 ^ (R + 1)) (N / U)) (V * 2 ^ R) hVle hRle f
      · have hmin1 : min (V * 2 ^ R) (N / U) = N / U := Nat.min_eq_right (by omega)
        have hmin2 : min (V * 2 ^ (R + 1)) (N / U) = N / U := by
          apply Nat.min_eq_right
          have : V * 2 ^ R ≤ V * 2 ^ (R + 1) :=
            Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ R))
          omega
        have hempty : Finset.Ioc (blockLo V R) (blockHi N U V R) = ∅ := by
          unfold blockLo blockHi; rw [hmin2]; exact Finset.Ioc_eq_empty (by omega)
        rw [hmin1, hmin2, hempty, Finset.sum_empty, add_zero]
  have htop : N / U ≤ V * 2 ^ (Nat.log 2 N + 1) := by
    have h1 : N / U ≤ N := Nat.div_le_self N U
    have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
    have h3 : 2 ^ (Nat.log 2 N + 1) ≤ V * 2 ^ (Nat.log 2 N + 1) := Nat.le_mul_of_pos_left _ hV
    omega
  have hmin : min (V * 2 ^ (Nat.log 2 N + 1)) (N / U) = N / U := Nat.min_eq_right htop
  rw [← hmin]
  exact hstep (Nat.log 2 N + 1)

private lemma sum_Ioc_uniform {α : Type*} [AddCommMonoid α] (a b h L : ℕ) (hL : b ≤ a + L * h)
    (f : ℕ → α) :
    ∑ m ∈ Finset.Ioc a b, f m =
      ∑ j ∈ Finset.range L, ∑ m ∈ Finset.Ioc (a + j * h) (min (a + (j + 1) * h) b), f m := by
  have hgen : ∀ K : ℕ,
      ∑ m ∈ Finset.Ioc a (min (a + K * h) b), f m =
        ∑ j ∈ Finset.range K, ∑ m ∈ Finset.Ioc (a + j * h) (min (a + (j + 1) * h) b), f m := by
    intro K
    induction K with
    | zero =>
      simp only [zero_mul, add_zero, Finset.range_zero, Finset.sum_empty]
      have : Finset.Ioc a (min a b) = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
    | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases hle : a + K * h ≤ b
      · have hmin1 : min (a + K * h) b = a + K * h := Nat.min_eq_left hle
        rw [hmin1]
        have hstep_le : a + K * h ≤ min (a + (K + 1) * h) b :=
          le_min (by nlinarith) hle
        exact sum_Ioc_split a (min (a + (K + 1) * h) b) (a + K * h) (by omega) hstep_le f
      · have hmin1 : min (a + K * h) b = b := Nat.min_eq_right (by omega)
        have hmin2 : min (a + (K + 1) * h) b = b := Nat.min_eq_right (by nlinarith)
        have hempty : Finset.Ioc (a + K * h) (min (a + (K + 1) * h) b) = ∅ := by
          rw [hmin2]; exact Finset.Ioc_eq_empty (by omega)
        rw [hempty, hmin1, hmin2, Finset.sum_empty, add_zero]
  have hmin : min (a + L * h) b = b := Nat.min_eq_right hL
  conv_lhs => rw [← hmin]
  exact hgen L

private lemma blockHi_le_blockLo_add_count_mul_step (N U V : ℕ) (Δ : ℝ) (r : ℕ) :
    blockHi N U V r ≤ blockLo V r + blockCount N U V Δ r * blockStep V Δ r := by
  unfold blockCount
  set a := blockLo V r
  set b := blockHi N U V r
  set h := blockStep V Δ r
  have hh : 1 ≤ h := le_max_left 1 _
  by_cases hba : b ≤ a
  · omega
  · have hdiv := Nat.div_add_mod (b - a + h - 1) h
    have hmod : (b - a + h - 1) % h < h := Nat.mod_lt _ (by omega)
    have hmul : b - a ≤ (b - a + h - 1) / h * h := by
      have : h * ((b - a + h - 1) / h) + (b - a + h - 1) % h = b - a + h - 1 := hdiv
      have hcomm : h * ((b - a + h - 1) / h) = (b - a + h - 1) / h * h := mul_comm _ _
      omega
    omega

private def vaughanS3Rect {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x Δ : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), (Λ m : ℂ) * χ (m : ZMod q)) *
      (∑ k ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), (vaughanMollifier U k : ℂ) * χ (k : ZMod q))

private def vaughanS3Bdy {q : ℕ} (χ : DirichletCharacter ℂ q) (U V : ℕ) (x Δ : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
        (Λ m : ℂ) * χ (m : ZMod q) *
          ∑ k ∈ Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m),
            (vaughanMollifier U k : ℂ) * χ (k : ZMod q)

private lemma vaughanS3_eq_rect_add_bdy {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x Δ : ℝ) :
    vaughanS3 χ U V x = vaughanS3Rect χ U V x Δ + vaughanS3Bdy χ U V x Δ := by
  unfold vaughanS3 vaughanS3Rect vaughanS3Bdy
  rw [sum_Ioc_dyadic ⌊x⌋₊ U V hU hV]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_Ioc_uniform (blockLo V r) (blockHi ⌊x⌋₊ U V r) (blockStep V Δ r) (blockCount ⌊x⌋₊ U V Δ r)
    (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmb : m ≤ subHi ⌊x⌋₊ U V Δ r j := (Finset.mem_Ioc.mp hm).2
  have hm_pos : 0 < m := by
    have h1 := (Finset.mem_Ioc.mp hm).1
    have hlo : 1 ≤ blockLo V r := Nat.mul_pos hV (by positivity)
    unfold subLo at h1; omega
  have hdiv_le : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j ≤ ⌊x⌋₊ / m :=
    Nat.div_le_div_left hmb hm_pos
  rw [← mul_add]
  congr 1
  by_cases hUle : U ≤ ⌊x⌋₊ / m
  · have h1 : U ≤ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) := le_max_left _ _
    have h2 : max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) ≤ ⌊x⌋₊ / m := max_le hUle hdiv_le
    have hsplit := sum_Ioc_split U (⌊x⌋₊ / m) (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) h1 h2
      (fun k => (vaughanMollifier U k : ℂ) * χ (k : ZMod q))
    rw [hsplit]
    congr 1
    have hIoc_eq : Finset.Ioc U (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) =
        Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) := by
      ext k; simp only [Finset.mem_Ioc]; omega
    rw [hIoc_eq]
  · have he1 : Finset.Ioc U (⌊x⌋₊ / m) = ∅ := Finset.Ioc_eq_empty (by omega)
    have he2 : Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) = ∅ := Finset.Ioc_eq_empty (by omega)
    have he3 : Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m) = ∅ :=
      Finset.Ioc_eq_empty (by omega)
    rw [he1, he2, he3]; simp

private def bdyCoeff (U V : ℕ) (x Δ : ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
    ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
      ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
          (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
        Λ m * vaughanMollifier U (n / m)

private lemma bdy_prod_mem_annulus {U V r j m k : ℕ} {x Δ : ℝ}
    (_hV : 1 ≤ V) (hx : 1 ≤ x) (hΔ0 : 0 < Δ)
    (hm : m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j))
    (hk : k ∈ Finset.Ioc (max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)) (⌊x⌋₊ / m)) :
    m * k ∈ Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊ := by
  simp only [Finset.mem_Ioc] at hm hk ⊢
  set a := subLo V Δ r j
  set b := subHi ⌊x⌋₊ U V Δ r j
  set h := blockStep V Δ r
  have hmk_le : m * k ≤ ⌊x⌋₊ := by
    calc m * k ≤ m * (⌊x⌋₊ / m) := Nat.mul_le_mul_left m hk.2
      _ ≤ ⌊x⌋₊ := Nat.mul_div_le ⌊x⌋₊ m
  have hm_lt_b : m < b := by
    by_contra hge
    have hmb : m = b := by omega
    rw [hmb] at hk
    have : ⌊x⌋₊ / b < k := lt_of_le_of_lt (le_max_right _ _) hk.1
    omega
  have hb_le_ah : b ≤ a + h := by
    dsimp only [a, b, subLo, subHi]
    calc min (blockLo V r + (j + 1) * h) (blockHi ⌊x⌋₊ U V r)
        ≤ blockLo V r + (j + 1) * h := Nat.min_le_left _ _
      _ = blockLo V r + j * h + h := by ring
  have hh_ge2 : 2 ≤ h := by
    have ha_lt_m : a < m := hm.1
    omega
  have hh_eq : h = ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊ := by
    rcases le_total 1 ⌊Δ * ((blockLo V r : ℕ) : ℝ)⌋₊ with h1 | h1
    · exact max_eq_right h1
    · have hh1 : h = 1 := max_eq_left h1
      omega
  have hh_le_R : (h : ℝ) ≤ Δ * (a : ℝ) := by
    have h1 : (h : ℝ) ≤ Δ * ((blockLo V r : ℕ) : ℝ) := by
      rw [hh_eq]; exact Nat.floor_le (by positivity)
    have h2 : ((blockLo V r : ℕ) : ℝ) ≤ (a : ℝ) := by
      dsimp only [a, subLo]; exact_mod_cast Nat.le_add_right (blockLo V r) (j * h)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hΔ0.le)
  have hb_le_R : (b : ℝ) ≤ (1 + Δ) * (a : ℝ) := by
    have hbaR : (b : ℝ) ≤ (a : ℝ) + (h : ℝ) := by exact_mod_cast hb_le_ah
    linarith
  have hbk_gt_x : x < (b : ℝ) * (k : ℝ) := by
    have hk_gt : ⌊x⌋₊ / b < k := lt_of_le_of_lt (le_max_right _ _) hk.1
    have hbk_nat : ⌊x⌋₊ + 1 ≤ b * k := by
      have hdiv := Nat.div_add_mod ⌊x⌋₊ b
      have hb_pos : 0 < b := by omega
      have hmod : ⌊x⌋₊ % b < b := Nat.mod_lt _ hb_pos
      have h1 : ⌊x⌋₊ < b * (⌊x⌋₊ / b + 1) := by nlinarith
      have h2 : b * (⌊x⌋₊ / b + 1) ≤ b * k := Nat.mul_le_mul_left b hk_gt
      omega
    have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hbkR : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((b * k : ℕ) : ℝ) := by exact_mod_cast hbk_nat
    push_cast at hbkR
    linarith
  have hmk_gt : x / (1 + Δ) < ((m * k : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 + Δ)]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    have ham : (a : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
    have h1 : (b : ℝ) * (k : ℝ) ≤ (1 + Δ) * (a : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hb_le_R hk_pos.le
    have h2 : (1 + Δ) * (a : ℝ) * (k : ℝ) < (1 + Δ) * (m : ℝ) * (k : ℝ) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left ham (by linarith)) hk_pos
    have h3 : (1 + Δ) * (m : ℝ) * (k : ℝ) = ((m * k : ℕ) : ℝ) * (1 + Δ) := by push_cast; ring
    linarith
  have hfl_le : (⌊x / (1 + Δ)⌋₊ : ℝ) ≤ x / (1 + Δ) := Nat.floor_le (by positivity)
  have hlt_nat : ⌊x / (1 + Δ)⌋₊ < m * k := by
    exact_mod_cast lt_of_le_of_lt hfl_le hmk_gt
  exact ⟨hlt_nat, hmk_le⟩

private lemma vaughanS3Bdy_eq_annulus_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    {U V : ℕ} (hV : 1 ≤ V) {x Δ : ℝ} (hx : 1 ≤ x) (hΔ0 : 0 < Δ) :
    vaughanS3Bdy χ U V x Δ =
      ∑ n ∈ Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊, (bdyCoeff U V x Δ n : ℂ) * χ (n : ZMod q) := by
  set I := Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
  unfold vaughanS3Bdy bdyCoeff
  
  have hRHS :
      ∑ n ∈ I,
          ((∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
            ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
              ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                  (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
                Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) * χ (n : ZMod q) =
        ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ n ∈ I,
              ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                  (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
                ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
    have h1 : ∀ n ∈ I,
        ((∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
              Λ m * vaughanMollifier U (n / m) : ℝ) : ℂ) * χ (n : ZMod q) =
        ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
                (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
              ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
      intro n _
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
  rw [hRHS]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
  
  set S_m := Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)
  set K_lo := max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)
  have hswap :
      ∑ n ∈ I, ∑ m ∈ S_m.filter (fun m => m ∣ n ∧ K_lo < n / m),
          ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) =
        ∑ m ∈ S_m, ∑ n ∈ I.filter (fun n => m ∣ n ∧ K_lo < n / m),
          ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) := by
    have hL : ∀ n ∈ I,
        ∑ m ∈ S_m.filter (fun m => m ∣ n ∧ K_lo < n / m),
            ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) =
          ∑ m ∈ S_m, if m ∣ n ∧ K_lo < n / m then
            ((Λ m : ℂ) * (vaughanMollifier U (n / m) : ℂ)) * χ (n : ZMod q) else 0 :=
      fun _ _ => Finset.sum_filter _ _
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => (Finset.sum_filter _ _).symm
  rw [hswap]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_pos : 0 < m := by
    have h1 := (Finset.mem_Ioc.mp hm).1
    have hlo : 1 ≤ blockLo V r := Nat.mul_pos hV (by positivity)
    unfold subLo at h1; omega
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, I] at hn ⊢
    exact ⟨hn.2.2, (Nat.le_div_iff_mul_le hm_pos).mpr (by rw [Nat.div_mul_cancel hn.2.1]; exact hn.1.2)⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₁).2.1,
        ← Nat.mul_div_cancel' (Finset.mem_filter.mp hn₂).2.1, heq]
  · intro k hk
    refine ⟨m * k, ?_, Nat.mul_div_cancel_left k hm_pos⟩
    have hmemI : m * k ∈ I := bdy_prod_mem_annulus hV hx hΔ0 hm hk
    refine Finset.mem_filter.mpr ⟨hmemI, dvd_mul_right m k, ?_⟩
    rw [Nat.mul_div_cancel_left k hm_pos]
    exact (Finset.mem_Ioc.mp hk).1
  · intro n hn
    have hmn : m ∣ n := (Finset.mem_filter.mp hn).2.1
    have hmul : (n : ZMod q) = (m : ZMod q) * ((n / m : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]
    rw [hmul, map_mul]; ring

private lemma abs_bdyCoeff_le {U V n : ℕ} {x Δ : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 1 ≤ x)
    (hn1 : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    |bdyCoeff U V x Δ n| ≤ (n.divisors.card : ℝ) * Real.log x := by
  unfold bdyCoeff
  have hinner :
      |∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ (Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j)).filter
              (fun m => m ∣ n ∧ max U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) < n / m),
            Λ m * vaughanMollifier U (n / m)| ≤
      ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
            if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun m _ => ?_
    split_ifs with h1 h2
    · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      refine (abs_vaughanMollifier_le_divisors U (n / m)).trans ?_
      have hdvd : n / m ∣ n := Nat.div_dvd_of_dvd h1.1
      have hsub : (n / m).divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd (by omega) hdvd
      exact_mod_cast Finset.card_le_card hsub
    · exact absurd h1.1 h2
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    · exact le_rfl
  
  have hcollapse :
      ∑ r ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1),
        ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
          ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
            (if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0) =
        ∑ m ∈ Finset.Ioc V (⌊x⌋₊ / U),
          if m ∣ n then Λ m * (n.divisors.card : ℝ) else 0 := by
    rw [sum_Ioc_dyadic ⌊x⌋₊ U V hU hV]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact (sum_Ioc_uniform (blockLo V r) (blockHi ⌊x⌋₊ U V r) (blockStep V Δ r) (blockCount ⌊x⌋₊ U V Δ r)
      (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r) _).symm
  refine hinner.trans ?_
  rw [hcollapse, ← Finset.sum_filter]
  have hsub : (Finset.Ioc V (⌊x⌋₊ / U)).filter (fun m => m ∣ n) ⊆ n.divisors := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, by omega⟩
  calc ∑ m ∈ (Finset.Ioc V (⌊x⌋₊ / U)).filter (fun m => m ∣ n), Λ m * (n.divisors.card : ℝ)
      ≤ ∑ m ∈ n.divisors, Λ m * (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ = (∑ m ∈ n.divisors, Λ m) * (n.divisors.card : ℝ) := (Finset.sum_mul _ _ _).symm
    _ = Real.log (n : ℝ) * (n.divisors.card : ℝ) := by rw [ArithmeticFunction.vonMangoldt_sum]
    _ ≤ Real.log x * (n.divisors.card : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact Real.log_le_log (Nat.cast_pos.mpr hn1)
          ((by exact_mod_cast hnx : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith)))
    _ = (n.divisors.card : ℝ) * Real.log x := mul_comm _ _

private lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsq : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have : 0 ≤ 2 * Real.sqrt a * Real.sqrt b := by positivity
    linarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

open Classical in

private lemma sum_vaughanS3Bdy_le {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ ≤
      2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) *
        (1 + Real.log x) ^ 3 := by
  have hx1 : 1 ≤ x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx1)
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  set I := Finset.Ioc ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
  
  let S : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range (2 * D)).sigma fun k =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun p => ((p.1 + 1 : ℕ) : ℝ) / (Nat.totient (p.1 + 1) : ℝ)
  have hLHS :
      ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖vaughanS3Bdy χ U V x Δ‖ =
        ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    dsimp only [w]
    rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]
  have hCS :
      ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) ≤
        Real.sqrt (∑ p ∈ S, w p) *
          Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun p => Real.sqrt (w p)) (fun p => Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖)
    have hW : ∑ p ∈ S, (Real.sqrt (w p)) ^ 2 = ∑ p ∈ S, w p :=
      Finset.sum_congr rfl fun p _ => Real.sq_sqrt (by dsimp only [w]; positivity)
    have hV2 : ∑ p ∈ S, (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖) ^ 2 =
        ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow, Real.sq_sqrt (by dsimp only [w]; positivity)]
    rw [hW, hV2] at h1
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun p _ => by dsimp only [w]; positivity)]
    exact Real.le_sqrt_of_sq_le h1
  have hW_le : ∑ p ∈ S, w p ≤ (2 * (D : ℝ)) ^ 2 := by
    have hEq : ∑ p ∈ S, w p =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hEq]
    simpa [Nat.cast_mul] using sum_prim_weight_le (2 * D)
  have hLS :
      ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 ≤
        (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
          ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 := by
    have hEq : ∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2 =
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖∑ n ∈ I, (bdyCoeff U V x Δ n : ℂ) * χ (n : ZMod (k + 1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [vaughanS3Bdy_eq_annulus_sum χ hV hx1 hΔ0]
    rw [hEq]
    exact multiplicative_large_sieve_Ioc_interval (2 * D) ⌊x / (1 + Δ)⌋₊ ⌊x⌋₊
      (fun n => (bdyCoeff U V x Δ n : ℂ))
  
  have hlen : ((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) ≤ Δ * x + 1 := by
    have hle_fl : ⌊x / (1 + Δ)⌋₊ ≤ ⌊x⌋₊ :=
      Nat.floor_mono (div_le_self (by linarith) (by linarith))
    rw [Nat.cast_sub hle_fl]
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h2 : x / (1 + Δ) - 1 < (⌊x / (1 + Δ)⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (x / (1 + Δ))]
    have h3 : x - x / (1 + Δ) ≤ Δ * x := by
      have hEq : x - x / (1 + Δ) = (Δ / (1 + Δ)) * x := by field_simp [(by linarith : 1 + Δ ≠ 0)]; ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_right (div_le_self hΔ0.le (by linarith)) (by linarith)
    linarith
  
  have hL2 : ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 ≤ x * (1 + Real.log x) ^ 5 := by
    have hI_sub : I ⊆ Finset.Icc 1 ⌊x⌋₊ := by
      intro n hn; simp only [I, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
    calc ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hI_sub fun _ _ _ => sq_nonneg _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.divisors.card : ℝ) * Real.log x) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_bdyCoeff_le hU hV hx1 (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2) 2
      _ = (Real.log x) ^ 2 * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
      _ ≤ (Real.log x) ^ 2 * ((⌊x⌋₊ : ℝ) * (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 3) :=
          mul_le_mul_of_nonneg_left (Stage10ZeroDensity.sum_divisors_card_sq_le hN1) (sq_nonneg _)
      _ ≤ (1 + Real.log x) ^ 2 * (x * (1 + Real.log x) ^ 3) := by
          have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
          have hlog_fl : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
            Real.log_le_log (Nat.cast_pos.mpr hN1) hfl_le
          gcongr
          linarith
      _ = x * (1 + Real.log x) ^ 5 := by ring
  
  have hsqrtW : Real.sqrt (∑ p ∈ S, w p) ≤ 2 * (D : ℝ) :=
    (Real.sqrt_le_sqrt hW_le).trans_eq (Real.sqrt_sq (by positivity))
  have hfac1 : Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2)) ≤
      Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ) := by
    have hbound : (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) ≤
        Δ * x + 1 + 16 * (D : ℝ) ^ 2 := by
      have hcast : 3 * ((2 * D : ℕ) : ℝ) ^ 2 = 12 * (D : ℝ) ^ 2 := by push_cast; ring
      nlinarith
    calc Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2))
        ≤ Real.sqrt (Δ * x + 1 + 16 * (D : ℝ) ^ 2) := Real.sqrt_le_sqrt hbound
      _ ≤ Real.sqrt (Δ * x + 1) + Real.sqrt (16 * (D : ℝ) ^ 2) :=
          sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
      _ ≤ (Real.sqrt (Δ * x) + Real.sqrt 1) + Real.sqrt ((4 * (D : ℝ)) ^ 2) := by
          have h1 := sqrt_add_le_sqrt_add_sqrt (by positivity : 0 ≤ Δ * x) zero_le_one
          have h2 : 16 * (D : ℝ) ^ 2 = (4 * (D : ℝ)) ^ 2 := by ring
          rw [h2]; linarith
      _ = Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ) := by
          rw [Real.sqrt_mul hΔ0.le, Real.sqrt_one, Real.sqrt_sq (by positivity)]
  have hfac2 : Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) ≤
      Real.sqrt x * (1 + Real.log x) ^ 3 := by
    have h5le6 : (1 + Real.log x) ^ 5 ≤ (1 + Real.log x) ^ 6 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hsq6 : Real.sqrt ((1 + Real.log x) ^ 6) = (1 + Real.log x) ^ 3 := by
      rw [show (1 + Real.log x) ^ 6 = ((1 + Real.log x) ^ 3) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    calc Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2)
        ≤ Real.sqrt (x * (1 + Real.log x) ^ 5) := Real.sqrt_le_sqrt hL2
      _ ≤ Real.sqrt (x * (1 + Real.log x) ^ 6) := Real.sqrt_le_sqrt (by gcongr)
      _ = Real.sqrt x * (1 + Real.log x) ^ 3 := by rw [Real.sqrt_mul (by linarith), hsq6]
  have hprod_sqrt :
      Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) ≤
        (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by
    calc Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2)
        ≤ Real.sqrt ((((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            ∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) := Real.sqrt_le_sqrt hLS
      _ = Real.sqrt (((⌊x⌋₊ - ⌊x / (1 + Δ)⌋₊ : ℕ) : ℝ) + 3 * ((2 * D : ℕ) : ℝ) ^ 2) *
            Real.sqrt (∑ n ∈ I, ‖(bdyCoeff U V x Δ n : ℂ)‖ ^ 2) := Real.sqrt_mul (by positivity) _
      _ ≤ (Real.sqrt Δ * Real.sqrt x + 1 + 4 * (D : ℝ)) * (Real.sqrt x * (1 + Real.log x) ^ 3) :=
          mul_le_mul hfac1 hfac2 (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt Δ * (Real.sqrt x * Real.sqrt x) + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) *
            (1 + Real.log x) ^ 3 := by ring
      _ = (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by
          rw [Real.mul_self_sqrt (by linarith)]
  rw [hLHS]
  calc ∑ p ∈ S, Real.sqrt (w p) * (Real.sqrt (w p) * ‖vaughanS3Bdy p.2 U V x Δ‖)
      ≤ Real.sqrt (∑ p ∈ S, w p) * Real.sqrt (∑ p ∈ S, w p * ‖vaughanS3Bdy p.2 U V x Δ‖ ^ 2) := hCS
    _ ≤ (2 * (D : ℝ)) * ((Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3) :=
        mul_le_mul hsqrtW hprod_sqrt (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 := by ring

private lemma blockCount_le_three_div {N U V r : ℕ} {Δ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (blockCount N U V Δ r : ℝ) ≤ 3 / Δ := by
  unfold blockCount
  set M := blockLo V r
  set M' := blockHi N U V r
  set h := blockStep V Δ r
  have hh1 : 1 ≤ h := le_max_left 1 _
  have hdiff_le : M' - M ≤ M := by
    dsimp only [M, M', blockLo, blockHi]
    have h1 : min (V * 2 ^ (r + 1)) (N / U) ≤ V * 2 ^ (r + 1) := Nat.min_le_left _ _
    have h2 : V * 2 ^ (r + 1) = V * 2 ^ r + V * 2 ^ r := by rw [pow_succ]; ring
    omega
  by_cases hh_eq1 : h = 1
  · have hfl_le1 : ⌊Δ * (M : ℝ)⌋₊ ≤ 1 := by
      have : ⌊Δ * (M : ℝ)⌋₊ ≤ h := le_max_right 1 _
      omega
    have hΔM_lt2 : Δ * (M : ℝ) < 2 := by
      have := Nat.lt_floor_add_one (Δ * (M : ℝ))
      have h1 : (⌊Δ * (M : ℝ)⌋₊ : ℝ) ≤ 1 := by exact_mod_cast hfl_le1
      linarith
    have hM_le : (M : ℝ) ≤ 2 / Δ := (le_div_iff₀ hΔ0).mpr (by linarith)
    have hnat : (M' - M + h - 1) / h = M' - M := by rw [hh_eq1]; simp
    rw [hnat]
    calc ((M' - M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hdiff_le
      _ ≤ 2 / Δ := hM_le
      _ ≤ 3 / Δ := div_le_div_of_nonneg_right (by norm_num) hΔ0.le
  · have hh_ge2 : 2 ≤ h := by omega
    have hh_eq : h = ⌊Δ * (M : ℝ)⌋₊ := by
      rcases le_total 1 ⌊Δ * (M : ℝ)⌋₊ with h1 | h1
      · exact max_eq_right h1
      · have hh1' : h = 1 := max_eq_left h1; omega
    have h2h_gt : Δ * (M : ℝ) < 2 * (h : ℝ) := by
      have h1 := Nat.lt_floor_add_one (Δ * (M : ℝ))
      rw [← hh_eq] at h1
      have h2 : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge2
      linarith
    have hdiv_le : (((M' - M + h - 1) / h : ℕ) : ℝ) ≤ (M : ℝ) / (h : ℝ) + 1 := by
      have hnum : M' - M + h - 1 ≤ M + h :=
        (Nat.sub_le (M' - M + h) 1).trans (Nat.add_le_add_right hdiff_le h)
      have hle1 : ((M' - M + h - 1) / h : ℕ) ≤ (M + h) / h := Nat.div_le_div_right hnum
      have hle2 : ((M + h) / h : ℕ) = M / h + 1 := Nat.add_div_right M (by omega)
      have h1 : (((M' - M + h - 1) / h : ℕ) : ℝ) ≤ ((M / h : ℕ) : ℝ) + 1 := by
        exact_mod_cast (hle1.trans_eq hle2)
      have h2 : ((M / h : ℕ) : ℝ) ≤ (M : ℝ) / (h : ℝ) := Nat.cast_div_le
      linarith
    have hMh : (M : ℝ) / (h : ℝ) ≤ 2 / Δ := by
      rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hΔ0]
      linarith
    have h1le : (1 : ℝ) ≤ 1 / Δ := (one_le_div hΔ0).mpr hΔ1.le
    have hadd : 2 / Δ + 1 / Δ = 3 / Δ := by ring
    linarith

open Classical in

private lemma sum_vaughanS3Rect_le {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.range (2 * D),
        (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ ≤
      120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hU_pos : (0 : ℝ) < (U : ℝ) := Nat.cast_pos.mpr hU
  have hV_pos : (0 : ℝ) < (V : ℝ) := Nat.cast_pos.mpr hV
  set R : ℕ := Nat.log 2 ⌊x⌋₊ + 1
  
  have htri :
      ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖vaughanS3Rect χ U V x Δ‖ ≤
        ∑ r ∈ Finset.range R,
          ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                      (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                   (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                      (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := by
    have hpt : ∀ k ∈ Finset.range (2 * D), ∀ χ : DirichletCharacter ℂ (k + 1),
        ‖vaughanS3Rect χ U V x Δ‖ ≤
          ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
            ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
             (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := fun _ _ χ => by
      unfold vaughanS3Rect
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    calc _ ≤ ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                    ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                        (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                     (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                        (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun χ _ => hpt k hk χ) (by positivity)
      _ = _ := by
            have h1 :
                ∑ k ∈ Finset.range (2 * D),
                    (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                        ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                          ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                              (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                           (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                              (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ =
                ∑ k ∈ Finset.range (2 * D),
                  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
                    (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                        ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                            (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                         (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                            (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_comm, Finset.mul_sum]
            rw [h1, Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => Finset.sum_comm
  
  have hblock : ∀ r ∈ Finset.range R,
      ∑ j ∈ Finset.range (blockCount ⌊x⌋₊ U V Δ r),
        ∑ k ∈ Finset.range (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                  (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
               (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                  (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ ≤
      28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3 := by
    intro r _
    set M := blockLo V r
    set M' := blockHi ⌊x⌋₊ U V r
    set h := blockStep V Δ r
    set L := blockCount ⌊x⌋₊ U V Δ r
    by_cases hM_ge : ⌊x⌋₊ / U ≤ M
    · have hM'_le : M' ≤ M := (Nat.min_le_right _ _).trans hM_ge
      have hL0 : L = 0 := by
        dsimp only [L, blockCount]
        have hsub : M' - M = 0 := Nat.sub_eq_zero_of_le hM'_le
        rw [hsub, zero_add]
        exact Nat.div_eq_of_lt (by have : 1 ≤ h := le_max_left 1 _; omega)
      rw [hL0, Finset.range_zero, Finset.sum_empty]
      positivity
    · push Not at hM_ge
      have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hV (by positivity))
      have hVM : (V : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right V (show 0 < 2 ^ r by positivity)
      have hMU : (M : ℝ) ≤ x / (U : ℝ) := by
        rw [le_div_iff₀ hU_pos]
        have h1 : M * U ≤ ⌊x⌋₊ := by
          have := (Nat.le_div_iff_mul_le hU).mp hM_ge.le
          exact this
        exact (by exact_mod_cast h1 : (M : ℝ) * (U : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
      have hNM_pos : 1 ≤ ⌊x⌋₊ / M := by
        have hM_le_N : M ≤ ⌊x⌋₊ := hM_ge.le.trans (Nat.div_le_self ⌊x⌋₊ U)
        exact Nat.div_pos hM_le_N (Nat.mul_pos hV (by positivity))
      have hstep_le : (h : ℝ) ≤ Δ * (M : ℝ) + 1 := by
        dsimp only [h, blockStep]
        rcases le_total 1 ⌊Δ * (M : ℝ)⌋₊ with h1 | h1
        · rw [max_eq_right h1]; linarith [Nat.floor_le (by positivity : 0 ≤ Δ * (M : ℝ))]
        · rw [max_eq_left h1]; norm_num; positivity
      
      have hper_j : ∀ j ∈ Finset.range L,
          ∑ k ∈ Finset.range (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                    (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                 (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                    (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖ ≤
          Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
            Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
            Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) *
            Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) := by
        intro j _
        have hbls := bilinear_multiplicative_large_sieve (2 * D)
          (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j) U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j)
          (fun m => (Λ m : ℂ)) (fun n => (vaughanMollifier U n : ℂ))
        have hlen_m : ((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) ≤ Δ * (M : ℝ) + 1 := by
          have h1 : subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j ≤ h := by
            dsimp only [subHi, subLo]
            have hle1 : min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi ⌊x⌋₊ U V r) ≤
                blockLo V r + (j + 1) * blockStep V Δ r := Nat.min_le_left _ _
            have hmul : blockLo V r + (j + 1) * blockStep V Δ r =
                blockLo V r + j * blockStep V Δ r + blockStep V Δ r := by ring
            have h2 : min (blockLo V r + (j + 1) * blockStep V Δ r) (blockHi ⌊x⌋₊ U V r) -
                (blockLo V r + j * blockStep V Δ r) ≤ blockStep V Δ r := by omega
            exact h2
          exact (by exact_mod_cast h1 : ((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) ≤ (h : ℝ)).trans hstep_le
        have hM_le_b : M ≤ subHi ⌊x⌋₊ U V Δ r j := by
          unfold subHi
          apply le_min
          · exact Nat.le_add_right M _
          · unfold blockHi
            apply le_min
            · exact Nat.mul_le_mul_left V (Nat.pow_le_pow_right (by omega) (Nat.le_succ r))
            · exact hM_ge.le
        have hdiv_le : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j ≤ ⌊x⌋₊ / M :=
          Nat.div_le_div_left hM_le_b (Nat.mul_pos hV (by positivity))
        have hNM_le_R : ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ x / (M : ℝ) := by
          calc ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / (M : ℝ) := Nat.cast_div_le
            _ ≤ x / (M : ℝ) := div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) hM_pos.le
        have hlen_n : ((⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U : ℕ) : ℝ) ≤ x / (M : ℝ) := by
          have h1 : ⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U ≤ ⌊x⌋₊ / M := (Nat.sub_le _ _).trans hdiv_le
          exact (by exact_mod_cast h1 : _ ≤ ((⌊x⌋₊ / M : ℕ) : ℝ)).trans hNM_le_R
        have hL2_m :
            ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), ‖(Λ m : ℂ)‖ ^ 2 =
              ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2 :=
          Finset.sum_congr rfl fun m _ => by
            rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hL2_n :
            ∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), ‖(vaughanMollifier U n : ℂ)‖ ^ 2 ≤
              (x / (M : ℝ)) * (1 + Real.log x) ^ 3 := by
          have hsub : Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j) ⊆ Finset.Icc 1 (⌊x⌋₊ / M) := by
            intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
          calc ∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j), ‖(vaughanMollifier U n : ℂ)‖ ^ 2
              ≤ ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / M), ‖(vaughanMollifier U n : ℂ)‖ ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
            _ ≤ ∑ n ∈ Finset.Icc 1 (⌊x⌋₊ / M), (n.divisors.card : ℝ) ^ 2 := by
                refine Finset.sum_le_sum fun n _ => ?_
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (abs_vaughanMollifier_le_divisors U n) 2
            _ ≤ ((⌊x⌋₊ / M : ℕ) : ℝ) * (1 + Real.log ((⌊x⌋₊ / M : ℕ) : ℝ)) ^ 3 :=
                Stage10ZeroDensity.sum_divisors_card_sq_le hNM_pos
            _ ≤ (x / (M : ℝ)) * (1 + Real.log x) ^ 3 := by
                have hlog_le : Real.log ((⌊x⌋₊ / M : ℕ) : ℝ) ≤ Real.log x := by
                  refine Real.log_le_log (Nat.cast_pos.mpr hNM_pos) ?_
                  exact (by exact_mod_cast Nat.div_le_self ⌊x⌋₊ M : _ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
                have hnn : 0 ≤ 1 + Real.log ((⌊x⌋₊ / M : ℕ) : ℝ) := by
                  have := Real.log_natCast_nonneg (⌊x⌋₊ / M); linarith
                gcongr
        have h3Q2 : 3 * ((2 * D : ℕ) : ℝ) ^ 2 = 12 * (D : ℝ) ^ 2 := by push_cast; ring
        refine hbls.trans ?_
        rw [h3Q2, hL2_m]
        have h1 : Real.sqrt (((subHi ⌊x⌋₊ U V Δ r j - subLo V Δ r j : ℕ) : ℝ) + 12 * (D : ℝ) ^ 2) ≤
            Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have h2 : Real.sqrt (((⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j - U : ℕ) : ℝ) + 12 * (D : ℝ) ^ 2) ≤
            Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have h3 := Real.sqrt_le_sqrt hL2_n
        have hmul12 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have hmul123 := mul_le_mul hmul12 h3 (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        have hmul1234 := mul_le_mul_of_nonneg_right hmul123
          (Real.sqrt_nonneg (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2))
        linarith
      
      have hsum_j :
          ∑ j ∈ Finset.range L,
            Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) ≤
          Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x) := by
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L)
          (fun _ => (1 : ℝ))
          (fun j => Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2))
        simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hCS
        have hsq_sum :
            ∑ j ∈ Finset.range L,
              (Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)) ^ 2 =
            ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 := by
          have h1 : ∀ j ∈ Finset.range L,
              (Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)) ^ 2 =
                ∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2 :=
            fun j _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [Finset.sum_congr rfl h1]
          exact (sum_Ioc_uniform M M' h L (blockHi_le_blockLo_add_count_mul_step ⌊x⌋₊ U V Δ r) _).symm
        rw [hsq_sum] at hCS
        have hM_L2 : ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 ≤ (M : ℝ) * (Real.log x) ^ 2 := by
          calc ∑ m ∈ Finset.Ioc M M', Λ m ^ 2
              ≤ ∑ _m ∈ Finset.Ioc M M', (Real.log x) ^ 2 := by
                refine Finset.sum_le_sum fun m hm => ?_
                have hm1 : 1 ≤ m := by
                  have := (Finset.mem_Ioc.mp hm).1
                  have : 1 ≤ M := Nat.mul_pos hV (by positivity); omega
                have hmx : (m : ℝ) ≤ x := by
                  have h1 : m ≤ ⌊x⌋₊ := ((Finset.mem_Ioc.mp hm).2.trans (Nat.min_le_right _ _)).trans
                    (Nat.div_le_self ⌊x⌋₊ U)
                  exact (by exact_mod_cast h1 : (m : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
                exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
                  (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hm1) hmx)) 2
            _ = ((Finset.Ioc M M').card : ℝ) * (Real.log x) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (M : ℝ) * (Real.log x) ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                rw [Nat.card_Ioc]
                have hle : M' - M ≤ M := by
                  dsimp only [M, M', blockLo, blockHi]
                  have h1 : min (V * 2 ^ (r + 1)) (⌊x⌋₊ / U) ≤ V * 2 ^ (r + 1) := Nat.min_le_left _ _
                  have h2 : V * 2 ^ (r + 1) = V * 2 ^ r + V * 2 ^ r := by rw [pow_succ]; ring
                  omega
                exact_mod_cast hle
        have hprod : (L : ℝ) * ∑ m ∈ Finset.Ioc M M', Λ m ^ 2 ≤ (3 / Δ) * ((M : ℝ) * (Real.log x) ^ 2) :=
          mul_le_mul (blockCount_le_three_div hΔ0 hΔ1) hM_L2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        calc ∑ j ∈ Finset.range L,
              Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2)
            ≤ Real.sqrt ((3 / Δ) * ((M : ℝ) * (Real.log x) ^ 2)) :=
              Real.le_sqrt_of_sq_le (hCS.trans hprod)
          _ = Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x) := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hM_pos.le, Real.sqrt_sq hlogx_nn]
      
      have hA_fac : Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) ≤
          2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ := by
        have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        have hEq : (3 / Δ) * (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) =
            3 * (M : ℝ) + (3 + 36 * (D : ℝ) ^ 2) / Δ := by field_simp [hΔ0.ne']; ring
        have hle : 3 * (M : ℝ) + (3 + 36 * (D : ℝ) ^ 2) / Δ ≤
            4 * (M : ℝ) + 49 * (D : ℝ) ^ 2 / Δ := by
          have h1 : 3 + 36 * (D : ℝ) ^ 2 ≤ 49 * (D : ℝ) ^ 2 := by nlinarith
          have h2 : (3 + 36 * (D : ℝ) ^ 2) / Δ ≤ 49 * (D : ℝ) ^ 2 / Δ :=
            div_le_div_of_nonneg_right h1 hΔ0.le
          linarith
        calc Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)
            = Real.sqrt ((3 / Δ) * (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)) :=
              (Real.sqrt_mul (by positivity) _).symm
          _ ≤ Real.sqrt (4 * (M : ℝ) + 49 * (D : ℝ) ^ 2 / Δ) := by
              rw [hEq]; exact Real.sqrt_le_sqrt hle
          _ ≤ Real.sqrt (4 * (M : ℝ)) + Real.sqrt (49 * (D : ℝ) ^ 2 / Δ) :=
              sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
          _ = 2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
                  show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
                  Real.sqrt_div (by positivity),
                  show 49 * (D : ℝ) ^ 2 = (7 * (D : ℝ)) ^ 2 by ring,
                  Real.sqrt_sq (by positivity)]
      have hB_fac : Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) ≤
          Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ) := by
        calc Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2)
            ≤ Real.sqrt (x / (M : ℝ) + 16 * (D : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ ≤ Real.sqrt (x / (M : ℝ)) + Real.sqrt (16 * (D : ℝ) ^ 2) :=
              sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
          _ = Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ) := by
              rw [show 16 * (D : ℝ) ^ 2 = (4 * (D : ℝ)) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have hC_fac : Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) ≤
          Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2 := by
        have h34 : (1 + Real.log x) ^ 3 ≤ (1 + Real.log x) ^ 4 :=
          pow_le_pow_right₀ (by linarith) (by omega)
        calc Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)
            ≤ Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 4) := Real.sqrt_le_sqrt (by gcongr)
          _ = Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2 := by
              rw [Real.sqrt_mul (by positivity),
                  show (1 + Real.log x) ^ 4 = ((1 + Real.log x) ^ 2) ^ 2 by ring,
                  Real.sqrt_sq (by positivity)]
      have hlog_prod : Real.log x * (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 3 := by
        have : Real.log x ≤ 1 + Real.log x := by linarith
        nlinarith [sq_nonneg (1 + Real.log x)]
      
      have hcross :
          (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
            ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ))) ≤
          28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
            (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
            (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) := by
        have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM_pos.le
        have hsqxM : Real.sqrt (x / (M : ℝ)) * Real.sqrt (x / (M : ℝ)) = x / (M : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hsq_prod : Real.sqrt (M : ℝ) * Real.sqrt (x / (M : ℝ)) = Real.sqrt x := by
          rw [← Real.sqrt_mul hM_pos.le, mul_div_cancel₀ x hM_pos.ne']
        have hterm1 : (M : ℝ) * (x / (M : ℝ)) = x := mul_div_cancel₀ x hM_pos.ne'
        have hterm2 : (M : ℝ) * Real.sqrt (x / (M : ℝ)) ≤ x / Real.sqrt (U : ℝ) := by
          have h1 : (M : ℝ) * Real.sqrt (x / (M : ℝ)) = Real.sqrt (M : ℝ) * Real.sqrt x := by
            rw [← hsq_prod, ← mul_assoc, hsqM]
          rw [h1]
          have h2 : Real.sqrt (M : ℝ) ≤ Real.sqrt x / Real.sqrt (U : ℝ) := by
            rw [← Real.sqrt_div (by linarith)]
            exact Real.sqrt_le_sqrt hMU
          calc Real.sqrt (M : ℝ) * Real.sqrt x
              ≤ (Real.sqrt x / Real.sqrt (U : ℝ)) * Real.sqrt x :=
                mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
            _ = (Real.sqrt x * Real.sqrt x) / Real.sqrt (U : ℝ) := by ring
            _ = x / Real.sqrt (U : ℝ) := by rw [Real.mul_self_sqrt (by linarith)]
        have hterm3 : (Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ)) ≤
            x / Real.sqrt (Δ * (V : ℝ)) := by
          have hEq : (Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ)) =
              x / (Real.sqrt Δ * Real.sqrt (M : ℝ)) := by
            have hne : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hM_pos).ne'
            have hneΔ : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
            field_simp [hne, hneΔ, hM_pos.ne']
            exact Real.sq_sqrt hM_pos.le
          rw [hEq, Real.sqrt_mul hΔ0.le]
          exact div_le_div_of_nonneg_left (by linarith)
            (mul_pos (Real.sqrt_pos.mpr hΔ0) (Real.sqrt_pos.mpr hV_pos))
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVM) (Real.sqrt_nonneg _))
        have hexpand :
            (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ))) =
            2 * ((M : ℝ) * (x / (M : ℝ))) +
            8 * (D : ℝ) * ((M : ℝ) * Real.sqrt (x / (M : ℝ))) +
            7 * (D : ℝ) * ((Real.sqrt (M : ℝ) / Real.sqrt Δ) * (x / (M : ℝ))) +
            28 * (D : ℝ) ^ 2 * ((Real.sqrt (M : ℝ) * Real.sqrt (x / (M : ℝ))) / Real.sqrt Δ) := by
          have h1 : (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) =
              2 * (M : ℝ) + 7 * (D : ℝ) * (Real.sqrt (M : ℝ) / Real.sqrt Δ) := by
            rw [add_mul, mul_assoc, hsqM]; ring
          have h2 : (Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ)) =
              x / (M : ℝ) + 4 * (D : ℝ) * Real.sqrt (x / (M : ℝ)) := by
            rw [add_mul, hsqxM]
          rw [h1, h2]; ring
        rw [hexpand, hterm1, hsq_prod]
        have h2' := mul_le_mul_of_nonneg_left hterm2 (show 0 ≤ 8 * (D : ℝ) by positivity)
        have h3' := mul_le_mul_of_nonneg_left hterm3 (show 0 ≤ 7 * (D : ℝ) by positivity)
        have hx_nn : 0 ≤ x := by linarith
        have hU_nn : 0 ≤ (D : ℝ) * x / Real.sqrt (U : ℝ) := by positivity
        have hV_nn : 0 ≤ (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) := by positivity
        have hD_nn : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ := by positivity
        have h2'' : 8 * (D : ℝ) * (x / Real.sqrt (U : ℝ)) = 8 * ((D : ℝ) * x / Real.sqrt (U : ℝ)) := by ring
        have h3'' : 7 * (D : ℝ) * (x / Real.sqrt (Δ * (V : ℝ))) = 7 * ((D : ℝ) * x / Real.sqrt (Δ * (V : ℝ))) := by ring
        have h4'' : 28 * (D : ℝ) ^ 2 * (Real.sqrt x / Real.sqrt Δ) = 28 * ((D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) := by ring
        linarith
      calc ∑ j ∈ Finset.range L,
            ∑ k ∈ Finset.range (2 * D),
              (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                  ‖(∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j),
                      (Λ m : ℂ) * χ (m : ZMod (k + 1))) *
                   (∑ n ∈ Finset.Ioc U (⌊x⌋₊ / subHi ⌊x⌋₊ U V Δ r j),
                      (vaughanMollifier U n : ℂ) * χ (n : ZMod (k + 1)))‖
          ≤ ∑ j ∈ Finset.range L,
              Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
                Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
                Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3) *
                Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) :=
            Finset.sum_le_sum hper_j
        _ = (Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
              Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
              Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) *
            ∑ j ∈ Finset.range L,
              Real.sqrt (∑ m ∈ Finset.Ioc (subLo V Δ r j) (subHi ⌊x⌋₊ U V Δ r j), Λ m ^ 2) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2) *
              Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
              Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) *
            (Real.sqrt (3 / Δ) * (Real.sqrt (M : ℝ) * Real.log x)) :=
            mul_le_mul_of_nonneg_left hsum_j (by positivity)
        _ = (Real.sqrt (3 / Δ) * Real.sqrt (Δ * (M : ℝ) + 1 + 12 * (D : ℝ) ^ 2)) *
              Real.sqrt (M : ℝ) *
              (Real.sqrt (x / (M : ℝ) + 12 * (D : ℝ) ^ 2) *
               Real.sqrt ((x / (M : ℝ)) * (1 + Real.log x) ^ 3)) * Real.log x := by ring
        _ ≤ (2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) *
              Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) *
               (Real.sqrt (x / (M : ℝ)) * (1 + Real.log x) ^ 2)) * Real.log x := by
            gcongr
        _ = ((2 * Real.sqrt (M : ℝ) + 7 * (D : ℝ) / Real.sqrt Δ) * Real.sqrt (M : ℝ) *
              ((Real.sqrt (x / (M : ℝ)) + 4 * (D : ℝ)) * Real.sqrt (x / (M : ℝ)))) *
            (Real.log x * (1 + Real.log x) ^ 2) := by ring
        _ ≤ (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
              (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
              (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ)) * (1 + Real.log x) ^ 3 :=
            mul_le_mul hcross hlog_prod (by positivity) (by positivity)
  
  have hR_le : (R : ℝ) ≤ 4 * (1 + Real.log x) := by
    have hpow : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by
      have : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
      omega)
    have hpowR : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x :=
      (by exact_mod_cast hpow : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊) hpowR
    rw [Real.log_pow] at hlog
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hnat : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ 2 * Real.log x := by nlinarith
    dsimp only [R]; push_cast; linarith
  calc _ ≤ ∑ _r ∈ Finset.range R,
            28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
              (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
              (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3 :=
          htri.trans (Finset.sum_le_sum hblock)
    _ = (R : ℝ) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (4 * (1 + Real.log x)) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_right hR_le (by positivity)
    _ ≤ 120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by
        have hnn : 0 ≤ (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4 := by positivity
        have hEq : (4 * (1 + Real.log x)) * (28 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 3) =
          112 * ((x + (D : ℝ) * x / Real.sqrt (U : ℝ) +
          (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) * (1 + Real.log x) ^ 4) := by ring
        rw [hEq]; linarith

open Classical in

theorem dyadic_prim_chebyshevPsiChar_bound {D U V : ℕ} {x Δ : ℝ}
    (hD : 1 ≤ D) (hU : 1 ≤ U) (hV : 1 ≤ V) (hx : 3 ≤ x) (hDx : (D : ℝ) ≤ x) (hVx : (V : ℝ) ≤ x)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∑ k ∈ Finset.Ico D (2 * D),
        (1 / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      180 * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
  have hx1 : 1 ≤ x := by linarith
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL_ge1 : 1 ≤ 1 + Real.log x := by linarith
  
  have hstep1 :
      ∑ k ∈ Finset.Ico D (2 * D),
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        (1 / (D : ℝ)) *
          ∑ k ∈ Finset.Ico D (2 * D),
            (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkD : D ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
    have hphi_pos : (0 : ℝ) < (Nat.totient (k + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
    have hfac : 1 / (Nat.totient (k + 1) : ℝ) ≤
        (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) := by
      have h1 : (D : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hkD
      rw [show (1 / (D : ℝ)) * (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) =
        (((k + 1 : ℕ) : ℝ) / (D : ℝ)) * (1 / (Nat.totient (k + 1) : ℝ)) by ring]
      exact le_mul_of_one_le_left (by positivity) ((one_le_div hD_pos).mpr h1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfac (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  
  have hsplit :
      ∑ k ∈ Finset.Ico D (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖)) +
        (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖) +
        (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖) := by
    have hsub : Finset.Ico D (2 * D) ⊆ Finset.range (2 * D) := by
      intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; exact hk.2
    have hR_mono :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ ≤
        ∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hB_mono :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ ≤
        ∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hpt :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) +
             ‖vaughanS3Rect χ U V x Δ‖ + ‖vaughanS3Bdy χ U V x Δ‖) := by
      refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) (by positivity)
      rw [chebyshevPsiChar_vaughan_decomp χ hU hx1, vaughanS3_eq_rect_add_bdy χ hU hV x Δ]
      have h1 := norm_sub_le (vaughanS0 χ V x + vaughanS1 χ U x - vaughanS2 χ U V x)
        (vaughanS3Rect χ U V x Δ + vaughanS3Bdy χ U V x Δ)
      have h2 := norm_sub_le (vaughanS0 χ V x + vaughanS1 χ U x) (vaughanS2 χ U V x)
      have h3 := norm_add_le (vaughanS0 χ V x) (vaughanS1 χ U x)
      have h4 := norm_add_le (vaughanS3Rect χ U V x Δ) (vaughanS3Bdy χ U V x Δ)
      linarith
    have hpt_eq :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ((‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) +
             ‖vaughanS3Rect χ U V x Δ‖ + ‖vaughanS3Bdy χ U V x Δ‖) =
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖)) +
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Rect χ U V x Δ‖) +
        (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            ‖vaughanS3Bdy χ U V x Δ‖) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [hpt_eq] at hpt
    linarith
  
  have hT01 :
      ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) ≤
      48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) *
        (1 + Real.log x) ^ 4 := by
    have hlog2D : 1 + Real.log (2 * (D : ℝ)) ≤ 2 * (1 + Real.log x) := by
      have h1 : Real.log (2 * (D : ℝ)) = Real.log 2 + Real.log (D : ℝ) :=
        Real.log_mul (by norm_num) hD_pos.ne'
      have h2 : Real.log (D : ℝ) ≤ Real.log x := Real.log_le_log hD_pos hDx
      have h3 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hsqrt2D : Real.sqrt (2 * (D : ℝ)) ≤ 2 * Real.sqrt (D : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hsq2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _)
    set M01 : ℝ := (V : ℝ) * Real.log x +
      (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x
    have hpt01 : ∀ k ∈ Finset.Ico D (2 * D),
        ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖ ≤ M01 := by
      intro k hk χ hχ
      have hprim : χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
      have hk2 : 2 ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
      have hk_le : ((k + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
        have := (Finset.mem_Ico.mp hk).2; exact_mod_cast (by omega : k + 1 ≤ 2 * D)
      have hsqk : Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (D : ℝ) :=
        (Real.sqrt_le_sqrt hk_le).trans hsqrt2D
      have hlogk : 1 + Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log x) := by
        have hlk := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) hk_le
        linarith
      have h0 := norm_vaughanS0_le χ V hx1
      have h1 := norm_vaughanS1_le hk2 hprim U hx1
      have h2 := norm_vaughanS2_le (U := U) hk2 hprim hx1 hVx
      have hprod_le : Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) :=
        mul_le_mul hsqk hlogk (by have := Real.log_natCast_nonneg (k + 1); linarith) (by positivity)
      have h1' : 2 * (U : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) * Real.log x ≤
          2 * (U : ℝ) * ((2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x))) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hprod_le (show 0 ≤ 2 * (U : ℝ) by positivity)
        have := mul_le_mul_of_nonneg_right this hlogx_nn
        linarith
      have h2' : (U : ℝ) * (V : ℝ) * Real.log x * Real.sqrt ((k + 1 : ℕ) : ℝ) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) ≤
          (U : ℝ) * (V : ℝ) * ((2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x))) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hprod_le (show 0 ≤ (U : ℝ) * (V : ℝ) * Real.log x by positivity)
        linarith
      dsimp only [M01]; linarith
    have hM01_le : M01 ≤ 12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by
      have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
      have hUV : 2 * (U : ℝ) + (U : ℝ) * (V : ℝ) ≤ 3 * ((U : ℝ) * (V : ℝ)) := by nlinarith
      have hL1 : Real.log x ≤ 1 + Real.log x := by linarith
      have hL12 : Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
      have hL2 : (1 + Real.log x) * Real.log x ≤ (1 + Real.log x) ^ 2 := by nlinarith
      have h1 : (V : ℝ) * Real.log x ≤ (V : ℝ) * (1 + Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left hL12 (Nat.cast_nonneg _)
      have h2 : (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x ≤
          12 * ((U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by
        have hEq : (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * (2 * Real.sqrt (D : ℝ)) * (2 * (1 + Real.log x)) * Real.log x =
            4 * (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * Real.sqrt (D : ℝ) * ((1 + Real.log x) * Real.log x) := by ring
        rw [hEq]
        have ha : 4 * (2 * (U : ℝ) + (U : ℝ) * (V : ℝ)) * Real.sqrt (D : ℝ) ≤
            12 * ((U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) := by nlinarith [Real.sqrt_nonneg (D : ℝ)]
        exact mul_le_mul ha hL2 (by positivity) (by positivity)
      dsimp only [M01]
      have hVnn : 0 ≤ (V : ℝ) * (1 + Real.log x) ^ 2 := by positivity
      linarith
    have hsum_le :
        ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
            (‖vaughanS0 χ V x‖ + ‖vaughanS1 χ U x‖ + ‖vaughanS2 χ U V x‖) ≤
        ((2 * D : ℕ) : ℝ) ^ 2 * M01 := by
      have hsub : Finset.Ico D (2 * D) ⊆ Finset.range (2 * D) := by
        intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      calc _ ≤ ∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
                ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive), M01 :=
              Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun χ hχ => hpt01 k hk χ hχ) (by positivity)
        _ = (∑ k ∈ Finset.Ico D (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)) * M01 := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (∑ k ∈ Finset.range (2 * D), (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
              ((Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)).card : ℝ)) * M01 :=
              mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
                (by dsimp only [M01]; positivity)
        _ ≤ ((2 * D : ℕ) : ℝ) ^ 2 * M01 :=
              mul_le_mul_of_nonneg_right (sum_prim_weight_le (2 * D)) (by dsimp only [M01]; positivity)
    have hL24 : (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 4 := pow_le_pow_right₀ hL_ge1 (by omega)
    calc _ ≤ ((2 * D : ℕ) : ℝ) ^ 2 * M01 := hsum_le
      _ ≤ (4 * (D : ℝ) ^ 2) * (12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2) := by
          have hcast : ((2 * D : ℕ) : ℝ) ^ 2 = 4 * (D : ℝ) ^ 2 := by push_cast; ring
          rw [hcast]; exact mul_le_mul_of_nonneg_left hM01_le (by positivity)
      _ ≤ 48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) *
            (1 + Real.log x) ^ 4 := by
          have hEq : (4 * (D : ℝ) ^ 2) * (12 * ((V : ℝ) + (U : ℝ) * (V : ℝ) * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2) =
              48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) * (1 + Real.log x) ^ 2 := by ring
          rw [hEq]
          exact mul_le_mul_of_nonneg_left hL24 (by positivity)
  
  have hRect := sum_vaughanS3Rect_le hD hU hV hx hΔ0 hΔ1
  have hBdy := sum_vaughanS3Bdy_le hD hU hV hx hΔ0 hΔ1
  have hL34 : (1 + Real.log x) ^ 3 ≤ (1 + Real.log x) ^ 4 := pow_le_pow_right₀ hL_ge1 (by omega)
  have hBdy' :
      2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 3 ≤
      8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
    have h1 : 2 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + 4 * (D : ℝ) * Real.sqrt x) ≤
        8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) := by
      have : 0 ≤ (D : ℝ) * Real.sqrt Δ * x := by positivity
      have : 0 ≤ (D : ℝ) * Real.sqrt x := by positivity
      linarith
    exact mul_le_mul h1 hL34 (by positivity) (by positivity)
  refine hstep1.trans ?_
  have hsum_comb :
      ∑ k ∈ Finset.Ico D (2 * D),
          (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) * (1 + Real.log x) ^ 4 := by
    have hD_cancel : (D : ℝ) * (x / (D : ℝ)) = x := mul_div_cancel₀ x hD_pos.ne'
    have h1 :
        48 * ((D : ℝ) ^ 2 * (V : ℝ) + (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) +
        120 * (x + (D : ℝ) * x / Real.sqrt (U : ℝ) + (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) +
        8 * (D : ℝ) * (Real.sqrt Δ * x + Real.sqrt x + (D : ℝ) * Real.sqrt x) ≤
        180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) := by
      have ha : 0 ≤ (D : ℝ) ^ 2 * (V : ℝ) := by positivity
      have hb : 0 ≤ (U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ) := by positivity
      have hc : 0 ≤ x := by linarith
      have hd : 0 ≤ (D : ℝ) * x / Real.sqrt (U : ℝ) := by positivity
      have he : 0 ≤ (D : ℝ) * x / Real.sqrt (Δ * (V : ℝ)) := by positivity
      have hf : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ := by positivity
      have hg : 0 ≤ (D : ℝ) * Real.sqrt Δ * x := by positivity
      have hh : 0 ≤ (D : ℝ) * Real.sqrt x := by positivity
      have hi : 0 ≤ (D : ℝ) ^ 2 * Real.sqrt x := by positivity
      have hR_exp : 180 * (D : ℝ) * ((D : ℝ) * (V : ℝ) + (U : ℝ) * (V : ℝ) * ((D : ℝ) * Real.sqrt (D : ℝ)) +
          x / (D : ℝ) + x / Real.sqrt (U : ℝ) + x / Real.sqrt (Δ * (V : ℝ)) +
          (D : ℝ) * Real.sqrt x / Real.sqrt Δ + Real.sqrt Δ * x + Real.sqrt x +
          (D : ℝ) * Real.sqrt x) =
          180 * ((D : ℝ) ^ 2 * (V : ℝ)) + 180 * ((U : ℝ) * (V : ℝ) * (D : ℝ) ^ 2 * Real.sqrt (D : ℝ)) +
          180 * ((D : ℝ) * (x / (D : ℝ))) + 180 * ((D : ℝ) * x / Real.sqrt (U : ℝ)) +
          180 * ((D : ℝ) * x / Real.sqrt (Δ * (V : ℝ))) + 180 * ((D : ℝ) ^ 2 * Real.sqrt x / Real.sqrt Δ) +
          180 * ((D : ℝ) * Real.sqrt Δ * x) + 180 * ((D : ℝ) * Real.sqrt x) +
          180 * ((D : ℝ) ^ 2 * Real.sqrt x) := by ring
      rw [hR_exp, hD_cancel]
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (1 + Real.log x) ^ 4 by positivity)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum_comb (show 0 ≤ 1 / (D : ℝ) by positivity)
  refine hmul.trans_eq ?_
  field_simp [hD_pos.ne']

end RHDirect.Stage11BombieriVinogradov
end

theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1_H2_R1.H2 := @RHDirect.Stage11BombieriVinogradov.dyadic_prim_chebyshevPsiChar_bound
