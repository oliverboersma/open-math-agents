import OMAReductions.R_Erdos323_erdos_323_variants_k_eq_2_R1
import Mathlib

/-!
The effective prime number theorem in progressions, its analytic dependencies,
and the Abel summation identities are adapted from @nil-commits, Arithmetica4,
https://github.com/nil-commits/Arithmetica4, at commit
023f6441c22a9ca0db1670e351e8ac44f00555ea. Used under Apache-2.0.
Arithmetica4 builds on Mathlib4, rev 0df444a360eaa60ab8c11dca51a86af692955474,
released under Apache-2.0. The source modules used here are identified below.

The final argument specializes to modulus four, bounds the Abel integral by
comparison with the derivative of x divided by the cube of its logarithm,
and includes the exceptional prime two in the counting set.
-/

/-! ## From RHDirect/ElementaryEquiv.lean -/

noncomputable section

open Complex DirichletCharacter Filter Topology

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect

theorem LSeries_vonMangoldt_eq_neg_deriv_zeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
  simpa using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

theorem LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (Λ n : ℂ)) s =
      -deriv (LFunction χ) s / LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs, deriv_LFunction_eq_deriv_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs

def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n

theorem chebyshevPsi_nonneg (x : ℝ) : 0 ≤ chebyshevPsi x :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

end RHDirect

end

/-! ## From RHDirect/Stage2DirichletAP.lean -/

noncomputable section

open Complex DirichletCharacter Finset RHDirect

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage2DirichletAP

theorem LFunction_ne_zero_of_one_le_re_bridge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

theorem norm_LFunction_three_four_one_ge_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖LFunction (1 : DirichletCharacter ℂ q) (1 + x) ^ 3 *
          LFunction χ (1 + x + I * y) ^ 4 *
          LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ :=
  DirichletCharacter.norm_LFunction_product_ge_one χ hx y

theorem conj_dirichletChar_eq_apply_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) :
    starRingEnd ℂ (χ a) = χ a⁻¹ := by
  have hstar : starRingEnd ℂ (χ a) = (χ a)⁻¹ := by
    have h1 : starRingEnd ℂ (χ a) = χ⁻¹ a := by
      simpa [RCLike.star_def] using MulChar.star_apply' χ a
    exact h1.trans (MulChar.inv_apply_eq_inv' χ a)
  rw [hstar]
  have hmul : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl, map_one]
  exact (eq_inv_of_mul_eq_one_left hmul).symm

theorem isUnit_zmod_of_coprime {q a : ℕ} (hcop : Nat.Coprime a q) :
    IsUnit (a : ZMod q) :=
  (ZMod.isUnit_iff_coprime a q).mpr hcop

theorem char_orthogonality_indicator_zmod {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (b : ZMod q) :
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
      if b = a then 1 else 0 := by
  have hphi_ne : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hsum :
      ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
        if a = b then (q.totient : ℂ) else 0 := by
    have hcongr :
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ a) * χ b =
          ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ b :=
      Finset.sum_congr rfl fun χ _ => by rw [conj_dirichletChar_eq_apply_inv χ ha]
    rw [hcongr]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  rw [hsum]
  by_cases hba : b = a
  · subst hba
    simp [hphi_ne]
  · have hab : a ≠ b := Ne.symm hba
    simp [hba, hab]

theorem char_orthogonality_indicator_nat {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (n : ℕ) :
    (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q) =
      if n ≡ a [MOD q] then 1 else 0 := by
  have h := char_orthogonality_indicator_zmod (isUnit_zmod_of_coprime hcop) (n : ZMod q)
  simpa only [ZMod.natCast_eq_natCast_iff] using h

theorem principal_char_apply_nat {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if Nat.Coprime n q then 1 else 0 := by
  by_cases hcop : Nat.Coprime n q
  · simp [hcop, MulChar.one_apply (isUnit_zmod_of_coprime hcop)]
  · have hnu : ¬ IsUnit (n : ZMod q) := fun hu => hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
    simp [hcop, MulChar.map_nonunit _ hnu]

def chebyshevPsiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n ≡ a [MOD q] then Λ n else 0

def chebyshevThetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0

def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime then Real.log (n : ℝ) else 0

def primeCountAP (q a : ℕ) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ a [MOD q]).card

def chebyshevPsiChar {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ (n : ZMod q) * (Λ n : ℂ)

def chebyshevPsiCoprime (q : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if Nat.Coprime n q then Λ n else 0

theorem chebyshevThetaAP_le_chebyshevPsiAP (q a : ℕ) (x : ℝ) :
    chebyshevThetaAP q a x ≤ chebyshevPsiAP q a x := by
  apply Finset.sum_le_sum
  intro n _
  by_cases hmod : n ≡ a [MOD q]
  · by_cases hp : n.Prime
    · simp [hmod, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hmod, hp, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [hmod]

theorem chebyshevPsiAP_eq_char_sum {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) (x : ℝ) :
    (chebyshevPsiAP q a x : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x := by
  unfold chebyshevPsiAP chebyshevPsiChar
  rw [Complex.ofReal_sum]
  calc
    ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ((if n ≡ a [MOD q] then Λ n else 0 : ℝ) : ℂ)
        = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ((q.totient : ℂ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * χ (n : ZMod q)) *
            (Λ n : ℂ) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [char_orthogonality_indicator_nat hcop n]
          split_ifs <;> simp
    _ = (q.totient : ℂ)⁻¹ *
          ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ∑ χ : DirichletCharacter ℂ q,
              starRingEnd ℂ (χ (a : ZMod q)) * (χ (n : ZMod q) * (Λ n : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
    _ = (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            starRingEnd ℂ (χ (a : ZMod q)) *
              ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ (n : ZMod q) * (Λ n : ℂ) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]

theorem chebyshevPsiChar_one_eq_coprime (q : ℕ) (x : ℝ) :
    chebyshevPsiChar (1 : DirichletCharacter ℂ q) x = (chebyshevPsiCoprime q x : ℂ) := by
  unfold chebyshevPsiChar chebyshevPsiCoprime
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [principal_char_apply_nat]
  split_ifs <;> simp

open Classical in
theorem chebyshevPsiAP_eq_principal_add_nonprincipal {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) (x : ℝ) :
    (chebyshevPsiAP q a x : ℂ) =
      (q.totient : ℂ)⁻¹ * (chebyshevPsiCoprime q x : ℂ) +
        (q.totient : ℂ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x := by
  rw [chebyshevPsiAP_eq_char_sum hcop x]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x) (Finset.mem_univ 1)
  rw [← hsplit, mul_add]
  congr 1
  have h1 : (1 : DirichletCharacter ℂ q) (a : ZMod q) = 1 :=
    MulChar.one_apply (isUnit_zmod_of_coprime hcop)
  rw [h1, map_one, one_mul, chebyshevPsiChar_one_eq_coprime]

open Classical in
theorem chebyshevPsiAP_eq_principal_add_nonprincipal_re {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) (x : ℝ) :
    chebyshevPsiAP q a x =
      chebyshevPsiCoprime q x / (q.totient : ℝ) +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
  have h := congrArg Complex.re (chebyshevPsiAP_eq_principal_add_nonprincipal hcop x)
  rw [Complex.ofReal_re, Complex.add_re] at h
  have h1 : ((q.totient : ℂ)⁻¹ * (chebyshevPsiCoprime q x : ℂ)).re =
      chebyshevPsiCoprime q x / (q.totient : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
      div_eq_inv_mul]
  have h2 :
      ((q.totient : ℂ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re =
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  rw [h1, h2] at h
  exact h

private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg (s := t a ∩ s.biUnion t) (f := f) fun b _ => hf b]
    linarith

private lemma log_pow_natLog_le {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) :
    (Nat.log p N : ℝ) * Real.log (p : ℝ) ≤ Real.log x := by
  have hpow : p ^ Nat.log p N ≤ N := Nat.pow_log_le_self p (by omega)
  have hpowR : ((p : ℝ) ^ Nat.log p N) ≤ x :=
    le_trans (by exact_mod_cast hpow) hNx
  have hpos : (0 : ℝ) < (p : ℝ) ^ Nat.log p N := pow_pos (Nat.cast_pos.mpr hp.pos) _
  calc (Nat.log p N : ℝ) * Real.log (p : ℝ)
      = Real.log ((p : ℝ) ^ Nat.log p N) := (Real.log_pow (p : ℝ) (Nat.log p N)).symm
    _ ≤ Real.log x := Real.log_le_log hpos hpowR

private lemma sum_vonMangoldt_primePow_le_log {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (a : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ (Finset.Icc a (Nat.log p N)).image (fun k => p ^ k), Λ n ≤ Real.log x := by
  calc ∑ n ∈ (Finset.Icc a (Nat.log p N)).image (fun k => p ^ k), Λ n
      ≤ ∑ k ∈ Finset.Icc a (Nat.log p N), Λ (p ^ k) :=
        Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ _k ∈ Finset.Icc a (Nat.log p N), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk0 : k ≠ 0 := by
          rw [Finset.mem_Icc] at hk; omega
        rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ = ((Finset.Icc a (Nat.log p N)).card : ℝ) * Real.log (p : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.log p N : ℝ) * Real.log (p : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
        have hcard : (Finset.Icc a (Nat.log p N)).card ≤ Nat.log p N := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast hcard
    _ ≤ Real.log x := log_pow_natLog_le hp hN hNx

theorem chebyshevPsi_sub_chebyshevPsiCoprime_bounds {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ chebyshevPsi x - chebyshevPsiCoprime q x ∧
      chebyshevPsi x - chebyshevPsiCoprime q x ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  have hdiff :
      chebyshevPsi x - chebyshevPsiCoprime q x =
        ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n), Λ n := by
    unfold chebyshevPsi chebyshevPsiCoprime
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop, if_neg (fun h => h.1 hcop), sub_self]
    · by_cases hpp : IsPrimePow n
      · rw [if_neg hcop, if_pos ⟨hcop, hpp⟩, sub_zero]
      · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
        rw [if_neg hcop, if_neg (fun h => hpp h.2), sub_zero, h0]
  rw [hdiff]
  refine ⟨Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsub :
      (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n) ⊆
        q.primeFactors.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnle, hncop, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      have hpcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
      exact hncop (hpcop.pow_left k)
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩, k, ⟨hkpos, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  calc ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ IsPrimePow n), Λ n
      ≤ ∑ n ∈ q.primeFactors.biUnion
          (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
        sum_biUnion_le_of_nonneg _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact sum_vonMangoldt_primePow_le_log (Nat.prime_of_mem_primeFactors hp) hN hNx 1 le_rfl
    _ = (q.primeFactors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

open Classical in
theorem abs_chebyshevPsiAP_sub_le_of_char_sums {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q)
    {x : ℝ} (hx : 1 ≤ x) :
    |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) +
        (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [chebyshevPsiAP_eq_principal_add_nonprincipal_re hcop x]
  have hsplit :
      chebyshevPsiCoprime q x / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re -
          x / (q.totient : ℝ) =
        ((chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)) / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re := by
    ring
  rw [hsplit]
  have h1 :
      |((chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)) / (q.totient : ℝ)| ≤
        (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) := by
    rw [abs_div, abs_of_pos hphi_pos]
    refine div_le_div_of_nonneg_right ?_ hphi_pos.le
    obtain ⟨hnn, hup⟩ := chebyshevPsi_sub_chebyshevPsiCoprime_bounds (NeZero.pos q) hx
    calc |(chebyshevPsi x - x) - (chebyshevPsi x - chebyshevPsiCoprime q x)|
        ≤ |chebyshevPsi x - x| + |chebyshevPsi x - chebyshevPsiCoprime q x| := abs_sub _ _
      _ = |chebyshevPsi x - x| + (chebyshevPsi x - chebyshevPsiCoprime q x) := by
          rw [abs_of_nonneg hnn]
      _ ≤ |chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x := by linarith
  have h2 :
      |(q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re| ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hphi_pos)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
    calc |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re|
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            |(starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ := by
          refine Finset.sum_le_sum fun χ _ => ?_
          calc |(starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x).re|
              ≤ ‖starRingEnd ℂ (χ (a : ZMod q)) * chebyshevPsiChar χ x‖ := Complex.abs_re_le_norm _
            _ = ‖χ (a : ZMod q)‖ * ‖chebyshevPsiChar χ x‖ := by
                rw [norm_mul, Complex.norm_conj]
            _ ≤ 1 * ‖chebyshevPsiChar χ x‖ :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
            _ = ‖chebyshevPsiChar χ x‖ := one_mul _
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_chebyshevPsiAP_sub_le_of_uniform_char_bound {q a : ℕ} [NeZero q]
    (hcop : Nat.Coprime a q) {x E₁ E₂ : ℝ} (hx : 1 ≤ x) (hE₂ : 0 ≤ E₂)
    (h1 : |chebyshevPsi x - x| ≤ E₁)
    (h2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖chebyshevPsiChar χ x‖ ≤ E₂) :
    |chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      (E₁ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) + E₂ := by
  classical
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hbase := abs_chebyshevPsiAP_sub_le_of_char_sums hcop hx
  have hfirst :
      (|chebyshevPsi x - x| + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) ≤
        (E₁ + (q.primeFactors.card : ℝ) * Real.log x) / (q.totient : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hphi_pos.le
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
    have htot : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
        ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card (Finset.erase_subset _ _)
      _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
      _ = q.totient := htot
  have hsecond :
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖ ≤ E₂ := by
    calc (q.totient : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖chebyshevPsiChar χ x‖
        ≤ (q.totient : ℝ)⁻¹ *
            ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), E₂ := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
          exact Finset.sum_le_sum fun χ hχ => h2 χ (Finset.mem_erase.mp hχ).1
      _ = (q.totient : ℝ)⁻¹ *
            (((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * E₂) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * E₂) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi_pos.le)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE₂
      _ = E₂ := by field_simp [hphi_pos.ne']
  linarith

theorem chebyshevPsi_sub_chebyshevTheta_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ chebyshevPsi x - chebyshevTheta x ∧
      chebyshevPsi x - chebyshevTheta x ≤ Real.sqrt x * Real.log x := by
  have hdiff :
      chebyshevPsi x - chebyshevTheta x =
        ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n), Λ n := by
    unfold chebyshevPsi chebyshevTheta
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · by_cases hpp : IsPrimePow n
      · simp [hp, hpp]
      · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
        simp [hp, hpp, h0]
  rw [hdiff]
  refine ⟨Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  set P : Finset ℕ := (Finset.Icc 2 (Nat.sqrt ⌊x⌋₊)).filter Nat.Prime
  have hsub :
      (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n) ⊆
        P.biUnion (fun p => (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc, P] at hn ⊢
    obtain ⟨hnle, hnp, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hnp
      exact hnp hp
    have hp2_le : p * p ≤ ⌊x⌋₊ := by
      have hsq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      rw [sq] at hsq
      omega
    have hp_sqrt : p ≤ Nat.sqrt ⌊x⌋₊ := Nat.le_sqrt.mpr hp2_le
    refine ⟨p, ⟨⟨hp.two_le, hp_sqrt⟩, hp⟩, k, ⟨hk2, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hP_card : (P.card : ℝ) ≤ Real.sqrt x := by
    have hcard_nat : P.card ≤ Nat.sqrt ⌊x⌋₊ := by
      calc P.card ≤ (Finset.Icc 2 (Nat.sqrt ⌊x⌋₊)).card := Finset.card_filter_le _ _
        _ ≤ Nat.sqrt ⌊x⌋₊ := by rw [Nat.card_Icc]; omega
    have hsqrt_le : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
      have hsq : (Nat.sqrt ⌊x⌋₊ : ℝ) ^ 2 ≤ x := by
        have hnat : Nat.sqrt ⌊x⌋₊ * Nat.sqrt ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.sqrt_le ⌊x⌋₊
        have hR : (Nat.sqrt ⌊x⌋₊ : ℝ) * (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
          exact_mod_cast hnat
        rw [sq]
        exact hR.trans hNx
      exact Real.le_sqrt_of_sq_le hsq
    exact (by exact_mod_cast hcard_nat : (P.card : ℝ) ≤ (Nat.sqrt ⌊x⌋₊ : ℝ)).trans hsqrt_le
  calc ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ n.Prime ∧ IsPrimePow n), Λ n
      ≤ ∑ n ∈ P.biUnion (fun p => (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ p ∈ P, ∑ n ∈ (Finset.Icc 2 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
        sum_biUnion_le_of_nonneg _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ _p ∈ P, Real.log x := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpr : p.Prime := (Finset.mem_filter.mp hp).2
        exact sum_vonMangoldt_primePow_le_log hpr hN hNx 2 (by norm_num)
    _ = (P.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt x * Real.log x :=
        mul_le_mul_of_nonneg_right hP_card (Real.log_nonneg hx)

theorem chebyshevPsiAP_sub_chebyshevThetaAP_le (q a : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsiAP q a x - chebyshevThetaAP q a x ≤ Real.sqrt x * Real.log x := by
  have hle : chebyshevPsiAP q a x - chebyshevThetaAP q a x ≤ chebyshevPsi x - chebyshevTheta x := by
    unfold chebyshevPsiAP chebyshevThetaAP chebyshevPsi chebyshevTheta
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hmod : n ≡ a [MOD q]
    · by_cases hp : n.Prime <;> simp [hmod, hp]
    · by_cases hp : n.Prime
      · simp [hmod, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp [hmod, hp, ArithmeticFunction.vonMangoldt_nonneg]
  exact hle.trans (chebyshevPsi_sub_chebyshevTheta_bounds hx).2

end RHDirect.Stage2DirichletAP

end

/-! ## From RHDirect/Stage3RealAnalyticLandau.lean -/

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage3RealAnalyticLandau

theorem dirSeriesSummable_iff_real {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n) (s : ℂ) :
    LSeriesSummable (fun n => (a n : ℂ)) s ↔ Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s.re)) := by
  rw [LSeriesSummable, ← summable_norm_iff]
  refine summable_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term_zero, ha0]
  · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_of_nonneg (ha n),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_neg hpos.le,
      div_eq_mul_inv]

def stepSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

theorem stepSum_const_on_Ico (a : ℕ → ℂ) (k : ℕ) {t : ℝ} (ht1 : (k : ℝ) ≤ t)
    (ht2 : t < ((k + 1 : ℕ) : ℝ)) :
    stepSum a t = stepSum a (k : ℝ) := by
  unfold stepSum
  have hfl : ⌊t⌋₊ = k := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) ht1)).mpr
    ⟨ht1, by exact_mod_cast ht2⟩
  rw [hfl, Nat.floor_natCast]

theorem measurable_stepSum (a : ℕ → ℂ) : Measurable (stepSum a) := by
  have h : stepSum a = (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, a n) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

private lemma intervalIntegral_stepSum_unit (a : ℕ → ℂ) (k : ℕ) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), stepSum a t * φ' t =
      stepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      stepSum a t * φ' t = stepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]

private lemma intervalIntegrable_stepSum_mul_unit (a : ℕ → ℂ) (k : ℕ) {φ' : ℝ → ℂ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => stepSum a t * φ' t) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => stepSum a (k : ℝ) * φ' t) volume (k : ℝ)
      ((k + 1 : ℕ) : ℝ) :=
    (hc.intervalIntegrable).const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  exact (congrArg (· * φ' t) (stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne))).symm

theorem abel_summation_general (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (1 : ℝ) x)) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (n : ℝ) =
      stepSum a x * φ x - ∫ t in (1 : ℝ)..x, stepSum a t * φ' t := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  
  have hint_nat : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => stepSum a t * φ' t) volume (1 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 1 N, a n * φ (n : ℝ) =
        stepSum a (N : ℝ) * φ (N : ℝ) - ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      simp [stepSum]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (1 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm1R : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
        exact ⟨le_trans hm1R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit a m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit a m (fun t ht => hd t (hsub_u ht))
        (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
      have hstep_succ : stepSum a ((m + 1 : ℕ) : ℝ) = stepSum a (m : ℝ) + a (m + 1) := by
        unfold stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc, Finset.sum_insert hnot]
        ring
      rw [hIcc, Finset.sum_insert hnot, heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN1 hfl_le
  
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (1 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (Nat.one_le_cast.mpr hN1) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      stepSum a t * φ' t = stepSum a (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [stepSum_const_on_Ico a ⌊x⌋₊ ht.1.le hlt]
  have hint_tail : IntervalIntegrable (fun t => stepSum a t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul (stepSum a (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, stepSum a t * φ' t =
      stepSum a (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : stepSum a x = stepSum a (⌊x⌋₊ : ℝ) := by
    unfold stepSum; rw [Nat.floor_natCast]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N,
    hstep_x]
  ring

theorem abel_summation_dirichlet (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) (s : ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (n : ℂ) ^ (-s) =
      stepSum a x * (x : ℂ) ^ (-s) + s * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun u : ℝ => (u : ℂ) ^ (-s)) =ᶠ[𝓝 t]
        fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht0] with u hu
      have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
      rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu.le]
    have h1 : HasDerivAt (fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)))
        (cexp ((Real.log t : ℂ) * (-s)) * (((t⁻¹ : ℝ) : ℂ) * (-s))) t := by
      exact (((Real.hasDerivAt_log ht0.ne').ofReal_comp).mul_const (-s)).cexp
    refine (h1.congr_of_eventuallyEq hfun).congr_deriv ?_
    have hcp : cexp ((Real.log t : ℂ) * (-s)) = (t : ℂ) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hcp, Complex.cpow_sub _ _ htC, Complex.cpow_one]
    push_cast; field_simp
  have hc : ContinuousOn (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (1 : ℝ) x) := by
    refine continuousOn_const.mul ?_
    have hcont_exp : ContinuousOn (fun t : ℝ => cexp ((Real.log t : ℂ) * (-s - 1))) (Set.Icc (1 : ℝ) x) := by
      refine ContinuousOn.cexp (ContinuousOn.mul ?_ continuousOn_const)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans_le ht.1).ne'
    refine hcont_exp.congr fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    dsimp only
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
  have hab := abel_summation_general a hx hd hc
  have hcast : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((n : ℝ) : ℂ) ^ (-s) = a n * (n : ℂ) ^ (-s) := by
    intro n _; push_cast; rfl
  rw [Finset.sum_congr rfl hcast] at hab
  rw [hab]
  have hint : ∫ t in (1 : ℝ)..x, stepSum a t * ((-s) * (t : ℂ) ^ (-s - 1)) =
      (-s) * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  ring

theorem integrableOn_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
  have hexp : θ - s.re - 1 < -1 := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul C) ?_ ?_
  · have hpow : Measurable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) :=
      Complex.measurable_ofReal.pow_const (-s - 1)
    exact (hE.mul hpow).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc ‖E t‖ * t ^ (-s.re - 1)
        ≤ (C * t ^ θ) * t ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hbd t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = C * (t ^ θ * t ^ (-s.re - 1)) := by ring
      _ = C * t ^ (θ - s.re - 1) := by
          rw [← Real.rpow_add ht0]; congr 2; ring

theorem hasDerivAt_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) s := by
  set δ : ℝ := (s.re - θ) / 2 with hδ_def
  have hδ0 : 0 < δ := by linarith
  set e : ℝ := δ / 2 with he_def
  have he0 : 0 < e := by linarith
  have hre : ∀ z ∈ Metric.ball s δ, θ + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz.le)).1
    rw [Complex.sub_re] at h1
    linarith
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => E t * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := fun z =>
    (hE.mul (Complex.measurable_ofReal.pow_const (-z - 1))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun t : ℝ => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)))
      (volume.restrict (Ioi 1)) :=
    (hE.mul (((Complex.measurable_ofReal.comp Real.measurable_log).neg).mul
      (Complex.measurable_ofReal.pow_const (-s - 1)))).aestronglyMeasurable
  have hint := integrableOn_mellin_of_rpow_bound hE hbd hs
  have hdom_int : Integrable (fun t : ℝ => C * e⁻¹ * t ^ (-1 - δ / 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - δ / 2 < -1) zero_lt_one).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => E t * (t : ℂ) ^ (-z - 1))
    (F' := fun z t => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-z - 1)))
    (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall hmeasF) hint hmeasF' ?_ hdom_int ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht1
    have hzr : θ + δ ≤ z.re := hre z hz
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre_z : (-z - 1).re = -z.re - 1 := by simp
    rw [hre_z]
    have hz_pow : t ^ (-z.re - 1) ≤ t ^ (-(θ + δ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hcomb : t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1)) = t ^ (-1 - δ / 2) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
      congr 1; linarith
    calc ‖E t‖ * (Real.log t * t ^ (-z.re - 1))
        ≤ (C * t ^ θ) * ((e⁻¹ * t ^ e) * t ^ (-(θ + δ) - 1)) := by
          refine mul_le_mul (hbd t ht1.le) ?_ (mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _))
            (mul_nonneg hC (Real.rpow_nonneg ht0.le _))
          exact mul_le_mul hlog hz_pow (Real.rpow_nonneg ht0.le _) (by positivity)
      _ = C * e⁻¹ * (t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1))) := by ring
      _ = C * e⁻¹ * t ^ (-1 - δ / 2) := by rw [hcomb]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z _ => ?_)
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun w : ℂ => E t * (t : ℂ) ^ (-w - 1)) =
        fun w : ℂ => E t * cexp ((Real.log t : ℂ) * (-w - 1)) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (Real.log t : ℂ) * (-w - 1)) (-(Real.log t : ℂ)) z := by
      have h0 : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) z := by
        simpa using (hasDerivAt_id' z).neg.sub_const (1 : ℂ)
      simpa using h0.const_mul (Real.log t : ℂ)
    refine (h1.cexp.const_mul (E t)).congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    ring

theorem analyticOnNhd_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) :
    AnalyticOnNhd ℂ (fun s : ℂ => 1 + s * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1))
      {s : ℂ | θ < s.re} := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hopen
  have hd := hasDerivAt_mellin_of_rpow_bound hE hC hbd hs
  exact (differentiableAt_const (1 : ℂ)).add
    (differentiableAt_id.mul hd.differentiableAt) |>.differentiableWithinAt

theorem LSeries_eq_mul_mellin_stepSum {a : ℕ → ℂ} {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s = s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1) := by
  
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries a s)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term a s n) atTop
        (𝓝 (LSeries a s)) :=
      h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun N => ?_
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N), LSeries.term_zero, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  
  have hBdry : Tendsto (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (-(s.re - θ)))) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      simpa using h
    refine squeeze_zero_norm' ?_ hpow
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, neg_re]
    calc ‖stepSum a (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (C * (N : ℝ) ^ θ) * (N : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hbd (N : ℝ) hN1) (Real.rpow_nonneg hN0.le _)
      _ = C * ((N : ℝ) ^ θ * (N : ℝ) ^ (-s.re)) := by ring
      _ = C * (N : ℝ) ^ (-(s.re - θ)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  
  have hint := integrableOn_mellin_of_rpow_bound (measurable_stepSum a) hbd hs
  have hInt : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).comp tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun N : ℕ =>
      stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (0 + s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    hBdry.add (hInt.const_mul s)
  have hEq : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := abel_summation_dirichlet a (Nat.one_le_cast.mpr hN) s
    simpa [Nat.floor_natCast] using h
  simpa using tendsto_nhds_unique (hLHS.congr' hEq) hRHS

theorem LSeries_sub_pole_eq_mellin_error {a : ℕ → ℂ} {C : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s - 1 / (s - 1) =
      1 + s * ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ha_pow : (-s).re < -1 := by simp; linarith
  have hlin_int : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_cpow_of_lt ha_pow zero_lt_one).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    dsimp only
    rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
  have hlin_val : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-s - 1) = 1 / (s - 1) := by
    have hcongr : EqOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1))
        (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := fun t ht => by
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
      dsimp only
      rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_cpow_of_lt ha_pow zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
    have h1s : -s + 1 = -(s - 1) := by ring
    rw [h1s]; field_simp
  have hstep_int : IntegrableOn (fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_mellin_of_rpow_bound (measurable_stepSum a)
      (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs
  have hL := LSeries_eq_mul_mellin_stepSum
    (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs hsum
  have hsub_eq : ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) =
      (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) - 1 / (s - 1) := by
    have hpt : (fun t : ℝ => (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1)) =
        fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1) - (t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      funext t; ring
    rw [hpt, integral_sub hstep_int hlin_int, hlin_val]
  rw [hL, hsub_eq]
  field_simp
  ring

theorem chebyshevPsi_eq_mathlib_psi (x : ℝ) :
    chebyshevPsi x = Chebyshev.psi x := by
  unfold chebyshevPsi Chebyshev.psi
  have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 ⌊x⌋₊)]
  simp

theorem chebyshevPsi_le_six_mul {t : ℝ} (ht : 1 ≤ t) :
    chebyshevPsi t ≤ 6 * t := by
  rw [chebyshevPsi_eq_mathlib_psi]
  have h := Chebyshev.psi_le ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hl4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hlog : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h1
    linarith
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have h2 : 2 * Real.sqrt t * Real.log t ≤ 4 * t := by
    calc 2 * Real.sqrt t * Real.log t
        ≤ 2 * Real.sqrt t * (2 * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4 * (Real.sqrt t * Real.sqrt t) := by ring
      _ = 4 * t := by rw [hsq]
  nlinarith

end RHDirect.Stage3RealAnalyticLandau
end

/-! ## From RHDirect/Stage3ZeroFreeRegion.lean -/

noncomputable section

open Complex DirichletCharacter Finset RHDirect

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage3ZeroFreeRegion

def negLogDerivZeta (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

def negLogDerivL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

theorem three_four_one_complex_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hns : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [Complex.normSq_apply] at h1
    linarith
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [sq, Complex.mul_re]
    ring
  rw [hsq]
  nlinarith [sq_nonneg (1 + z.re)]

theorem negLogDerivZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    negLogDerivZeta s = LSeries (fun n => (Λ n : ℂ)) s :=
  (RHDirect.LSeries_vonMangoldt_eq_neg_deriv_zeta_div hs).symm

theorem negLogDerivL_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    negLogDerivL χ s = LSeries (fun n => χ n * (Λ n : ℂ)) s :=
  (RHDirect.LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div χ hs).symm

private lemma LSeries_term_add_I_mul (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f ((σ : ℂ) + I * (t : ℂ)) n =
      LSeries.term (fun m => f m * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg]
    ring

theorem three_four_one_negLogDerivL_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    3 * negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ) +
      4 * negLogDerivL χ ((σ : ℂ) + I * (t : ℂ)) +
      negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ)) =
    LSeries (fun n => (Λ n : ℂ) *
      (3 * (1 : DirichletCharacter ℂ q) n +
        4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
        (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ))))) (σ : ℂ) := by
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs2 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simp [hσ]
  rw [negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs0,
      negLogDerivL_eq_LSeries χ hs1,
      negLogDerivL_eq_LSeries (χ ^ 2) hs2]
  have hsum0 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs0
  have hsum1 : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs1
  have hsum2 : LSeriesSummable (fun n => (χ ^ 2) n * (Λ n : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) :=
    (χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2
  have hterm1 : ∀ n, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((σ : ℂ) + I * (t : ℂ)) n =
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n :=
    fun n => LSeries_term_add_I_mul _ σ t n
  have hterm2 : ∀ n, LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ)) ((σ : ℂ) + 2 * I * (t : ℂ)) n =
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n := by
    intro n
    have h2 : (σ : ℂ) + 2 * I * (t : ℂ) = (σ : ℂ) + I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
    have h2' : -(2 * I * (t : ℂ)) = -(I * ((2 * t : ℝ) : ℂ)) := by push_cast; ring
    rw [h2, h2']
    exact LSeries_term_add_I_mul _ σ (2 * t) n
  have hsum1' : Summable (fun n =>
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n) :=
    hsum1.congr hterm1
  have hsum2' : Summable (fun n =>
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n) :=
    hsum2.congr hterm2
  unfold LSeries
  rw [tsum_congr hterm1, tsum_congr hterm2, ← tsum_mul_left, ← tsum_mul_left,
      ← (hsum0.mul_left 3).tsum_add (hsum1'.mul_left 4),
      ← ((hsum0.mul_left 3).add (hsum1'.mul_left 4)).tsum_add hsum2']
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte]
    ring

private lemma real_tsum_nonneg_of_complex {f : ℕ → ℂ} (hf : Summable f)
    (hre : ∀ n, 0 ≤ (f n).re) : 0 ≤ (∑' n, f n).re := by
  have hsum_re : Summable (fun n => (f n).re) := Complex.reCLM.summable hf
  have heq : (∑' n, f n).re = ∑' n, (f n).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hf
  rw [heq]
  exact tsum_nonneg hre

private lemma norm_cpow_neg_I_mul_nat {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(I * (t : ℂ)))‖ = 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-(I * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.rpow_zero]

theorem three_four_one_negLogDerivL_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re +
        4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have hre_comb :
      3 * (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re +
          4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
          (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re =
        (3 * negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ) +
          4 * negLogDerivL χ ((σ : ℂ) + I * (t : ℂ)) +
          negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
    simp
  rw [hre_comb, three_four_one_negLogDerivL_eq_LSeries χ hσ t]
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hs2 : 1 < ((σ : ℂ) + 2 * I * (t : ℂ)).re := by simp [hσ]
  have hsum0 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs0
  have hsum1 : Summable (fun n =>
      LSeries.term (fun m => χ m * (Λ m : ℂ) * (m : ℂ) ^ (-(I * (t : ℂ)))) (σ : ℂ) n) :=
    (χ.LSeriesSummable_twist_vonMangoldt hs1).congr (fun n => LSeries_term_add_I_mul _ σ t n)
  have hsum2 : Summable (fun n =>
      LSeries.term (fun m => (χ ^ 2) m * (Λ m : ℂ) * (m : ℂ) ^ (-(2 * I * (t : ℂ)))) (σ : ℂ) n) := by
    refine ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2).congr fun n => ?_
    have h2 : (σ : ℂ) + 2 * I * (t : ℂ) = (σ : ℂ) + I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
    have h2' : -(2 * I * (t : ℂ)) = -(I * ((2 * t : ℝ) : ℂ)) := by push_cast; ring
    rw [h2, h2']
    exact LSeries_term_add_I_mul _ σ (2 * t) n
  have hsumm : Summable (LSeries.term (fun n => (Λ n : ℂ) *
      (3 * (1 : DirichletCharacter ℂ q) n +
        4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
        (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ))))) (σ : ℂ)) := by
    refine (((hsum0.mul_left 3).add (hsum1.mul_left 4)).add hsum2).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn, ↓reduceIte]
      ring
  refine real_tsum_nonneg_of_complex hsumm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow, div_eq_mul_inv, ← Complex.ofReal_inv]
    have hcoeff :
        ((Λ n : ℂ) *
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) *
          ((((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ)).re =
        (Λ n * ((n : ℝ) ^ σ)⁻¹) *
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))).re := by
      have hreorder :
          (Λ n : ℂ) *
            (3 * (1 : DirichletCharacter ℂ q) n +
              4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
              (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) *
            ((((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) =
          (((Λ n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ)) *
            (3 * (1 : DirichletCharacter ℂ q) n +
              4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
              (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))) := by
        push_cast; ring
      rw [hreorder, Complex.re_ofReal_mul]
    rw [hcoeff]
    refine mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (inv_nonneg.mpr (Real.rpow_nonneg hnR.le σ))) ?_
    by_cases hu : IsUnit (n : ZMod q)
    · set z : ℂ := χ (n : ZMod q) * (n : ℂ) ^ (-(I * (t : ℂ)))
      have hz_sq : (χ ^ 2) (n : ZMod q) * (n : ℂ) ^ (-(2 * I * (t : ℂ))) = z ^ 2 := by
        have hpow2 : (n : ℂ) ^ (-(2 * I * (t : ℂ))) = ((n : ℂ) ^ (-(I * (t : ℂ)))) ^ 2 := by
          rw [sq, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne')]
          congr 1; ring
        rw [sq, MulChar.mul_apply, hpow2]
        dsimp only [z]
        ring
      have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 1 := MulChar.one_apply hu
      have hz_norm : ‖z‖ ≤ 1 := by
        rw [norm_mul, norm_cpow_neg_I_mul_nat hn t, mul_one]
        exact χ.norm_le_one _
      have hre_z :
          (3 * (1 : DirichletCharacter ℂ q) n +
            4 * χ n * (n : ℂ) ^ (-(I * (t : ℂ))) +
            (χ ^ 2) n * (n : ℂ) ^ (-(2 * I * (t : ℂ)))).re =
          3 + 4 * z.re + (z ^ 2).re := by
        rw [h1, hz_sq]
        have h4 : 4 * χ (n : ZMod q) * (n : ℂ) ^ (-(I * (t : ℂ))) = 4 * z := by
          dsimp only [z]; ring
        rw [h4]
        simp
      rw [hre_z]
      exact three_four_one_complex_nonneg hz_norm
    · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
      simp

theorem negLogDerivL_one_re_le_negLogDerivZeta_re {q : ℕ} [NeZero q] {σ : ℝ} (hσ : 1 < σ) :
    (negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ (negLogDerivZeta (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivL_eq_LSeries (1 : DirichletCharacter ℂ q) hs, negLogDerivZeta_eq_LSeries hs]
  have hsum1 : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ) :=
    (1 : DirichletCharacter ℂ q).LSeriesSummable_twist_vonMangoldt hs
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hdiff : 0 ≤ (LSeries (fun n => (Λ n : ℂ)) (σ : ℂ) -
      LSeries (fun n => (1 : DirichletCharacter ℂ q) n * (Λ n : ℂ)) (σ : ℂ)).re := by
    unfold LSeries
    rw [← Summable.tsum_sub hsumZ hsum1]
    refine real_tsum_nonneg_of_complex (Summable.sub hsumZ hsum1) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn.ne', ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
      rw [hcpow]
      by_cases hu : IsUnit (n : ZMod q)
      · rw [MulChar.one_apply hu, one_mul, sub_self, Complex.zero_re]
      · rw [MulChar.map_nonunit _ hu, zero_mul, zero_div, sub_zero, ← Complex.ofReal_div,
          Complex.ofReal_re]
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ)
  simpa [Complex.sub_re] using hdiff

theorem three_four_one_zeta_negLogDerivL_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivZeta (σ : ℂ)).re +
        4 * (negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivL (χ ^ 2) ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have h1 := three_four_one_negLogDerivL_re_nonneg χ hσ t
  have h2 := negLogDerivL_one_re_le_negLogDerivZeta_re (q := q) hσ
  linarith

theorem three_four_one_zeta_re_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (negLogDerivZeta (σ : ℂ)).re +
        4 * (negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))).re +
        (negLogDerivZeta ((σ : ℂ) + 2 * I * (t : ℂ))).re := by
  have h := three_four_one_zeta_negLogDerivL_re_nonneg (1 : DirichletCharacter ℂ 1) hσ t
  have hL : ∀ s : ℂ, negLogDerivL (1 : DirichletCharacter ℂ 1) s = negLogDerivZeta s := fun s => by
    unfold negLogDerivL negLogDerivZeta
    rw [DirichletCharacter.LFunction_modOne_eq]
  rw [one_pow, hL, hL] at h
  exact h

end RHDirect.Stage3ZeroFreeRegion

end

/-! ## From RHDirect/Stage4ExplicitFormula.lean -/

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage4ExplicitFormula

theorem integral_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ = Real.pi / c := by
  have h1 : (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    field_simp [hc.ne', hc2]
  rw [h1, integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) c⁻¹,
    integral_univ_inv_one_add_sq]
  simp only [inv_inv, smul_eq_mul, abs_of_pos hc]
  field_simp [hc.ne']

theorem integrable_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun t : ℝ => (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    h1.comp_mul_left' (inv_ne_zero hc.ne')
  refine (h2.const_mul (c ^ 2)⁻¹).congr (Eventually.of_forall fun t => ?_)
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  field_simp [hc.ne', hc2]

def cesaro1Integrand (y c t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
    (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))

def perronKernel1Full (y c : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, cesaro1Integrand y c t

private lemma norm_sq_vertical_eq (c t : ℝ) :
    ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [sq]

private lemma norm_cesaro1Integrand_le_inv_sq_add_sq {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (t : ℝ) :
    ‖cesaro1Integrand y c t‖ ≤ y ^ c * (c ^ 2 + t ^ 2)⁻¹ := by
  unfold cesaro1Integrand
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
  rw [hre]
  have hle : ‖(c : ℂ) + I * (t : ℂ)‖ ≤ ‖(c : ℂ) + 1 + I * (t : ℂ)‖ := by
    have hsq : ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 ≤ ‖(c : ℂ) + 1 + I * (t : ℂ)‖ ^ 2 := by
      have h1 : ‖(c : ℂ) + I * (t : ℂ)‖ ^ 2 = c ^ 2 + t ^ 2 := norm_sq_vertical_eq c t
      have h2 : ‖(c : ℂ) + 1 + I * (t : ℂ)‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
        have : (c : ℂ) + 1 + I * (t : ℂ) = ((c + 1 : ℝ) : ℂ) + I * (t : ℂ) := by push_cast; ring
        rw [this, norm_sq_vertical_eq]
      nlinarith
    nlinarith [norm_nonneg ((c : ℂ) + I * (t : ℂ)), norm_nonneg ((c : ℂ) + 1 + I * (t : ℂ))]
  have hden_pos : 0 < c ^ 2 + t ^ 2 := by positivity
  have hprod : c ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ := by
    calc c ^ 2 + t ^ 2 = ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + I * (t : ℂ)‖ := by
          rw [← sq, norm_sq_vertical_eq]
      _ ≤ ‖(c : ℂ) + I * (t : ℂ)‖ * ‖(c : ℂ) + 1 + I * (t : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le c) hden_pos hprod

theorem continuous_cesaro1Integrand {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (cesaro1Integrand y c) := by
  unfold cesaro1Integrand
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) := by
    have hEq : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) =
        fun t : ℝ => cexp (Complex.log (y : ℂ) * ((c : ℂ) + I * (t : ℂ))) :=
      funext fun t => Complex.cpow_def_of_ne_zero hyC _
    rw [hEq]; fun_prop
  refine hpow.div (by fun_prop) fun t => mul_ne_zero ?_ ?_
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith

theorem integrable_cesaro1Integrand {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable (cesaro1Integrand y c) :=
  ((integrable_inv_sq_add_sq hc).const_mul (y ^ c)).mono'
    (continuous_cesaro1Integrand hy hc).aestronglyMeasurable
    (Eventually.of_forall (norm_cesaro1Integrand_le_inv_sq_add_sq hy hc))

set_option maxHeartbeats 2000000 in
theorem perronKernel1Full_eq_max {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    perronKernel1Full y c = ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
  
  let h : ℝ → ℂ := fun u =>
    ((Real.exp (-c * max u 0) - Real.exp (-(c + 1) * max u 0) : ℝ) : ℂ)
  have hh_cont : Continuous h := by
    dsimp only [h]; fun_prop
  have hh_le_zero : ∀ u ≤ (0 : ℝ), h u = 0 := by
    intro u hu
    simp [h, max_eq_right hu]
  have hh_pos : ∀ u : ℝ, 0 < u →
      h u = cexp (-(c : ℂ) * (u : ℂ)) - cexp (-((c + 1 : ℝ) : ℂ) * (u : ℂ)) := by
    intro u hu
    simp only [h, max_eq_left hu.le, Complex.ofReal_sub, Complex.ofReal_exp]
    push_cast
    rfl
  have hh_int : Integrable h := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · refine (integrableOn_zero (μ := volume) (s := Iic (0 : ℝ))).congr_fun
        (fun u hu => (hh_le_zero u hu).symm) measurableSet_Iic
    · have hi1 : IntegrableOn (fun u : ℝ => cexp (-(c : ℂ) * (u : ℂ))) (Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp [hc]) 0
      have hi2 : IntegrableOn (fun u : ℝ => cexp (-((c + 1 : ℝ) : ℂ) * (u : ℂ))) (Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
      exact (hi1.sub hi2).congr_fun (fun u hu => (hh_pos u hu).symm) measurableSet_Ioi
  
  have hf_eq : ∀ ξ : ℝ, FourierTransform.fourier h ξ =
      1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
           ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))) := by
    intro ξ
    rw [Real.fourier_eq']
    have hsplit : ∫ u : ℝ, cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u =
        (∫ u in Iic (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) +
        (∫ u in Ioi (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) := by
      have hint_all : Integrable (fun u : ℝ =>
          cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u) := by
        refine hh_int.norm.mono' ?_ (Eventually.of_forall fun u => ?_)
        · exact ((by fun_prop : Continuous fun u : ℝ =>
            cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I)).smul hh_cont).aestronglyMeasurable
        · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hint_all.integrableOn hint_all.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
    rw [hsplit]
    have hleft : ∫ u in Iic (0 : ℝ), cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [hh_le_zero u hu, smul_zero]
    rw [hleft, zero_add]
    set a₁ : ℂ := -((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ))
    set a₂ : ℂ := -((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))
    have ha₁ : a₁.re < 0 := by simp [a₁, hc]
    have ha₂ : a₂.re < 0 := by simp [a₂]; linarith
    have hcongr : Set.EqOn
        (fun u : ℝ => cexp (((-2 * Real.pi * inner ℝ u ξ : ℝ) : ℂ) * I) • h u)
        (fun u : ℝ => cexp (a₁ * (u : ℂ)) - cexp (a₂ * (u : ℂ))) (Ioi 0) := by
      intro u hu
      dsimp only
      rw [smul_eq_mul, hh_pos u hu, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      have hinner : inner ℝ u ξ = u * ξ := by simp [mul_comm]
      rw [hinner]
      congr 1
      · congr 1; dsimp only [a₁]; push_cast; ring
      · congr 1; dsimp only [a₂]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_sub (integrableOn_exp_mul_complex_Ioi ha₁ 0) (integrableOn_exp_mul_complex_Ioi ha₂ 0),
      integral_exp_mul_complex_Ioi ha₁ 0, integral_exp_mul_complex_Ioi ha₂ 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hne₁ : (c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hne₂ : (c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    dsimp only [a₁, a₂]
    field_simp [hne₁, hne₂]
    ring
  
  have hfh_int : Integrable (FourierTransform.fourier h) := by
    have hfun : FourierTransform.fourier h = fun ξ : ℝ =>
        1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
             ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ))) := funext hf_eq
    rw [hfun]
    have hdom : Integrable (fun ξ : ℝ => (c ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹) :=
      (integrable_inv_sq_add_sq hc).comp_mul_left' (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    refine hdom.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have hcont : Continuous (fun ξ : ℝ =>
          1 / (((c : ℂ) + I * ((2 * Real.pi * ξ : ℝ) : ℂ)) *
               ((c : ℂ) + 1 + I * ((2 * Real.pi * ξ : ℝ) : ℂ)))) := by
        refine continuous_const.div (by fun_prop) fun ξ => mul_ne_zero ?_ ?_
        · intro h0; have := congrArg Complex.re h0; simp at this; linarith
        · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      exact hcont.aestronglyMeasurable
    · have h0 := norm_cesaro1Integrand_le_inv_sq_add_sq one_pos hc (2 * Real.pi * ξ)
      simpa [cesaro1Integrand, Complex.one_cpow] using h0
  
  have hinv := hh_int.fourierInv_fourier_eq hfh_int (hh_cont.continuousAt (x := Real.log y))
  rw [Real.fourierInv_eq'] at hinv
  have hsub : ∫ ξ : ℝ, cexp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) •
      FourierTransform.fourier h ξ =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
          (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
    have hrew : (fun ξ : ℝ =>
        cexp (((2 * Real.pi * inner ℝ ξ (Real.log y) : ℝ) : ℂ) * I) •
          FourierTransform.fourier h ξ) =
        fun ξ : ℝ => (fun t : ℝ => cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
          (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) (2 * Real.pi * ξ) := by
      funext ξ
      rw [hf_eq ξ, smul_eq_mul, mul_one_div]
      have hinner : inner ℝ ξ (Real.log y) = Real.log y * ξ := rfl
      rw [hinner]
      congr 2
      push_cast; ring
    rw [hrew]
    have hcomp := MeasureTheory.Measure.integral_comp_mul_left
      (fun t : ℝ => cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) (2 * Real.pi)
    rw [hcomp]
    have h2pi : 0 < 2 * Real.pi := by positivity
    rw [abs_of_pos (inv_pos.mpr h2pi), Complex.real_smul, Complex.ofReal_inv]
  rw [hsub] at hinv
  
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hmul := congrArg ((y : ℂ) ^ (c : ℂ) * ·) hinv
  have hLHS : (y : ℂ) ^ (c : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, cexp (I * (t : ℂ) * (Real.log y : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) =
      perronKernel1Full y c := by
    unfold perronKernel1Full
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    unfold cesaro1Integrand
    rw [mul_div_assoc', Complex.cpow_def_of_ne_zero hyC, Complex.cpow_def_of_ne_zero hyC,
      ← Complex.ofReal_log hy.le, ← Complex.exp_add]
    congr 2; ring
  have hRHS : (y : ℂ) ^ (c : ℂ) * h (Real.log y) = ((max (1 - 1 / y) 0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hy.le]
    by_cases hy1 : 1 ≤ y
    · have hlog_nn : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hmax : max (1 - 1 / y) 0 = 1 - 1 / y := by
        rw [max_eq_left]
        have : 1 / y ≤ 1 := (div_le_one hy).mpr hy1
        linarith
      rw [hmax]
      dsimp only [h]
      rw [max_eq_left hlog_nn, ← Complex.ofReal_mul]
      congr 1
      have h1 : y ^ c * Real.exp (-c * Real.log y) = 1 := by
        rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
        have : Real.log y * c + -c * Real.log y = 0 := by ring
        rw [this, Real.exp_zero]
      have h2 : y ^ c * Real.exp (-(c + 1) * Real.log y) = 1 / y := by
        rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
        have : Real.log y * c + -(c + 1) * Real.log y = -Real.log y := by ring
        rw [this, Real.exp_neg, Real.exp_log hy, one_div]
      rw [mul_sub, h1, h2]
    · push Not at hy1
      have hlog_np : Real.log y ≤ 0 := Real.log_nonpos hy.le hy1.le
      have hmax : max (1 - 1 / y) 0 = 0 := by
        rw [max_eq_right]
        have : 1 ≤ 1 / y := (one_le_div hy).mpr hy1.le
        linarith
      rw [hmax, hh_le_zero (Real.log y) hlog_np, mul_zero, Complex.ofReal_zero]
  rw [hLHS, hRHS] at hmul
  exact hmul

private lemma integral_diff_Icc_tail {f : ℝ → ℂ} (hf : Integrable f) {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, f t) - (∫ t : ℝ, f t) =
      -((∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t)) := by
  have h1 : (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) = ∫ t in Iic T, f t := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hf.integrableOn hf.integrableOn, Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have h2 : (∫ t in Iic T, f t) + (∫ t in Ioi T, f t) = ∫ t : ℝ, f t := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hf.integrableOn hf.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  linear_combination h1 + h2

private lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioi T, (t ^ 2)⁻¹ = 1 / T := by
  have hcongr : Set.EqOn (fun t : ℝ => (t ^ 2)⁻¹) (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi T) := by
    intro t ht
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
  have hpow : T ^ (-2 + 1 : ℝ) = T⁻¹ := by
    rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow]
  field_simp [hT.ne']
  ring

private lemma integral_Iic_neg_eq_Ioi (g : ℝ → ℝ) (T : ℝ) :
    ∫ t in Iic (-T), g (-t) = ∫ t in Ioi T, g t := by
  rw [← integral_indicator measurableSet_Iic, ← MeasureTheory.integral_neg_eq_self _ volume,
    ← MeasureTheory.integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : T ≤ t
  · have h1 : -t ∈ Iic (-T) := by simp [ht]
    have h2 : t ∈ Ici T := ht
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : -t ∉ Iic (-T) := by simp [ht]
    have h2 : t ∉ Ici T := ht
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

private lemma chebyshevPsi_nonneg (x : ℝ) : 0 ≤ RHDirect.chebyshevPsi x :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem chebyshevPsi_le_six_mul {x : ℝ} (hx : 1 ≤ x) :
    RHDirect.chebyshevPsi x ≤ 6 * x := by
  have hx0 : 0 < x := by linarith
  have hpsi : RHDirect.chebyshevPsi x = Chebyshev.psi x := by
    unfold RHDirect.chebyshevPsi Chebyshev.psi
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
    simp
  rw [hpsi]
  have h1 := Chebyshev.psi_le hx
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le]; ring
    have h3 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  nlinarith

set_option maxHeartbeats 2000000 in
theorem tsum_vonMangoldt_mul_rpow_le {c : ℝ} (hc : 1 < c) :
    ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) ≤ 6 * c / (c - 1) := by
  have hc0 : 0 < c := by linarith
  have hsumm : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  refine hsumm.tsum_le_of_sum_range_le fun N => ?_
  by_cases hN : N ≤ 1
  · interval_cases N <;> simp [div_nonneg (by positivity : 0 ≤ 6 * c) (by linarith : 0 ≤ c - 1)]
  · push Not at hN
    set M : ℕ := N - 1
    have hM1 : 1 ≤ M := by omega
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have hrange : ∑ n ∈ Finset.range N, Λ n * (n : ℝ) ^ (-c) =
        ∑ n ∈ Finset.Icc 1 M, Λ n * (n : ℝ) ^ (-c) := by
      have hsub : Finset.range N = insert 0 (Finset.Icc 1 M) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      simp
    rw [hrange]
    have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet (fun n => (Λ n : ℂ)) hMR (c : ℂ)
    have hre := congrArg Complex.re hab
    have hLHS : (∑ n ∈ Finset.Icc 1 ⌊(M : ℝ)⌋₊, (Λ n : ℂ) * (n : ℂ) ^ (-(c : ℂ))).re =
        ∑ n ∈ Finset.Icc 1 M, Λ n * (n : ℝ) ^ (-c) := by
      rw [Nat.floor_natCast, Complex.re_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
      have hpow : (n : ℂ) ^ (-(c : ℂ)) = (((n : ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]; simp
      rw [hpow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hstep : ∀ t : ℝ, Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t =
        (RHDirect.chebyshevPsi t : ℂ) := fun t => by
      unfold Stage3RealAnalyticLandau.stepSum RHDirect.chebyshevPsi
      rw [Complex.ofReal_sum]
      have hsub : Finset.range (⌊t⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsub, Finset.sum_insert (by simp)]; simp
    have hMpow : ((M : ℝ) : ℂ) ^ (-(c : ℂ)) = (((M : ℝ) ^ (-c) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith)]; simp
    have hint_re : (∫ t in (1 : ℝ)..(M : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t * (t : ℂ) ^ (-(c : ℂ) - 1)).re =
        ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) := by
      have hcongr : Set.EqOn
          (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => (Λ n : ℂ)) t * (t : ℂ) ^ (-(c : ℂ) - 1))
          (fun t : ℝ => ((RHDirect.chebyshevPsi t * t ^ (-c - 1) : ℝ) : ℂ)) (Set.uIcc 1 M) := by
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hMR] at ht
        have ht0 : 0 < t := by linarith [ht.1]
        rw [hstep t, Complex.ofReal_mul]
        congr 1
        rw [Complex.ofReal_cpow ht0.le]; simp
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, Complex.ofReal_re]
    rw [hLHS, hstep M, hMpow, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.re_ofReal_mul, hint_re] at hre
    rw [hre]
    
    have hpsiM : RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c) ≤ 6 * (M : ℝ) ^ (1 - c) := by
      have h1 : RHDirect.chebyshevPsi M ≤ 6 * (M : ℝ) := chebyshevPsi_le_six_mul hMR
      have hpow : (M : ℝ) * (M : ℝ) ^ (-c) = (M : ℝ) ^ (1 - c) := by
        calc (M : ℝ) * (M : ℝ) ^ (-c) = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-c) := by rw [Real.rpow_one]
          _ = (M : ℝ) ^ (1 + -c) := (Real.rpow_add (by linarith) _ _).symm
          _ = (M : ℝ) ^ (1 - c) := by rw [sub_eq_add_neg]
      calc RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c)
          ≤ (6 * (M : ℝ)) * (M : ℝ) ^ (-c) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)
        _ = 6 * ((M : ℝ) * (M : ℝ) ^ (-c)) := by ring
        _ = 6 * (M : ℝ) ^ (1 - c) := by rw [hpow]
    have hint_le : ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) ≤
        ∫ t in (1 : ℝ)..(M : ℝ), 6 * t ^ (-c) := by
      have hint1 : IntervalIntegrable (fun t : ℝ => RHDirect.chebyshevPsi t * t ^ (-c - 1))
          volume (1 : ℝ) M := by
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hMR).mpr ?_
        refine Integrable.mono'
          (integrableOn_const (C := 6 * (M : ℝ)) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
        · have hm : Measurable RHDirect.chebyshevPsi := by
            have h : RHDirect.chebyshevPsi =
                (fun k : ℕ => ∑ n ∈ Finset.range (k + 1), Λ n) ∘ Nat.floor := rfl
            rw [h]; exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor
          exact (hm.mul (measurable_id.pow_const _)).aestronglyMeasurable
        · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
          have ht1 : 1 ≤ t := ht.1.le
          have ht0 : 0 < t := by linarith
          have hpow_le : t ^ (-c - 1) ≤ 1 := by
            calc t ^ (-c - 1) ≤ t ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
              _ = 1 := Real.rpow_zero t
          rw [Real.norm_of_nonneg (mul_nonneg (chebyshevPsi_nonneg t)
            (Real.rpow_nonneg ht0.le _))]
          calc RHDirect.chebyshevPsi t * t ^ (-c - 1)
              ≤ RHDirect.chebyshevPsi t * 1 :=
                mul_le_mul_of_nonneg_left hpow_le (chebyshevPsi_nonneg t)
            _ = RHDirect.chebyshevPsi t := mul_one _
            _ ≤ 6 * t := chebyshevPsi_le_six_mul ht1
            _ ≤ 6 * (M : ℝ) := by linarith [ht.2]
      have hint2 : IntervalIntegrable (fun t : ℝ => 6 * t ^ (-c)) volume (1 : ℝ) M := by
        have hc_cont : ContinuousOn (fun t : ℝ => 6 * t ^ (-c)) (Set.uIcc 1 M) := by
          rw [Set.uIcc_of_le hMR]
          exact continuousOn_const.mul
            (continuousOn_id.rpow_const fun t ht => Or.inl (by simp; linarith [ht.1]))
        exact hc_cont.intervalIntegrable
      refine intervalIntegral.integral_mono_on hMR hint1 hint2 fun t ht => ?_
      have ht0 : 0 < t := by linarith [ht.1]
      have hpow : t * t ^ (-c - 1) = t ^ (-c) := by
        calc t * t ^ (-c - 1) = t ^ (1 : ℝ) * t ^ (-c - 1) := by rw [Real.rpow_one]
          _ = t ^ (1 + (-c - 1)) := (Real.rpow_add ht0 _ _).symm
          _ = t ^ (-c) := by congr 1; ring
      calc RHDirect.chebyshevPsi t * t ^ (-c - 1)
          ≤ (6 * t) * t ^ (-c - 1) :=
            mul_le_mul_of_nonneg_right (chebyshevPsi_le_six_mul ht.1) (Real.rpow_nonneg ht0.le _)
        _ = 6 * (t * t ^ (-c - 1)) := by ring
        _ = 6 * t ^ (-c) := by rw [hpow]
    have hint_eval : ∫ t in (1 : ℝ)..(M : ℝ), 6 * t ^ (-c) =
        6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨by linarith, fun h => by
          rw [Set.uIcc_of_le hMR] at h; linarith [h.1]⟩)]
      rw [Real.one_rpow]
      have heq : -c + 1 = 1 - c := by ring
      rw [heq]
      field_simp [show c - 1 ≠ 0 by linarith, show 1 - c ≠ 0 by linarith]
      ring
    have hstep1 : RHDirect.chebyshevPsi M * (M : ℝ) ^ (-c) +
        c * ∫ t in (1 : ℝ)..(M : ℝ), RHDirect.chebyshevPsi t * t ^ (-c - 1) ≤
        6 * (M : ℝ) ^ (1 - c) + c * (6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1)) := by
      linarith [mul_le_mul_of_nonneg_left (hint_le.trans_eq hint_eval) hc0.le]
    have hstep2 : 6 * (M : ℝ) ^ (1 - c) + c * (6 * (1 - (M : ℝ) ^ (1 - c)) / (c - 1)) =
        6 * c / (c - 1) - 6 * (M : ℝ) ^ (1 - c) / (c - 1) := by
      field_simp [show c - 1 ≠ 0 by linarith]
      ring
    have hnn : 0 ≤ 6 * (M : ℝ) ^ (1 - c) / (c - 1) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) (by linarith)
    linarith

def psi1Char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ)

def truncatedPerronPsi1 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T,
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))

private lemma psi1Char_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ)))
      (psi1Char χ x) := by
  have hEq : ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      (if n = 0 then (0 : ℂ)
       else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ))) = psi1Char χ x := by
    unfold psi1Char
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [if_neg hn0, ← Complex.ofReal_mul]
      congr 2
      rw [mul_max_of_nonneg _ _ hx.le, mul_sub, mul_one, mul_div_cancel₀ _ hx.ne', mul_zero]
  rw [← hEq]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  have hn' : ⌊x⌋₊ + 1 ≤ n := by simpa using hn
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0]
  have hlt : x < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one x
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2; linarith
  have hmax : max (1 - (n : ℝ) / x) 0 = 0 :=
    max_eq_right (by rw [sub_nonpos, one_le_div hx]; exact hlt.le)
  rw [hmax]; simp

private lemma norm_negLogDerivL_le_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ ≤
      ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) := by
  have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
  rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
  have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsumL.norm).trans (hsumL.norm.tsum_le_tsum (fun n => ?_) hsumR)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn]
    have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hre, Real.rpow_neg hnR.le, div_eq_mul_inv]
    calc ‖χ (n : ZMod q)‖ * Λ n * ((n : ℝ) ^ c)⁻¹
        ≤ 1 * Λ n * ((n : ℝ) ^ c)⁻¹ := by
          gcongr; exact χ.norm_le_one _
      _ = Λ n * ((n : ℝ) ^ c)⁻¹ := by ring

set_option maxHeartbeats 2000000 in
theorem psi1Char_eq_perron_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    psi1Char χ x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ,
          Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
            (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
  have hc0 : 0 < c := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  
  let F : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0
    else (Λ n : ℂ) * χ n * (x : ℂ) * cesaro1Integrand (x / (n : ℝ)) c t
  have hF_int : ∀ n : ℕ, Integrable (F n) := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact (integrable_cesaro1Integrand (div_pos hx hnR) hc0).const_mul _
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  have hF_sum_norm : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      (hsumR.mul_left (x ^ (c + 1) * (Real.pi / c)))
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      calc ∫ t : ℝ, ‖(Λ n : ℂ) * χ n * (x : ℂ) * cesaro1Integrand (x / (n : ℝ)) c t‖
          ≤ ∫ t : ℝ, (Λ n * x * (x / (n : ℝ)) ^ c) * (c ^ 2 + t ^ 2)⁻¹ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_inv_sq_add_sq hc0).const_mul _) (Eventually.of_forall fun t => ?_)
            dsimp only
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_of_nonneg hx.le]
            calc Λ n * ‖χ n‖ * x * ‖cesaro1Integrand (x / (n : ℝ)) c t‖
                ≤ Λ n * 1 * x * ((x / (n : ℝ)) ^ c * (c ^ 2 + t ^ 2)⁻¹) := by
                  gcongr
                  · exact χ.norm_le_one _
                  · exact norm_cesaro1Integrand_le_inv_sq_add_sq (div_pos hx hnR) hc0 t
              _ = Λ n * x * (x / (n : ℝ)) ^ c * (c ^ 2 + t ^ 2)⁻¹ := by ring
        _ = (Λ n * x * (x / (n : ℝ)) ^ c) * (Real.pi / c) := by
            rw [integral_const_mul, integral_inv_sq_add_sq hc0]
        _ = x ^ (c + 1) * (Real.pi / c) * (Λ n * (n : ℝ) ^ (-c)) := by
            rw [Real.div_rpow hx.le hnR.le, Real.rpow_add hx, Real.rpow_one,
              Real.rpow_neg hnR.le, div_eq_mul_inv]
            ring
  
  have hswap := hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
  
  have htsum_t : ∀ t : ℝ, ∑' n : ℕ, F n t =
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
        (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))) := by
    intro t
    have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
    set W : ℂ := (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))
    have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
      χ.LSeriesSummable_twist_vonMangoldt hs
    have h1 := (hsumL.hasSum.mul_right W).tsum_eq
    rw [mul_div_assoc]
    change ∑' n : ℕ, F n t = (∑' n : ℕ, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((c : ℂ) + I * (t : ℂ)) n) * W
    rw [← h1]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term]
    · simp only [F, LSeries.term, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      unfold cesaro1Integrand
      have hpow1 : ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) := by
        have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx hnR).ne'
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
        rw [Complex.cpow_def_of_ne_zero hxnC, Complex.cpow_def_of_ne_zero hxC,
          Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_sub, ← Complex.ofReal_log (div_pos hx hnR).le,
          Real.log_div hx.ne' hnR.ne', ← Complex.ofReal_log hx.le, ← Complex.ofReal_natCast,
          ← Complex.ofReal_log hnR.le]
        congr 1; push_cast; ring
      have hpow2 : (x : ℂ) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) := by
        have hadd : (c : ℂ) + 1 + I * (t : ℂ) = 1 + ((c : ℂ) + I * (t : ℂ)) := by ring
        rw [hadd, Complex.cpow_add 1 ((c : ℂ) + I * (t : ℂ)) hxC, Complex.cpow_one]
      rw [hpow1]
      dsimp only [W]
      calc (Λ n : ℂ) * χ (n : ZMod q) * (x : ℂ) *
              ((x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
                (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))))
          = χ (n : ZMod q) * (Λ n : ℂ) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) *
              (((x : ℂ) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) /
                (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) := by ring
        _ = _ := by rw [hpow2]
  simp_rw [htsum_t] at hswap
  
  have hmul := hswap.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hterm_eq : ∀ n : ℕ, ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, F n t =
      if n = 0 then (0 : ℂ)
      else (Λ n : ℂ) * χ n * ((x : ℂ) * ((max (1 - (n : ℝ) / x) 0 : ℝ) : ℂ)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [integral_const_mul, mul_left_comm]
      change (Λ n : ℂ) * χ n * (x : ℂ) * perronKernel1Full (x / (n : ℝ)) c = _
      rw [perronKernel1Full_eq_max (div_pos hx hnR) hc0]
      have hdiv : 1 / (x / (n : ℝ)) = (n : ℝ) / x := by field_simp [hx.ne', hnR.ne']
      rw [hdiv]
      ring
  have hsum1 := hmul.congr_fun fun n => (hterm_eq n).symm
  exact (psi1Char_hasSum χ hx).unique hsum1

set_option maxHeartbeats 2000000 in
theorem norm_psi1Char_sub_truncatedPerron_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    ‖psi1Char χ x - truncatedPerronPsi1 χ x c T‖ ≤
      (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T) := by
  have hc0 : 0 < c := by linarith
  set f : ℝ → ℂ := fun t =>
    Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
      (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))
  set S : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c)
  have hS_nn : 0 ≤ S := tsum_nonneg fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hS_le : S ≤ 6 * c / (c - 1) := tsum_vonMangoldt_mul_rpow_le hc
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcont : Continuous f := by
      dsimp only [f]
      have hL : Continuous (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
        have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} := by
          intro s hs
          have hs1 : s ≠ 1 := fun h => by subst h; simp at hs
          exact (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs1)).differentiableWithinAt
        have hcontL : ContinuousOn (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} :=
          hdiff.continuousOn
        have hcontL' : ContinuousOn (deriv (DirichletCharacter.LFunction χ)) {s : ℂ | 1 < s.re} :=
          (hdiff.deriv hopen).continuousOn
        have hmap : Continuous (fun t : ℝ => (c : ℂ) + I * (t : ℂ)) := by fun_prop
        have hmem : ∀ t : ℝ, ((c : ℂ) + I * (t : ℂ)) ∈ {s : ℂ | 1 < s.re} := fun t => by simp [hc]
        refine (hcontL'.comp_continuous hmap hmem).neg.div (hcontL.comp_continuous hmap hmem) fun t => ?_
        have hs1 : (c : ℂ) + I * (t : ℂ) ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr hs1) (by simp [hc.le])
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) := by
        have hEq : (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * ((c : ℂ) + 1 + I * (t : ℂ))) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hL.mul hpow).div (by fun_prop) fun t => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    exact hcont.aestronglyMeasurable
  have hf_norm_all : ∀ t : ℝ, ‖f t‖ ≤ (S * x ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
    intro t
    dsimp only [f]
    have hre : ((c : ℂ) + 1 + I * (t : ℂ)).re = c + 1 := by simp
    have h0 := norm_cesaro1Integrand_le_inv_sq_add_sq one_pos hc0 t
    have hden : ‖(1 : ℂ) / (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))‖ ≤
        (c ^ 2 + t ^ 2)⁻¹ := by
      simpa [cesaro1Integrand, Complex.one_cpow] using h0
    rw [mul_div_assoc, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    have hden' : x ^ (c + 1) / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))‖ ≤
        x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx.le _)
      simpa [norm_div, norm_one, one_div] using hden
    calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ *
            (x ^ (c + 1) / ‖((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ))‖)
        ≤ S * (x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹) :=
          mul_le_mul (norm_negLogDerivL_le_tsum χ hc t) hden' (by positivity) hS_nn
      _ = S * x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by ring
  have hf_int : Integrable f :=
    ((integrable_inv_sq_add_sq hc0).const_mul (S * x ^ (c + 1))).mono' hf_meas
      (Eventually.of_forall hf_norm_all)
  have hf_norm_t : ∀ t : ℝ, t ≠ 0 → ‖f t‖ ≤ S * x ^ (c + 1) / t ^ 2 := by
    intro t ht
    have h1 := hf_norm_all t
    have h2 : (c ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_ne_zero ht) (by linarith [sq_nonneg c])
    calc ‖f t‖ ≤ S * x ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := h1
      _ ≤ S * x ^ (c + 1) * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = S * x ^ (c + 1) / t ^ 2 := by rw [div_eq_mul_inv]
  rw [psi1Char_eq_perron_integral χ hx hc]
  unfold truncatedPerronPsi1
  change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, f t) -
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, f t)‖ ≤ _
  rw [← mul_sub, ← neg_sub (∫ t in (-T)..T, f t), integral_diff_Icc_tail hf_int hT, neg_neg,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_sq : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / t ^ 2) (Ioi T) := by
    have h1 : IntegrableOn (fun t : ℝ => (S * x ^ (c + 1)) * t ^ (-2 : ℝ)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul (S * x ^ (c + 1))
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have hpos_tail : ‖∫ t in Ioi T, f t‖ ≤ S * x ^ (c + 1) / T := by
    calc ‖∫ t in Ioi T, f t‖ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, S * x ^ (c + 1) / t ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq measurableSet_Ioi fun t ht =>
            hf_norm_t t (hT.trans ht).ne'
      _ = S * x ^ (c + 1) / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  have hint_sq_neg : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / (-t) ^ 2) (Iic (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / t ^ 2) (Ici T) :=
      hint_sq.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun t : ℝ => S * x ^ (c + 1) / (-t) ^ 2) (Neg.neg ⁻¹' Ici T) := h1.comp_neg
    have hset : Neg.neg ⁻¹' Ici T = Iic (-T) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rwa [hset] at h2
  have hneg_tail : ‖∫ t in Iic (-T), f t‖ ≤ S * x ^ (c + 1) / T := by
    calc ‖∫ t in Iic (-T), f t‖ ≤ ∫ t in Iic (-T), ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Iic (-T), S * x ^ (c + 1) / (-t) ^ 2 :=
          setIntegral_mono_on hf_int.integrableOn.norm hint_sq_neg measurableSet_Iic fun t ht => by
            have ht0 : t ≠ 0 := by linarith [Set.mem_Iic.mp ht]
            simpa [neg_sq] using hf_norm_t t ht0
      _ = ∫ t in Ioi T, S * x ^ (c + 1) / t ^ 2 :=
          integral_Iic_neg_eq_Ioi (fun u => S * x ^ (c + 1) / u ^ 2) T
      _ = S * x ^ (c + 1) / T := by
          simp_rw [div_eq_mul_inv]; rw [integral_const_mul, integral_Ioi_inv_sq hT]; ring
  calc (2 * Real.pi)⁻¹ * ‖(∫ t in Iic (-T), f t) + (∫ t in Ioi T, f t)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * (S * x ^ (c + 1) / T)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (by positivity)
    _ = S * x ^ (c + 1) / (Real.pi * T) := by field_simp [Real.pi_ne_zero, hT.ne']
    _ ≤ (6 * c / (c - 1)) * x ^ (c + 1) / (Real.pi * T) := by gcongr
    _ = (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T) := by
        field_simp [Real.pi_ne_zero, hT.ne', show c - 1 ≠ 0 by linarith]

end RHDirect.Stage4ExplicitFormula

end

/-! ## From RHDirect/Stage5ZetaZeroFree.lean -/

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage5ZetaZeroFree

theorem borelCaratheodory_sub_center {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re) := by
  have hz_ball : z - z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hrR
  have hz₀_mem : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
  have hA_nonneg : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ hz₀_mem)
  set g : ℂ → ℂ := fun w => f (z₀ + w) - f z₀
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
    refine (hf.comp (differentiableOn_const z₀ |>.fun_add differentiableOn_id) ?_).sub
      (differentiableOn_const (f z₀))
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hg0 : g 0 = 0 := by simp [g]
  
  have hε : ∀ ε : ℝ, 0 < ε →
      ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
    intro ε hε0
    have hM' : 0 < M - (f z₀).re + ε := by linarith
    have hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M - (f z₀).re + ε} := by
      intro w hw
      have hw' : z₀ + w ∈ Metric.ball z₀ R := by
        rw [Metric.mem_ball, dist_zero_right] at hw
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hw
      show (f (z₀ + w) - f z₀).re ≤ M - (f z₀).re + ε
      rw [Complex.sub_re]
      linarith [hre (z₀ + w) hw']
    have hbc := Complex.borelCaratheodory_zero hM' hg_diff hmaps hR hz_ball hg0
    have hgz : g (z - z₀) = f z - f z₀ := by simp [g]
    rw [hgz] at hbc
    have hmono : 2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤
        (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
      have hden1 : 0 < R - ‖z - z₀‖ := by linarith
      have hden2 : 0 < R - r := by linarith
      have h1 : ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ r / (R - r) := by
        rw [div_le_div_iff₀ hden1 hden2]
        nlinarith [norm_nonneg (z - z₀)]
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * (M - (f z₀).re + ε))
      linarith [show 2 * (M - (f z₀).re + ε) * (‖z - z₀‖ / (R - ‖z - z₀‖)) =
          2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) by ring,
        show 2 * (M - (f z₀).re + ε) * (r / (R - r)) =
          (2 * r / (R - r)) * (M - (f z₀).re + ε) by ring]
    exact hbc.trans hmono
  
  by_contra hlt
  push Not at hlt
  set gap : ℝ := ‖f z - f z₀‖ - (2 * r / (R - r)) * (M - (f z₀).re)
  have hgap : 0 < gap := sub_pos.mpr hlt
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg (z - z₀)) hz
  have hcoeff_nonneg : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  set ε : ℝ := gap / (2 * (2 * r / (R - r) + 1))
  have hε0 : 0 < ε := by positivity
  have hbd := hε ε hε0
  have hmul : (2 * r / (R - r)) * ε ≤ gap / 2 := by
    dsimp only [ε]
    have hden : 0 < 2 * (2 * r / (R - r) + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hden two_pos]
    nlinarith
  linarith [show (2 * r / (R - r)) * (M - (f z₀).re + ε) =
      (2 * r / (R - r)) * (M - (f z₀).re) + (2 * r / (R - r)) * ε by ring]

theorem borelCaratheodory_deriv_at_center {f : ℂ → ℂ} {z₀ : ℂ} {M R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) :
    ‖deriv f z₀‖ ≤ (2 / R) * (M - (f z₀).re) := by
  have hd : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (Metric.ball_mem_nhds z₀ hR)).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => ‖(f (z₀ + (t : ℂ)) - f z₀) / (t : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖deriv f z₀‖) := by
    have h1 : Tendsto (fun w : ℂ => (f (z₀ + w) - f z₀) / w) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv f z₀)) := by
      have hs := hd.tendsto_slope_zero
      refine hs.congr' (Eventually.of_forall fun w => ?_)
      simp [div_eq_inv_mul]
    have h2 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    exact (h1.comp h2).norm
  have hlim_rhs : Tendsto (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / R) * (M - (f z₀).re))) := by
    have hcont : ContinuousAt (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re)) 0 := by
      have hsub : ContinuousAt (fun t : ℝ => R - t) 0 := continuousAt_const.sub continuousAt_id
      have hne : R - (0 : ℝ) ≠ 0 := by simpa using hR.ne'
      exact ((continuousAt_const.div hsub hne).mul continuousAt_const)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlim hlim_rhs ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with t ht
  have ht0 : 0 < t := ht.1
  have htR : t < R := ht.2
  have hbc := borelCaratheodory_sub_center hR htR hf hre
    (z := z₀ + (t : ℂ)) (r := t) (by simp [Real.norm_of_nonneg ht0.le])
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le, div_le_iff₀ ht0]
  have hmul : (2 / (R - t)) * (M - (f z₀).re) * t = (2 * t / (R - t)) * (M - (f z₀).re) := by
    ring
  linarith

private lemma circleIntegral_sub_sq_inv_mul_eq_deriv {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hw : w ∈ Metric.ball c R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) :
    ∮ z in C(c, R), (z - w)⁻¹ ^ 2 * f z = (2 * Real.pi * I) * deriv f w := by
  have hmem_nhds : Metric.closedBall c R ∈ 𝓝 w :=
    Filter.mem_of_superset (Metric.ball_mem_nhds w (sub_pos.mpr (Metric.mem_ball.mp hw)))
      (fun x hx => by
        rw [Metric.mem_closedBall]
        exact le_of_lt (lt_of_le_of_lt (dist_triangle x w c) (by
          rw [Metric.mem_ball] at hx
          linarith)))
  have hds_diff : DifferentiableOn ℂ (dslope f w) (Metric.closedBall c R) :=
    (Complex.differentiableOn_dslope hmem_nhds).mpr hf
  have hds_dc : DiffContOnCl ℂ (dslope f w) (Metric.ball c R) := by
    refine ⟨hds_diff.mono Metric.ball_subset_closedBall, ?_⟩
    rw [closure_ball c hR.ne']
    exact hds_diff.continuousOn
  have hcauchy := hds_dc.circleIntegral_sub_inv_smul hw
  rw [dslope_same] at hcauchy
  
  have hzero : ∮ z in C(c, R), (z - w)⁻¹ ^ 2 * f w = 0 := by
    unfold circleIntegral
    have hcm_ne : ∀ θ : ℝ, circleMap c R θ - w ≠ 0 := by
      intro θ h0
      have heq : circleMap c R θ = w := sub_eq_zero.mp h0
      have hdist : dist w c = R := by
        rw [← heq]
        exact Metric.mem_sphere.mp (circleMap_mem_sphere c hR.le θ)
      exact (Metric.mem_ball.mp hw).ne hdist
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => -(circleMap c R t - w)⁻¹ * f w)
          (deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ ^ 2 * f w)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => circleMap c R t - w) (deriv (circleMap c R) θ) θ := by
        rw [deriv_circleMap]
        exact (hasDerivAt_circleMap c R θ).sub_const w
      have h2 := (h1.inv (hcm_ne θ)).neg.mul_const (f w)
      refine h2.congr_deriv ?_
      rw [smul_eq_mul]
      field_simp [hcm_ne θ]
    have hcont : ContinuousOn (fun θ : ℝ =>
        deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ ^ 2 * f w))
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
      have hEq : (fun θ : ℝ => deriv (circleMap c R) θ) = fun θ => circleMap 0 R θ * I := by
        funext θ; exact deriv_circleMap c R θ
      have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap c R) θ) (Set.uIcc 0 (2 * Real.pi)) := by
        rw [hEq]; exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => (circleMap c R θ - w)⁻¹ ^ 2 * f w)
          (Set.uIcc 0 (2 * Real.pi)) :=
        ((ContinuousOn.inv₀ ((continuous_circleMap c R).continuousOn.sub continuousOn_const)
          (fun θ _ => hcm_ne θ)).pow 2).mul continuousOn_const
      exact h1.smul h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have h2pi : circleMap c R (2 * Real.pi) = circleMap c R 0 := by
      simp [circleMap, Complex.exp_two_pi_mul_I]
    rw [h2pi, sub_self]
  have hcongr : EqOn (fun z : ℂ => (z - w)⁻¹ • dslope f w z)
      (fun z : ℂ => (z - w)⁻¹ ^ 2 * f z - (z - w)⁻¹ ^ 2 * f w) (Metric.sphere c R) := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    have hzw : z ≠ w := by
      intro h; subst h; exact (Metric.mem_ball.mp hw).ne hz
    dsimp only
    rw [dslope_of_ne f hzw, slope_def_field, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hzw]
  have hint1 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ ^ 2 * f z) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ((ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_).pow 2).mul
      (hf.continuousOn.mono Metric.sphere_subset_closedBall)
    rw [Metric.mem_sphere] at hz
    intro h; have heq : z = w := sub_eq_zero.mp h; subst heq; exact (Metric.mem_ball.mp hw).ne hz
  have hint2 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ ^ 2 * f w) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ((ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_).pow 2).mul
      continuousOn_const
    rw [Metric.mem_sphere] at hz
    intro h; have heq : z = w := sub_eq_zero.mp h; subst heq; exact (Metric.mem_ball.mp hw).ne hz
  have hsub := circleIntegral.integral_sub hint1 hint2
  rw [hzero, sub_zero] at hsub
  rw [← hsub, ← circleIntegral.integral_congr hR.le hcongr]
  simpa [smul_eq_mul] using hcauchy

set_option maxHeartbeats 2000000 in
theorem borelCaratheodory_deriv_le {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ R))
    (hre : ∀ ζ ∈ Metric.closedBall z₀ R, (f ζ).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖deriv f z‖ ≤ (2 * R / (R - r) ^ 2) * (M - (f z₀).re) := by
  have hz_ball : z ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hz hrR
  set w : ℂ := z - z₀ with hw_def
  have hw_norm : ‖w‖ ≤ r := hz
  have hw_lt : ‖w‖ < R := lt_of_le_of_lt hz hrR
  
  have hcauchy := circleIntegral_sub_sq_inv_mul_eq_deriv hR hz_ball hf

  have hden_ne : ∀ ζ ∈ Metric.closedBall z₀ R,
      (R : ℂ) ^ 2 - starRingEnd ℂ w * (ζ - z₀) ≠ 0 := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    intro h0
    have heq : (R : ℂ) ^ 2 = starRingEnd ℂ w * (ζ - z₀) := sub_eq_zero.mp h0
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at hn
    have hlt : ‖w‖ * ‖ζ - z₀‖ < R ^ 2 := by nlinarith [norm_nonneg w, norm_nonneg (ζ - z₀)]
    linarith
  have hconj_zero :
      ∮ ζ in C(z₀, R), f ζ * (R : ℂ) ^ 2 * ((R : ℂ) ^ 2 - starRingEnd ℂ w * (ζ - z₀))⁻¹ ^ 2 = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty ?_ ?_
    · refine (hf.continuousOn.mul continuousOn_const).mul ?_
      refine (ContinuousOn.inv₀ (continuousOn_const.sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
        (fun ζ hζ => hden_ne ζ hζ)).pow 2
    · intro ζ hζ
      have hζ_ball : ζ ∈ Metric.ball z₀ R := hζ.1
      have hζ_cb : ζ ∈ Metric.closedBall z₀ R := Metric.ball_subset_closedBall hζ_ball
      have hf_at : DifferentiableAt ℂ f ζ :=
        (hf.mono Metric.ball_subset_closedBall).differentiableAt (Metric.isOpen_ball.mem_nhds hζ_ball)
      have hden_at : DifferentiableAt ℂ
          (fun u : ℂ => (R : ℂ) ^ 2 - starRingEnd ℂ w * (u - z₀)) ζ :=
        (differentiableAt_const _).sub
          ((differentiableAt_const _).mul ((differentiableAt_id).sub (differentiableAt_const _)))
      exact (hf_at.mul (differentiableAt_const _)).mul ((hden_at.inv (hden_ne ζ hζ_cb)).pow 2)
  
  have hM_zero : ∮ ζ in C(z₀, R), (ζ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ) = 0 := by
    have hconst := circleIntegral_sub_sq_inv_mul_eq_deriv (f := fun _ => ((2 * M : ℝ) : ℂ))
      hR hz_ball (differentiableOn_const _)
    simpa [deriv_const] using hconst
  
  have hmean := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
    hR Set.countable_empty hf.continuousOn
    (fun ζ hζ => (hf.mono Metric.ball_subset_closedBall).differentiableAt
      (Metric.isOpen_ball.mem_nhds hζ.1))
  
  unfold circleIntegral at hcauchy hconj_zero hM_zero hmean
  
  have hkern_conj : ∀ θ : ℝ,
      starRingEnd ℂ (deriv (circleMap z₀ R) θ *
        (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
          ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)) =
      -(deriv (circleMap z₀ R) θ *
        ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) := by
    intro θ
    set e : ℂ := cexp ((θ : ℂ) * I) with he_def
    have he_ne : e ≠ 0 := Complex.exp_ne_zero _
    have he_conj : starRingEnd ℂ e = e⁻¹ := by
      rw [he_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        Complex.exp_neg]
    have hcm : circleMap z₀ R θ - z₀ = (R : ℂ) * e := by simp [circleMap, he_def]
    have hcm_z : circleMap z₀ R θ - z = (R : ℂ) * e - w := by
      rw [hw_def]; simp [circleMap, he_def]; ring
    have hdcm : deriv (circleMap z₀ R) θ = (R : ℂ) * e * I := by
      rw [deriv_circleMap, circleMap, zero_add, he_def]
    have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hsub_ne : (R : ℂ) * e - w ≠ 0 := by
      intro h0
      have h1 : (R : ℂ) * e = w := sub_eq_zero.mp h0
      have hn := congrArg norm h1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, he_def,
        Complex.norm_exp_ofReal_mul_I, mul_one] at hn
      linarith
    rw [hcm, hcm_z, hdcm, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
      map_inv₀, map_sub, map_pow, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
      he_conj, Complex.conj_conj]
    have hfac : (R : ℂ) ^ 2 - w * ((R : ℂ) * e⁻¹) = (R : ℂ) * e⁻¹ * ((R : ℂ) * e - w) := by
      field_simp [he_ne]
    rw [hfac]
    field_simp [hRne, he_ne, hsub_ne]
  
  have hconj_int :
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ *
          ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))) = 0 := by
    have hint_conj : IntervalIntegrable (fun θ : ℝ =>
        deriv (circleMap z₀ R) θ *
          (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
            ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2))
        volume 0 (2 * Real.pi) := by
      have h1 : ContinuousOn (fun θ : ℝ => deriv (circleMap z₀ R) θ) (Set.uIcc 0 (2 * Real.pi)) := by
        have hEq : (fun θ : ℝ => deriv (circleMap z₀ R) θ) = fun θ => circleMap 0 R θ * I := by
          funext θ; exact deriv_circleMap z₀ R θ
        rw [hEq]; exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => f (circleMap z₀ R θ) * (R : ℂ) ^ 2)
          (Set.uIcc 0 (2 * Real.pi)) :=
        (hf.continuousOn.comp (continuous_circleMap z₀ R).continuousOn
          (fun θ _ => Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))).mul
          continuousOn_const
      have h3 : ContinuousOn (fun θ : ℝ =>
          ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)
          (Set.uIcc 0 (2 * Real.pi)) := by
        refine (ContinuousOn.inv₀ (continuousOn_const.sub (continuousOn_const.mul
          ((continuous_circleMap z₀ R).continuousOn.sub continuousOn_const))) fun θ _ => ?_).pow 2
        exact hden_ne _ (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))
      exact (h1.mul (h2.mul h3)).intervalIntegrable
    have h1 : starRingEnd ℂ (∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ *
          (f (circleMap z₀ R θ) * (R : ℂ) ^ 2 *
            ((R : ℂ) ^ 2 - starRingEnd ℂ w * (circleMap z₀ R θ - z₀))⁻¹ ^ 2)) = 0 := by
      simpa [smul_eq_mul] using congrArg (starRingEnd ℂ) hconj_zero
    rw [← Complex.conjCLE_apply, ← ContinuousLinearEquiv.coe_coe,
      ← Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_conj] at h1
    have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        -(deriv (circleMap z₀ R) θ *
          ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) = 0 := by
      refine Eq.trans ?_ h1
      refine intervalIntegral.integral_congr fun θ _ => (hkern_conj θ).symm
    rw [intervalIntegral.integral_neg] at h2
    exact neg_eq_zero.mp h2
  
  have hcont_f : ContinuousOn (fun θ : ℝ => f (circleMap z₀ R θ)) (Set.uIcc 0 (2 * Real.pi)) :=
    hf.continuousOn.comp (continuous_circleMap z₀ R).continuousOn
      (fun θ _ => Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ))
  have hcont_kern : ContinuousOn (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2) (Set.uIcc 0 (2 * Real.pi)) := by
    refine ContinuousOn.mul ?_ ?_
    · show ContinuousOn (fun θ : ℝ => deriv (circleMap z₀ R) θ) (Set.uIcc 0 (2 * Real.pi))
      have hEq : (fun θ : ℝ => deriv (circleMap z₀ R) θ) = fun θ => circleMap 0 R θ * I := by
        funext θ; exact deriv_circleMap z₀ R θ
      rw [hEq]
      exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn
    · refine (ContinuousOn.inv₀ ((continuous_circleMap z₀ R).continuousOn.sub continuousOn_const)
        fun θ _ => ?_).pow 2
      intro h0
      have h1 : circleMap z₀ R θ = z := sub_eq_zero.mp h0
      have h2 : dist z z₀ = R := by
        rw [← h1]
        exact Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hR.le θ)
      rw [Metric.mem_ball] at hz_ball
      linarith
  have hint_f : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ)))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul hcont_f).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply]; ring
  have hint_fc : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul (Complex.continuous_conj.comp_continuousOn hcont_f)).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply, Function.comp]; ring
  have hint_M : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ)))
      volume 0 (2 * Real.pi) := by
    have h := (hcont_kern.mul (continuousOn_const (c := ((2 * M : ℝ) : ℂ)))).intervalIntegrable (μ := volume)
    refine h.congr fun θ _ => ?_
    dsimp [Pi.mul_apply]; ring
  have hcomb : (2 * Real.pi * I) * deriv f z =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
          (((2 * ((f (circleMap z₀ R θ)).re - M) : ℝ) : ℂ)) := by
    have h1 : (2 * Real.pi * I) * deriv f z =
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ))) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ)))) -
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ))) := by
      simp only [smul_eq_mul] at hcauchy hM_zero
      rw [hcauchy, hconj_int, hM_zero]
      ring
    rw [h1, ← intervalIntegral.integral_add hint_f hint_fc,
      ← intervalIntegral.integral_sub (hint_f.add hint_fc) hint_M]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hre_sum : f (circleMap z₀ R θ) + starRingEnd ℂ (f (circleMap z₀ R θ)) =
        (((2 * (f (circleMap z₀ R θ)).re : ℝ) : ℂ)) := by
      simpa using Complex.add_conj (f (circleMap z₀ R θ))
    calc deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * f (circleMap z₀ R θ)) +
            deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * starRingEnd ℂ (f (circleMap z₀ R θ))) -
            deriv (circleMap z₀ R) θ * ((circleMap z₀ R θ - z)⁻¹ ^ 2 * ((2 * M : ℝ) : ℂ))
        = deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
            (f (circleMap z₀ R θ) + starRingEnd ℂ (f (circleMap z₀ R θ)) - ((2 * M : ℝ) : ℂ)) := by
          ring
      _ = deriv (circleMap z₀ R) θ * (circleMap z₀ R θ - z)⁻¹ ^ 2 *
            (((2 * ((f (circleMap z₀ R θ)).re - M) : ℝ) : ℂ)) := by
          rw [hre_sum]; push_cast; ring
  
  have hmean_re :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (M - (f (circleMap z₀ R θ)).re) =
        2 * Real.pi * (M - (f z₀).re) := by
    have hsimpl : ∀ θ : ℝ,
        deriv (circleMap z₀ R) θ • ((circleMap z₀ R θ - z₀)⁻¹ • f (circleMap z₀ R θ)) =
          I * f (circleMap z₀ R θ) := by
      intro θ
      rw [deriv_circleMap, smul_eq_mul, smul_eq_mul]
      have h1 : circleMap z₀ R θ - z₀ = circleMap 0 R θ := by simp [circleMap]
      have hne : circleMap 0 R θ ≠ 0 := by
        simp [circleMap, hR.ne', Complex.exp_ne_zero]
      rw [h1]
      field_simp [hne]
    have hmean2 : I * ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap z₀ R θ) =
        (2 * Real.pi * I) * f z₀ := by
      rw [← intervalIntegral.integral_const_mul]
      have hEq : ∫ θ in (0 : ℝ)..(2 * Real.pi), I * f (circleMap z₀ R θ) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap z₀ R) θ • ((circleMap z₀ R θ - z₀)⁻¹ • f (circleMap z₀ R θ)) :=
        intervalIntegral.integral_congr fun θ _ => (hsimpl θ).symm
      rw [hEq]
      simpa [smul_eq_mul] using hmean
    have hmean3 : ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap z₀ R θ) =
        ((2 * Real.pi : ℝ) : ℂ) * f z₀ := by
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      apply mul_left_cancel₀ hI
      rw [hmean2]; push_cast; ring
    have hre_int : ∫ θ in (0 : ℝ)..(2 * Real.pi), (f (circleMap z₀ R θ)).re =
        2 * Real.pi * (f z₀).re := by
      have h1 := congrArg Complex.re hmean3
      rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hcont_f.intervalIntegrable] at h1
      simpa [Complex.reCLM_apply] using h1
    have hint_re : IntervalIntegrable (fun θ : ℝ => (f (circleMap z₀ R θ)).re)
        volume 0 (2 * Real.pi) :=
      (Complex.continuous_re.comp_continuousOn hcont_f).intervalIntegrable
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint_re,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, hre_int]
    ring
  
  have hnorm_lhs : ‖(2 * Real.pi * I) * deriv f z‖ = (2 * Real.pi) * ‖deriv f z‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hRr_pos : 0 < R - r := by linarith
  have hnorm_bound :
      (2 * Real.pi) * ‖deriv f z‖ ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (2 * R / (R - r) ^ 2) * (M - (f (circleMap z₀ R θ)).re) := by
    rw [← hnorm_lhs, hcomb]
    refine (intervalIntegral.norm_integral_le_integral_norm h2pi_pos.le).trans ?_
    refine intervalIntegral.integral_mono_on h2pi_pos.le ?_ ?_ fun θ _ => ?_
    · exact ((hcont_kern.mul (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hcont_f).sub
          continuousOn_const)))).norm).intervalIntegrable
    · exact (continuousOn_const.mul (continuousOn_const.sub
        (Complex.continuous_re.comp_continuousOn hcont_f))).intervalIntegrable
    · have hmem : circleMap z₀ R θ ∈ Metric.closedBall z₀ R :=
        Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hR.le θ)
      have hMge : 0 ≤ M - (f (circleMap z₀ R θ)).re := sub_nonneg.mpr (hre _ hmem)
      have hdist : R - r ≤ ‖circleMap z₀ R θ - z‖ := by
        have htri : ‖circleMap z₀ R θ - z₀‖ ≤ ‖circleMap z₀ R θ - z‖ + ‖z - z₀‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (circleMap z₀ R θ - z) (z - z₀)
        have hnormR : ‖circleMap z₀ R θ - z₀‖ = R := by
          simpa [dist_eq_norm] using Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hR.le θ)
        linarith
      have hd_norm : ‖deriv (circleMap z₀ R) θ‖ = R := by
        rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one]
        simpa [dist_eq_norm] using Metric.mem_sphere.mp (circleMap_mem_sphere (0 : ℂ) hR.le θ)
      rw [norm_mul, norm_mul, norm_pow, norm_inv, hd_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos two_pos, abs_sub_comm, abs_of_nonneg hMge]
      have hinv_le : (‖circleMap z₀ R θ - z‖)⁻¹ ^ 2 ≤ ((R - r) ^ 2)⁻¹ := by
        rw [← inv_pow]
        simpa [inv_pow] using inv_anti₀ (sq_pos_of_pos hRr_pos) (pow_le_pow_left₀ hRr_pos.le hdist 2)
      calc R * (‖circleMap z₀ R θ - z‖)⁻¹ ^ 2 * (2 * (M - (f (circleMap z₀ R θ)).re))
          ≤ R * ((R - r) ^ 2)⁻¹ * (2 * (M - (f (circleMap z₀ R θ)).re)) := by
            gcongr
        _ = 2 * R / (R - r) ^ 2 * (M - (f (circleMap z₀ R θ)).re) := by ring
  rw [intervalIntegral.integral_const_mul, hmean_re] at hnorm_bound
  have hfinal : (2 * Real.pi) * ‖deriv f z‖ ≤
      (2 * Real.pi) * ((2 * R / (R - r) ^ 2) * (M - (f z₀).re)) := by
    linarith
  exact le_of_mul_le_mul_left hfinal h2pi_pos

def blaschkeFactor (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ :=
  (R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))

lemma blaschkeFactor_denom_ne_zero {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : ‖z - s₀‖ ≤ R) :
    (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀) ≠ 0 := by
  intro h0
  have heq : (R : ℂ) ^ 2 = starRingEnd ℂ (ρ - s₀) * (z - s₀) := sub_eq_zero.mp h0
  have hn := congrArg norm heq
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at hn
  have hlt : ‖ρ - s₀‖ * ‖z - s₀‖ < R ^ 2 := by nlinarith [norm_nonneg (ρ - s₀), norm_nonneg (z - s₀)]
  linarith

theorem blaschkeFactor_norm_eq_one_on_sphere {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : z ∈ Metric.sphere s₀ R) :
    ‖blaschkeFactor s₀ R ρ z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hden := blaschkeFactor_denom_ne_zero hR hρ hz.le
  unfold blaschkeFactor
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  
  have hsq : ‖(R : ℂ) * (z - ρ)‖ ^ 2 = ‖(R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    set a : ℂ := ρ - s₀
    set w : ℂ := z - s₀
    have hzr : z - ρ = w - a := by simp [a, w]
    have hw_sq : Complex.normSq w = R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hz]
    rw [hzr, map_mul, Complex.normSq_ofReal]
    have h1 : Complex.normSq (w - a) = Complex.normSq w - 2 * (w * starRingEnd ℂ a).re + Complex.normSq a := by
      rw [Complex.normSq_sub, Complex.normSq_apply, Complex.normSq_apply]
      simp [Complex.mul_re]; ring
    have h2 : Complex.normSq ((R : ℂ) ^ 2 - starRingEnd ℂ a * w) =
        R ^ 4 - 2 * R ^ 2 * (w * starRingEnd ℂ a).re + Complex.normSq a * Complex.normSq w := by
      rw [Complex.normSq_sub, map_pow, Complex.normSq_ofReal, map_mul, Complex.normSq_conj]
      have hre : ((R : ℂ) ^ 2 * starRingEnd ℂ (starRingEnd ℂ a * w)).re =
          R ^ 2 * (w * starRingEnd ℂ a).re := by
        rw [map_mul, Complex.conj_conj]
        have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [hR2, Complex.re_ofReal_mul]
        have hconj : (a * starRingEnd ℂ w).re = (w * starRingEnd ℂ a).re := by
          have := Complex.conj_re (a * starRingEnd ℂ w)
          rw [map_mul, Complex.conj_conj, mul_comm] at this
          exact this.symm
        rw [hconj]
      rw [hre]; ring
    rw [h1, h2, hw_sq]; ring
  nlinarith [norm_nonneg ((R : ℂ) * (z - ρ)),
    norm_nonneg ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))]

theorem blaschkeFactor_eval_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    blaschkeFactor s₀ R ρ s₀ = -(ρ - s₀) / (R : ℂ) := by
  unfold blaschkeFactor
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

theorem blaschkeFactor_norm_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    ‖blaschkeFactor s₀ R ρ s₀‖ = ‖ρ - s₀‖ / R := by
  rw [blaschkeFactor_eval_center hR, norm_div, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hR.le]

theorem blaschkeFactor_hasDerivAt_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    HasDerivAt (blaschkeFactor s₀ R ρ)
      (1 / (R : ℂ) - (ρ - s₀) * starRingEnd ℂ (ρ - s₀) / (R : ℂ) ^ 3) s₀ := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hnum : HasDerivAt (fun z : ℂ => (R : ℂ) * (z - ρ)) (R : ℂ) s₀ := by
    simpa using ((hasDerivAt_id s₀).sub_const ρ).const_mul (R : ℂ)
  have hden : HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))
      (-(starRingEnd ℂ (ρ - s₀))) s₀ := by
    have h1 := ((hasDerivAt_id s₀).sub_const s₀).const_mul (starRingEnd ℂ (ρ - s₀))
    simpa using (hasDerivAt_const s₀ ((R : ℂ) ^ 2)).fun_sub h1
  have hden_ne : (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (s₀ - s₀) ≠ 0 := by
    simp [pow_ne_zero 2 hRne]
  refine (hnum.div hden hden_ne).congr_deriv ?_
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

theorem blaschkeFactor_logDeriv_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀ =
      1 / (s₀ - ρ) - starRingEnd ℂ (s₀ - ρ) / (R : ℂ) ^ 2 := by
  rw [(blaschkeFactor_hasDerivAt_center hR).deriv, blaschkeFactor_eval_center hR]
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hsub : s₀ - ρ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hsub' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hneg : starRingEnd ℂ (ρ - s₀) = -starRingEnd ℂ (s₀ - ρ) := by
    rw [← map_neg]; congr 1; ring
  rw [hneg]
  field_simp [hRne, hsub, hsub']
  ring

theorem blaschkeFactor_logDeriv_center_re {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re =
      (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2) := by
  rw [blaschkeFactor_logDeriv_center hR hne, Complex.sub_re, one_div, Complex.inv_re,
    Complex.normSq_eq_norm_sq]
  have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hR2, Complex.div_ofReal_re, Complex.conj_re]
  ring

lemma blaschkeFactor_logDeriv_center_re_nonneg {s₀ ρ : ℂ} {R : ℝ}
    (hR : 0 < R) (hne : ρ ≠ s₀) (hρR : ‖ρ - s₀‖ < R) (hre : ρ.re ≤ s₀.re) :
    0 ≤ (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re := by
  rw [blaschkeFactor_logDeriv_center_re hR hne]
  have hpos : 0 < ‖s₀ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hnorm_lt : ‖s₀ - ρ‖ < R := by rwa [norm_sub_rev]
  have h1 : 1 / R ^ 2 ≤ 1 / ‖s₀ - ρ‖ ^ 2 := by
    rw [one_div, one_div]
    exact inv_anti₀ (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hnorm_lt.le 2)
  exact mul_nonneg (by simp [hre]) (sub_nonneg.mpr h1)

set_option maxHeartbeats 2000000 in
theorem exists_blaschke_factorization {g : ℂ → ℂ} {s₀ : ℂ} {R r M₀ : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hM₀ : ∀ z ∈ Metric.sphere s₀ R, ‖g z‖ ≤ M₀) :
    ∃ (L : List ℂ) (h : ℂ → ℂ),
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
      (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall s₀ R,
        g z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
      (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
  have hR : 0 < R := lt_trans hr hrR
  set q : ℝ := R / r with hq_def
  have hq1 : 1 < q := (one_lt_div hr).mpr hrR
  have hg0_pos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M₀ < ‖g s₀‖ * q ^ N := by
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually
      (Filter.eventually_gt_atTop (M₀ / ‖g s₀‖))
    obtain ⟨N, hN⟩ := hev.exists
    exact ⟨N, by have := (div_lt_iff₀ hg0_pos).mp hN; linarith⟩
  have hfr_sub : frontier (Metric.ball s₀ R) ⊆ Metric.sphere s₀ R := by
    intro z hz
    rw [Metric.mem_sphere]
    have hcl : z ∈ Metric.closedBall s₀ R := by
      rw [← closure_ball s₀ hR.ne']
      exact hz.1
    have hnot : z ∉ Metric.ball s₀ R := by
      rw [← interior_eq_iff_isOpen.mpr Metric.isOpen_ball]
      exact hz.2
    rw [Metric.mem_closedBall] at hcl
    rw [Metric.mem_ball, not_lt] at hnot
    exact le_antisymm hcl hnot
  
  have hpeel : ∀ (n : ℕ) (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall s₀ R) →
      f s₀ ≠ 0 →
      (∀ z ∈ Metric.sphere s₀ R, ‖f z‖ ≤ M₀) →
      M₀ < ‖f s₀‖ * q ^ n →
      ∃ (L : List ℂ) (h : ℂ → ℂ),
        (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀) ∧
        AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
        (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
        (∀ z ∈ Metric.closedBall s₀ R,
          f z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
        (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
    intro n
    induction n with
    | zero =>
      intro f hf _ hfM hlt
      simp only [pow_zero, mul_one] at hlt
      
      have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
        refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
        rw [closure_ball s₀ hR.ne']
        exact hf.continuousOn
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
        (fun z hz => hfM z (hfr_sub hz))
        (by rw [closure_ball s₀ hR.ne']; exact Metric.mem_closedBall_self hR.le)
      linarith
    | succ k ih =>
      intro f hf hf0 hfM hlt
      by_cases hnz : ∀ z ∈ Metric.closedBall s₀ r, f z ≠ 0
      · 
        have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
          refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
          rw [closure_ball s₀ hR.ne']
          exact hf.continuousOn
        have hmax : ∀ z ∈ Metric.closedBall s₀ R, ‖f z‖ ≤ M₀ := fun z hz =>
          Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
            (fun w hw => hfM w (hfr_sub hw))
            (by rwa [closure_ball s₀ hR.ne'])
        exact ⟨[], f, by simp, hf, hnz, fun z _ => by simp, hmax⟩
      · 
        push Not at hnz
        obtain ⟨ρ, hρ_mem, hρ_zero⟩ := hnz
        have hρ_ne : ρ ≠ s₀ := fun h => hf0 (h ▸ hρ_zero)
        have hρ_norm : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem
        have hρ_lt : ‖ρ - s₀‖ < R := lt_of_le_of_lt hρ_norm hrR
        set f₁ : ℂ → ℂ := fun z =>
          (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ)) * dslope f ρ z
        have hf₁_an : AnalyticOnNhd ℂ f₁ (Metric.closedBall s₀ R) := by
          
          have hopen_ex : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall s₀ R ⊆ U ∧
              DifferentiableOn ℂ f U := by
            refine ⟨{z | AnalyticAt ℂ f z}, isOpen_analyticAt ℂ f, fun z hz => hf z hz,
              fun z hz => hz.differentiableAt.differentiableWithinAt⟩
          obtain ⟨U, hU_open, hU_sub, hfU⟩ := hopen_ex
          have hρU : U ∈ 𝓝 ρ :=
            hU_open.mem_nhds (hU_sub (Metric.closedBall_subset_closedBall hrR.le hρ_mem))
          have hdsU : DifferentiableOn ℂ (dslope f ρ) U :=
            (Complex.differentiableOn_dslope hρU).mpr hfU
          have hds_an : AnalyticOnNhd ℂ (dslope f ρ) (Metric.closedBall s₀ R) :=
            (hdsU.analyticOnNhd hU_open).mono hU_sub
          have hlin_an : AnalyticOnNhd ℂ
              (fun z : ℂ => ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ))
              (Metric.closedBall s₀ R) := by
            refine (((analyticOnNhd_const.sub
              (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))).div
              analyticOnNhd_const) fun z _ => Complex.ofReal_ne_zero.mpr hR.ne')
          exact hlin_an.mul hds_an
        have hfac : ∀ z ∈ Metric.closedBall s₀ R, f z = f₁ z * blaschkeFactor s₀ R ρ z := by
          intro z hz
          have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
          have hden := blaschkeFactor_denom_ne_zero hR hρ_lt
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
          have hds_eq : (z - ρ) * dslope f ρ z = f z := by
            have := sub_smul_dslope f ρ z
            rw [hρ_zero, sub_zero, smul_eq_mul] at this
            exact this
          dsimp only [f₁, blaschkeFactor]
          calc f z = (z - ρ) * dslope f ρ z := hds_eq.symm
            _ = (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ) * dslope f ρ z) *
                ((R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))) := by
                field_simp [hRne, hden]
        have hf₁0 : f₁ s₀ ≠ 0 := by
          intro h0
          have := hfac s₀ (Metric.mem_closedBall_self hR.le)
          rw [h0, zero_mul] at this
          exact hf0 this
        have hf₁M : ∀ z ∈ Metric.sphere s₀ R, ‖f₁ z‖ ≤ M₀ := by
          intro z hz
          have h1 := congrArg norm (hfac z (Metric.sphere_subset_closedBall hz))
          rw [norm_mul, blaschkeFactor_norm_eq_one_on_sphere hR hρ_lt hz, mul_one] at h1
          rw [← h1]
          exact hfM z hz
        have hgrowth : ‖f s₀‖ * q ≤ ‖f₁ s₀‖ := by
          have h1 := congrArg norm (hfac s₀ (Metric.mem_closedBall_self hR.le))
          rw [norm_mul, blaschkeFactor_norm_center hR] at h1
          have hpos_ρ : 0 < ‖ρ - s₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ_ne)
          have hle : ‖ρ - s₀‖ / R ≤ r / R := div_le_div_of_nonneg_right hρ_norm hR.le
          have h2 : ‖f s₀‖ ≤ ‖f₁ s₀‖ * (r / R) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          rw [hq_def, mul_div_assoc', div_le_iff₀ hr]
          have h3 := mul_le_mul_of_nonneg_right h2 hR.le
          have h4 : ‖f₁ s₀‖ * (r / R) * R = ‖f₁ s₀‖ * r := by field_simp [hR.ne']
          linarith
        have hlt₁ : M₀ < ‖f₁ s₀‖ * q ^ k := by
          have hq_pow_nonneg : 0 ≤ q ^ k := pow_nonneg (by positivity) k
          calc M₀ < ‖f s₀‖ * q ^ (k + 1) := hlt
            _ = (‖f s₀‖ * q) * q ^ k := by rw [pow_succ']; ring
            _ ≤ ‖f₁ s₀‖ * q ^ k := mul_le_mul_of_nonneg_right hgrowth hq_pow_nonneg
        obtain ⟨L₁, h, hL₁, hh_an, hh_nz, hh_eq, hh_M⟩ := ih f₁ hf₁_an hf₁0 hf₁M hlt₁
        refine ⟨ρ :: L₁, h, ?_, hh_an, hh_nz, ?_, hh_M⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨hρ_mem, hρ_ne⟩
          · exact hL₁ w hw'
        · intro z hz
          rw [hfac z hz, hh_eq z hz, List.map_cons, List.prod_cons]
          ring
  obtain ⟨L, h, hL, hh_an, hh_nz, hh_eq, hh_M⟩ := hpeel N g hg hg0 hM₀ hN
  refine ⟨L, h, ?_, ?_, hh_an, hh_nz, hh_eq, hh_M⟩
  · intro ρ hρ
    obtain ⟨hρ_mem, hρ_ne⟩ := hL ρ hρ
    refine ⟨hρ_mem, hρ_ne, ?_⟩
    rw [hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)]
    have hzero_fac : blaschkeFactor s₀ R ρ ρ = 0 := by simp [blaschkeFactor]
    have hprod_zero : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨ρ, hρ, hzero_fac⟩)
    rw [hprod_zero, mul_zero]
  · intro ρ hρ_mem hρ_zero
    have hprod := hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    rw [hρ_zero] at hprod
    have h0 : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      (mul_eq_zero.mp hprod.symm).resolve_left (hh_nz ρ hρ_mem)
    obtain ⟨w, hwL, hBw⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    have hden := blaschkeFactor_denom_ne_zero hR
      (lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL w hwL).1) hrR)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using
        Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    unfold blaschkeFactor at hBw
    have hnum : (R : ℂ) * (ρ - w) = 0 := (div_eq_zero_iff.mp hBw).resolve_right hden
    have hρw : ρ = w := sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left
      (Complex.ofReal_ne_zero.mpr hR.ne'))
    exact hρw ▸ hwL

set_option maxHeartbeats 2000000 in
theorem hasDerivAt_radial_primitive_ball {H : ℂ → ℂ} {s₀ z : ℂ} {r : ℝ}
    (hH : DifferentiableOn ℂ H (Metric.ball s₀ r)) (hz : z ∈ Metric.ball s₀ r) :
    HasDerivAt (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (H z) z := by
  have hH_an : AnalyticOnNhd ℂ H (Metric.ball s₀ r) := hH.analyticOnNhd Metric.isOpen_ball
  have hH_cont : ContinuousOn H (Metric.ball s₀ r) := hH_an.continuousOn
  have hH'_an : AnalyticOnNhd ℂ (deriv H) (Metric.ball s₀ r) := fun w hw => (hH_an w hw).deriv
  have hH'_cont : ContinuousOn (deriv H) (Metric.ball s₀ r) := hH'_an.continuousOn
  set δ : ℝ := (r - ‖z - s₀‖) / 2 with hδ_def
  have hδ0 : 0 < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    linarith
  have hmem_ball : ∀ w ∈ Metric.closedBall z δ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      s₀ + (u : ℂ) * (w - s₀) ∈ Metric.ball s₀ r := by
    intro w hw u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hu.1]
    have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
      have htri := norm_add_le (w - z) (z - s₀)
      rw [sub_add_sub_cancel] at htri
      linarith
    have hlt : ‖z - s₀‖ + δ < r := by
      rw [Metric.mem_ball, dist_eq_norm] at hz; linarith
    calc u * ‖w - s₀‖ ≤ 1 * ‖w - s₀‖ := mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)
      _ = ‖w - s₀‖ := one_mul _
      _ ≤ ‖z - s₀‖ + δ := hws
      _ < r := hlt
  set Φ : ℂ × ℝ → ℂ := fun p => s₀ + (p.2 : ℂ) * (p.1 - s₀)
  have hΦ_cont : Continuous Φ := by fun_prop
  set K : Set ℂ := Φ '' (Metric.closedBall z δ ×ˢ Set.Icc (0 : ℝ) 1)
  have hK_comp : IsCompact K := ((isCompact_closedBall z δ).prod isCompact_Icc).image hΦ_cont
  have hK_sub : K ⊆ Metric.ball s₀ r := by
    rintro _ ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
    exact hmem_ball w hw u hu
  obtain ⟨M₁, hM₁⟩ := hK_comp.exists_bound_of_continuousOn (hH_cont.mono hK_sub)
  obtain ⟨M₂, hM₂⟩ := hK_comp.exists_bound_of_continuousOn (hH'_cont.mono hK_sub)
  set B : ℝ := |M₁| + (‖z - s₀‖ + δ) * |M₂|
  have hstep : HasDerivAt
      (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (∫ u in (0 : ℝ)..1,
        (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))) z := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (F' := fun w u => H (s₀ + (u : ℂ) * (w - s₀)) +
        (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀))))
      (bound := fun _ : ℝ => B)
      (Metric.ball_mem_nhds z hδ0) ?_ ?_ ?_ ?_ (intervalIntegrable_const (c := B)) ?_).2
    · filter_upwards [Metric.ball_mem_nhds z hδ0] with w hw
      have hcw : ContinuousOn (fun u : ℝ => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball w (Metric.ball_subset_closedBall hw) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hcw.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · have hcz : ContinuousOn (fun u : ℝ => (z - s₀) * H (s₀ + (u : ℂ) * (z - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact hcz.intervalIntegrable
    · have hcz' : ContinuousOn (fun u : ℝ =>
          H (s₀ + (u : ℂ) * (z - s₀)) +
            (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
          continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
        exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
          (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
            (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
      exact (hcz'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hw_cb : w ∈ Metric.closedBall z δ := Metric.ball_subset_closedBall hw
      have hKmem : s₀ + (u : ℂ) * (w - s₀) ∈ K :=
        ⟨(w, u), ⟨hw_cb, hu_cc⟩, rfl⟩
      have h1 : ‖H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₁| :=
        (hM₁ _ hKmem).trans (le_abs_self M₁)
      have h2 : ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₂| :=
        (hM₂ _ hKmem).trans (le_abs_self M₂)
      have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
        have htri := norm_add_le (w - z) (z - s₀)
        rw [sub_add_sub_cancel] at htri
        rw [Metric.mem_closedBall, dist_eq_norm] at hw_cb
        linarith
      have huM2 : u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ 1 * |M₂| :=
        mul_le_mul hu_cc.2 h2 (norm_nonneg _) zero_le_one
      calc ‖H (s₀ + (u : ℂ) * (w - s₀)) +
              (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀)))‖
          ≤ ‖H (s₀ + (u : ℂ) * (w - s₀))‖ +
            ‖w - s₀‖ * (u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu_cc.1]
        _ ≤ |M₁| + (‖z - s₀‖ + δ) * (1 * |M₂|) := by
            gcongr
            exact mul_nonneg hu_cc.1 (norm_nonneg _)
        _ = B := by dsimp only [B]; ring
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hmem := hmem_ball w (Metric.ball_subset_closedBall hw) u hu_cc
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (w - s₀))) (s₀ + (u : ℂ) * (w - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun x : ℂ => s₀ + (u : ℂ) * (x - s₀)) (u : ℂ) w := by
        simpa using (hasDerivAt_const w s₀).fun_add (((hasDerivAt_id w).sub_const s₀).const_mul (u : ℂ))
      have hcomp := hH_at.comp w hlin
      have hmul := ((hasDerivAt_id w).sub_const s₀).fun_mul hcomp
      refine hmul.congr_deriv ?_
      dsimp [Function.comp]
      ring
  
  have hftc : ∫ u in (0 : ℝ)..1,
      (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) =
      H z := by
    have hderiv_u : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * H (s₀ + (t : ℂ) * (z - s₀)))
          (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) u := by
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hmem := hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (z - s₀))) (s₀ + (u : ℂ) * (z - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => s₀ + (t : ℂ) * (z - s₀)) (z - s₀) u := by
        have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
        simpa using (hasDerivAt_const u s₀).fun_add (hof.mul_const (z - s₀))
      have hcomp : HasDerivAt (fun t : ℝ => H (s₀ + (t : ℂ) * (z - s₀)))
          (deriv H (s₀ + (u : ℂ) * (z - s₀)) * (z - s₀)) u :=
        HasDerivAt.comp u hH_at hlin
      have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
      refine (hof.fun_mul hcomp).congr_deriv ?_
      ring
    have hcont_u : ContinuousOn (fun u : ℝ =>
        H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))
        (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
        continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
          (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_u hcont_u.intervalIntegrable
    simpa using h
  rwa [hftc] at hstep

theorem exists_holomorphic_log_ball {h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (Metric.ball s₀ r))
    (hnz : ∀ z ∈ Metric.ball s₀ r, h z ≠ 0) :
    ∃ L : ℂ → ℂ, L s₀ = 0 ∧
      (∀ z ∈ Metric.ball s₀ r, HasDerivAt L (deriv h z / h z) z) ∧
      (∀ z ∈ Metric.ball s₀ r, cexp (L z) = h z / h s₀) := by
  set H : ℂ → ℂ := fun z => deriv h z / h z
  have hH_diff : DifferentiableOn ℂ H (Metric.ball s₀ r) :=
    (hh.deriv Metric.isOpen_ball).div hh hnz
  set L : ℂ → ℂ := fun w => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))
  have hL0 : L s₀ = 0 := by simp [L]
  have hL_deriv : ∀ z ∈ Metric.ball s₀ r, HasDerivAt L (H z) z :=
    fun z hz => hasDerivAt_radial_primitive_ball hH_diff hz
  refine ⟨L, hL0, hL_deriv, fun z hz => ?_⟩
  
  set q : ℂ → ℂ := fun w => h w * cexp (-L w)
  have hq_deriv : ∀ w ∈ Metric.ball s₀ r, HasDerivAt q 0 w := by
    intro w hw
    have hh_at : HasDerivAt h (deriv h w) w :=
      (hh.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hL_at : HasDerivAt L (deriv h w / h w) w := hL_deriv w hw
    have hexp : HasDerivAt (fun x => cexp (-L x)) (cexp (-L w) * -(deriv h w / h w)) w :=
      hL_at.neg.cexp
    refine (hh_at.mul hexp).congr_deriv ?_
    have hne := hnz w hw
    field_simp [hne]
    ring
  have hq_const : q z = q s₀ := by
    have hconv : Convex ℝ (Metric.ball s₀ r) := convex_ball s₀ r
    refine hconv.is_const_of_fderivWithin_eq_zero
      (fun w hw => ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).differentiableAt.differentiableWithinAt) ?_
      hz (Metric.mem_ball_self hr)
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw,
      ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hqs₀ : q s₀ = h s₀ := by simp [q, hL0]
  have hhz₀ : h s₀ ≠ 0 := hnz s₀ (Metric.mem_ball_self hr)
  rw [hqs₀] at hq_const
  dsimp only [q] at hq_const
  have hmul : h z = h s₀ * cexp (L z) := by
    calc h z = (h z * cexp (-L z)) * cexp (L z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = h s₀ * cexp (L z) := by rw [hq_const]
  rw [hmul, mul_div_cancel_left₀ _ hhz₀]

private lemma hasDerivAt_logDeriv_list_prod {s₀ : ℂ} {L : List ℂ} {F : ℂ → ℂ → ℂ} {F' : ℂ → ℂ}
    (hd : ∀ ρ ∈ L, HasDerivAt (F ρ) (F' ρ) s₀)
    (hnz : ∀ ρ ∈ L, F ρ s₀ ≠ 0) :
    HasDerivAt (fun z => (L.map (fun ρ => F ρ z)).prod)
      ((L.map (fun ρ => F ρ s₀)).prod * (L.map (fun ρ => F' ρ / F ρ s₀)).sum) s₀ := by
  induction L with
  | nil => simp [hasDerivAt_const]
  | cons a t ih =>
    have ha_d : HasDerivAt (F a) (F' a) s₀ := hd a (List.mem_cons_self ..)
    have ha_nz : F a s₀ ≠ 0 := hnz a (List.mem_cons_self ..)
    have ht_ih := ih (fun ρ hρ => hd ρ (List.mem_cons_of_mem a hρ))
      (fun ρ hρ => hnz ρ (List.mem_cons_of_mem a hρ))
    have hfun : (fun z => ((a :: t).map (fun ρ => F ρ z)).prod) =
        fun z => F a z * (t.map (fun ρ => F ρ z)).prod := by
      funext z; simp
    rw [hfun]
    refine (ha_d.fun_mul ht_ih).congr_deriv ?_
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    field_simp [ha_nz]

set_option maxHeartbeats 2000000 in
theorem landau_negLogDeriv_full {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖) :
    ∃ L : List ℂ,
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      (-deriv g s₀ / g s₀).re ≤
        (2 / r) * Real.log M -
          (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, h, hL, hL_cov, hh_an, hh_nz, hh_eq, hh_M⟩ :=
    exists_blaschke_factorization hr hrR hg hg0
      (fun z hz => hbd z (Metric.sphere_subset_closedBall hz))
  
  have hprod_le_one : ‖(L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, ‖ρ - s₀‖ ≤ R) →
        ‖(l.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.prod_cons, norm_mul]
        have ha : ‖blaschkeFactor s₀ R a s₀‖ ≤ 1 := by
          rw [blaschkeFactor_norm_center hR]
          exact (div_le_one hR).mpr (hl a (List.mem_cons_self ..))
        have ht := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))
        nlinarith [norm_nonneg (blaschkeFactor s₀ R a s₀),
          norm_nonneg (t.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod]
    refine haux L fun ρ hρ => ?_
    have h1 : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL ρ hρ).1
    exact h1.trans hrR.le
  have hh0_ge : ‖g s₀‖ ≤ ‖h s₀‖ := by
    have h1 := congrArg norm (hh_eq s₀ (Metric.mem_closedBall_self hR.le))
    rw [norm_mul] at h1
    rw [h1]
    exact mul_le_of_le_one_right (norm_nonneg _) hprod_le_one
  have hh0_ne : h s₀ ≠ 0 := hh_nz s₀ (Metric.mem_closedBall_self hr.le)
  have hh0_pos : 0 < ‖h s₀‖ := norm_pos_iff.mpr hh0_ne
  
  have hh_diff : DifferentiableOn ℂ h (Metric.ball s₀ r) :=
    (hh_an.mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrR.le))).differentiableOn
  obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
    exists_holomorphic_log_ball hr hh_diff (fun z hz => hh_nz z (Metric.ball_subset_closedBall hz))
  have hLog_diff : DifferentiableOn ℂ Log (Metric.ball s₀ r) :=
    fun z hz => (hLog_d z hz).differentiableAt.differentiableWithinAt
  have hLog_re : ∀ z ∈ Metric.ball s₀ r, (Log z).re ≤ Real.log M := by
    intro z hz
    have h1 : Real.exp (Log z).re = ‖h z / h s₀‖ := by
      rw [← Complex.norm_exp, hLog_exp z hz]
    have h2 : ‖h z / h s₀‖ ≤ M := by
      rw [norm_div, div_le_iff₀ hh0_pos]
      have hhz : ‖h z‖ ≤ M * ‖g s₀‖ :=
        hh_M z (Metric.closedBall_subset_closedBall hrR.le (Metric.ball_subset_closedBall hz))
      have hM0 : 0 ≤ M := by linarith
      exact hhz.trans (mul_le_mul_of_nonneg_left hh0_ge hM0)
    have h3 : (Log z).re = Real.log ‖h z / h s₀‖ := by
      rw [← h1, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖h z / h s₀‖ := by
      rw [norm_div]
      exact div_pos (norm_pos_iff.mpr (hh_nz z (Metric.ball_subset_closedBall hz))) hh0_pos
    exact Real.log_le_log hpos h2
  have hbc_h : ‖deriv h s₀ / h s₀‖ ≤ (2 / r) * Real.log M := by
    have h1 := borelCaratheodory_deriv_at_center hr hLog_diff hLog_re
    rw [(hLog_d s₀ (Metric.mem_ball_self hr)).deriv, hLog0, Complex.zero_re, sub_zero] at h1
    exact h1
  
  have hB_nz : ∀ ρ ∈ L, blaschkeFactor s₀ R ρ s₀ ≠ 0 := by
    intro ρ hρ
    rw [blaschkeFactor_eval_center hR]
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (hL ρ hρ).2.1))
      (Complex.ofReal_ne_zero.mpr hR.ne')
  have hP_d := hasDerivAt_logDeriv_list_prod (s₀ := s₀) (L := L)
    (F := fun ρ z => blaschkeFactor s₀ R ρ z)
    (F' := fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀)
    (fun ρ _ => (blaschkeFactor_hasDerivAt_center hR).congr_deriv
      (blaschkeFactor_hasDerivAt_center hR).deriv.symm)
    hB_nz
  have hh_at : HasDerivAt h (deriv h s₀) s₀ :=
    (hh_an s₀ (Metric.mem_closedBall_self hR.le)).differentiableAt.hasDerivAt
  have hmul_d := hh_at.fun_mul hP_d
  have hEq_nhds : g =ᶠ[𝓝 s₀] fun z => h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod := by
    filter_upwards [Metric.closedBall_mem_nhds s₀ hR] with z hz
    exact hh_eq z hz
  have hg_d : deriv g s₀ =
      deriv h s₀ * (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod +
      h s₀ * ((L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod *
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum) := by
    rw [hEq_nhds.deriv_eq, hmul_d.deriv]
  have hP_ne : (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod ≠ 0 :=
    List.prod_ne_zero (by
      intro hmem
      obtain ⟨ρ, hρL, h0⟩ := List.mem_map.mp hmem
      exact hB_nz ρ hρL h0)
  have hlogd : deriv g s₀ / g s₀ =
      deriv h s₀ / h s₀ +
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum := by
    rw [hg_d, hh_eq s₀ (Metric.mem_closedBall_self hR.le)]
    field_simp [hh0_ne, hP_ne]
  have hre_sum :
      ((L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
      (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    have hmap_re : ∀ (l : List ℂ), (∀ ρ ∈ l, ρ ≠ s₀) →
        ((l.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
        (l.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.sum_cons, Complex.add_re]
        rw [blaschkeFactor_logDeriv_center_re hR (hl a (List.mem_cons_self ..)),
          ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))]
    exact hmap_re L (fun ρ hρ => (hL ρ hρ).2.1)
  have hneg_le : (-(deriv h s₀ / h s₀)).re ≤ (2 / r) * Real.log M := by
    rw [Complex.neg_re]
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (deriv h s₀ / h s₀))).1
    linarith
  refine ⟨L, hL, hL_cov, ?_⟩
  have hneg_eq : -deriv g s₀ / g s₀ = -(deriv g s₀ / g s₀) := by ring
  rw [hneg_eq, hlogd, neg_add, Complex.add_re, Complex.neg_re, Complex.neg_re, hre_sum]
  rw [Complex.neg_re] at hneg_le
  linarith

theorem landau_negLogDeriv_le {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re) :
    (-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, _, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hsum_nonneg :
      0 ≤ (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨ρ, hρL, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  linarith

theorem landau_negLogDeriv_le_one_zero {g : ℂ → ℂ} {s₀ ρ₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re)
    (hρ₀_mem : ρ₀ ∈ Metric.closedBall s₀ r) (hρ₀_zero : g ρ₀ = 0) :
    (-deriv g s₀ / g s₀).re ≤
      (2 / r) * Real.log M + (s₀ - ρ₀).re / R ^ 2 - (1 / (s₀ - ρ₀)).re := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, hL_cov, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hρ₀L : ρ₀ ∈ L := hL_cov ρ₀ hρ₀_mem hρ₀_zero
  set φ : ℂ → ℝ := fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2)
  have hφ_nonneg : ∀ ρ ∈ L, 0 ≤ φ ρ := by
    intro ρ hρL
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    dsimp only [φ]
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  have hterm_le : φ ρ₀ ≤ (L.map φ).sum := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, 0 ≤ φ ρ) → ρ₀ ∈ l → φ ρ₀ ≤ (l.map φ).sum := by
      intro l
      induction l with
      | nil => intro _ h; simp at h
      | cons a t ih =>
        intro hl hmem
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hmem with rfl | ht
        · have ht_nn : 0 ≤ (t.map φ).sum := List.sum_nonneg fun x hx => by
            obtain ⟨ρ, hρt, rfl⟩ := List.mem_map.mp hx
            exact hl ρ (List.mem_cons_of_mem _ hρt)
          linarith
        · have ha_nn : 0 ≤ φ a := hl a (List.mem_cons_self ..)
          have hih := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ)) ht
          linarith
    exact haux L hφ_nonneg hρ₀L
  have hφ_eq : φ ρ₀ = (1 / (s₀ - ρ₀)).re - (s₀ - ρ₀).re / R ^ 2 := by
    dsimp only [φ]
    have hre1 : (1 / (s₀ - ρ₀)).re = (s₀ - ρ₀).re / ‖s₀ - ρ₀‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [hre1]
    ring
  linarith

def fractNat (t : ℝ) : ℝ := t - (⌊t⌋₊ : ℝ)

lemma fractNat_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fractNat t :=
  sub_nonneg.mpr (Nat.floor_le ht)

lemma fractNat_lt_one (t : ℝ) : fractNat t < 1 := by
  unfold fractNat
  linarith [Nat.lt_floor_add_one t]

lemma norm_fractNat_le_one {t : ℝ} (ht : 0 ≤ t) : ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (fractNat_nonneg ht)]
  exact (fractNat_lt_one t).le

lemma measurable_fractNat : Measurable fractNat :=
  measurable_id.sub (measurable_from_top.comp Nat.measurable_floor)

private lemma stepSum_const_one (t : ℝ) :
    Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t = (⌊t⌋₊ : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  simp

private lemma isPreconnected_re_pos_sdiff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {(1 : ℂ)}
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨by norm_num, ?_⟩
    intro h; have := congrArg Complex.re h; norm_num at this
  have hseg : ∀ a b : ℂ, a ∈ U → b ∈ U →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ)) * a + (t : ℂ) * b ∈ U) →
      JoinedIn U a b := by
    intro a b ha hb hmem
    refine ⟨{
      toFun := fun t => (1 - ((t : ℝ) : ℂ)) * a + ((t : ℝ) : ℂ) * b
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => hmem t t.2⟩
  have hjoin2 : ∀ z ∈ U, JoinedIn U z (2 : ℂ) := by
    intro z hz
    have hz_re : 0 < z.re := hz.1
    have hz_ne : z ≠ 1 := hz.2
    by_cases him : z.im = 0
    · by_cases hgt : 1 < z.re
      · refine hseg z 2 hz h2U fun t ht => ?_
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = (1 - t) * z.re + 2 * t := by
          simp [Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re by rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
        intro h1
        have h1' : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = 1 := by
          rw [Set.mem_singleton_iff] at h1; rw [h1, Complex.one_re]
        rw [hre] at h1'
        have hnn : 0 ≤ (1 - t) * (z.re - 1) := mul_nonneg (by linarith [ht.2]) (by linarith)
        rcases eq_or_lt_of_le ht.1 with rfl | ht0
        · linarith
        · nlinarith
      · 
        have hlt : z.re < 1 := lt_of_le_of_ne (le_of_not_gt hgt) fun heq =>
          hz_ne (Complex.ext heq (by simpa using him))
        have hzI : z + I ∈ U := by
          refine ⟨by simpa using hz_re, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp [him] at this
        have h2I : (2 : ℂ) + I ∈ U := by
          refine ⟨by norm_num, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp at this
        have h1 : JoinedIn U z (z + I) := hseg z (z + I) hz hzI fun t ht => by
          have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re = z.re := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re by rw [hre]; exact hz_re, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; linarith
        have h2 : JoinedIn U (z + I) (2 + I) := hseg (z + I) (2 + I) hzI h2I fun t ht => by
          have hre : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re = (1 - t) * z.re + 2 * t := by
            simp [Complex.mul_re]; ring
          have him' : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).im = 1 := by
            simp [Complex.mul_im, him]
          refine ⟨show 0 < ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re by
            rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; norm_num at this
        have h3 : JoinedIn U (2 + I) 2 := hseg (2 + I) 2 h2I h2U fun t ht => by
          have hre : ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re = 2 := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
        exact (h1.trans h2).trans h3
    · 
      set w : ℂ := (2 : ℂ) + I * (z.im : ℂ)
      have hw : w ∈ U := by
        refine ⟨by simp [w], ?_⟩
        intro h1; have := congrArg Complex.re h1; simp [w] at this
      have h1 : JoinedIn U z w := hseg z w hz hw fun t ht => by
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * w).re = (1 - t) * z.re + 2 * t := by
          simp [w, Complex.mul_re]; ring
        have him' : ((1 - (t : ℂ)) * z + (t : ℂ) * w).im = z.im := by
          simp [w, Complex.mul_im]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * w).re by
          rw [hre]; rcases eq_or_lt_of_le ht.1 with rfl | ht0 <;> nlinarith [ht.1, ht.2], ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; exact him this
      have h2 : JoinedIn U w 2 := hseg w 2 hw h2U fun t ht => by
        have hre : ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re = 2 := by
          simp [w, Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
      exact h1.trans h2
  have hpc : IsPathConnected U := ⟨2, h2U, fun z hz => (hjoin2 z hz).symm⟩
  exact hpc.isConnected.isPreconnected

theorem riemannZeta_sub_pole_eq_eulerMaclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - 1 / (s - 1) =
      1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hLHS_an : AnalyticOnNhd ℂ (fun z : ℂ => riemannZeta z - 1 / (z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hz1 : z ≠ 1 := hz.2
    exact ((differentiableAt_riemannZeta hz1).sub
      ((differentiableAt_const (1 : ℂ)).div ((differentiableAt_id).sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz1))).differentiableWithinAt
  have hE_meas : Measurable (fun t : ℝ => -((fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖-((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact norm_fractNat_le_one (zero_le_one.trans ht)
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) U := by
    have h1 := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
    have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ), (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
      funext z
      have hneg : (fun t : ℝ => (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
          fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by funext t; ring
      rw [hneg, integral_neg]
      ring
    rw [hEq] at h1
    exact h1.mono (fun z hz => hz.1)
  have hEq_gt1 : ∀ z : ℂ, 1 < z.re →
      riemannZeta z - 1 / (z - 1) =
        1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    intro z hz
    have hL_eq : LSeries (fun _ : ℕ => (1 : ℂ)) z = riemannZeta z := by
      have h1 := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz
      rw [ArithmeticFunction.LSeries_zeta_eq] at h1
      exact h1
    have hsum : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) z := by
      have h1 := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz
      refine h1.congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp [LSeries.term, hn, ArithmeticFunction.zeta_apply]
    have hbd_step : ∀ t : ℝ, 1 ≤ t → ‖Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t‖ ≤ 1 * t := by
      intro t ht
      rw [stepSum_const_one, one_mul, Complex.norm_natCast]
      exact Nat.floor_le (zero_le_one.trans ht)
    have hmel := Stage3RealAnalyticLandau.LSeries_sub_pole_eq_mellin_error hbd_step hz hsum
    rw [hL_eq] at hmel
    rw [hmel]
    have hpt : (fun t : ℝ => (Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t - (t : ℂ)) *
          (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t
      rw [stepSum_const_one]
      unfold fractNat
      push_cast
      ring
    rw [hpt, integral_neg]
    ring
  have hEv : (fun z : ℂ => riemannZeta z - 1 / (z - 1)) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact hEq_gt1 z hz
  have h2U : (2 : ℂ) ∈ U := ⟨by norm_num, fun h => by
    have := congrArg Complex.re h; norm_num at this⟩
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an isPreconnected_re_pos_sdiff_one
    h2U hEv ⟨hs, hs1⟩

lemma norm_eulerMaclaurin_tail_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re) / s.re := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hre : -s.re - 1 < -1 := by linarith
  have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt hre ha0
  have hint_val : ∫ t in Ioi a, t ^ (-s.re - 1) = a ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt hre ha0]
    have h1 : -s.re - 1 + 1 = -s.re := by ring
    rw [h1]; field_simp [hs.ne']
  calc ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ∫ t in Ioi a, ‖((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi a, t ^ (-s.re - 1) := by
        refine setIntegral_mono_on ?_ hint_dom measurableSet_Ioi fun t ht => ?_
        · have hint_full : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
            Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
              (Complex.measurable_ofReal.comp measurable_fractNat)
              (fun u hu => by simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans hu)) hs
          exact (hint_full.mono_set (Ioi_subset_Ioi ha)).norm
        · have ht0 : 0 < t := ha0.trans ht
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          have hre' : (-s - 1).re = -s.re - 1 := by simp
          rw [hre']
          exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (norm_fractNat_le_one ht0.le)
    _ = a ^ (-s.re) / s.re := hint_val

theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs hs1
  have hzeta : riemannZeta s =
      1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    linear_combination hem
  have htail := norm_eulerMaclaurin_tail_le le_rfl hs
  rw [Real.one_rpow] at htail
  rw [hzeta]
  calc ‖1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖1 / (s - 1) + 1‖ + ‖s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
        norm_sub_le _ _
    _ ≤ (‖1 / (s - 1)‖ + ‖(1 : ℂ)‖) + ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ (1 / ‖s - 1‖ + 1) + ‖s‖ * (1 / s.re) := by
        rw [norm_div, norm_one]; gcongr
    _ = 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by ring

theorem norm_riemannZeta_strip_le {s : ℂ} (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2)
    (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 * (|s.im| + 2) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_im, abs_zero] at him; linarith
  have hbd := norm_riemannZeta_le_of_re_pos hs0 hs1
  have hsub_ge : 1 ≤ ‖s - 1‖ := by
    have h1 := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h1
    linarith
  have hinv_le : 1 / ‖s - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hsub_ge
  have hnorm_s : ‖s‖ ≤ |s.im| + 2 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h1
    linarith
  have hdiv_le : ‖s‖ / s.re ≤ 2 * (|s.im| + 2) := by
    rw [div_le_iff₀ hs0]
    nlinarith [abs_nonneg s.im]
  linarith

theorem riemannZeta_real_bounds {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).im = 0 ∧
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs0 hs1
  have hreal_int : ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      (((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    exact Complex.ofRealCLM.integral_comp_comm (by
      have hre : -σ - 1 < -1 := by linarith
      refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
        ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le)
  have hzeta_real : riemannZeta (σ : ℂ) =
      (((1 / (σ - 1) + 1 - σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have h1 : riemannZeta (σ : ℂ) =
        1 / ((σ : ℂ) - 1) + 1 - (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) := by
      linear_combination hem
    rw [h1, hreal_int]
    push_cast; rfl
  have hint_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _)
  have hint_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
    have hre : -σ - 1 < -1 := by linarith
    have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hre zero_lt_one
    have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
      rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
      have h1 : -σ - 1 + 1 = -σ := by ring
      rw [h1]; field_simp [(by linarith : σ ≠ 0)]
    rw [← hval]
    refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  rw [hzeta_real, Complex.ofReal_im, Complex.ofReal_re]
  have hσ_pos : 0 < σ := by linarith
  have hσ1_ne : σ - 1 ≠ 0 := by linarith
  have hupper : 1 / (σ - 1) + 1 = σ / (σ - 1) := by field_simp [hσ1_ne]; ring
  have hmul_le : σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hint_le hσ_pos.le
    rw [mul_one_div_cancel hσ_pos.ne'] at h1
    exact h1
  refine ⟨rfl, ?_, ?_⟩
  · linarith
  · linarith [mul_nonneg hσ_pos.le hint_nn]

private lemma norm_LSeries_le_riemannZeta_real {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries f ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hsum_z : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
    have h1 := (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ).norm
    refine h1.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, ArithmeticFunction.zeta_apply, if_neg hn, Nat.cast_one,
        norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.ofReal_re, if_neg hn, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  have hsum_f : Summable (fun n : ℕ => ‖LSeries.term f ((σ : ℂ) + I * (t : ℂ)) n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_z
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)
  have hzeta_re : (riemannZeta (σ : ℂ)).re = ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsσ]
    unfold LSeries
    have hsumZ := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumZ]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one,
        Complex.reCLM_apply]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, one_div,
        Real.rpow_neg hn0.le]
  rw [hzeta_re]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum_f).trans ?_
  refine hsum_f.tsum_le_tsum (fun n => ?_) hsum_z
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)

private lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  · simp [ArithmeticFunction.moebius, h]

theorem norm_riemannZeta_and_inv_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re ∧
    ‖1 / riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have h1 : ‖riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    refine norm_LSeries_le_riemannZeta_real (fun n => ?_) hσ t
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [ArithmeticFunction.zeta_apply, hn]
  have h2 : ‖1 / riemannZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
    have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
    have hinv : 1 / riemannZeta ((σ : ℂ) + I * (t : ℂ)) =
        LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + I * (t : ℂ)) := by
      have hne : riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re hs.le
      rw [div_eq_iff hne, mul_comm, hmul]
    rw [hinv]
    exact norm_LSeries_le_riemannZeta_real norm_moebius_le_one hσ t
  exact ⟨h1, h2, (riemannZeta_real_bounds hσ).2.2⟩

set_option maxHeartbeats 2000000 in
theorem negLogDerivZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE_meas : Measurable (fun t : ℝ => ((fractNat t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_fractNat
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht; simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans ht)
  
  have hI_d := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas zero_le_one hE_bd hs0
  have hEq : riemannZeta =ᶠ[𝓝 (σ : ℂ)] fun z : ℂ =>
      1 / (z - 1) + 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    have hopen : IsOpen ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
    linear_combination riemannZeta_sub_pole_eq_eulerMaclaurin hz.1 hz.2
  have hpole_d : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-1 / ((σ : ℂ) - 1) ^ 2) (σ : ℂ) := by
    have h1 := ((hasDerivAt_id' (σ : ℂ)).sub_const 1).inv (sub_ne_zero.mpr hs1)
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun z => by simp [one_div])).congr_deriv ?_
    ring
  have hzeta_d : deriv riemannZeta (σ : ℂ) =
      -1 / ((σ : ℂ) - 1) ^ 2 -
        (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)) -
        (σ : ℂ) * (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))) := by
    rw [hEq.deriv_eq]
    have h1 := (hpole_d.add_const (1 : ℂ)).fun_sub ((hasDerivAt_id' (σ : ℂ)).fun_mul hI_d)
    rw [h1.deriv]
    ring
  
  have hint_real1 : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
    have hre : -σ - 1 < -1 := by linarith
    refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
      ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  have hreal1 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re =
      ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real1
    simpa [Complex.ofRealCLM_apply] using congrArg Complex.re hcomm
  have hint_real2 : IntegrableOn (fun t : ℝ => -(fractNat t * Real.log t * t ^ (-σ - 1))) (Ioi (1 : ℝ)) := by
    set e : ℝ := (σ - 1) / 2
    have he0 : 0 < e := by dsimp only [e]; linarith
    have hre : e - σ - 1 < -1 := by dsimp only [e]; linarith
    refine ((integrableOn_Ioi_rpow_of_lt hre zero_lt_one).const_mul e⁻¹).mono'
      (((measurable_fractNat.mul Real.measurable_log).mul (measurable_id.pow_const _)).neg.aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le)
      (Real.log_nonneg ht1.le)) (Real.rpow_nonneg ht0.le _))]
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    have hcomb : t ^ e * t ^ (-σ - 1) = t ^ (e - σ - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have h1 : fractNat t * Real.log t ≤ 1 * (e⁻¹ * t ^ e) :=
      mul_le_mul (fractNat_lt_one t).le hlog (Real.log_nonneg ht1.le) zero_le_one
    calc fractNat t * Real.log t * t ^ (-σ - 1)
        ≤ (1 * (e⁻¹ * t ^ e)) * t ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = e⁻¹ * (t ^ e * t ^ (-σ - 1)) := by ring
      _ = e⁻¹ * t ^ (e - σ - 1) := by rw [hcomb]
  have hreal2 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
        (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))).re =
      -(∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)))
        (fun t : ℝ => (((-(fractNat t * Real.log t * t ^ (-σ - 1)) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real2
    simpa [Complex.ofRealCLM_apply, integral_neg] using congrArg Complex.re hcomm
  have hneg_deriv_re : (-deriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) ^ 2 + 1 / σ := by
    have h1 : (-deriv riemannZeta (σ : ℂ)).re =
        1 / (σ - 1) ^ 2 +
          (∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1)) -
          σ * (∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
      rw [hzeta_d]
      have hp : (1 / ((σ : ℂ) - 1) ^ 2).re = 1 / (σ - 1) ^ 2 := by
        have hcast : ((σ : ℂ) - 1) ^ 2 = ((((σ - 1) ^ 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      simp only [neg_sub, Complex.sub_re, Complex.re_ofReal_mul, hreal1, hreal2]
      have hp' : (-1 / ((σ : ℂ) - 1) ^ 2).re = -(1 / (σ - 1) ^ 2) := by
        rw [neg_div, Complex.neg_re, hp]
      rw [hp']
      ring
    rw [h1]
    have hint1_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
      have hre : -σ - 1 < -1 := by linarith
      have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
        integrableOn_Ioi_rpow_of_lt hre zero_lt_one
      have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
        refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := zero_lt_one.trans ht
        change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
        rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
      have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
        rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
        have h2 : -σ - 1 + 1 = -σ := by ring
        rw [h2]; field_simp [(by linarith : σ ≠ 0)]
      rw [← hval]
      refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hint2_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1) := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      exact mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.log_nonneg ht1.le))
        (Real.rpow_nonneg ht0.le _)
    nlinarith
  
  obtain ⟨hz_im, hz_ge, _⟩ := riemannZeta_real_bounds hσ
  have hz_pos : 0 < (riemannZeta (σ : ℂ)).re := lt_of_lt_of_le (by positivity) hz_ge
  have hz_eq : riemannZeta (σ : ℂ) = (((riemannZeta (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hz_im])
  unfold Stage3ZeroFreeRegion.negLogDerivZeta
  rw [hz_eq, Complex.div_ofReal_re]
  have hσ1_pos : 0 < σ - 1 := by linarith
  have hσ_pos : 0 < σ := by linarith
  calc (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re
      ≤ (1 / (σ - 1) ^ 2 + 1 / σ) / (1 / (σ - 1)) := by
        refine div_le_div₀ (by positivity) hneg_deriv_re (by positivity) hz_ge
    _ = 1 / (σ - 1) + (σ - 1) / σ := by
        field_simp [hσ1_pos.ne', hσ_pos.ne']
    _ ≤ 1 / (σ - 1) + 1 := by
        have hfrac : (σ - 1) / σ ≤ 1 := (div_le_one hσ_pos).mpr (by linarith)
        linarith

theorem norm_negLogDerivZeta_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤
      (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ∧
    (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  refine ⟨?_, negLogDerivZeta_real_le hσ⟩
  rw [Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hs,
    Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hsσ]
  have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hsσ
  have hsumt := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumσ]
  refine (norm_tsum_le_tsum_norm hsumt.norm).trans ?_
  refine hsumt.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumσ)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [LSeries.term, hn, ↓reduceIte, Complex.reCLM_apply, norm_div, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]

theorem norm_LFunction_and_inv_and_logDeriv_of_one_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hζ_le := (riemannZeta_real_bounds hσ).2.2
  have h1 : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (norm_LSeries_le_riemannZeta_real (fun n => χ.norm_le_one _) hσ t).trans hζ_le
  have h2 : ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at hmul
    have hne : DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)) hs.le
    have hinv : 1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) =
        LSeries ((fun n : ℕ => χ (n : ZMod q)) * fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          ((σ : ℂ) + I * (t : ℂ)) := by
      rw [div_eq_iff hne, mul_comm, hmul]
    rw [hinv]
    refine (norm_LSeries_le_riemannZeta_real (fun n => ?_) hσ t).trans hζ_le
    dsimp [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_moebius_le_one n)
  have h3 : ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
    refine le_trans ?_ (negLogDerivZeta_real_le hσ)
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs,
      Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hsσ]
    have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hsσ
    have hsumt := χ.LSeriesSummable_twist_vonMangoldt hs
    unfold LSeries
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumσ]
    refine (norm_tsum_le_tsum_norm hsumt.norm).trans ?_
    refine hsumt.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumσ)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.reCLM_apply,
        norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
      gcongr
      dsimp [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  exact ⟨h1, h2, h3⟩

private lemma numerical_dlvp_closing : 87 + 40 * Real.log (48000 : ℝ) < 1000 := by
  have hpow : (48000 : ℝ) ≤ (2 : ℝ) ^ (16 : ℕ) := by norm_num
  have hlog : Real.log (48000 : ℝ) ≤ 16 * Real.log 2 := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 48000) hpow
    rw [Real.log_pow] at h1
    simpa using h1
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

set_option maxHeartbeats 2000000 in
theorem riemannZeta_zeroFree_large_im {s : ℂ} (him : 4 ≤ |s.im|)
    (hre : 1 - 1 / (14000 * Real.log (|s.im| + 2)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  
  have hlt1 : s.re < 1 := by
    by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hz
  set γ : ℝ := s.im
  set β : ℝ := s.re
  set L : ℝ := Real.log (|γ| + 2)
  have hL_gt1 : 1 < L := by
    have h6 : Real.exp 1 < |γ| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h6)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  set δ : ℝ := 1 / (2000 * L)
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp only [δ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hβ_gt : 7 / 8 < β := by
    have h1 : 1 / (14000 * L) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ_le : σ ≤ 5 / 4 := by linarith
  
  set s₁ : ℂ := (σ : ℂ) + I * (γ : ℂ)
  have hs₁_re : s₁.re = σ := by simp [s₁]
  have hs₁_im : s₁.im = γ := by simp [s₁]
  have hs₁_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₁ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton (x := (1 : ℂ)))).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    intro h1
    rw [h1] at hz
    have him_diff := Complex.abs_im_le_norm (1 - s₁)
    rw [Complex.sub_im, Complex.one_im, hs₁_im] at him_diff
    have hge4 : 4 ≤ |0 - γ| := by simpa [abs_neg] using him
    linarith
  have hs₁_nz : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₁_re]; linarith)
  set M₁ : ℝ := 12 * (|γ| + 2) / δ
  have hM₁_ge1 : 1 ≤ M₁ := by
    dsimp only [M₁]
    rw [le_div_iff₀ hδ_pos]
    linarith [abs_nonneg γ]
  have hs₁_bd : ∀ z ∈ Metric.closedBall s₁ (1 / 2), ‖riemannZeta z‖ ≤ M₁ * ‖riemannZeta s₁‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₁)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₁)).trans hz))
    rw [Complex.sub_re, hs₁_re] at hre_diff
    rw [Complex.sub_im, hs₁_im] at him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 2 := by linarith
    have hz_im_lo : 1 ≤ |z.im| := by
      have : |γ| - 1 / 2 ≤ |z.im| := by
        have htri : |γ| ≤ |z.im| + |z.im - γ| := by
          have := abs_sub_le γ z.im 0
          linarith [abs_sub_comm γ z.im, show |γ - 0| = |γ| by simp, show |z.im - 0| = |z.im| by simp]
        linarith [(abs_le.mpr him_diff)]
      linarith
    have hz_im_hi : |z.im| ≤ |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |γ| + |z.im - γ| := by
        simpa [add_sub_cancel] using abs_add_le γ (z.im - γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖riemannZeta z‖ ≤ 6 * (|γ| + 2) := by
      have h := norm_riemannZeta_strip_le hz_re_lo hz_re_hi hz_im_lo
      linarith
    have hinv_s₁ : ‖1 / riemannZeta s₁‖ ≤ 2 / δ := by
      have h := norm_riemannZeta_and_inv_of_one_lt_re hσ1 γ
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      have hle : σ / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ_pos.le
      exact (h.2.1.trans h.2.2).trans hle
    have h1 : ‖riemannZeta z‖ / ‖riemannZeta s₁‖ ≤ M₁ := by
      rw [← norm_div, show riemannZeta z / riemannZeta s₁ = riemannZeta z * (1 / riemannZeta s₁) by ring,
        norm_mul]
      calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₁‖
          ≤ (6 * (|γ| + 2)) * (2 / δ) :=
            mul_le_mul hz_strip hinv_s₁ (norm_nonneg _) (by positivity)
        _ = M₁ := by dsimp only [M₁]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₁_nz)).mp h1
  have hs₁_zeros : ∀ ρ ∈ Metric.closedBall s₁ (1 / 4), riemannZeta ρ = 0 → ρ.re ≤ s₁.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hs₁_re] at hgt; linarith) hρ0
  have hs_mem : s ∈ Metric.closedBall s₁ (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : s - s₁ = (((β - σ : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hlandau₁ := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM₁_ge1 hs₁_an hs₁_nz hs₁_bd hs₁_zeros hs_mem hz
  have hs₁_sub_s : s₁ - s = (((σ - β : ℝ) : ℂ)) := Complex.ext (by simp [s₁, β]) (by simp [s₁, γ])
  have hre_inv : (1 / (s₁ - s)).re = 1 / (σ - β) := by
    rw [hs₁_sub_s, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_err : (s₁ - s).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    rw [hs₁_sub_s, Complex.ofReal_re, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    have hle : σ - β ≤ 1 / 4 := by dsimp only [σ]; linarith
    linarith
  have hbound₁ : (Stage3ZeroFreeRegion.negLogDerivZeta s₁).re ≤
      8 * Real.log M₁ + 1 - 1 / (σ - β) := by
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    rw [hre_inv] at hlandau₁
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at hlandau₁
    linarith
  
  set s₂ : ℂ := (σ : ℂ) + I * ((2 * γ : ℝ) : ℂ)
  have hs₂_re : s₂.re = σ := by simp [s₂]
  have hs₂_im : s₂.im = 2 * γ := by simp [s₂]
  have hs₂_an : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₂ (1 / 2)) := by
    refine (DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton (x := (1 : ℂ)))).mono ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    intro h1
    rw [h1] at hz
    have him_diff := Complex.abs_im_le_norm (1 - s₂)
    rw [Complex.sub_im, Complex.one_im, hs₂_im] at him_diff
    have hge8 : 8 ≤ |0 - 2 * γ| := by
      rw [zero_sub, abs_neg, abs_mul, abs_of_pos two_pos]; linarith
    linarith
  have hs₂_nz : riemannZeta s₂ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₂_re]; linarith)
  set M₂ : ℝ := 24 * (|γ| + 2) / δ
  have hM₂_ge1 : 1 ≤ M₂ := by
    dsimp only [M₂]
    rw [le_div_iff₀ hδ_pos]
    linarith [abs_nonneg γ]
  have hs₂_bd : ∀ z ∈ Metric.closedBall s₂ (1 / 2), ‖riemannZeta z‖ ≤ M₂ * ‖riemannZeta s₂‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₂)).trans hz))
    have him_diff := (abs_le.mp ((Complex.abs_im_le_norm (z - s₂)).trans hz))
    rw [Complex.sub_re, hs₂_re] at hre_diff
    rw [Complex.sub_im, hs₂_im] at him_diff
    have hz_re_lo : 1 / 2 ≤ z.re := by linarith
    have hz_re_hi : z.re ≤ 2 := by linarith
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_of_pos two_pos]
    have hz_im_lo : 1 ≤ |z.im| := by
      have htri : |2 * γ| ≤ |z.im| + |z.im - 2 * γ| := by
        have := abs_sub_le (2 * γ) z.im 0
        linarith [abs_sub_comm (2 * γ) z.im, show |2 * γ - 0| = |2 * γ| by simp,
          show |z.im - 0| = |z.im| by simp]
      linarith [(abs_le.mpr him_diff)]
    have hz_im_hi : |z.im| ≤ 2 * |γ| + 1 / 2 := by
      have htri : |z.im| ≤ |2 * γ| + |z.im - 2 * γ| := by
        simpa [add_sub_cancel] using abs_add_le (2 * γ) (z.im - 2 * γ)
      linarith [(abs_le.mpr him_diff)]
    have hz_strip : ‖riemannZeta z‖ ≤ 12 * (|γ| + 2) := by
      have h := norm_riemannZeta_strip_le hz_re_lo hz_re_hi hz_im_lo
      linarith
    have hinv_s₂ : ‖1 / riemannZeta s₂‖ ≤ 2 / δ := by
      have h := norm_riemannZeta_and_inv_of_one_lt_re hσ1 (2 * γ)
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      have hle : σ / δ ≤ 2 / δ := div_le_div_of_nonneg_right (by linarith) hδ_pos.le
      exact (h.2.1.trans h.2.2).trans hle
    have h1 : ‖riemannZeta z‖ / ‖riemannZeta s₂‖ ≤ M₂ := by
      rw [← norm_div, show riemannZeta z / riemannZeta s₂ = riemannZeta z * (1 / riemannZeta s₂) by ring,
        norm_mul]
      calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₂‖
          ≤ (12 * (|γ| + 2)) * (2 / δ) :=
            mul_le_mul hz_strip hinv_s₂ (norm_nonneg _) (by positivity)
        _ = M₂ := by dsimp only [M₂]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hs₂_nz)).mp h1
  have hs₂_zeros : ∀ ρ ∈ Metric.closedBall s₂ (1 / 4), riemannZeta ρ = 0 → ρ.re ≤ s₂.re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hs₂_re] at hgt; linarith) hρ0
  have hbound₂ : (Stage3ZeroFreeRegion.negLogDerivZeta s₂).re ≤ 8 * Real.log M₂ := by
    have h := landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
      (by norm_num) (by norm_num) hM₂_ge1 hs₂_an hs₂_nz hs₂_bd hs₂_zeros
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
    rw [h8] at h
    exact h
  
  have hbound₀ : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  
  have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_re_nonneg hσ1 γ
  have h2it : (σ : ℂ) + 2 * I * (γ : ℂ) = s₂ := by dsimp only [s₂]; push_cast; ring
  rw [h2it] at h341
  
  have hM₁_le_M₂ : M₁ ≤ M₂ := by
    dsimp only [M₁, M₂]
    exact div_le_div_of_nonneg_right (by linarith [abs_nonneg γ]) hδ_pos.le
  have hlogM₁ : Real.log M₁ ≤ Real.log M₂ := Real.log_le_log (by linarith) hM₁_le_M₂
  have hlogM₂ : Real.log M₂ ≤ Real.log (48000 : ℝ) + 2 * L := by
    have hL_le : L ≤ |γ| + 2 := (Real.log_le_sub_one_of_pos (by linarith [abs_nonneg γ])).trans (by linarith)
    have hM₂_le : M₂ ≤ 48000 * (|γ| + 2) ^ 2 := by
      have hM₂_eq : M₂ = 48000 * (|γ| + 2) * L := by
        dsimp only [M₂, δ]; field_simp [hL_pos.ne']; ring
      rw [hM₂_eq]
      nlinarith [abs_nonneg γ]
    calc Real.log M₂ ≤ Real.log (48000 * (|γ| + 2) ^ 2) := Real.log_le_log (by linarith) hM₂_le
      _ = Real.log (48000 : ℝ) + Real.log ((|γ| + 2) ^ 2) :=
          Real.log_mul (by norm_num) (by positivity)
      _ = Real.log (48000 : ℝ) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  
  have herr_strict : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ < 1 / (2 * δ) := by
    have h1000 : 1000 * L = 1 / (2 * δ) := by
      dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hcomb : 7 + 32 * Real.log M₁ + 8 * Real.log M₂ ≤ (87 + 40 * Real.log (48000 : ℝ)) * L := by
      nlinarith [hlogM₁, hlogM₂, hL_gt1, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 48000)]
    have h2 : (87 + 40 * Real.log (48000 : ℝ)) * L < 1000 * L :=
      mul_lt_mul_of_pos_right numerical_dlvp_closing hL_pos
    linarith
  have hineq_strict : 4 / (σ - β) < 7 / (2 * δ) := by
    have h1 : 4 / (σ - β) < 3 / δ + 1 / (2 * δ) := by
      have h4 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
      have h3 : 3 * (1 / δ) = 3 / δ := by ring
      linarith
    have h2 : 3 / δ + 1 / (2 * δ) = 7 / (2 * δ) := by field_simp [hδ_pos.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by linarith
  have hmul_strict : 8 * δ < 7 * (σ - β) := by
    have h := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq_strict
    linarith
  have hβ_strict : β < 1 - δ / 7 := by dsimp only [σ] at hmul_strict; linarith
  have hδ7 : δ / 7 = 1 / (14000 * L) := by
    dsimp only [δ]; field_simp [hL_pos.ne']; ring
  linarith

theorem riemannZeta_zeroFree_bounded_im :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ s : ℂ, |s.im| ≤ 4 → 1 - ε₀ ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  set K : Set ℂ := {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 4}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 / 2 : ℝ) 1 ×ˢ Set.Icc (-4 : ℝ) 4) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, by
          apply Complex.ext <;> simp⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hfin : (K ∩ riemannZetaZeros).Finite := hK_comp.inter_riemannZetaZeros_finite
  set F : Finset ℂ := hfin.toFinset
  
  have hall_pos : ∀ z ∈ F, 0 < 1 - z.re := by
    intro z hz
    have hmem : z ∈ K ∩ riemannZetaZeros := hfin.mem_toFinset.mp hz
    have hz0 : riemannZeta z = 0 := mem_riemannZetaZeros.mp hmem.2
    have hlt : z.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz0
    linarith
  by_cases hF : F.Nonempty
  · set m : ℝ := F.inf' hF (fun z => 1 - z.re)
    have hm_pos : 0 < m := (Finset.lt_inf'_iff hF).mpr hall_pos
    refine ⟨min (1 / 4) (m / 2), by positivity, fun s him hre _ hz => ?_⟩
    have hlt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz
    have hsK : s ∈ K := ⟨by linarith [min_le_left (1 / 4 : ℝ) (m / 2)], hlt1.le, him⟩
    have hsF : s ∈ F := hfin.mem_toFinset.mpr ⟨hsK, mem_riemannZetaZeros.mpr hz⟩
    have hm_le : m ≤ 1 - s.re := Finset.inf'_le (fun z => 1 - z.re) hsF
    linarith [min_le_right (1 / 4 : ℝ) (m / 2)]
  · refine ⟨1 / 4, by norm_num, fun s him hre _ hz => ?_⟩
    have hlt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      exact riemannZeta_ne_zero_of_one_le_re hge hz
    have hsK : s ∈ K := ⟨by linarith, hlt1.le, him⟩
    have hsF : s ∈ F := hfin.mem_toFinset.mpr ⟨hsK, mem_riemannZetaZeros.mpr hz⟩
    exact hF ⟨s, hsF⟩

theorem riemannZeta_deLaValleePoussin_zeroFree :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨ε₀, hε₀, hbdd⟩ := riemannZeta_zeroFree_bounded_im
  set c : ℝ := min (1 / 14000) (ε₀ * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, fun s hre hs1 => ?_⟩
  have hlog_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hlog_ge
  by_cases him : 4 ≤ |s.im|
  · refine riemannZeta_zeroFree_large_im him ?_
    have hc1 : c ≤ 1 / 14000 := min_le_left _ _
    have hdiv : c / Real.log (|s.im| + 2) ≤ 1 / (14000 * Real.log (|s.im| + 2)) := by
      have h1 := div_le_div_of_nonneg_right hc1 hlog_pos.le
      linarith [show (1 / 14000 : ℝ) / Real.log (|s.im| + 2) =
          1 / (14000 * Real.log (|s.im| + 2)) by ring]
    linarith
  · push Not at him
    refine hbdd s him.le ?_ hs1
    have hc2 : c ≤ ε₀ * Real.log 2 := min_le_right _ _
    have hdiv : c / Real.log (|s.im| + 2) ≤ ε₀ := by
      rw [div_le_iff₀ hlog_pos]
      exact hc2.trans (mul_le_mul_of_nonneg_left hlog_ge hε₀.le)
    linarith

end RHDirect.Stage5ZetaZeroFree
end

/-! ## From RHDirect/Stage5DirichletLZeroFree.lean -/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage5DirichletLZeroFree

theorem harmonic_sum_le_log_add_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ ≤ Real.log (m : ℝ) + 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (((k + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hexp := Real.add_one_le_exp (-(((k + 1 : ℕ) : ℝ))⁻¹)
      have hdiv : (k : ℝ) / ((k + 1 : ℕ) : ℝ) = -(((k + 1 : ℕ) : ℝ))⁻¹ + 1 := by
        push_cast
        field_simp [hk1_pos.ne']
        ring
      rw [← hdiv] at hexp
      have hlog := Real.log_le_log (div_pos hk_pos hk1_pos) hexp
      rw [Real.log_div hk_pos.ne' hk1_pos.ne', Real.log_exp] at hlog
      linarith
    linarith

theorem two_le_of_dirichletChar_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 2 ≤ q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  by_contra hlt
  have hq1 : q = 1 := by omega
  subst hq1
  exact hχ (DirichletCharacter.level_one χ)

theorem sum_dirichletChar_zmod_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ a : ZMod q, χ a = 0 := by
  have hex : ∃ u : (ZMod q)ˣ, χ (u : ZMod q) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hχ
    ext a
    rw [hall a, MulChar.one_apply a.isUnit]
  obtain ⟨u, hu⟩ := hex
  set S : ℂ := ∑ a : ZMod q, χ a
  have hshift : χ (u : ZMod q) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    calc ∑ a : ZMod q, χ (u : ZMod q) * χ a
        = ∑ a : ZMod q, χ ((u : ZMod q) * a) := by
          refine Finset.sum_congr rfl fun a _ => (map_mul χ _ _).symm
      _ = ∑ a : ZMod q, χ a :=
          Fintype.sum_equiv (MulAction.toPerm u) _ _ fun _ => rfl
  have hmul : (χ (u : ZMod q) - 1) * S = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hu)

theorem sum_dirichletChar_Ico_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = 0 := by
  have hbij :
      ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = ∑ a : ZMod q, χ a := by
    have hshift :
        ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) =
          ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) := by
      refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨M + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [Finset.mem_Ico] at hn; congr 2; omega
    rw [hshift]
    have hrange :
        ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) =
          ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [Finset.mem_range] at hk₁ hk₂
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hv
        exact hv
      · intro a _
        exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
      · intro k _; simp [Nat.cast_add]
    rw [hrange]
    exact Fintype.sum_equiv (Equiv.addLeft (M : ZMod q)) _ _ fun _ => rfl
  rw [hbij, sum_dirichletChar_zmod_eq_zero hχ]

theorem norm_sum_dirichletChar_Ico_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  have hperiod_mul : ∀ m : ℕ, ∑ n ∈ Finset.Ico M (M + q * m), χ (n : ZMod q) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hqm : q * (m + 1) = q * m + q := by ring
      have hsplit : Finset.Ico M (M + q * (m + 1)) =
          Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + q * m + q) := by
        ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + q * m + q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj, ih, sum_dirichletChar_Ico_period hχ (M + q * m), add_zero]
  set m := N / q
  set r := N % q
  have hN : N = q * m + r := (Nat.div_add_mod N q).symm
  have hr : r < q := Nat.mod_lt N hq_pos
  have hsplit : Finset.Ico M (M + N) =
      Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + N) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, hperiod_mul m, zero_add]
  calc ‖∑ n ∈ Finset.Ico (M + q * m) (M + N), χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Ico (M + q * m) (M + N), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (M + q * m) (M + N), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => χ.norm_le_one _
    _ = ((Finset.Ico (M + q * m) (M + N)).card : ℝ) := by simp
    _ = (r : ℝ) := by
        rw [Nat.card_Ico]
        exact_mod_cast (by omega : M + N - (M + q * m) = r)
    _ ≤ (q : ℝ) := by exact_mod_cast hr.le

theorem norm_stepSum_dirichletChar_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (x : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) x‖ ≤ (q : ℝ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ico 1 (1 + ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  exact norm_sum_dirichletChar_Ico_le_modulus hχ 1 ⌊x⌋₊

theorem integral_Ioi_log_mul_rpow {a σ : ℝ} (ha : 1 ≤ a) (hσ : 0 < σ) :
    ∫ t in Ioi a, Real.log t * t ^ (-σ - 1) =
      ((σ * Real.log a + 1) / σ ^ 2) * a ^ (-σ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let F : ℝ → ℝ := fun t => -((σ * Real.log t + 1) / σ ^ 2) * t ^ (-σ)
  have hderiv : ∀ t ∈ Ici a, HasDerivAt F (Real.log t * t ^ (-σ - 1)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht
    have hlog : HasDerivAt (fun u : ℝ => -((σ * Real.log u + 1) / σ ^ 2))
        (-((σ * t⁻¹) / σ ^ 2)) t := by
      have h1 : HasDerivAt (fun u : ℝ => σ * Real.log u + 1) (σ * t⁻¹) t := by
        simpa using ((Real.hasDerivAt_log ht0.ne').const_mul σ).add_const (1 : ℝ)
      exact (h1.div_const (σ ^ 2)).neg
    have hpow : HasDerivAt (fun u : ℝ => u ^ (-σ)) ((-σ) * t ^ (-σ - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    refine (hlog.mul hpow).congr_deriv ?_
    have htpow : t⁻¹ * t ^ (-σ) = t ^ (-σ - 1) := by
      rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0]
      congr 1; ring
    calc -((σ * t⁻¹) / σ ^ 2) * t ^ (-σ) +
            -((σ * Real.log t + 1) / σ ^ 2) * (-σ * t ^ (-σ - 1))
        = -(σ / σ ^ 2) * (t⁻¹ * t ^ (-σ)) + ((σ * Real.log t + 1) * σ / σ ^ 2) * t ^ (-σ - 1) := by
          ring
      _ = (-(σ / σ ^ 2) + (σ * Real.log t + 1) * σ / σ ^ 2) * t ^ (-σ - 1) := by
          rw [htpow]; ring
      _ = Real.log t * t ^ (-σ - 1) := by
          field_simp [hσ.ne']; ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hdom : Tendsto (fun t : ℝ => ((2 + 1) / σ ^ 2) * t ^ (-(σ / 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (half_pos hσ)).const_mul ((2 + 1) / σ ^ 2)
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hlog_le : Real.log t ≤ t ^ (σ / 2) / (σ / 2) :=
      Real.log_le_rpow_div ht0.le (half_pos hσ)
    have hlog_mul : σ * Real.log t ≤ 2 * t ^ (σ / 2) := by
      have h1 : σ * (t ^ (σ / 2) / (σ / 2)) = 2 * t ^ (σ / 2) := by field_simp [hσ.ne']
      nlinarith
    have h1_le : (1 : ℝ) ≤ t ^ (σ / 2) := Real.one_le_rpow ht (half_pos hσ).le
    have hnum_nn : 0 ≤ σ * Real.log t + 1 := by
      have := Real.log_nonneg ht; positivity
    have hnum_le : σ * Real.log t + 1 ≤ (2 + 1) * t ^ (σ / 2) := by linarith
    have hpow_comb : t ^ (σ / 2) * t ^ (-σ) = t ^ (-(σ / 2)) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (div_nonneg hnum_nn (sq_nonneg σ)),
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc (σ * Real.log t + 1) / σ ^ 2 * t ^ (-σ)
        ≤ ((2 + 1) * t ^ (σ / 2)) / σ ^ 2 * t ^ (-σ) := by gcongr
      _ = ((2 + 1) / σ ^ 2) * (t ^ (σ / 2) * t ^ (-σ)) := by ring
      _ = ((2 + 1) / σ ^ 2) * t ^ (-(σ / 2)) := by rw [hpow_comb]
  have hint : IntegrableOn (fun t : ℝ => Real.log t * t ^ (-σ - 1)) (Ioi a) := by
    have hdom_int : IntegrableOn (fun t : ℝ => (σ / 2)⁻¹ * t ^ (-1 - σ / 2)) (Ioi a) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - σ / 2 < -1) ha0).const_mul _
    refine hdom_int.mono' ?_ ?_
    · exact (Real.measurable_log.mul (measurable_id.pow_const (-σ - 1))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 ≤ t := ha.trans ht.le
      have ht0 : 0 < t := zero_lt_one.trans_le ht1
      have hlog_le : Real.log t ≤ t ^ (σ / 2) / (σ / 2) :=
        Real.log_le_rpow_div ht0.le (half_pos hσ)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))]
      have hpow_comb : t ^ (σ / 2) * t ^ (-σ - 1) = t ^ (-1 - σ / 2) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      calc Real.log t * t ^ (-σ - 1)
          ≤ (t ^ (σ / 2) / (σ / 2)) * t ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg ht0.le _)
        _ = (σ / 2)⁻¹ * (t ^ (σ / 2) * t ^ (-σ - 1)) := by ring
        _ = (σ / 2)⁻¹ * t ^ (-1 - σ / 2) := by rw [hpow_comb]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hftc]
  dsimp only [F]
  ring

theorem LFunction_eq_mul_mellin_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    show 0 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1
      have hy0 : 0 < y.re := hy
      simpa using hy0
    · have hx0 : 0 < x.re := hx
      have hy0 : 0 < y.re := hy
      have h1 : 0 < a * x.re := mul_pos ha_pos hx0
      have h2 : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy0)
      linarith
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hLHS_an : AnalyticOnNhd ℂ (LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU_open
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum (fun n => χ (n : ZMod q)))
      (Nat.cast_nonneg q) hbd hz
    exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp [U]
  have hEv : LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : 1 < (2 : ℂ).re)] with z (hz : 1 < z.re)
    have hz0 : 0 < z.re := by linarith
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hbd hz0
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz)
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hU_pre h2U hEv hs

private lemma integral_Ioi_one_eq_interval_add_Ioi {f : ℝ → ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hint : IntegrableOn f (Ioi (1 : ℝ))) :
    ∫ t in Ioi (1 : ℝ), f t =
      (∫ t in (1 : ℝ)..a, f t) + ∫ t in Ioi a, f t := by
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi_same
  have hsub1 : Ioc (1 : ℝ) a ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
  have hsub2 : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha
  rw [hunion, setIntegral_union hdisj measurableSet_Ioi (hint.mono_set hsub1) (hint.mono_set hsub2),
    intervalIntegral.integral_of_le ha]

theorem LFunction_eq_partialSum_add_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hint : IntegrableOn
      (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum _) hbd hs
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs, integral_Ioi_one_eq_interval_add_Ioi hN1 hint,
    mul_add]
  have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet
    (fun n => χ (n : ZMod q)) hN1 s
  rw [Nat.floor_natCast] at hab
  linear_combination -hab

set_option maxHeartbeats 2000000 in
theorem deriv_LFunction_eq_partialSum_add_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    deriv (LFunction χ) s =
      -(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
        (∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) -
        s * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  
  let E : ℝ → ℂ := Set.indicator (Ioi (N : ℝ))
    (Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)))
  have hE_meas : Measurable E :=
    (Stage3RealAnalyticLandau.measurable_stepSum _).indicator measurableSet_Ioi
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simp only [Real.rpow_zero, mul_one, E]
    by_cases ht : t ∈ Ioi (N : ℝ)
    · rw [Set.indicator_of_mem ht]
      exact norm_stepSum_dirichletChar_le_modulus hχ t
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact Nat.cast_nonneg q
  have hIoi_eq : ∀ z : ℂ,
      ∫ t in Ioi (N : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1) =
      ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1) := by
    intro z
    have hsub : Ioi (N : ℝ) ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hN1
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1; funext t
    by_cases htN : t ∈ Ioi (N : ℝ)
    · simp [E, htN, hsub htN]
    · by_cases ht1 : t ∈ Ioi (1 : ℝ) <;> simp [E, htN, ht1]
  have hIoi_log_eq :
      ∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
        -(∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) := by
    have hsub : Ioi (N : ℝ) ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hN1
    rw [← integral_neg]
    have h1 :
        ∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
          ∫ t : ℝ, Set.indicator (Ioi (1 : ℝ))
            (fun t : ℝ => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) t :=
      (integral_indicator measurableSet_Ioi).symm
    have h2 :
        ∫ t in Ioi (N : ℝ),
            -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)) =
          ∫ t : ℝ, Set.indicator (Ioi (N : ℝ))
            (fun t : ℝ => -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) t :=
      (integral_indicator measurableSet_Ioi).symm
    rw [h1, h2]
    congr 1; funext t
    by_cases htN : t ∈ Ioi (N : ℝ)
    · simp only [Set.indicator_of_mem htN, Set.indicator_of_mem (hsub htN), E]; ring
    · simp [E, htN]
  
  have hd_cpow : ∀ (n : ℕ), 1 ≤ n →
      HasDerivAt (fun z : ℂ => (n : ℂ) ^ (-z)) (-(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) s := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hfun : (fun z : ℂ => (n : ℂ) ^ (-z)) =
        fun z : ℂ => cexp ((-(Real.log (n : ℝ) : ℂ)) * z) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
      congr 1; ring
    rw [hfun]
    have hlin : HasDerivAt (fun z : ℂ => (-(Real.log (n : ℝ) : ℂ)) * z) (-(Real.log (n : ℝ) : ℂ)) s := by
      simpa using (hasDerivAt_id' s).const_mul (-(Real.log (n : ℝ) : ℂ))
    refine hlin.cexp.congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
    have : (-(Real.log (n : ℝ) : ℂ)) * s = (Real.log (n : ℝ) : ℂ) * (-s) := by ring
    rw [this]; ring
  have hd_sum : HasDerivAt
      (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z))
      (-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))) s := by
    have h := HasDerivAt.fun_sum (u := Finset.Icc 1 N)
      (A := fun n (z : ℂ) => χ (n : ZMod q) * (n : ℂ) ^ (-z))
      (A' := fun n => χ (n : ZMod q) * (-(Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)))
      fun n hn => (hd_cpow n (Finset.mem_Icc.mp hn).1).const_mul (χ (n : ZMod q))
    refine h.congr_deriv ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hd_bdry : HasDerivAt
      (fun z : ℂ => Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z))
      (-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
        (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s))) s := by
    refine ((hd_cpow N hN).const_mul _).congr_deriv ?_
    ring
  have hd_int := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas
    (Nat.cast_nonneg q) hE_bd hs
  have hd_tail : HasDerivAt
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      (1 * (∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
        s * (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)))) s :=
    (hasDerivAt_id' s).mul hd_int
  have hd_tot : HasDerivAt
      (fun z : ℂ =>
        (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z) +
          z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      ((-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) -
        -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s))) +
        (1 * (∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
          s * (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))))) s :=
    (hd_sum.sub hd_bdry).add hd_tail
  have hEv : LFunction χ =ᶠ[𝓝 s]
      (fun z : ℂ =>
        (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-z)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-z) +
          z * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [LFunction_eq_partialSum_add_tail hχ hN hz, hIoi_eq z]
  rw [hEv.deriv_eq, hd_tot.deriv, ← hIoi_eq s, hIoi_log_eq]
  ring

theorem norm_LFunction_le_of_stepSum_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {B : ℝ} (_hB : 0 ≤ B)
    (hstep : ∀ t : ℝ, 1 ≤ t → ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ B * (s.re + |s.im|) / s.re := by
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs, norm_mul]
  have hint_norm :
      ‖∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        B / s.re := by
    have hdom : IntegrableOn (fun t : ℝ => B * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul B
    have hle :
        ‖∫ t in Ioi (1 : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hstep t ht.le) (Real.rpow_nonneg ht0.le _)
    have heval : ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) = B / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]; field_simp [hs.ne']
    exact hle.trans_eq heval
  have hns : ‖s‖ ≤ s.re + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rwa [abs_of_pos hs] at h
  calc ‖s‖ *
        ‖∫ t in Ioi (1 : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ (s.re + |s.im|) * (B / s.re) :=
        mul_le_mul hns hint_norm (norm_nonneg _) (by linarith [abs_nonneg s.im])
    _ = B * (s.re + |s.im|) / s.re := by ring

private lemma log_four_gt : (1.38 : ℝ) < Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

private lemma log_q_mul_abs_add_two_ge {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    (1.38 : ℝ) < Real.log ((q : ℝ) * (|t| + 2)) := by
  have h4le : (4 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have htR : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  exact lt_of_lt_of_le log_four_gt (Real.log_le_log (by norm_num) h4le)

private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

set_option maxHeartbeats 2000000 in
theorem norm_LFunction_le_log_of_one_le_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖LFunction χ s‖ ≤ 5 * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < s.re := by linarith
  set L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 s.im
  set X : ℝ := (q : ℝ) * (|s.im| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith [abs_nonneg s.im]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  rw [LFunction_eq_partialSum_add_tail hχ hN1 hs0]
  
  have hT1 : ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤ Real.log (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re]
          calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-s.re)
              ≤ 1 * (n : ℝ) ^ (-s.re) :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
            _ = (n : ℝ) ^ (-s.re) := one_mul _
            _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
            _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_sum_le_log_add_one hN1
  
  have hT2 : ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1, neg_re]
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (q : ℝ) * ((N : ℝ))⁻¹ :=
          mul_le_mul (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hpow
            (Real.rpow_nonneg hN_pos.le _) hq_pos.le
      _ = (q : ℝ) / (N : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one hN_pos]
          have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg s.im]
          linarith
  
  have hT3 : ‖s * ∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    rw [norm_mul]
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have hint_le :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have h1 :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN_pos.trans ht
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact h1.trans_eq heval
    have hns : ‖s‖ ≤ |s.im| + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0] at h
      linarith
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖s‖ *
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
        ≤ (|s.im| + 2) * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hns hint_le (norm_nonneg _) (by positivity)
      _ ≤ (|s.im| + 2) * ((q : ℝ) * ((N : ℝ))⁻¹ / 1) := by
          gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  have hlogN : Real.log (N : ℝ) ≤ L + Real.log 2 := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  calc ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
          s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
          ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖) +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.log (N : ℝ) + 1 + 1) + 1 := by linarith
    _ ≤ 5 * L := by linarith

set_option maxHeartbeats 2000000 in
theorem norm_deriv_LFunction_le_log_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ}
    (hs1 : 1 - (Real.log ((q : ℝ) * (|s.im| + 2)))⁻¹ ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv (LFunction χ) s‖ ≤ 288 * (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 2 := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  set L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 s.im
  have hL_pos : 0 < L := by linarith
  have hL_ge1 : 1 ≤ L := by linarith
  have hinvL : L⁻¹ < 3 / 4 := by
    rw [inv_lt_comm₀ hL_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    linarith
  have hs_quarter : (1 / 4 : ℝ) ≤ s.re := by linarith
  have hs0 : 0 < s.re := by linarith
  set X : ℝ := (q : ℝ) * (|s.im| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith [abs_nonneg s.im]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * L := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1R
  
  have hN_pow : (N : ℝ) ^ (1 - s.re) ≤ 8 := by
    rw [Real.rpow_def_of_pos hN_pos]
    have hexp_le : Real.log (N : ℝ) * (1 - s.re) ≤ 2 := by
      rcases le_total 1 s.re with hge | hle
      · have hnp : Real.log (N : ℝ) * (1 - s.re) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlogN_nn (by linarith)
        linarith
      · have h1s : 1 - s.re ≤ L⁻¹ := by linarith
        calc Real.log (N : ℝ) * (1 - s.re)
            ≤ (2 * L) * L⁻¹ := mul_le_mul hlogN_le h1s (by linarith) (by positivity)
          _ = 2 := by field_simp [hL_pos.ne']
    exact (Real.exp_le_exp.mpr hexp_le).trans exp_two_lt_eight.le
  
  have hn_pow : ∀ n : ℕ, 1 ≤ n → n ≤ N → (n : ℝ) ^ (-s.re) ≤ 8 * ((n : ℝ))⁻¹ := by
    intro n hn1 hnN
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1R
    have hsplit : (n : ℝ) ^ (-s.re) = (n : ℝ) ^ (1 - s.re) * ((n : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]; congr 1; ring
    rw [hsplit]
    have hfac : (n : ℝ) ^ (1 - s.re) ≤ 8 := by
      rcases le_total 1 s.re with hge | hle
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)).trans (by norm_num)
      · exact (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) (by linarith)).trans hN_pow
    exact mul_le_mul_of_nonneg_right hfac (inv_nonneg.mpr hn0.le)
  
  have hN_split : (N : ℝ) ^ (-s.re) = (N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹ := by
    rw [← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hN_pos]; congr 1; ring
  have hqN : (q : ℝ) * ((N : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN_pos]
    have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg s.im]
    linarith
  have hns : ‖s‖ ≤ |s.im| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h; linarith
  have hsqN : ‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹ ≤ 1 := by
    calc ‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹
        ≤ (|s.im| + 2) * (q : ℝ) * ((N : ℝ))⁻¹ := by gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  rw [deriv_LFunction_eq_partialSum_add_tail hχ hN1 hs0]
  
  have hT1 : ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))‖ ≤
      48 * L ^ 2 := by
    rw [norm_neg]
    have hsum_le :
        ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤
          8 * Real.log (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1R),
        Complex.norm_natCast_cpow_of_pos hn1, neg_re]
      have hlog_n : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (zero_lt_one.trans_le hn1R) (by exact_mod_cast hnN)
      calc ‖χ (n : ZMod q)‖ * Real.log (n : ℝ) * (n : ℝ) ^ (-s.re)
          ≤ 1 * Real.log (N : ℝ) * (8 * ((n : ℝ))⁻¹) := by
            refine mul_le_mul ?_ (hn_pow n hn1 hnN) (Real.rpow_nonneg (by positivity) _) (by positivity)
            exact mul_le_mul (χ.norm_le_one _) hlog_n (Real.log_nonneg hn1R) zero_le_one
        _ = 8 * Real.log (N : ℝ) * ((n : ℝ))⁻¹ := by ring
    have hharm := harmonic_sum_le_log_add_one hN1
    have h1 : Real.log (N : ℝ) + 1 ≤ 3 * L := by linarith
    calc ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)‖
        ≤ 8 * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) :=
          hsum_le.trans (mul_le_mul_of_nonneg_left hharm (by positivity))
      _ ≤ 8 * (2 * L) * (3 * L) := by
          refine mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = 48 * L ^ 2 := by ring
  
  have hT2 : ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
      (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)‖ ≤ 16 * L ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogN_nn,
      Complex.norm_natCast_cpow_of_pos hN1, neg_re, hN_split]
    calc ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ)‖ *
          Real.log (N : ℝ) * ((N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹)
        ≤ (q : ℝ) * (2 * L) * (8 * ((N : ℝ))⁻¹) := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · exact mul_le_mul (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hlogN_le
              hlogN_nn hq_pos.le
          · exact mul_le_mul_of_nonneg_right hN_pow (inv_nonneg.mpr hN_pos.le)
      _ = 16 * L * ((q : ℝ) * ((N : ℝ))⁻¹) := by ring
      _ ≤ 16 * L * 1 := mul_le_mul_of_nonneg_left hqN (by positivity)
      _ = 16 * L := mul_one _
      _ ≤ 16 * L ^ 2 := by nlinarith
  
  have hT3 : ‖∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
      32 * L ^ 2 := by
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have hle :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN_pos.trans ht
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact hle.trans_eq heval
    refine h1.trans ?_
    rw [hN_split]
    have h4 : (s.re)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hs0 (by norm_num : (0 : ℝ) < 4)]; linarith
    calc (q : ℝ) * ((N : ℝ) ^ (1 - s.re) * ((N : ℝ))⁻¹) / s.re
        = ((q : ℝ) * ((N : ℝ))⁻¹) * (N : ℝ) ^ (1 - s.re) * (s.re)⁻¹ := by ring
      _ ≤ 1 * 8 * 4 := by
          refine mul_le_mul ?_ h4 (inv_nonneg.mpr hs0.le) (by norm_num)
          exact mul_le_mul hqN hN_pow (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 32 := by norm_num
      _ ≤ 32 * L ^ 2 := by nlinarith
  
  have hT4 : ‖s * ∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
        (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ 192 * L ^ 2 := by
    rw [norm_mul]
    have hint_log : IntegrableOn (fun t : ℝ => (q : ℝ) * (Real.log t * t ^ (-s.re - 1))) (Ioi (N : ℝ)) := by
      have hdom_int : IntegrableOn (fun t : ℝ => (s.re / 2)⁻¹ * t ^ (-1 - s.re / 2)) (Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - s.re / 2 < -1) hN_pos).const_mul _
      refine (hdom_int.mono' ?_ ?_).const_mul (q : ℝ)
      · exact (Real.measurable_log.mul (measurable_id.pow_const (-s.re - 1))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        have hlog_le : Real.log t ≤ t ^ (s.re / 2) / (s.re / 2) :=
          Real.log_le_rpow_div ht0.le (half_pos hs0)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))]
        have hpow_comb : t ^ (s.re / 2) * t ^ (-s.re - 1) = t ^ (-1 - s.re / 2) := by
          rw [← Real.rpow_add ht0]; congr 1; ring
        calc Real.log t * t ^ (-s.re - 1)
            ≤ (t ^ (s.re / 2) / (s.re / 2)) * t ^ (-s.re - 1) :=
              mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg ht0.le _)
          _ = (s.re / 2)⁻¹ * (t ^ (s.re / 2) * t ^ (-s.re - 1)) := by ring
          _ = (s.re / 2)⁻¹ * t ^ (-1 - s.re / 2) := by rw [hpow_comb]
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) * (N : ℝ) ^ (-s.re)) := by
      have hle :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * (Real.log t * t ^ (-s.re - 1)) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint_log ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        dsimp only
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg ht1),
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre, mul_assoc]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (mul_nonneg (Real.log_nonneg ht1) (Real.rpow_nonneg ht0.le _))
      rw [integral_const_mul, integral_Ioi_log_mul_rpow hN1R hs0] at hle
      exact hle
    have hfrac : (s.re * Real.log (N : ℝ) + 1) / s.re ^ 2 ≤ 24 * L := by
      have h4 : (s.re)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ hs0 (by norm_num : (0 : ℝ) < 4)]; linarith
      have h16 : (s.re ^ 2)⁻¹ ≤ 16 := by
        have : (s.re ^ 2)⁻¹ = (s.re)⁻¹ ^ 2 := by rw [inv_pow]
        rw [this]; nlinarith [inv_nonneg.mpr hs0.le]
      have hsplit2 : (s.re * Real.log (N : ℝ) + 1) / s.re ^ 2 =
          Real.log (N : ℝ) * (s.re)⁻¹ + (s.re ^ 2)⁻¹ := by
        field_simp [hs0.ne']
      rw [hsplit2]
      have hm1 : Real.log (N : ℝ) * (s.re)⁻¹ ≤ (2 * L) * 4 :=
        mul_le_mul hlogN_le h4 (inv_nonneg.mpr hs0.le) (by positivity)
      linarith
    calc ‖s‖ *
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * ((q : ℝ) * (((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) * (N : ℝ) ^ (-s.re))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
      _ = (‖s‖ * (q : ℝ) * ((N : ℝ))⁻¹) * (N : ℝ) ^ (1 - s.re) *
            ((s.re * Real.log (N : ℝ) + 1) / s.re ^ 2) := by
          rw [hN_split]; ring
      _ ≤ 1 * 8 * (24 * L) := by
          refine mul_le_mul ?_ hfrac (by positivity) (by norm_num)
          exact mul_le_mul hsqN hN_pow (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 192 * L := by ring
      _ ≤ 192 * L ^ 2 := by nlinarith
  
  calc ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
          (∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) -
          s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) +
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
              (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s) +
            (∫ t in Ioi (N : ℝ),
              Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1))‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖-(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ (-s))‖ +
          ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (Real.log (N : ℝ) : ℂ) * (N : ℂ) ^ (-s)‖) +
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 48 * L ^ 2 + 16 * L ^ 2 + 32 * L ^ 2 + 192 * L ^ 2 := by linarith
    _ = 288 * L ^ 2 := by ring

private lemma sum_rpow_neg_one_add_le {x : ℝ} (hx : 0 < x) {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(1 + x)) ≤ 1 + (1 - (M : ℝ) ^ (-x)) / x := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk_lt : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hdiff : x * ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤
        (k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) := by
      have hcont : ContinuousOn (fun u : ℝ => -(u ^ (-x))) (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
        refine ContinuousOn.neg (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
        exact Or.inl (lt_of_lt_of_le hk_pos hu.1).ne'
      have hderiv : ∀ u ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ),
          HasDerivAt (fun t : ℝ => -(t ^ (-x))) (x * u ^ (-x - 1)) u := by
        intro u hu
        have hu0 : 0 < u := hk_pos.trans hu.1
        have h := (Real.hasDerivAt_rpow_const (p := -x) (Or.inl hu0.ne')).neg
        refine h.congr_deriv ?_; ring
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun u : ℝ => -(u ^ (-x)))
        (fun u => x * u ^ (-x - 1)) hk_lt hcont hderiv
      have hden : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
      rw [hden, div_one] at hslope
      have hsub : -((k + 1 : ℕ) : ℝ) ^ (-x) - -((k : ℝ) ^ (-x)) =
          (k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x) := by ring
      rw [hsub] at hslope
      rw [← hslope]
      have hc0 : 0 < c := hk_pos.trans hc.1
      have hmono : ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤ c ^ (-x - 1) := by
        rw [show -(1 + x) = -x - 1 by ring]
        exact Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
      exact mul_le_mul_of_nonneg_left hmono hx.le
    have hstep : ((k + 1 : ℕ) : ℝ) ^ (-(1 + x)) ≤
        ((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x := by
      rw [le_div_iff₀ hx]; linarith
    have halg : (1 + (1 - (k : ℝ) ^ (-x)) / x) +
        ((k : ℝ) ^ (-x) - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x =
        1 + (1 - ((k + 1 : ℕ) : ℝ) ^ (-x)) / x := by
      field_simp [hx.ne']; ring
    linarith

theorem norm_LFunction_one_real_le {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 < x) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 1 + 1 / x := by
  have hs : 1 < (1 + (x : ℂ)).re := by simp [hx]
  rw [DirichletCharacter.LFunction_eq_LSeries (1 : DirichletCharacter ℂ q) hs]
  have hsum : LSeriesSummable (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) (1 + (x : ℂ)) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re _ hs
  have hsum_real : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) := by
    have h1 := Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + x)
    refine h1.congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [Real.zero_rpow (by linarith : 1 + x ≠ 0)]
    · simp only [hn, ↓reduceIte, Real.rpow_neg (Nat.cast_nonneg n)]
  have htsum_le : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) ≤ 1 + 1 / x := by
    refine hsum_real.tsum_le_of_sum_range_le (fun N => ?_)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp; positivity
    · have hsplit : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 (N - 1))]
      simp only [↓reduceIte, zero_add]
      have hcongr : ∑ n ∈ Finset.Icc 1 (N - 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) =
          ∑ n ∈ Finset.Icc 1 (N - 1), (n : ℝ) ^ (-(1 + x)) :=
        Finset.sum_congr rfl fun n hn => by
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          simp [hn0]
      rw [hcongr]
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | hpos
      · rw [h0]; simp; positivity
      · have hbd := sum_rpow_neg_one_add_le hx hpos
        have hnn : 0 ≤ (((N - 1 : ℕ) : ℝ)) ^ (-x) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hdiv : (1 - (((N - 1 : ℕ) : ℝ)) ^ (-x)) / x ≤ 1 / x :=
          div_le_div_of_nonneg_right (by linarith) hx.le
        linarith
  have hnorm_le :
      ‖LSeries (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) (1 + (x : ℂ))‖ ≤
        ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-(1 + x))) := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
    refine hsum.norm.tsum_le_tsum (fun n => ?_) hsum_real
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [hn, ↓reduceIte]
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos]
      have hre : (1 + (x : ℂ)).re = 1 + x := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_right ((1 : DirichletCharacter ℂ q).norm_le_one (n : ZMod q))
        (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact hnorm_le.trans htsum_le

theorem norm_LFunction_one_real_le_two_div {q : ℕ} [NeZero q] {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 2 / x := by
  have h1 := norm_LFunction_one_real_le (q := q) hx0
  have h2 : (1 : ℝ) ≤ 1 / x := (one_le_div hx0).mpr hx1
  linarith [show 1 / x + 1 / x = 2 / x by ring]

private lemma sum_coprime_Ico_period {q : ℕ} [NeZero q] (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) = (q.totient : ℝ) := by
  have hbij :
      ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) =
        ∑ a : ZMod q, (if IsUnit a then (1 : ℝ) else 0) := by
    have hshift :
        ∑ n ∈ Finset.Ico M (M + q), (if Nat.Coprime n q then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range q, (if IsUnit ((M + k : ℕ) : ZMod q) then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨M + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [Finset.mem_Ico] at hn
        have hsub : M + (n - M) = n := by omega
        rw [hsub]
        simp [ZMod.isUnit_iff_coprime]
    rw [hshift]
    have hrange :
        ∑ k ∈ Finset.range q, (if IsUnit ((M + k : ℕ) : ZMod q) then (1 : ℝ) else 0) =
          ∑ a : ZMod q, (if IsUnit ((M : ZMod q) + a) then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [Finset.mem_range] at hk₁ hk₂
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hv
        exact hv
      · intro a _
        exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
      · intro k _; simp [Nat.cast_add]
    rw [hrange]
    exact Fintype.sum_equiv (Equiv.addLeft (M : ZMod q)) _ _ fun _ => rfl
  rw [hbij]
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = Fintype.card (ZMod q)ˣ := by
    refine Finset.card_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q)) ?_ ?_ ?_ |>.symm
    · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
    · intro u₁ _ u₂ _ h; exact Units.ext h
    · intro a ha
      obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp ha).2
      exact ⟨u, Finset.mem_univ _, rfl⟩
  rw [hcard, ZMod.card_units_eq_totient]

theorem norm_stepSum_principal_sub_linear_le {q : ℕ} [NeZero q] {u : ℝ} (hu : 0 ≤ u) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) u -
      ((((q.totient : ℝ) / (q : ℝ)) * u : ℝ) : ℂ)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  have hq_posR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
  have hreal :
      Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) u =
        ((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, if Nat.Coprime n q then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    unfold Stage3RealAnalyticLandau.stepSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [Stage2DirichletAP.principal_char_apply_nat]
    split_ifs <;> simp
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set N := ⌊u⌋₊
  set m := N / q
  set r := N % q
  have hN : N = q * m + r := (Nat.div_add_mod N q).symm
  have hr : r < q := Nat.mod_lt N hq_pos
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (1 + q * m) ∪ Finset.Ico (1 + q * m) (1 + N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Ico 1 (1 + q * m)) (Finset.Ico (1 + q * m) (1 + N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  have hblocks : ∀ j : ℕ,
      ∑ n ∈ Finset.Ico 1 (1 + q * j), (if Nat.Coprime n q then (1 : ℝ) else 0) =
        (j : ℝ) * (q.totient : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hqj : q * (j + 1) = q * j + q := by ring
      have hsp : Finset.Ico 1 (1 + q * (j + 1)) =
          Finset.Ico 1 (1 + q * j) ∪ Finset.Ico (1 + q * j) (1 + q * j + q) := by
        ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hd : Disjoint (Finset.Ico 1 (1 + q * j)) (Finset.Ico (1 + q * j) (1 + q * j + q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsp, Finset.sum_union hd, ih, sum_coprime_Ico_period (1 + q * j)]
      push_cast; ring
  rw [hIcc, Finset.sum_union hdisj, hblocks m]
  set R : ℝ := ∑ n ∈ Finset.Ico (1 + q * m) (1 + N), if Nat.Coprime n q then (1 : ℝ) else 0
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hR_le : R ≤ (q : ℝ) := by
    calc R ≤ ∑ _n ∈ Finset.Ico (1 + q * m) (1 + N), (1 : ℝ) :=
            Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = ((Finset.Ico (1 + q * m) (1 + N)).card : ℝ) := by simp
      _ = (r : ℝ) := by rw [Nat.card_Ico]; exact_mod_cast (by omega : 1 + N - (1 + q * m) = r)
      _ ≤ (q : ℝ) := by exact_mod_cast hr.le
  set μ : ℝ := (q.totient : ℝ) / (q : ℝ)
  have hμ_nn : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hq_posR.le
  have hμ_le1 : μ ≤ 1 := (div_le_one hq_posR).mpr (by exact_mod_cast Nat.totient_le q)
  have hu_ge : ((q * m : ℕ) : ℝ) ≤ u := by
    have h1 : (q * m : ℕ) ≤ N := by omega
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hu)
  have hu_lt : u - ((q * m : ℕ) : ℝ) ≤ (q : ℝ) := by
    have h1 : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
    have h2 : (N : ℝ) = ((q * m : ℕ) : ℝ) + (r : ℝ) := by exact_mod_cast hN
    have hr1 : (r : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hr
    linarith
  have hlin_split : μ * u = (m : ℝ) * (q.totient : ℝ) + μ * (u - ((q * m : ℕ) : ℝ)) := by
    dsimp only [μ]; push_cast; field_simp [hq_posR.ne']; ring
  have htail_nn : 0 ≤ μ * (u - ((q * m : ℕ) : ℝ)) := mul_nonneg hμ_nn (by linarith)
  have htail_le : μ * (u - ((q * m : ℕ) : ℝ)) ≤ (q : ℝ) := by
    calc μ * (u - ((q * m : ℕ) : ℝ)) ≤ 1 * (q : ℝ) :=
          mul_le_mul hμ_le1 hu_lt (by linarith) zero_le_one
      _ = (q : ℝ) := one_mul _
  rw [hlin_split]
  have hcancel : (m : ℝ) * (q.totient : ℝ) + R -
      ((m : ℝ) * (q.totient : ℝ) + μ * (u - ((q * m : ℕ) : ℝ))) =
      R - μ * (u - ((q * m : ℕ) : ℝ)) := by ring
  rw [hcancel, abs_le]
  constructor <;> linarith

set_option maxHeartbeats 2000000 in
theorem norm_LFunction_one_strip_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (((1 + x : ℝ) : ℂ) + I * (y : ℂ))‖ ≤
      6 * Real.log ((q : ℝ) * (|y| + 2)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  set s : ℂ := ((1 + x : ℝ) : ℂ) + I * (y : ℂ)
  have hs_re : s.re = 1 + x := by simp [s]
  have hs_im : s.im = y := by simp [s]
  have hs1 : 1 < s.re := by linarith
  have hs0 : 0 < s.re := by linarith
  have hs_ne1 : s - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp [hs_re] at this; linarith
  set L : ℝ := Real.log ((q : ℝ) * (|y| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq y
  set X : ℝ := (q : ℝ) * (|y| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith [abs_nonneg y]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  set μ : ℝ := (q.totient : ℝ) / (q : ℝ)
  have hμ_nn : 0 ≤ μ := div_nonneg (Nat.cast_nonneg _) hq_pos.le
  have hμ_le1 : μ ≤ 1 := (div_le_one hq_pos).mpr (by exact_mod_cast Nat.totient_le q)
  set S : ℝ → ℂ := Stage3RealAnalyticLandau.stepSum (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q))
  set E : ℝ → ℂ := fun t => S t - ((μ * t : ℝ) : ℂ)
  have hS_bd : ∀ t : ℝ, 1 ≤ t → ‖S t‖ ≤ 1 * t ^ (1 : ℝ) := by
    intro t ht
    rw [one_mul, Real.rpow_one]
    have h1 : ‖S t‖ ≤ (⌊t⌋₊ : ℝ) := by
      dsimp only [S, Stage3RealAnalyticLandau.stepSum]
      calc ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : DirichletCharacter ℂ q) (n : ZMod q)‖
          ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ‖(1 : DirichletCharacter ℂ q) (n : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => (1 : DirichletCharacter ℂ q).norm_le_one _
        _ = (⌊t⌋₊ : ℝ) := by simp
    exact h1.trans (Nat.floor_le (by linarith))
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ (q : ℝ) := fun t ht =>
    norm_stepSum_principal_sub_linear_le (by linarith)

  have hL_eq :
      LFunction (1 : DirichletCharacter ℂ q) s =
        (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
          E (N : ℝ) * (N : ℂ) ^ (-s) +
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
          s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hs1]
    have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ q) hs1
    have hmel := Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hS_bd hs1 hsum
    have hintS : IntegrableOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
      Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
        (Stage3RealAnalyticLandau.measurable_stepSum _) hS_bd hs1
    rw [hmel, integral_Ioi_one_eq_interval_add_Ioi hN1R hintS, mul_add]
    have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet
      (fun n => (1 : DirichletCharacter ℂ q) (n : ZMod q)) hN1R s
    rw [Nat.floor_natCast] at hab
    have hlin_int : IntegrableOn (fun t : ℝ => ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
      have ha_pow : (-s).re < -1 := by simp [hs_re]; linarith
      refine IntegrableOn.congr_fun ((integrableOn_Ioi_cpow_of_lt ha_pow hN_pos).const_mul (μ : ℂ))
        (fun t ht => ?_) measurableSet_Ioi
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (hN_pos.trans ht).ne'
      rw [Complex.ofReal_mul, mul_assoc, Complex.cpow_sub _ _ htC, Complex.cpow_one]
      field_simp
    have hlin_val :
        ∫ t in Ioi (N : ℝ), ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) =
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      have ha_pow : (-s).re < -1 := by simp [hs_re]; linarith
      have hcongr : EqOn (fun t : ℝ => ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
          (fun t : ℝ => (μ : ℂ) * (t : ℂ) ^ (-s)) (Ioi (N : ℝ)) := fun t ht => by
        have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (hN_pos.trans ht).ne'
        dsimp only
        rw [Complex.ofReal_mul, mul_assoc, Complex.cpow_sub _ _ htC, Complex.cpow_one]
        field_simp
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
        integral_Ioi_cpow_of_lt ha_pow hN_pos]
      have h1s' : -s + 1 = 1 - s := by ring
      have h1s_ne : 1 - s ≠ 0 := by intro h; apply hs_ne1; linear_combination -h
      rw [Complex.ofReal_natCast, h1s']
      field_simp [hs_ne1, h1s_ne]
      ring
    have hE_int : IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
      have h1 : IntegrableOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
        hintS.mono_set (Ioi_subset_Ioi hN1R)
      refine IntegrableOn.congr_fun (h1.sub hlin_int) (fun t _ => ?_) measurableSet_Ioi
      dsimp only [Pi.sub_apply, E]; ring
    have hsplit_int :
        ∫ t in Ioi (N : ℝ), S t * (t : ℂ) ^ (-s - 1) =
          (∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
            (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      have hpt : EqOn (fun t : ℝ => S t * (t : ℂ) ^ (-s - 1))
          (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1) + ((μ * t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1))
          (Ioi (N : ℝ)) := fun t _ => by dsimp only [E]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hE_int hlin_int, hlin_val]
    have hN_pow : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
      have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
      rw [Complex.cpow_sub _ _ hNC, Complex.cpow_one, Complex.cpow_neg, div_eq_mul_inv]
    rw [hsplit_int]
    have hS_N : S (N : ℝ) = E (N : ℝ) + (μ : ℂ) * (N : ℂ) := by
      dsimp only [E]; push_cast; ring
    have hmul_comb :
        -((μ : ℂ) * (N : ℂ)) * (N : ℂ) ^ (-s) + s * ((μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)) =
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) := by
      rw [hN_pow]
      field_simp [hs_ne1]
      ring
    calc (s * ∫ t in (1 : ℝ)..(N : ℝ), S t * (t : ℂ) ^ (-s - 1)) +
            s * ((∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
              (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1))
        = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            S (N : ℝ) * (N : ℂ) ^ (-s) +
            s * ((∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)) +
              (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)) := by
          linear_combination -hab
      _ = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            E (N : ℝ) * (N : ℂ) ^ (-s) +
            (-((μ : ℂ) * (N : ℂ)) * (N : ℂ) ^ (-s) + s * ((μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1))) +
            s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
          rw [hS_N]; ring
      _ = (∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
            E (N : ℝ) * (N : ℂ) ^ (-s) +
            (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
            s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1) := by
          rw [hmul_comb]
  rw [hL_eq]
  
  have hT1 : ‖∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
      Real.log (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖(1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re, hs_re]
          calc ‖(1 : DirichletCharacter ℂ q) (n : ZMod q)‖ * (n : ℝ) ^ (-(1 + x))
              ≤ 1 * (n : ℝ) ^ (-(1 + x)) :=
                mul_le_mul_of_nonneg_right ((1 : DirichletCharacter ℂ q).norm_le_one _)
                  (Real.rpow_nonneg (by positivity) _)
            _ = (n : ℝ) ^ (-(1 + x)) := one_mul _
            _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
            _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_sum_le_log_add_one hN1
  have hT2 : ‖E (N : ℝ) * (N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1, neg_re, hs_re]
    have hpow : (N : ℝ) ^ (-(1 + x)) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    calc ‖E (N : ℝ)‖ * (N : ℝ) ^ (-(1 + x))
        ≤ (q : ℝ) * ((N : ℝ))⁻¹ :=
          mul_le_mul (hE_bd (N : ℝ) hN1R) hpow (Real.rpow_nonneg hN_pos.le _) hq_pos.le
      _ = (q : ℝ) / (N : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one hN_pos]
          have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg y]
          linarith
  have hT3 : ‖(μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ_nn,
      Complex.norm_natCast_cpow_of_pos hN1]
    have hre1 : (1 - s).re = -x := by simp [hs_re]
    rw [hre1]
    have hpow1 : (N : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
    have hden : 1 ≤ ‖s - 1‖ := by
      have him1 : (s - 1).im = y := by simp [hs_im]
      calc (1 : ℝ) ≤ |y| := hy
        _ = |(s - 1).im| := by rw [him1]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    rw [div_le_one (by linarith)]
    calc μ * (N : ℝ) ^ (-x) ≤ 1 * 1 :=
          mul_le_mul hμ_le1 hpow1 (Real.rpow_nonneg hN_pos.le _) zero_le_one
      _ = 1 := one_mul _
      _ ≤ ‖s - 1‖ := hden
  have hT4 : ‖s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    rw [norm_mul]
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have hint_le :
        ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤ (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have h1 :
          ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ ≤
            ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := hN1R.trans ht.le
        have ht0 : 0 < t := zero_lt_one.trans_le ht1
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (hE_bd t ht1) (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact h1.trans_eq heval
    have hns : ‖s‖ ≤ |y| + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0, hs_re, hs_im] at h; linarith
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    calc ‖s‖ * ‖∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖
        ≤ (|y| + 2) * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hns hint_le (norm_nonneg _) (by positivity)
      _ ≤ (|y| + 2) * ((q : ℝ) * ((N : ℝ))⁻¹ / 1) := by gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  have hlogN : Real.log (N : ℝ) ≤ L + Real.log 2 := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  calc ‖(∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)) -
          E (N : ℝ) * (N : ℂ) ^ (-s) +
          (μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1) +
          s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖
      ≤ (‖∑ n ∈ Finset.Icc 1 N, (1 : DirichletCharacter ℂ q) (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
          ‖E (N : ℝ) * (N : ℂ) ^ (-s)‖) +
          ‖(μ : ℂ) * (N : ℂ) ^ (1 - s) / (s - 1)‖ +
          ‖s * ∫ t in Ioi (N : ℝ), E t * (t : ℂ) ^ (-s - 1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (Real.log (N : ℝ) + 1 + 1) + 1 + 1 := by linarith
    _ ≤ 6 * L := by linarith

theorem norm_LFunction_sub_le_of_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {σ₁ σ₂ t : ℝ}
    (hσ₁ : 1 - (Real.log ((q : ℝ) * (|t| + 2)))⁻¹ ≤ σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2) :
    ‖LFunction χ ((σ₂ : ℂ) + I * (t : ℂ)) - LFunction χ ((σ₁ : ℂ) + I * (t : ℂ))‖ ≤
      (σ₂ - σ₁) * (288 * (Real.log ((q : ℝ) * (|t| + 2))) ^ 2) := by
  let f : ℝ → ℂ := fun u => LFunction χ ((u : ℂ) + I * (t : ℂ))
  have hf_deriv : ∀ u : ℝ,
      HasDerivAt f (deriv (LFunction χ) ((u : ℂ) + I * (t : ℂ))) u := by
    intro u
    have hL : HasDerivAt (LFunction χ) (deriv (LFunction χ) ((u : ℂ) + I * (t : ℂ)))
        ((u : ℂ) + I * (t : ℂ)) :=
      (DirichletCharacter.differentiable_LFunction hχ ((u : ℂ) + I * (t : ℂ))).hasDerivAt
    have hshift := hL.comp (u : ℂ) ((hasDerivAt_id (u : ℂ)).add_const (I * (t : ℂ)))
    rw [mul_one] at hshift
    exact hshift.comp_ofReal
  have hbd := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f)
    (s := Set.Icc σ₁ σ₂) (C := 288 * (Real.log ((q : ℝ) * (|t| + 2))) ^ 2)
    (fun u _ => (hf_deriv u).differentiableAt)
    (fun u hu => by
      rw [(hf_deriv u).deriv]
      have h := norm_deriv_LFunction_le_log_sq hχ (s := (u : ℂ) + I * (t : ℂ))
        (by simp; linarith [hu.1]) (by simp; linarith [hu.2])
      simpa using h)
    (convex_Icc σ₁ σ₂) ⟨le_rfl, hσ₁₂⟩ ⟨hσ₁₂, le_rfl⟩
  have hnorm : ‖σ₂ - σ₁‖ = σ₂ - σ₁ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hσ₁₂)]
  rw [hnorm] at hbd
  simpa only [f, mul_comm] using hbd

def oneLineLowerConst : ℝ := 1 / (1536 * 288 ^ 3)

theorem oneLineLowerConst_pos : 0 < oneLineLowerConst := by
  unfold oneLineLowerConst; positivity

theorem norm_LFunction_one_add_I_mul_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {t : ℝ} (hcase : χ ^ 2 ≠ 1 ∨ 1 ≤ |t|) :
    oneLineLowerConst / (Real.log ((q : ℝ) * (|t| + 2))) ^ 7 ≤
      ‖LFunction χ (1 + I * (t : ℂ))‖ := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  set L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 t
  have hL_pos : 0 < L := by linarith
  have hL_ge1 : 1 ≤ L := by linarith
  set a : ℝ := 1 / (1536 * 288 ^ 4)
  have ha_pos : 0 < a := by positivity
  have ha_le1 : a ≤ 1 := by dsimp only [a]; norm_num
  set x : ℝ := a / L ^ 9
  have hx_pos : 0 < x := div_pos ha_pos (pow_pos hL_pos 9)
  have hx_le1 : x ≤ 1 := by
    rw [div_le_one (pow_pos hL_pos 9)]
    exact ha_le1.trans (one_le_pow₀ hL_ge1)
  have htarget_eq : oneLineLowerConst / L ^ 7 = 288 * x * L ^ 2 := by
    dsimp only [oneLineLowerConst, x, a]
    field_simp [hL_pos.ne']
  rw [htarget_eq]
  by_contra hlt
  push Not at hlt
  
  have hmvt := norm_LFunction_sub_le_of_strip hχ (σ₁ := 1) (σ₂ := 1 + x) (t := t)
    (by linarith [inv_pos.mpr hL_pos]) (by linarith) (by linarith)
  have hsub_eq : (1 + x : ℝ) - 1 = x := by ring
  rw [hsub_eq] at hmvt
  have hcast1 : ((1 : ℝ) : ℂ) + I * (t : ℂ) = 1 + I * (t : ℂ) := by simp
  have hcastx : ((1 + x : ℝ) : ℂ) + I * (t : ℂ) = 1 + (x : ℂ) + I * (t : ℂ) := by push_cast; ring
  rw [hcast1, hcastx] at hmvt
  have hL_chi_lt : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ < 2 * (288 * x * L ^ 2) := by
    have htri : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ≤
        ‖LFunction χ (1 + I * (t : ℂ))‖ +
          ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ)) - LFunction χ (1 + I * (t : ℂ))‖ := by
      have := norm_add_le (LFunction χ (1 + I * (t : ℂ)))
        (LFunction χ (1 + (x : ℂ) + I * (t : ℂ)) - LFunction χ (1 + I * (t : ℂ)))
      simpa using this
    linarith
  
  have hL1 : ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ≤ 2 / x :=
    norm_LFunction_one_real_le_two_div hx_pos hx_le1
  
  have hL2 : ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖ ≤ 12 * L := by
    have harg : (1 + (x : ℂ) + 2 * I * (t : ℂ)) = ((1 + x : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ) := by
      push_cast; ring
    have hlog2t : Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * L := by
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
      have hle : (q : ℝ) * (|2 * t| + 2) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [abs_nonneg t]
      have h1 := Real.log_le_log (by positivity) hle
      have hmul : Real.log (2 * ((q : ℝ) * (|t| + 2))) = Real.log 2 + L :=
        Real.log_mul (by norm_num) (by positivity)
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    rcases hcase with hsq_ne | ht1
    · have hbd := norm_LFunction_le_log_of_one_le_re hsq_ne
        (s := 1 + (x : ℂ) + 2 * I * (t : ℂ)) (by simp [hx_pos.le]) (by simp; linarith)
      have him2 : (1 + (x : ℂ) + 2 * I * (t : ℂ)).im = 2 * t := by simp
      rw [him2] at hbd
      linarith
    · by_cases hsq_ne : χ ^ 2 ≠ 1
      · have hbd := norm_LFunction_le_log_of_one_le_re hsq_ne
          (s := 1 + (x : ℂ) + 2 * I * (t : ℂ)) (by simp [hx_pos.le]) (by simp; linarith)
        have him2 : (1 + (x : ℂ) + 2 * I * (t : ℂ)).im = 2 * t := by simp
        rw [him2] at hbd
        linarith
      · push Not at hsq_ne
        rw [hsq_ne, harg]
        have h2t : 1 ≤ |2 * t| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have hbd := norm_LFunction_one_strip_le (q := q) hq2 hx_pos hx_le1 h2t
        linarith
  
  have h341 := Stage2DirichletAP.norm_LFunction_three_four_one_ge_one χ hx_pos t
  simp only [norm_mul, norm_pow] at h341
  have hpow3 : ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 ≤ (2 / x) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hL1 3
  have hpow4 : ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 < (2 * (288 * x * L ^ 2)) ^ 4 :=
    pow_lt_pow_left₀ hL_chi_lt (norm_nonneg _) (by norm_num)
  have hprod_lt :
      ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
        ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 *
        ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖ <
      (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) := by
    have h12 :
        ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
          ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 <
        (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 := by
      have hpos3 : 0 < (2 / x) ^ 3 := by positivity
      calc ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
              ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4
          ≤ (2 / x) ^ 3 * ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 :=
            mul_le_mul_of_nonneg_right hpow3 (pow_nonneg (norm_nonneg _) 4)
        _ < (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 :=
            mul_lt_mul_of_pos_left hpow4 hpos3
    calc ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
            ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 *
            ‖LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * I * (t : ℂ))‖
        ≤ ‖LFunction (1 : DirichletCharacter ℂ q) (1 + (x : ℂ))‖ ^ 3 *
            ‖LFunction χ (1 + (x : ℂ) + I * (t : ℂ))‖ ^ 4 * (12 * L) :=
          mul_le_mul_of_nonneg_left hL2 (mul_nonneg (pow_nonneg (norm_nonneg _) 3) (pow_nonneg (norm_nonneg _) 4))
      _ < (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) :=
          mul_lt_mul_of_pos_right h12 (by positivity)
  have hrhs_eq : (2 / x) ^ 3 * (2 * (288 * x * L ^ 2)) ^ 4 * (12 * L) = 1 := by
    dsimp only [x, a]
    field_simp [hL_pos.ne']
    ring
  linarith

def zeroFreeConst : ℝ := 1 / (3072 * 288 ^ 4)

theorem zeroFreeConst_pos : 0 < zeroFreeConst := by
  unfold zeroFreeConst; positivity

theorem LFunction_ne_zero_in_zeroFreeRegion {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hcase : χ ^ 2 ≠ 1 ∨ 1 ≤ |s.im|)
    (hs : 1 - zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤ s.re) :
    LFunction χ s ≠ 0 := by
  by_cases hge1 : 1 ≤ s.re
  · exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) hge1
  · push Not at hge1
    have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
    set t : ℝ := s.im
    set L : ℝ := Real.log ((q : ℝ) * (|t| + 2))
    have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 t
    have hL_pos : 0 < L := by linarith
    have hL_ge1 : 1 ≤ L := by linarith
    have hc_le1 : zeroFreeConst ≤ 1 := by unfold zeroFreeConst; norm_num
    have hdiv_le : zeroFreeConst / L ^ 9 ≤ L⁻¹ := by
      rw [inv_eq_one_div]
      have hpow : L ≤ L ^ 9 := by
        calc L = L ^ 1 := (pow_one L).symm
          _ ≤ L ^ 9 := pow_le_pow_right₀ hL_ge1 (by norm_num)
      exact div_le_div₀ zero_le_one hc_le1 hL_pos hpow
    have hmvt := norm_LFunction_sub_le_of_strip hχ (σ₁ := s.re) (σ₂ := 1) (t := t)
      (by linarith) hge1.le (by norm_num)
    have hlow := norm_LFunction_one_add_I_mul_ge hχ hcase
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s
      simpa only [t, mul_comm I] using this
    have h1_eq : ((1 : ℝ) : ℂ) + I * (t : ℂ) = 1 + I * (t : ℂ) := by simp
    rw [hs_eq, h1_eq] at hmvt
    have hdiff_lt : (1 - s.re) * (288 * L ^ 2) < oneLineLowerConst / L ^ 7 := by
      have h1s : 1 - s.re ≤ zeroFreeConst / L ^ 9 := by linarith
      have hmul : (1 - s.re) * (288 * L ^ 2) ≤ (zeroFreeConst / L ^ 9) * (288 * L ^ 2) :=
        mul_le_mul_of_nonneg_right h1s (by positivity)
      have hhalf : (zeroFreeConst / L ^ 9) * (288 * L ^ 2) = (oneLineLowerConst / L ^ 7) / 2 := by
        unfold zeroFreeConst oneLineLowerConst
        field_simp [hL_pos.ne']
        ring
      have hpos_low : 0 < oneLineLowerConst / L ^ 7 :=
        div_pos oneLineLowerConst_pos (pow_pos hL_pos 7)
      linarith
    intro hzero
    rw [hzero, sub_zero] at hmvt
    linarith

end RHDirect.Stage5DirichletLZeroFree
end

/-! ## From RHDirect/Stage6EffectivePNT.lean -/

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage6EffectivePNT

def zetaReg (z : ℂ) : ℂ :=
  1 + (z - 1) *
    (1 - z * ∫ t in Ioi (1 : ℝ),
      ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))

def negLogDerivZetaReg (z : ℂ) : ℂ :=
  -deriv zetaReg z / zetaReg z

theorem zetaReg_one : zetaReg 1 = 1 := by
  simp [zetaReg]

theorem zetaReg_eq_mul_riemannZeta {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    zetaReg z = (z - 1) * riemannZeta z := by
  unfold zetaReg
  rw [← Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin hz hz1]
  have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hne]
  ring

theorem differentiableOn_zetaReg : DifferentiableOn ℂ zetaReg {z : ℂ | 0 < z.re} := by
  have hE_meas : Measurable (fun t : ℝ => -((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp Stage5ZetaZeroFree.measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t →
      ‖-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact Stage5ZetaZeroFree.norm_fractNat_le_one (zero_le_one.trans ht)
  have hH_an := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
  have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ),
        (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
      fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    funext z
    have hneg : (fun t : ℝ => (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t; ring
    rw [hneg, integral_neg]; ring
  rw [hEq] at hH_an
  have hH_diff : DifferentiableOn ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) {z : ℂ | 0 < z.re} :=
    hH_an.differentiableOn
  unfold zetaReg
  exact (differentiableOn_const 1).add ((differentiableOn_id.sub (differentiableOn_const 1)).mul hH_diff)

theorem negLogDerivZetaReg_eq_sub_pole {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1)
    (hnz : riemannZeta z ≠ 0) :
    negLogDerivZetaReg z = (-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1) := by
  have hopen : IsOpen ({w : ℂ | 0 < w.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : zetaReg =ᶠ[𝓝 z] fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [hopen.mem_nhds ⟨hz, hz1⟩] with w hw
    exact zetaReg_eq_mul_riemannZeta hw.1 hw.2
  have hdz : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (1 * riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
    ((hasDerivAt_id z).sub_const 1).mul (differentiableAt_riemannZeta hz1).hasDerivAt
  have hderiv_eq : deriv zetaReg z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
    rw [hev.deriv_eq, hdz.deriv, one_mul]
  unfold negLogDerivZetaReg
  rw [hderiv_eq, zetaReg_eq_mul_riemannZeta hz hz1]
  have hsub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hsub_ne, hnz]
  ring

theorem isOpen_re_pos_zetaReg_ne_zero :
    IsOpen {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ContinuousOn zetaReg {z : ℂ | 0 < z.re} := differentiableOn_zetaReg.continuousOn
  have hset : {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} =
      {z : ℂ | 0 < z.re} ∩ zetaReg ⁻¹' ({(0 : ℂ)}ᶜ) := by
    ext z; simp
  rw [hset]
  exact hcont.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl

theorem differentiableOn_negLogDerivZetaReg :
    DifferentiableOn ℂ negLogDerivZetaReg {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
  have hU := isOpen_re_pos_zetaReg_ne_zero
  have hsub : {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} ⊆ {z : ℂ | 0 < z.re} := fun _ hz => hz.1
  have hdiff : DifferentiableOn ℂ zetaReg {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} :=
    differentiableOn_zetaReg.mono hsub
  unfold negLogDerivZetaReg
  exact (hdiff.deriv hU).neg.div hdiff fun _ hz => hz.2

set_option maxHeartbeats 2000000 in
theorem negLogDerivZeta_zeroFree_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
        ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C₁ * (Real.log (|s.im| + 2)) ^ 2 := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  set c : ℝ := min c₀ (1 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc₀_pos (by norm_num)
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  set c₁ : ℝ := c / 16 with hc₁_def
  have hc₁_pos : 0 < c₁ := by positivity
  set C_right : ℝ := 1 / c₁ + 1
  set C_left : ℝ := (16 / c) * (Real.log (112 / c) + 2)
  have h112_gt1 : (1 : ℝ) < 112 / c := by
    rw [one_lt_div hc_pos]; linarith
  have hC_left_pos : 0 < C_left := by
    have hlog_pos : 0 < Real.log (112 / c) := Real.log_pos h112_gt1
    positivity
  set C₁ : ℝ := max C_right C_left
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c₁, hc₁_pos, C₁, hC₁_pos, fun s hre_lo hre_hi him => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have ht2_ge3 : (3 : ℝ) ≤ |t| + 2 := by linarith
  have ht2_pos : 0 < |t| + 2 := by linarith
  have hL_gt1 : 1 < L := by
    have h3 : Real.exp 1 < |t| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h3)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  by_cases hright : 1 + c₁ / L ≤ s.re
  · 
    have hs_re_gt1 : 1 < s.re := by
      have : 0 < c₁ / L := div_pos hc₁_pos hL_pos
      linarith
    have hs_eq : s = (s.re : ℂ) + I * (t : ℂ) := by
      apply Complex.ext <;> simp [t]
    have hbd := Stage5ZetaZeroFree.norm_negLogDerivZeta_of_one_lt_re hs_re_gt1 t
    have hnorm_le : ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + 1 := by
      have h1 := hbd.1.trans hbd.2
      unfold Stage3ZeroFreeRegion.negLogDerivZeta at h1
      rwa [← hs_eq] at h1
    have hinv_le : 1 / (s.re - 1) ≤ L / c₁ := by
      rw [div_le_div_iff₀ (by linarith) hc₁_pos, one_mul]
      have h1 : c₁ / L ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL_pos.le
      rw [div_mul_cancel₀ _ hL_pos.ne'] at h2
      linarith
    have hL_le_L2 : L ≤ L ^ 2 := by nlinarith
    have h1_le_L2 : 1 ≤ L ^ 2 := by nlinarith
    have hC_right_le : C_right ≤ C₁ := le_max_left _ _
    calc ‖-deriv riemannZeta s / riemannZeta s‖
        ≤ 1 / (s.re - 1) + 1 := hnorm_le
      _ ≤ (1 / c₁) * L + 1 := by linarith [show L / c₁ = (1 / c₁) * L by ring]
      _ ≤ (1 / c₁) * L ^ 2 + 1 * L ^ 2 := by
          have h1 : (1 / c₁) * L ≤ (1 / c₁) * L ^ 2 :=
            mul_le_mul_of_nonneg_left hL_le_L2 (by positivity)
          linarith
      _ = C_right * L ^ 2 := by dsimp only [C_right]; ring
      _ ≤ C₁ * L ^ 2 := mul_le_mul_of_nonneg_right hC_right_le (sq_nonneg L)
  · 
    push Not at hright
    set η : ℝ := c / (8 * L) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      dsimp only [η]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    
    have hball_ne1 : ∀ z ∈ Metric.ball s₀ R_open, z ≠ 1 := by
      intro z hz h1
      subst h1
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have him_diff := (Complex.abs_im_le_norm ((1 : ℂ) - s₀)).trans_lt hz
      rw [Complex.sub_im, Complex.one_im, hs₀_im, zero_sub, abs_neg] at him_diff
      have hR_lt : R_open < 1 := by dsimp only [R_open]; linarith
      linarith
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, riemannZeta z ≠ 0 := by
      intro z hz
      have hz1 : z ≠ 1 := hball_ne1 z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le_half : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv_ge : c / (2 * L) ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c / (2 * L) ≤ c / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_pos.le hlogz_pos hlog_le
          _ ≤ c₀ / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_le_c₀ hlogz_pos.le
      have h4η : 4 * η = c / (2 * L) := by dsimp only [η]; ring
      have hz_re_ge : 1 - c₀ / Real.log (|z.im| + 2) ≤ z.re := by
        dsimp only [R_open] at hre_diff
        linarith
      exact hzf₀ z hz_re_ge hz1
    have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball s₀ R_open) := fun z hz =>
      (differentiableAt_riemannZeta (hball_ne1 z hz)).differentiableWithinAt
    
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    
    set M : ℝ := (Real.log (112 / c) + 2) * L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hz1 : z ≠ 1 := hball_ne1 z hz_ball
      have hznz : riemannZeta z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_lo : 1 / 2 ≤ |z.im| := by
        have htri : |t| ≤ |z.im| + |z.im - t| := by
          have := abs_sub_le t z.im 0
          linarith [abs_sub_comm t z.im, show |t - 0| = |t| by simp, show |z.im - 0| = |z.im| by simp]
        linarith [abs_le.mpr him_diff]
      have hz_im_hi : |z.im| ≤ |t| + 1 / 8 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖riemannZeta z‖ ≤ 7 * (|t| + 2) := by
        have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith : 0 < z.re) hz1
        have hsub_ge : 1 / 2 ≤ ‖z - 1‖ := by
          have := Complex.abs_im_le_norm (z - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
          linarith
        have hinv_le : 1 / ‖z - 1‖ ≤ 2 := by
          rw [div_le_iff₀ (by linarith : 0 < ‖z - 1‖)]; linarith
        have hnorm_z : ‖z‖ ≤ 2 * (|t| + 2) := by
          have := Complex.norm_le_abs_re_add_abs_im z
          rw [abs_of_pos (by linarith : 0 < z.re)] at this
          linarith
        have hdiv_le : ‖z‖ / z.re ≤ 4 * (|t| + 2) := by
          rw [div_le_iff₀ (by linarith : 0 < z.re)]
          nlinarith
        linarith
      have hinv_s₀ : ‖1 / riemannZeta s₀‖ ≤ 16 * L / c := by
        have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (by linarith : 1 < 1 + η) t
        have h1 := h.2.1.trans h.2.2
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h1
        have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
        rw [hs₀_eq'] at h1
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
        have h3 : 2 / η = 16 * L / c := by dsimp only [η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
        linarith
      have hratio_le : ‖riemannZeta z / riemannZeta s₀‖ ≤ (112 / c) * (|t| + 2) ^ 2 := by
        have hL_le_t2 : L ≤ |t| + 2 :=
          (Real.log_le_sub_one_of_pos ht2_pos).trans (by linarith)
        rw [show riemannZeta z / riemannZeta s₀ = riemannZeta z * (1 / riemannZeta s₀) by ring,
          norm_mul]
        calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₀‖
            ≤ (7 * (|t| + 2)) * (16 * L / c) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = (112 / c) * ((|t| + 2) * L) := by ring
          _ ≤ (112 / c) * ((|t| + 2) * (|t| + 2)) := by
              gcongr
          _ = (112 / c) * (|t| + 2) ^ 2 := by ring
      have hre_eq : (Log z).re = Real.log ‖riemannZeta z / riemannZeta s₀‖ := by
        have hexp : Real.exp (Log z).re = ‖riemannZeta z / riemannZeta s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖riemannZeta z / riemannZeta s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      rw [hre_eq]
      calc Real.log ‖riemannZeta z / riemannZeta s₀‖
          ≤ Real.log ((112 / c) * (|t| + 2) ^ 2) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (112 / c) + Real.log ((|t| + 2) ^ 2) :=
            Real.log_mul (by positivity) (by positivity)
        _ = Real.log (112 / c) + 2 * L := by rw [Real.log_pow]; push_cast; rfl
        _ ≤ (Real.log (112 / c) + 2) * L := by
            nlinarith [Real.log_pos h112_gt1]
    
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc₁_eq : c₁ / L = η / 2 := by dsimp only [c₁, η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 16 * L / c := by
      dsimp only [R, r, η]
      field_simp [hc_pos.ne', hL_pos.ne']
      ring
    rw [hcoeff] at hbc
    have hneg_norm : ‖-deriv riemannZeta s / riemannZeta s‖ = ‖deriv riemannZeta s / riemannZeta s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ (16 * L / c) * M := hbc
      _ = C_left * L ^ 2 := by dsimp only [C_left, M]; ring
      _ ≤ C₁ * L ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg L)

theorem negLogDerivZeta_sub_pole_bounded_near_one :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ s : ℂ, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
        zetaReg s ≠ 0 ∧ ‖negLogDerivZetaReg s‖ ≤ C₂) ∧
      (∀ s : ℂ, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → s ≠ 1 →
        ‖(-deriv riemannZeta s / riemannZeta s) - 1 / (s - 1)‖ ≤ C₂) := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c₂ : ℝ := min (1 / 4) (c₀ / (2 * Real.log 3)) with hc₂_def
  have hc₂_pos : 0 < c₂ := lt_min (by norm_num) (by positivity)
  have hc₂_le_qtr : c₂ ≤ 1 / 4 := min_le_left _ _
  have hc₂_le_log : c₂ ≤ c₀ / (2 * Real.log 3) := min_le_right _ _
  set K : Set ℂ := {z : ℂ | 1 - c₂ ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 - c₂) 2 ×ˢ Set.Icc (-1 : ℝ) 1) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.ext (by simp) (by simp)⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
    intro z hz
    have hz_re : 0 < z.re := by linarith [hz.1]
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [zetaReg_one]; exact one_ne_zero
    · rw [zetaReg_eq_mul_riemannZeta hz_re hz1]
      refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
      have hlog_le : Real.log (|z.im| + 2) ≤ Real.log 3 :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith [hz.2.2])
      have hlog_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv : c₂ ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c₂ ≤ c₀ / (2 * Real.log 3) := hc₂_le_log
          _ ≤ c₀ / Real.log 3 := div_le_div_of_nonneg_left hc₀_pos.le hlog3_pos (by linarith)
          _ ≤ c₀ / Real.log (|z.im| + 2) := div_le_div_of_nonneg_left hc₀_pos.le hlog_pos hlog_le
      exact hzf₀ z (by linarith [hz.1]) hz1
  have hcont_K : ContinuousOn negLogDerivZetaReg K :=
    (differentiableOn_negLogDerivZetaReg.mono hK_sub).continuousOn
  obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn hcont_K
  set C₂ : ℝ := max M 1
  have hC₂_pos : 0 < C₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨c₂, hc₂_pos, C₂, hC₂_pos, ?_, ?_⟩
  · intro s hlo hhi him
    have hsK : s ∈ K := ⟨hlo, hhi, him⟩
    exact ⟨(hK_sub hsK).2, (hM s hsK).trans (le_max_left _ _)⟩
  · intro s hlo hhi him hs1
    have hsK : s ∈ K := ⟨hlo, hhi, him⟩
    have hs_re : 0 < s.re := (hK_sub hsK).1
    have hsnz : riemannZeta s ≠ 0 := by
      have hreg := (hK_sub hsK).2
      rw [zetaReg_eq_mul_riemannZeta hs_re hs1] at hreg
      exact (mul_ne_zero_iff.mp hreg).2
    rw [← negLogDerivZetaReg_eq_sub_pole hs_re hs1 hsnz]
    exact (hM s hsK).trans (le_max_left _ _)

def psi1 (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * max (x - (n : ℝ)) 0

theorem psi1_nonneg (x : ℝ) : 0 ≤ psi1 x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

theorem psi1_eq_psi1Char_one (x : ℝ) :
    (psi1 x : ℂ) = Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ 1) x := by
  unfold psi1 Stage4ExplicitFormula.psi1Char
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Stage2DirichletAP.principal_char_apply_nat (q := 1) n]
  simp

lemma negLogDerivL_one_eq_negLogDerivZeta (s : ℂ) :
    Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) s =
      Stage3ZeroFreeRegion.negLogDerivZeta s := by
  unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  rw [hL]

set_option maxHeartbeats 2000000 in
theorem integral_boundary_rect_inv_sub_one {σ c T : ℝ} (hσ : σ < 1) (hc : 1 < c) (hT : 0 < T) :
    ((∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
      (∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹)) +
      I • (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) -
      I • (∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      2 * Real.pi * I := by
  set a : ℝ := c - 1
  set b : ℝ := 1 - σ
  have ha : 0 < a := by dsimp only [a]; linarith
  have hb : 0 < b := by dsimp only [b]; linarith
  
  have hright : I • (∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      2 * I * (Real.arctan (T / a) : ℂ) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    set F_r : ℝ → ℂ := fun t =>
      ((Real.log (a ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) + I * (Real.arctan (t / a) : ℂ)
    have hderiv : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt F_r (I * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) t := by
      intro t _
      have hden_pos : 0 < a ^ 2 + t ^ 2 := by positivity
      have h1 : HasDerivAt (fun u : ℝ => Real.log (a ^ 2 + u ^ 2) / 2) (t / (a ^ 2 + t ^ 2)) t := by
        have hsq : HasDerivAt (fun u : ℝ => a ^ 2 + u ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_const t (a ^ 2)).fun_add (hasDerivAt_pow 2 t)
        refine ((hsq.log hden_pos.ne').div_const 2).congr_deriv ?_
        ring
      have h2 : HasDerivAt (fun u : ℝ => Real.arctan (u / a)) (a / (a ^ 2 + t ^ 2)) t := by
        have hlin : HasDerivAt (fun u : ℝ => u / a) (1 / a) t := by
          simpa using (hasDerivAt_id t).div_const a
        refine (hlin.arctan).congr_deriv ?_
        field_simp [ha.ne', hden_pos.ne']
      have h3 := h1.ofReal_comp.add (h2.ofReal_comp.const_mul I)
      refine h3.congr_deriv ?_
      have hca : (c : ℂ) + (t : ℂ) * I - 1 = (a : ℂ) + (t : ℂ) * I := by
        dsimp only [a]; push_cast; ring
      rw [hca]
      have hne1 : (a : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hdenC : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_pos.ne'
      push_cast
      rw [← div_eq_mul_inv, eq_div_iff hne1, ← mul_div_assoc, ← add_div, div_mul_eq_mul_div,
        div_eq_iff hdenC]
      linear_combination ((t : ℂ) * (a : ℂ)) * Complex.I_sq
    have hcont : ContinuousOn (fun t : ℝ => I * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹) (Set.uIcc (-T) T) := by
      refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => ?_)
      have := congrArg Complex.re h0; simp at this; linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    dsimp only [F_r]
    have hneg_sq : (-T) ^ 2 = T ^ 2 := by ring
    have hneg_div : -T / a = -(T / a) := neg_div a T
    rw [hneg_sq, hneg_div, Real.arctan_neg]
    push_cast; ring
  
  have hleft : I • (∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) =
      -(2 * I * (Real.arctan (T / b) : ℂ)) := by
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    set F_l : ℝ → ℂ := fun t =>
      ((Real.log (b ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan (t / b) : ℂ)
    have hderiv : ∀ t ∈ Set.uIcc (-T) T,
        HasDerivAt F_l (I * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) t := by
      intro t _
      have hden_pos : 0 < b ^ 2 + t ^ 2 := by positivity
      have h1 : HasDerivAt (fun u : ℝ => Real.log (b ^ 2 + u ^ 2) / 2) (t / (b ^ 2 + t ^ 2)) t := by
        have hsq : HasDerivAt (fun u : ℝ => b ^ 2 + u ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_const t (b ^ 2)).fun_add (hasDerivAt_pow 2 t)
        refine ((hsq.log hden_pos.ne').div_const 2).congr_deriv ?_
        ring
      have h2 : HasDerivAt (fun u : ℝ => Real.arctan (u / b)) (b / (b ^ 2 + t ^ 2)) t := by
        have hlin : HasDerivAt (fun u : ℝ => u / b) (1 / b) t := by
          simpa using (hasDerivAt_id t).div_const b
        refine (hlin.arctan).congr_deriv ?_
        field_simp [hb.ne', hden_pos.ne']
      have h3 := h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
      refine h3.congr_deriv ?_
      have hσb : (σ : ℂ) + (t : ℂ) * I - 1 = -(b : ℂ) + (t : ℂ) * I := by
        dsimp only [b]; push_cast; ring
      rw [hσb]
      have hne1 : -(b : ℂ) + (t : ℂ) * I ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hdenC : (b : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hden_pos.ne'
      push_cast
      rw [← div_eq_mul_inv, eq_div_iff hne1, ← mul_div_assoc, ← sub_div, div_mul_eq_mul_div,
        div_eq_iff hdenC]
      linear_combination (-(t : ℂ) * (b : ℂ)) * Complex.I_sq
    have hcont : ContinuousOn (fun t : ℝ => I * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹) (Set.uIcc (-T) T) := by
      refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => ?_)
      have := congrArg Complex.re h0; simp at this; linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    dsimp only [F_l]
    have hneg_sq : (-T) ^ 2 = T ^ 2 := by ring
    have hneg_div : -T / b = -(T / b) := neg_div b T
    rw [hneg_sq, hneg_div, Real.arctan_neg]
    push_cast; ring
  
  have hhoriz : (∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) -
      (∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) =
      2 * I * ((Real.arctan (a / T) : ℂ) + (Real.arctan (b / T) : ℂ)) := by
    have hcont_bot : ContinuousOn (fun u : ℝ => ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹) (Set.uIcc σ c) :=
      ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
    have hcont_top : ContinuousOn (fun u : ℝ => ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) (Set.uIcc σ c) :=
      ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
    rw [← intervalIntegral.integral_sub hcont_bot.intervalIntegrable hcont_top.intervalIntegrable]
    set F_h : ℝ → ℂ := fun u => 2 * I * (Real.arctan ((u - 1) / T) : ℂ)
    have hderiv : ∀ u ∈ Set.uIcc σ c,
        HasDerivAt F_h (((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ - ((u : ℂ) + (T : ℂ) * I - 1)⁻¹) u := by
      intro u _
      have hden_pos : 0 < (u - 1) ^ 2 + T ^ 2 := by positivity
      have h1 : HasDerivAt (fun x : ℝ => Real.arctan ((x - 1) / T))
          (T / ((u - 1) ^ 2 + T ^ 2)) u := by
        have hlin : HasDerivAt (fun x : ℝ => (x - 1) / T) (1 / T) u := by
          simpa using ((hasDerivAt_id u).sub_const 1).div_const T
        refine (hlin.arctan).congr_deriv ?_
        field_simp [hT.ne', hden_pos.ne']
        ring
      refine (h1.ofReal_comp.const_mul (2 * I)).congr_deriv ?_
      have hne1 : (u : ℂ) + ((-T : ℝ) : ℂ) * I - 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have hne2 : (u : ℂ) + (T : ℂ) * I - 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have hprod : ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1) * ((u : ℂ) + (T : ℂ) * I - 1) =
          ((u : ℂ) - 1) ^ 2 + (T : ℂ) ^ 2 := by
        push_cast
        linear_combination -((T : ℂ) ^ 2) * Complex.I_sq
      rw [inv_sub_inv hne1 hne2, hprod]
      push_cast
      rw [← mul_div_assoc]
      congr 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont_bot.sub hcont_top).intervalIntegrable]
    dsimp only [F_h]
    have hσ1 : (σ - 1) / T = -(b / T) := by dsimp only [b]; ring
    have hc1 : (c - 1) / T = a / T := rfl
    rw [hc1, hσ1, Real.arctan_neg]
    push_cast; ring
  
  rw [hhoriz, hright, hleft]
  have hpi_a : Real.arctan (T / a) + Real.arctan (a / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos (div_pos hT ha)
    rw [inv_div] at h
    linarith
  have hpi_b : Real.arctan (T / b) + Real.arctan (b / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos (div_pos hT hb)
    rw [inv_div] at h
    linarith
  have hpiC : ((Real.arctan (T / a) : ℂ) + (Real.arctan (a / T) : ℂ)) +
      ((Real.arctan (T / b) : ℂ) + (Real.arctan (b / T) : ℂ)) = (Real.pi : ℂ) := by
    norm_cast
    linarith
  calc 2 * I * ((Real.arctan (a / T) : ℂ) + (Real.arctan (b / T) : ℂ)) +
          2 * I * (Real.arctan (T / a) : ℂ) - -(2 * I * (Real.arctan (T / b) : ℂ))
      = 2 * I * (((Real.arctan (T / a) : ℂ) + (Real.arctan (a / T) : ℂ)) +
          ((Real.arctan (T / b) : ℂ) + (Real.arctan (b / T) : ℂ))) := by ring
    _ = 2 * I * (Real.pi : ℂ) := by rw [hpiC]
    _ = 2 * Real.pi * I := by ring

set_option maxHeartbeats 2000000 in
theorem perron_contour_shift_psi1 {x σ c T : ℝ} (hx : 0 < x)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hc1 : 1 < c) (hT : 0 < T)
    (hzf : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T → z ≠ 1 → riemannZeta z ≠ 0) :
    let F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T -
        ((x : ℂ) ^ 2 / 2) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  intro F
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set W : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))
  have hW_one : W 1 = (x : ℂ) ^ 2 / 2 := by
    dsimp only [W]
    rw [show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    ring
  have hW_diff : DifferentiableOn ℂ W {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs_re : 0 < s.re := hs
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (z + 1)) s := by
      have hEq : (fun z : ℂ => (x : ℂ) ^ (z + 1)) =
          fun z : ℂ => cexp (Complex.log (x : ℂ) * (z + 1)) :=
        funext fun z => Complex.cpow_def_of_ne_zero hxC _
      rw [hEq]; fun_prop
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; exact lt_irrefl 0 hs_re
    have hs1 : s + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact (hpow.div (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
      (mul_ne_zero hs0 hs1)).differentiableWithinAt
  set H₁ : ℂ → ℂ := fun s => negLogDerivZetaReg s * W s + dslope W 1 s
  
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ zetaReg s ≠ 0}
  have hrect_sub : Set.uIcc σ c ×ℂ Set.uIcc (-T) T ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : σ ≤ c),
      Set.uIcc_of_le (by linarith : -T ≤ T)] at hz
    have hz_re : 0 < z.re := lt_of_lt_of_le hσ0 hz.1.1
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [zetaReg_one]; exact one_ne_zero
    · rw [zetaReg_eq_mul_riemannZeta hz_re hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1)
        (hzf z hz.1.1 hz.1.2 (abs_le.mpr hz.2) hz1)
  have hH₁_diff : DifferentiableOn ℂ H₁ (Set.uIcc σ c ×ℂ Set.uIcc (-T) T) := by
    have hds_diff : DifferentiableOn ℂ (dslope W 1) {s : ℂ | 0 < s.re} :=
      (Complex.differentiableOn_dslope
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))).mpr hW_diff
    have h1 : DifferentiableOn ℂ H₁ U :=
      (differentiableOn_negLogDerivZetaReg.mul (hW_diff.mono fun _ h => h.1)).add
        (hds_diff.mono fun _ h => h.1)
    exact h1.mono hrect_sub
  
  set z₀ : ℂ := (σ : ℂ) + ((-T : ℝ) : ℂ) * I
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = σ := by simp [z₀]
  have hz₀_im : z₀.im = -T := by simp [z₀]
  have hw₀_re : w₀.re = c := by simp [w₀]
  have hw₀_im : w₀.im = T := by simp [w₀]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H₁ z₀ w₀
    (by simpa [hz₀_re, hz₀_im, hw₀_re, hw₀_im] using hH₁_diff)
  simp only [hz₀_re, hz₀_im, hw₀_re, hw₀_im] at hcauchy
  
  have hdecomp : ∀ s ∈ U, s ≠ 1 → F s = H₁ s + ((x : ℂ) ^ 2 / 2) * (s - 1)⁻¹ := by
    intro s hs hs1
    have hsnz : riemannZeta s ≠ 0 := by
      have hreg := hs.2
      rw [zetaReg_eq_mul_riemannZeta hs.1 hs1] at hreg
      exact (mul_ne_zero_iff.mp hreg).2
    have hreg_eq := negLogDerivZetaReg_eq_sub_pole hs.1 hs1 hsnz
    dsimp only [F, H₁, Stage3ZeroFreeRegion.negLogDerivZeta]
    rw [hreg_eq, dslope_of_ne W hs1, slope_def_field, hW_one]
    have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    dsimp only [W]
    field_simp [hsub_ne]
    ring
  
  have hH₁_cont : ContinuousOn H₁ (Set.uIcc σ c ×ℂ Set.uIcc (-T) T) := hH₁_diff.continuousOn
  have hbot_H₁ : IntervalIntegrable (fun u : ℝ => H₁ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) volume σ c := by
    refine (hH₁_cont.comp (by fun_prop) fun u hu => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [hu, Set.left_mem_uIcc]
  have htop_H₁ : IntervalIntegrable (fun u : ℝ => H₁ ((u : ℂ) + (T : ℂ) * I)) volume σ c := by
    refine (hH₁_cont.comp (by fun_prop) fun u hu => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [hu, Set.right_mem_uIcc]
  have hright_H₁ : IntervalIntegrable (fun t : ℝ => H₁ ((c : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine (hH₁_cont.comp (by fun_prop) fun t ht => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [ht, Set.right_mem_uIcc]
  have hleft_H₁ : IntervalIntegrable (fun t : ℝ => H₁ ((σ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
    refine (hH₁_cont.comp (by fun_prop) fun t ht => ?_).intervalIntegrable
    rw [Complex.mem_reProdIm]; simp [ht, Set.left_mem_uIcc]
  have hbot_inv : IntervalIntegrable (fun u : ℝ => ((x : ℂ) ^ 2 / 2) * ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹)
      volume σ c :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
      have := congrArg Complex.im h0; simp at this; linarith)).intervalIntegrable
  have htop_inv : IntervalIntegrable (fun u : ℝ => ((x : ℂ) ^ 2 / 2) * ((u : ℂ) + (T : ℂ) * I - 1)⁻¹)
      volume σ c :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun u _ h0 => by
      have := congrArg Complex.im h0; simp at this; linarith)).intervalIntegrable
  have hright_inv : IntervalIntegrable (fun t : ℝ => ((x : ℂ) ^ 2 / 2) * ((c : ℂ) + (t : ℂ) * I - 1)⁻¹)
      volume (-T) T :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => by
      have := congrArg Complex.re h0; simp at this; linarith)).intervalIntegrable
  have hleft_inv : IntervalIntegrable (fun t : ℝ => ((x : ℂ) ^ 2 / 2) * ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹)
      volume (-T) T :=
    (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t _ h0 => by
      have := congrArg Complex.re h0; simp at this; linarith)).intervalIntegrable
  
  have hbot_F : ∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I) =
      (∫ u in σ..c, H₁ ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ u in σ..c, ((u : ℂ) + ((-T : ℝ) : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hbot_H₁ hbot_inv]
    refine intervalIntegral.integral_congr fun u hu => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [hu, Set.left_mem_uIcc]
    · have := congrArg Complex.im h1; simp at this; linarith
  have htop_F : ∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I) =
      (∫ u in σ..c, H₁ ((u : ℂ) + (T : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ u in σ..c, ((u : ℂ) + (T : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add htop_H₁ htop_inv]
    refine intervalIntegral.integral_congr fun u hu => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [hu, Set.right_mem_uIcc]
    · have := congrArg Complex.im h1; simp at this; linarith
  have hright_F : ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) =
      (∫ t in (-T)..T, H₁ ((c : ℂ) + (t : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ t in (-T)..T, ((c : ℂ) + (t : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hright_H₁ hright_inv]
    refine intervalIntegral.integral_congr fun t ht => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [ht, Set.right_mem_uIcc]
    · have := congrArg Complex.re h1; simp at this; linarith
  have hleft_F : ∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I) =
      (∫ t in (-T)..T, H₁ ((σ : ℂ) + (t : ℂ) * I)) +
      ((x : ℂ) ^ 2 / 2) * ∫ t in (-T)..T, ((σ : ℂ) + (t : ℂ) * I - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hleft_H₁ hleft_inv]
    refine intervalIntegral.integral_congr fun t ht => hdecomp _ (hrect_sub ?_) fun h1 => ?_
    · rw [Complex.mem_reProdIm]; simp [ht, Set.left_mem_uIcc]
    · have := congrArg Complex.re h1; simp at this; linarith
  
  have hres := integral_boundary_rect_inv_sub_one hσ1 hc1 hT
  have hrect_F :
      ((∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I))) +
      I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) =
      (2 * Real.pi * I) * ((x : ℂ) ^ 2 / 2) := by
    rw [hbot_F, htop_F, hright_F, hleft_F]
    simp only [smul_eq_mul] at hcauchy hres
    linear_combination hcauchy + ((x : ℂ) ^ 2 / 2) * hres
  
  have htrunc_eq :
      Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I) := by
    unfold Stage4ExplicitFormula.truncatedPerronPsi1
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [F]
    rw [negLogDerivL_one_eq_negLogDerivZeta, mul_comm I (t : ℂ)]
    have hadd : (c : ℂ) + 1 + (t : ℂ) * I = (c : ℂ) + (t : ℂ) * I + 1 := by ring
    rw [hadd]
  rw [htrunc_eq]
  have h2pi_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2piI_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]
    exact mul_ne_zero h2pi_ne hI_ne
  
  apply mul_left_cancel₀ h2piI_ne
  have h2pi_cast : (2 * Real.pi * I : ℂ) * ((2 * Real.pi : ℝ) : ℂ)⁻¹ = I := by
    have : (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, mul_comm _ I, mul_assoc, mul_inv_cancel₀ h2pi_ne, mul_one]
  calc (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) - (x : ℂ) ^ 2 / 2)
      = I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) - (2 * Real.pi * I : ℂ) * ((x : ℂ) ^ 2 / 2) := by
        rw [mul_sub, ← mul_assoc, h2pi_cast]
    _ = I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
        linear_combination hrect_F
    _ = (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
          (2 * Real.pi * I : ℂ)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
          (2 * Real.pi * I : ℂ)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
        rw [mul_sub, mul_add, ← mul_assoc, h2pi_cast, ← mul_assoc, ← mul_assoc,
          mul_inv_cancel₀ h2piI_ne, one_mul, one_mul]

private lemma mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos u)).mpr h1

private lemma sq_mul_exp_neg_two_le_one {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * Real.exp (-2 * u) ≤ 1 := by
  have h1 := mul_exp_neg_le_one u
  have h2 : u ^ 2 * Real.exp (-2 * u) = (u * Real.exp (-u)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h2]
  nlinarith [mul_nonneg hu (Real.exp_pos (-u)).le]

set_option maxHeartbeats 2000000 in
theorem effective_pnt_psi1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |psi1 x - x ^ 2 / 2| ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := negLogDerivZeta_zeroFree_bound
  obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂, hbd₂'⟩ := negLogDerivZeta_sub_pole_bounded_near_one
  obtain ⟨c₀, hc₀, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  
  set c_star : ℝ := min (min c₀ c₁) (min (c₂ * Real.log 2) (1 / 4)) with hc_star_def
  have hc_star_pos : 0 < c_star := by positivity
  have hc_star_le_c₀ : c_star ≤ c₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_star_le_c₁ : c_star ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_star_le_c₂ : c_star ≤ c₂ * Real.log 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc_star_le_qtr : c_star ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  
  set α : ℝ := Real.sqrt (c_star / 2) with hα_def
  have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have hα_sq : α ^ 2 = c_star / 2 := Real.sq_sqrt (by positivity)
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  
  set x₀ : ℝ := max 2 (Real.exp (1 / α ^ 2)) with hx₀_def
  have hx₀_ge2 : 2 ≤ x₀ := le_max_left _ _
  
  set K_left : ℝ := C₁ + 2 * (C₂ + 1 / c_star)
  have hK_left_pos : 0 < K_left := by positivity
  set K_large : ℝ :=
    (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) * (16 / α ^ 2)
  have hK_large_pos : 0 < K_large := by positivity
  
  have hlarge : ∀ x : ℝ, x₀ ≤ x →
      |psi1 x - x ^ 2 / 2| ≤ K_large * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
    intro x hx
    have hx2 : 2 ≤ x := hx₀_ge2.trans hx
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_log2 : Real.log 2 ≤ Lx := Real.log_le_log (by norm_num) hx2
    have hLx_pos : 0 < Lx := hlog2_pos.trans_le hLx_ge_log2
    have hLx_ge_inv : 1 / α ^ 2 ≤ Lx := by
      have hexp : Real.exp (1 / α ^ 2) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp (1 / α ^ 2)).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    have hα_sqrt_ge1 : 1 ≤ α * Real.sqrt Lx := by
      have hsq : 1 ^ 2 ≤ (α * Real.sqrt Lx) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hLx_pos.le, one_pow]
        have h := mul_le_mul_of_nonneg_left hLx_ge_inv (sq_nonneg α)
        rwa [mul_one_div_cancel (sq_pos_of_pos hα_pos).ne'] at h
      nlinarith [mul_nonneg hα_pos.le (Real.sqrt_nonneg Lx)]
    set T : ℝ := Real.exp (α * Real.sqrt Lx) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hT_ge_e : Real.exp 1 ≤ T := Real.exp_le_exp.mpr hα_sqrt_ge1
    have hT_ge2 : 2 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlogT : Real.log T = α * Real.sqrt Lx := Real.log_exp _
    set LT : ℝ := Real.log (T + 2) with hLT_def
    have hLT_ge1 : 1 ≤ LT := by
      have h : Real.exp 1 ≤ T + 2 := by linarith
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h)
    have hLT_pos : 0 < LT := zero_lt_one.trans_le hLT_ge1
    have hLT_le : LT ≤ 2 * (α * Real.sqrt Lx) := by
      have hle2T : T + 2 ≤ 2 * T := by linarith
      have h1 : LT ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hle2T
      rw [Real.log_mul (by norm_num) hT_pos.ne', hlogT] at h1
      have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    
    set c : ℝ := 1 + 1 / (2 * Lx) with hc_def
    have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (by linarith : 0 < 2 * Lx)]
    have hc_le2 : c ≤ 2 := by
      have h2Lx : 1 ≤ 2 * Lx := by linarith [Real.log_two_gt_d9]
      have : 1 / (2 * Lx) ≤ 1 := (div_le_one (by linarith)).mpr h2Lx
      dsimp only [c]; linarith
    have hx_pow_c : x ^ (c + 1) ≤ 2 * x ^ 2 := by
      have h1 : x ^ (c + 1) = x ^ 2 * x ^ (1 / (2 * Lx)) := by
        rw [show c + 1 = (2 : ℝ) + 1 / (2 * Lx) by dsimp only [c]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (1 / (2 * Lx)) = Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]
        congr 1; field_simp [hLx_pos.ne']
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
          linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]
      rw [h1, h2]
      nlinarith [sq_nonneg x]
    set σ_T : ℝ := 1 - c_star / LT with hσ_def
    have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos hLT_pos]
    have hσ_ge_half : 1 / 2 ≤ σ_T := by
      have h1 : c_star / LT ≤ 1 / 4 := by
        calc c_star / LT ≤ c_star / 1 := div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLT_ge1
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le_qtr
      dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    have hσ_ge_c₂ : 1 - c₂ ≤ σ_T := by
      have hlog2_le_LT : Real.log 2 ≤ LT := Real.log_le_log (by norm_num) (by linarith)
      have h1 : c_star / LT ≤ c₂ := by
        rw [div_le_iff₀ hLT_pos]
        exact hc_star_le_c₂.trans (mul_le_mul_of_nonneg_left hlog2_le_LT hc₂.le)
      dsimp only [σ_T]; linarith
    
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T → z ≠ 1 → riemannZeta z ≠ 0 := by
      intro z hlo _ him hz1
      have hlog_le : Real.log (|z.im| + 2) ≤ LT :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
      have hlog_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have h1 : c_star / LT ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c_star / LT ≤ c_star / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
          _ ≤ c₀ / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_star_le_c₀ hlog_pos.le
      exact hzf₀ z (by linarith) hz1
    
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    
    have htrunc_err :
        ‖(psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      rw [psi1_eq_psi1Char_one]
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le
        (1 : DirichletCharacter ℂ 1) hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ 1) x -
              Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by
            gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    
    have hshift := perron_contour_shift_psi1 hx0 hσ_pos hσ_lt1 hc_gt1 hT_pos hzf_rect
    
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ u in σ_T..c, F ((u : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      have hle : σ_T ≤ c := by linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) fun u hu => ?_).trans ?_
      · rw [Set.uIoc_of_le hle] at hu
        set z : ℂ := (u : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = u := by simp [z]
        have hz_im : z.im = sgn * T := by simp [z]
        have hz_abs_im : |z.im| = T := by
          rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hz_re_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
          rw [hz_re, hz_abs_im]
          have : c_star / LT ≤ c₁ / LT := div_le_div_of_nonneg_right hc_star_le_c₁ hLT_pos.le
          dsimp only [σ_T] at hu; linarith [hu.1]
        have hz_re_hi : z.re ≤ 2 := by rw [hz_re]; linarith [hu.2]
        have hnd := hbd₁ z hz_re_lo hz_re_hi (by rw [hz_abs_im]; linarith)
        rw [hz_abs_im] at hnd
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = u + 1 := by simp [hz_re]
          rw [hre1]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hu.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by
            have := Complex.abs_im_le_norm (z + 1)
            simpa [hz_abs_im] using this
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [norm_div, norm_mul]
        calc ‖-deriv riemannZeta z / riemannZeta z‖ * ‖(x : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 2) * x ^ (c + 1) / T ^ 2 := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
                (sq_pos_of_pos hT_pos) hden_ge
          _ = C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd (-1) (by norm_num)
    
    have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hopen := isOpen_re_pos_zetaReg_ne_zero
      have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
      have hmem : ∀ t ∈ Set.Icc (-T) T, (σ_T : ℂ) + (t : ℂ) * I ∈ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
        intro t ht
        refine ⟨by simp [hσ_pos], ?_⟩
        have hne1 : (σ_T : ℂ) + (t : ℂ) * I ≠ 1 := fun h1 => by
          have := congrArg Complex.re h1; simp at this; linarith
        rw [zetaReg_eq_mul_riemannZeta (by simp [hσ_pos]) hne1]
        exact mul_ne_zero (sub_ne_zero.mpr hne1)
          (hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2]) hne1)
      have hnd_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivZeta ((σ_T : ℂ) + (t : ℂ) * I))
          (Set.Icc (-T) T) := by
        have hreg_cont : ContinuousOn (fun t : ℝ => negLogDerivZetaReg ((σ_T : ℂ) + (t : ℂ) * I) +
            1 / ((σ_T : ℂ) + (t : ℂ) * I - 1)) (Set.Icc (-T) T) := by
          refine (differentiableOn_negLogDerivZetaReg.continuousOn.comp hmap.continuousOn hmem).add ?_
          refine continuousOn_const.div (by fun_prop) fun t _ h0 => ?_
          have := congrArg Complex.re h0; simp at this; linarith
        refine hreg_cont.congr fun t ht => ?_
        have hne1 : (σ_T : ℂ) + (t : ℂ) * I ≠ 1 := fun h1 => by
          have := congrArg Complex.re h1; simp at this; linarith
        have hnz : riemannZeta ((σ_T : ℂ) + (t : ℂ) * I) ≠ 0 :=
          hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2]) hne1
        dsimp only [Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [negLogDerivZetaReg_eq_sub_pole (by simp [hσ_pos]) hne1 hnz]
        ring
      have hpow_cont : Continuous (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
        have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
        have hEq : (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hnd_cont.mul hpow_cont.continuousOn).div (by fun_prop) fun t _ => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hint_seg : ∀ a b : ℝ, -T ≤ a → a ≤ b → b ≤ T →
        IntervalIntegrable (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) volume a b := by
      intro a b ha hab hb
      refine (hleft_cont.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
    
    have hsplit_left :
        ∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I) =
          (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith))
        (hint_seg (-1) 1 (by linarith) (by norm_num) (by linarith))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) 1 le_rfl (by linarith) (by linarith))
        (hint_seg 1 T (by linarith) (by linarith) le_rfl)
      rw [h1, h2]
    
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hlog_le : Real.log (|t| + 2) ≤ LT := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have hlog_pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hz_re_lo : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by
        rw [hz_re, hz_im]
        have h1 : c_star / LT ≤ c₁ / Real.log (|t| + 2) := by
          calc c_star / LT ≤ c_star / Real.log (|t| + 2) :=
                div_le_div_of_nonneg_left hc_star_pos.le hlog_pos hlog_le
            _ ≤ c₁ / Real.log (|t| + 2) :=
                div_le_div_of_nonneg_right hc_star_le_c₁ hlog_pos.le
        dsimp only [σ_T]; linarith
      have hnd := hbd₁ z hz_re_lo (by rw [hz_re]; linarith) (by rw [hz_im]; exact ht1)
      have hnd' : ‖-deriv riemannZeta z / riemannZeta z‖ ≤ C₁ * LT ^ 2 := by
        rw [hz_im] at hnd
        exact hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 2) hC₁.le)
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp [hz_re]
      have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
        have h2 : |t| ≤ ‖z + 1‖ := by
          have := Complex.abs_im_le_norm (z + 1); simpa [hz_im] using this
        have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
        rw [hsq]
        exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
      have ht2_pos : 0 < t ^ 2 := by
        have : t ≠ 0 := fun h => by rw [h, abs_zero] at ht1; linarith
        positivity
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
      rw [norm_div, norm_mul, hpow]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _))
        ht2_pos hden
    have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        exact ((hasDerivAt_inv ht0).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      have : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
      linarith
    have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun u : ℝ => -(u⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have ht0 : t ≠ 0 := by linarith [ht.2]
        exact ((hasDerivAt_inv ht0).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      have : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
      simp only [inv_neg, neg_neg, inv_one]
      linarith
    have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 2 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * LT ^ 2 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 2 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C₁ * LT ^ 2 * x ^ (σ_T + 1) := mul_one _
    
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have hz_im : z.im = t := by simp [z]
        have hz1 : z ≠ 1 := fun h => by have := congrArg Complex.re h; rw [hz_re] at this; simp at this; linarith
        have hreg := hbd₂' z (by rw [hz_re]; exact hσ_ge_c₂) (by rw [hz_re]; linarith)
          (by rw [hz_im, abs_le]; exact ⟨ht.1.le, ht.2⟩) hz1
        have hpole_bd : ‖(1 : ℂ) / (z - 1)‖ ≤ LT / c_star := by
          rw [norm_div, norm_one]
          have hre_sub : c_star / LT ≤ ‖z - 1‖ := by
            have := Complex.abs_re_le_norm (z - 1)
            rw [Complex.sub_re, hz_re, Complex.one_re, show σ_T - 1 = -(c_star / LT) by dsimp only [σ_T]; ring,
              abs_neg, abs_of_pos (div_pos hc_star_pos hLT_pos)] at this
            exact this
          have h1 : 1 / ‖z - 1‖ ≤ 1 / (c_star / LT) :=
            div_le_div_of_nonneg_left zero_le_one (div_pos hc_star_pos hLT_pos) hre_sub
          simpa [one_div_div] using h1
        have hnd_bd : ‖-deriv riemannZeta z / riemannZeta z‖ ≤ (C₂ + 1 / c_star) * LT ^ 2 := by
          have htri : ‖-deriv riemannZeta z / riemannZeta z‖ ≤
              ‖(-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1)‖ + ‖(1 : ℂ) / (z - 1)‖ := by
            simpa [sub_add_cancel] using
              norm_add_le ((-deriv riemannZeta z / riemannZeta z) - 1 / (z - 1)) (1 / (z - 1))
          have hLT_le_sq : LT ≤ LT ^ 2 := by nlinarith
          have h1_le_sq : 1 ≤ LT ^ 2 := by nlinarith
          calc ‖-deriv riemannZeta z / riemannZeta z‖
              ≤ C₂ + LT / c_star := by linarith
            _ = C₂ * 1 + (1 / c_star) * LT := by ring
            _ ≤ C₂ * LT ^ 2 + (1 / c_star) * LT ^ 2 := by
                have h1 : C₂ * 1 ≤ C₂ * LT ^ 2 := mul_le_mul_of_nonneg_left h1_le_sq hC₂.le
                have h2 : (1 / c_star) * LT ≤ (1 / c_star) * LT ^ 2 :=
                  mul_le_mul_of_nonneg_left hLT_le_sq (by positivity)
                linarith
            _ = (C₂ + 1 / c_star) * LT ^ 2 := by ring
        have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
        have hden : 1 / 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : 1 / 2 ≤ ‖z‖ := by
            have := Complex.abs_re_le_norm z; rw [hz_re, abs_of_pos hσ_pos] at this; linarith
          have h2 : 1 ≤ ‖z + 1‖ := by
            have := Complex.abs_re_le_norm (z + 1)
            have hre1 : (z + 1).re = σ_T + 1 := by simp [hz_re]
            rw [hre1, abs_of_pos (by linarith)] at this; linarith
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [norm_div, norm_mul, hpow]
        calc ‖-deriv riemannZeta z / riemannZeta z‖ * x ^ (σ_T + 1) / ‖z * (z + 1)‖
            ≤ ((C₂ + 1 / c_star) * LT ^ 2) * x ^ (σ_T + 1) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hnd_bd (Real.rpow_nonneg hx0.le _)) (by norm_num) hden
          _ = 2 * (C₂ + 1 / c_star) * LT ^ 2 * x ^ (σ_T + 1) := by ring
      · norm_num
        linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        2 * K_left * LT ^ 2 * x ^ (σ_T + 1) := by
      rw [hsplit_left]
      have htri1 := norm_add_le
        ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
      have htri2 := norm_add_le
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
      dsimp only [K_left]
      linarith
    
    have hshift_bd :
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2)‖ ≤
          (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      rw [hshift]
      have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      have htri :
          ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)) -
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
          (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
        have h1 := norm_sub_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)))
        have h2 := norm_add_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)))
        simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2
        linarith
      have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
          (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (2 * K_left * LT ^ 2 * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
        intro Ival hIval
        have hxc_div : x ^ (c + 1) / T ^ 2 ≤ x ^ 2 / T := by
          have h1 : x ^ (c + 1) / T ^ 2 ≤ (2 * x ^ 2) / T ^ 2 :=
            div_le_div_of_nonneg_right hx_pow_c (sq_nonneg T)
          have h2 : 2 * x ^ 2 / T ^ 2 ≤ x ^ 2 / T := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
            have hT2 : 2 * T ≤ T ^ 2 := by nlinarith
            nlinarith [sq_nonneg x]
          linarith
        calc (2 * Real.pi)⁻¹ * ‖Ival‖
            ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * LT ^ 2 * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * (x ^ (c + 1) / T ^ 2) := by
              field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C₁ / Real.pi) * LT ^ 2 * (x ^ 2 / T) :=
              mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ_T..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T + (C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T =
          (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by ring
      linarith
    
    have htotal : |psi1 x - x ^ 2 / 2| ≤
        (48 / Real.pi) * x ^ 2 * Lx / T +
        (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T := by
      have hcast : |psi1 x - x ^ 2 / 2| = ‖(psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2)‖ := by
        have h : (psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2) = (((psi1 x - x ^ 2 / 2 : ℝ) : ℂ)) := by
          push_cast; ring
        rw [h, Complex.norm_real, Real.norm_eq_abs]
      rw [hcast]
      have htri : ‖(psi1 x : ℂ) - ((x : ℂ) ^ 2 / 2)‖ ≤
          ‖(psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T‖ +
          ‖Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2)‖ := by
        have h1 := norm_add_le
          ((psi1 x : ℂ) - Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T)
          (Stage4ExplicitFormula.truncatedPerronPsi1 (1 : DirichletCharacter ℂ 1) x c T - ((x : ℂ) ^ 2 / 2))
        rwa [sub_add_sub_cancel] at h1
      linarith
    
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-α * Real.sqrt Lx) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(c_star / LT)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / LT)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(c_star / LT)) = Real.exp (-(c_star * Lx / LT)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hexp_le : -(c_star * Lx / LT) ≤ -α * Real.sqrt Lx := by
        have hsqrt_pos : 0 < Real.sqrt Lx := Real.sqrt_pos.mpr hLx_pos
        have hdiv : α * Real.sqrt Lx ≤ c_star * Lx / LT := by
          rw [le_div_iff₀ hLT_pos]
          calc α * Real.sqrt Lx * LT
              ≤ α * Real.sqrt Lx * (2 * (α * Real.sqrt Lx)) :=
                mul_le_mul_of_nonneg_left hLT_le (by positivity)
            _ = 2 * α ^ 2 * (Real.sqrt Lx) ^ 2 := by ring
            _ = 2 * (c_star / 2) * Lx := by rw [hα_sq, Real.sq_sqrt hLx_pos.le]
            _ = c_star * Lx := by ring
        linarith
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-α * Real.sqrt Lx) := by
      rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
    have hLT_sq : LT ^ 2 ≤ (4 * α ^ 2) * Lx := by
      have h1 := pow_le_pow_left₀ hLT_pos.le hLT_le 2
      have h2 : (2 * (α * Real.sqrt Lx)) ^ 2 = (4 * α ^ 2) * Lx := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hLx_pos.le]; ring
      linarith
    
    have habsorb : Lx * Real.exp (-α * Real.sqrt Lx) ≤ (16 / α ^ 2) * Real.exp (-c_fin * Real.sqrt Lx) := by
      have hsplit : Real.exp (-α * Real.sqrt Lx) =
          Real.exp (-2 * ((α / 4) * Real.sqrt Lx)) * Real.exp (-c_fin * Real.sqrt Lx) := by
        rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hu_nn : 0 ≤ (α / 4) * Real.sqrt Lx := by positivity
      have hsq_id : Lx * Real.exp (-2 * ((α / 4) * Real.sqrt Lx)) =
          (16 / α ^ 2) * (((α / 4) * Real.sqrt Lx) ^ 2 * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) := by
        have h1 : Lx = (16 / α ^ 2) * ((α / 4) * Real.sqrt Lx) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hLx_pos.le]
          field_simp [hα_pos.ne']; ring
        have h2 := congrArg (· * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) h1
        simpa only [mul_assoc] using h2
      calc Lx * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))
          = (16 / α ^ 2) * (((α / 4) * Real.sqrt Lx) ^ 2 * Real.exp (-2 * ((α / 4) * Real.sqrt Lx))) := hsq_id
        _ ≤ (16 / α ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (sq_mul_exp_neg_two_le_one hu_nn) (by positivity)
        _ = 16 / α ^ 2 := mul_one _
    
    have hterm1 : (48 / Real.pi) * x ^ 2 * Lx / T =
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hterm2 : (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1) ≤
        ((K_left / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      calc (K_left / Real.pi) * LT ^ 2 * x ^ (σ_T + 1)
          ≤ (K_left / Real.pi) * ((4 * α ^ 2) * Lx) * (x ^ 2 * Real.exp (-α * Real.sqrt Lx)) := by
            gcongr
        _ = ((K_left / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by ring
    have hterm3 : (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 / T ≤
        ((2 * C₁ / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]
      calc (2 * C₁ / Real.pi) * LT ^ 2 * x ^ 2 * Real.exp (-α * Real.sqrt Lx)
          ≤ (2 * C₁ / Real.pi) * ((4 * α ^ 2) * Lx) * x ^ 2 * Real.exp (-α * Real.sqrt Lx) := by
            gcongr
        _ = ((2 * C₁ / Real.pi) * (4 * α ^ 2)) * x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by ring
    calc |psi1 x - x ^ 2 / 2|
        ≤ (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) *
            x ^ 2 * (Lx * Real.exp (-α * Real.sqrt Lx)) := by linarith
      _ ≤ (48 / Real.pi + (K_left / Real.pi + 2 * C₁ / Real.pi) * (4 * α ^ 2)) *
            x ^ 2 * ((16 / α ^ 2) * Real.exp (-c_fin * Real.sqrt Lx)) := by
          gcongr
      _ = K_large * x ^ 2 * Real.exp (-c_fin * Real.sqrt Lx) := by dsimp only [K_large]; ring
  
  set C_small : ℝ := (13 / 2) * Real.exp (c_fin * Real.sqrt (Real.log x₀))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge).trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : psi1 x ≤ 6 * x ^ 2 := by
      have h1 : psi1 x ≤ x * RHDirect.chebyshevPsi x := by
        unfold psi1 RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        have hmax : max (x - (n : ℝ)) 0 ≤ x := max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have habs_le : |psi1 x - x ^ 2 / 2| ≤ (13 / 2) * x ^ 2 := by
      rw [abs_le]
      constructor <;> linarith [psi1_nonneg x]
    have hexp_ge : Real.exp (-c_fin * Real.sqrt (Real.log x₀)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log x₀) := Real.sqrt_le_sqrt hlog
      nlinarith
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) = 13 / 2 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log x₀) + -c_fin * Real.sqrt (Real.log x₀) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc |psi1 x - x ^ 2 / 2|
        ≤ (13 / 2) * x ^ 2 := habs_le
      _ = C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
          gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
          gcongr; exact le_max_right _ _

theorem psi1_diff_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    h * Chebyshev.psi x ≤ psi1 (x + h) - psi1 x ∧
    psi1 (x + h) - psi1 x ≤ h * Chebyshev.psi (x + h) := by
  have hpsi_eq : ∀ y : ℝ, Chebyshev.psi y = RHDirect.chebyshevPsi y := fun y =>
    (Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi y).symm
  rw [hpsi_eq x, hpsi_eq (x + h)]
  have hfl_le : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊x + h⌋₊ + 1) := Finset.range_mono hfl_le
  
  have hpsi1_ext : psi1 x = ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * max (x - (n : ℝ)) 0 := by
    unfold psi1
    refine Finset.sum_subset hsub fun n _ hn => ?_
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hn
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    rw [max_eq_right (by linarith), mul_zero]
  have hdiff : psi1 (x + h) - psi1 x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
    rw [hpsi1_ext]
    unfold psi1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hdiff]
  constructor
  · 
    unfold RHDirect.chebyshevPsi
    rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.range (⌊x⌋₊ + 1), h * Λ n
        = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn_le : (n : ℝ) ≤ x := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            (Nat.floor_le hx)
          rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
      _ ≤ ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n * (max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
          refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
          rw [sub_nonneg]
          exact max_le_max (by linarith) le_rfl
  · 
    unfold RHDirect.chebyshevPsi
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hstep : max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0 ≤ h := by
      rcases le_or_gt (n : ℝ) x with hle | hgt
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith : x - (n : ℝ) ≤ 0), sub_zero]
        exact max_le (by linarith) hh
    have h1 := mul_le_mul_of_nonneg_left hstep (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    linarith

set_option maxHeartbeats 2000000 in
theorem effective_pnt_psi :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hpsi1⟩ := effective_pnt_psi1
  set c' : ℝ := c / 4 with hc'_def
  have hc'_pos : 0 < c' := by positivity
  set K_large : ℝ := 1 / 4 + 20 * C
  have hK_large_pos : 0 < K_large := by positivity
  
  have hge4 : ∀ x : ℝ, 4 ≤ x →
      |Chebyshev.psi x - x| ≤ K_large * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by
    intro x hx4
    have hx2 : 2 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
    set E_val : ℝ := Real.exp (-c' * Real.sqrt Lx) with hE_def
    have hE_pos : 0 < E_val := Real.exp_pos _
    have hE_le1 : E_val ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg Lx])
    set h : ℝ := (x / 2) * E_val with hh_def
    have hh_pos : 0 < h := by positivity
    have hh_le_half : h ≤ x / 2 := by nlinarith
    have hxh_ge2 : 2 ≤ x - h := by linarith
    have hxh_le : x - h ≤ x := by linarith
    have hxph_ge2 : 2 ≤ x + h := by linarith
    have hxph_le2x : x + h ≤ 2 * x := by linarith
    
    have hexp_half : Real.exp (-c * Real.sqrt (Real.log (x - h))) ≤ E_val ^ 2 := by
      have hlog_ge : Lx / 2 ≤ Real.log (x - h) := by
        have h1 : x / 2 ≤ x - h := by linarith
        have h2 : Real.log (x / 2) ≤ Real.log (x - h) := Real.log_le_log (by linarith) h1
        rw [Real.log_div hx0.ne' two_ne_zero] at h2
        have hlog4 : 2 * Real.log 2 ≤ Lx := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx4
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at this
          simpa [Lx] using this
        linarith
      have hsqrt_ge : Real.sqrt Lx / 2 ≤ Real.sqrt (Real.log (x - h)) := by
        have hsq : (Real.sqrt Lx / 2) ^ 2 ≤ Real.log (x - h) := by
          rw [div_pow, Real.sq_sqrt hLx_pos.le]; norm_num; linarith
        exact Real.le_sqrt_of_sq_le hsq
      have hE2 : E_val ^ 2 = Real.exp (-(c / 2) * Real.sqrt Lx) := by
        rw [hE_def, ← Real.exp_nat_mul]; congr 1; dsimp only [c']; push_cast; ring
      rw [hE2]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexp_x : Real.exp (-c * Real.sqrt Lx) ≤ E_val ^ 2 := by
      have hE2 : E_val ^ 2 = Real.exp (-(c / 2) * Real.sqrt Lx) := by
        rw [hE_def, ← Real.exp_nat_mul]; congr 1; dsimp only [c']; push_cast; ring
      rw [hE2]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_nonneg Lx]
    have hexp_plus : Real.exp (-c * Real.sqrt (Real.log (x + h))) ≤ E_val ^ 2 := by
      have hlog_ge : Lx ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
      have h1 : Real.exp (-c * Real.sqrt (Real.log (x + h))) ≤ Real.exp (-c * Real.sqrt Lx) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.sqrt_le_sqrt hlog_ge]
      exact h1.trans hexp_x
    have hE_sub : |psi1 (x - h) - (x - h) ^ 2 / 2| ≤ C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 (x - h) - (x - h) ^ 2 / 2|
          ≤ C * (x - h) ^ 2 * Real.exp (-c * Real.sqrt (Real.log (x - h))) := hpsi1 (x - h) hxh_ge2
        _ ≤ C * x ^ 2 * E_val ^ 2 := by
            have hsq : (x - h) ^ 2 ≤ x ^ 2 := by nlinarith
            gcongr
    have hE_cur : |psi1 x - x ^ 2 / 2| ≤ C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 x - x ^ 2 / 2|
          ≤ C * x ^ 2 * Real.exp (-c * Real.sqrt Lx) := hpsi1 x hx2
        _ ≤ C * x ^ 2 * E_val ^ 2 := by gcongr
    have hE_add : |psi1 (x + h) - (x + h) ^ 2 / 2| ≤ 4 * C * x ^ 2 * E_val ^ 2 := by
      calc |psi1 (x + h) - (x + h) ^ 2 / 2|
          ≤ C * (x + h) ^ 2 * Real.exp (-c * Real.sqrt (Real.log (x + h))) := hpsi1 (x + h) hxph_ge2
        _ ≤ C * (2 * x) ^ 2 * E_val ^ 2 := by
            have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
            gcongr
        _ = 4 * C * x ^ 2 * E_val ^ 2 := by ring
    
    have hup_sand := (psi1_diff_sandwich hx0.le hh_pos.le).1
    have hlo_sand := (psi1_diff_sandwich (by linarith : 0 ≤ x - h) hh_pos.le).2
    rw [sub_add_cancel] at hlo_sand
    rw [abs_le]
    constructor
    · 
      have h1 : h * Chebyshev.psi x ≥ h * x - h ^ 2 / 2 +
          (psi1 x - x ^ 2 / 2) - (psi1 (x - h) - (x - h) ^ 2 / 2) := by
        linarith [show x ^ 2 / 2 - (x - h) ^ 2 / 2 = h * x - h ^ 2 / 2 by ring]
      have h2 : -(2 * C * x ^ 2 * E_val ^ 2) ≤
          (psi1 x - x ^ 2 / 2) - (psi1 (x - h) - (x - h) ^ 2 / 2) := by
        linarith [(abs_le.mp hE_cur).1, (abs_le.mp hE_sub).2]
      have h3 : h * (Chebyshev.psi x - x) ≥ -h ^ 2 / 2 - 2 * C * x ^ 2 * E_val ^ 2 := by linarith
      have h4 : -((1 / 4 + 4 * C) * x * E_val) ≤ Chebyshev.psi x - x := by
        have hrhs : h * (-((1 / 4 + 4 * C) * x * E_val)) = -h ^ 2 / 2 - 2 * C * x ^ 2 * E_val ^ 2 := by
          dsimp only [h]; ring
        have : h * (-((1 / 4 + 4 * C) * x * E_val)) ≤ h * (Chebyshev.psi x - x) := by linarith
        exact le_of_mul_le_mul_left this hh_pos
      have hC_nn : 0 ≤ C * x * E_val := by positivity
      dsimp only [K_large]
      linarith
    · 
      have h1 : h * Chebyshev.psi x ≤ h * x + h ^ 2 / 2 +
          (psi1 (x + h) - (x + h) ^ 2 / 2) - (psi1 x - x ^ 2 / 2) := by
        linarith [show (x + h) ^ 2 / 2 - x ^ 2 / 2 = h * x + h ^ 2 / 2 by ring]
      have h2 : (psi1 (x + h) - (x + h) ^ 2 / 2) - (psi1 x - x ^ 2 / 2) ≤
          5 * C * x ^ 2 * E_val ^ 2 := by
        linarith [(abs_le.mp hE_add).2, (abs_le.mp hE_cur).1]
      have h3 : h * (Chebyshev.psi x - x) ≤ h ^ 2 / 2 + 5 * C * x ^ 2 * E_val ^ 2 := by linarith
      have h4 : Chebyshev.psi x - x ≤ (1 / 4 + 10 * C) * x * E_val := by
        have hrhs : h * ((1 / 4 + 10 * C) * x * E_val) = h ^ 2 / 2 + 5 * C * x ^ 2 * E_val ^ 2 := by
          dsimp only [h]; ring
        have : h * (Chebyshev.psi x - x) ≤ h * ((1 / 4 + 10 * C) * x * E_val) := by linarith
        exact le_of_mul_le_mul_left this hh_pos
      have hC_nn : 0 ≤ C * x * E_val := by positivity
      dsimp only [K_large]
      linarith
  
  set C_small : ℝ := 7 * Real.exp (c' * Real.sqrt (Real.log 4))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c', hc'_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hx4 : 4 ≤ x
  · exact (hge4 x hx4).trans (by gcongr; exact le_max_left _ _)
  · push Not at hx4
    have hpsi_le : Chebyshev.psi x ≤ 6 * x := by
      rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      exact Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith)
    have hpsi_nn : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have habs : |Chebyshev.psi x - x| ≤ 7 * x := by
      rw [abs_le]; constructor <;> linarith
    have hexp_ge : Real.exp (-c' * Real.sqrt (Real.log 4)) ≤ Real.exp (-c' * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hx4.le)
      nlinarith
    have hcancel : C_small * Real.exp (-c' * Real.sqrt (Real.log 4)) = 7 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c' * Real.sqrt (Real.log 4) + -c' * Real.sqrt (Real.log 4) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc |Chebyshev.psi x - x|
        ≤ 7 * x := habs
      _ = C_small * x * Real.exp (-c' * Real.sqrt (Real.log 4)) := by rw [← hcancel]; ring
      _ ≤ C_small * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr
      _ ≤ C_fin * x * Real.exp (-c' * Real.sqrt (Real.log x)) := by gcongr; exact le_max_right _ _

theorem effective_pnt_chebyshevPsi :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |RHDirect.chebyshevPsi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_pnt_psi
  refine ⟨c, hc, C, hC, fun x hx => ?_⟩
  rw [Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
  exact hbd x hx

end RHDirect.Stage6EffectivePNT
end

/-! ## From RHDirect/Stage7PNTInAP.lean -/

noncomputable section

open Complex DirichletCharacter MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage7PNTInAP

private lemma log_q_mul_le_const_mul_log {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤ (2 * Real.log (q : ℝ) + 1) * Real.log (|t| + 2) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : (0 : ℝ) < |t| + 2 := by linarith
  rw [Real.log_mul hq_pos.ne' ht2_pos.ne']
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_t_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2_gt.le.trans (Real.log_le_log (by norm_num) ht2_ge2)
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  nlinarith

theorem LFunction_zeroFreeRegion_fixed_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c_χ : ℝ, 0 < c_χ ∧
      ∀ s : ℂ, 1 - c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  
  have hcont_seg : ContinuousOn (fun t : ℝ => ‖DirichletCharacter.LFunction χ (1 + I * (t : ℂ))‖)
      (Set.Icc (-1 : ℝ) 1) := by
    have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous
    have hmap : Continuous (fun t : ℝ => (1 : ℂ) + I * (t : ℂ)) := by fun_prop
    exact (hL_cont.comp hmap).norm.continuousOn
  have hne_Icc : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  obtain ⟨t₀, ht₀_mem, ht₀_min⟩ := isCompact_Icc.exists_isMinOn hne_Icc hcont_seg
  set m : ℝ := ‖DirichletCharacter.LFunction χ (1 + I * (t₀ : ℂ))‖ with hm_def
  have hm_pos : 0 < m := by
    refine norm_pos_iff.mpr ?_
    exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) (by simp)
  set L3q : ℝ := Real.log ((q : ℝ) * 3) with hL3q_def
  have hL3q_pos : 0 < L3q := Real.log_pos (by linarith)
  set δ_χ : ℝ := min L3q⁻¹ (m / (2 * (288 * L3q ^ 2))) with hδ_def
  have hδ_pos : 0 < δ_χ := lt_min (inv_pos.mpr hL3q_pos) (by positivity)
  have hδ_le_inv : δ_χ ≤ L3q⁻¹ := min_le_left _ _
  have hδ_le_m : δ_χ ≤ m / (2 * (288 * L3q ^ 2)) := min_le_right _ _
  
  set A_q : ℝ := 2 * Real.log (q : ℝ) + 1 with hAq_def
  have hAq_pos : 0 < A_q := by
    have : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
    linarith
  set c_high : ℝ := Stage5DirichletLZeroFree.zeroFreeConst / A_q ^ 9 with hc_high_def
  have hc_high_pos : 0 < c_high :=
    div_pos Stage5DirichletLZeroFree.zeroFreeConst_pos (pow_pos hAq_pos 9)
  set c_χ : ℝ := min c_high (δ_χ * (Real.log 2) ^ 9) with hc_def
  have hc_pos : 0 < c_χ := lt_min hc_high_pos (by positivity)
  refine ⟨c_χ, hc_pos, fun s hs => ?_⟩
  by_cases hre1 : 1 ≤ s.re
  · exact Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ (Or.inl hχ) hre1
  · push Not at hre1
    have hlog_t_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have hlog_t_pos : 0 < Real.log (|s.im| + 2) := hlog2_pos.trans_le hlog_t_ge
    by_cases him1 : 1 ≤ |s.im|
    · 
      have hlog_cmp := log_q_mul_le_const_mul_log hq2 s.im
      have hlogq_pos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
        Real.log_pos (by nlinarith [abs_nonneg s.im])
      have hpow9 : (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 ≤
          A_q ^ 9 * (Real.log (|s.im| + 2)) ^ 9 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hlogq_pos.le hlog_cmp 9
      have hdiv : c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤
          Stage5DirichletLZeroFree.zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 := by
        calc c_χ / (Real.log (|s.im| + 2)) ^ 9
            ≤ c_high / (Real.log (|s.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg hlog_t_pos.le 9)
          _ = Stage5DirichletLZeroFree.zeroFreeConst / (A_q ^ 9 * (Real.log (|s.im| + 2)) ^ 9) := by
              dsimp only [c_high]; rw [div_div]
          _ ≤ Stage5DirichletLZeroFree.zeroFreeConst / (Real.log ((q : ℝ) * (|s.im| + 2))) ^ 9 :=
              div_le_div_of_nonneg_left Stage5DirichletLZeroFree.zeroFreeConst_pos.le
                (pow_pos hlogq_pos 9) hpow9
      exact Stage5DirichletLZeroFree.LFunction_ne_zero_in_zeroFreeRegion hχ (Or.inr him1)
        (by linarith)
    · 
      push Not at him1
      have hdiv_le_δ : c_χ / (Real.log (|s.im| + 2)) ^ 9 ≤ δ_χ := by
        have hpow_ge : (Real.log 2) ^ 9 ≤ (Real.log (|s.im| + 2)) ^ 9 :=
          pow_le_pow_left₀ hlog2_pos.le hlog_t_ge 9
        calc c_χ / (Real.log (|s.im| + 2)) ^ 9
            ≤ (δ_χ * (Real.log 2) ^ 9) / (Real.log (|s.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right (min_le_right _ _) (pow_nonneg hlog_t_pos.le 9)
          _ ≤ (δ_χ * (Real.log 2) ^ 9) / (Real.log 2) ^ 9 :=
              div_le_div_of_nonneg_left (by positivity) (pow_pos hlog2_pos 9) hpow_ge
          _ = δ_χ := mul_div_cancel_right₀ _ (pow_pos hlog2_pos 9).ne'
      have hs_re_ge : 1 - δ_χ ≤ s.re := by linarith
      set Lq : ℝ := Real.log ((q : ℝ) * (|s.im| + 2)) with hLq_def
      have hLq_pos : 0 < Lq := Real.log_pos (by nlinarith [abs_nonneg s.im])
      have hLq_le : Lq ≤ L3q := Real.log_le_log (by nlinarith [abs_nonneg s.im]) (by nlinarith)
      have hinv_le : L3q⁻¹ ≤ Lq⁻¹ := inv_anti₀ hLq_pos hLq_le
      have hmvt := Stage5DirichletLZeroFree.norm_LFunction_sub_le_of_strip hχ
        (σ₁ := s.re) (σ₂ := 1) (t := s.im) (by linarith) hre1.le (by norm_num)
      have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
        have := Complex.re_add_im s
        simpa only [mul_comm I] using this
      have h1_eq : ((1 : ℝ) : ℂ) + I * (s.im : ℂ) = 1 + I * (s.im : ℂ) := by simp
      rw [hs_eq, h1_eq] at hmvt
      have hmin_le : m ≤ ‖DirichletCharacter.LFunction χ (1 + I * (s.im : ℂ))‖ :=
        ht₀_min (abs_le.mp him1.le)
      have hdiff_lt : (1 - s.re) * (288 * Lq ^ 2) < m := by
        have h1s : 1 - s.re ≤ δ_χ := by linarith
        have hsq : Lq ^ 2 ≤ L3q ^ 2 := pow_le_pow_left₀ hLq_pos.le hLq_le 2
        have h1 : (1 - s.re) * (288 * Lq ^ 2) ≤ δ_χ * (288 * L3q ^ 2) :=
          mul_le_mul h1s (by linarith) (by positivity) hδ_pos.le
        have h2 : δ_χ * (288 * L3q ^ 2) ≤ m / 2 := by
          have := mul_le_mul_of_nonneg_right hδ_le_m (show 0 ≤ 288 * L3q ^ 2 by positivity)
          have hcancel : m / (2 * (288 * L3q ^ 2)) * (288 * L3q ^ 2) = m / 2 := by
            field_simp [hL3q_pos.ne']
          linarith
        linarith
      intro hzero
      rw [hzero, sub_zero] at hmvt
      linarith

set_option maxHeartbeats 2000000 in
theorem negLogDerivL_zeroFree_bound_pow10 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ s : ℂ, 1 - c' / (Real.log (|s.im| + 2)) ^ 9 ≤ s.re → s.re ≤ 2 →
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C' * (Real.log (|s.im| + 2)) ^ 10 := by
  have hq2 : 2 ≤ q := Stage5DirichletLZeroFree.two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c_zf, hc_zf_pos, hzf⟩ := LFunction_zeroFreeRegion_fixed_char hχ
  
  set c : ℝ := min c_zf ((Real.log 2) ^ 9 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc_zf_pos (by positivity)
  have hc_le_zf : c ≤ c_zf := min_le_left _ _
  have hc_le_qtr : c ≤ (Real.log 2) ^ 9 / 4 := min_le_right _ _
  have hc_le_one : c ≤ 1 := by
    have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hpow_le1 : (Real.log 2) ^ 9 ≤ 1 := pow_le_one₀ hlog2_pos.le hlog2_lt1.le
    linarith
  set P29 : ℝ := (2 : ℝ) ^ (9 : ℕ) with hP29_def
  have hP29_pos : 0 < P29 := by positivity
  set c' : ℝ := c / (16 * P29) with hc'_def
  have hc'_pos : 0 < c' := by positivity
  
  set C_right : ℝ := (1 / c') / Real.log 2 + 1 / (Real.log 2) ^ 10 with hC_right_def
  have hC_right_pos : 0 < C_right := by positivity
  set K_arg : ℝ := 64 * P29 * (q : ℝ) / c with hK_arg_def
  have hK_arg_gt1 : 1 < K_arg := by
    dsimp only [K_arg, P29]
    rw [one_lt_div hc_pos]
    nlinarith
  have hlogK_pos : 0 < Real.log K_arg := Real.log_pos hK_arg_gt1
  set A_M : ℝ := Real.log K_arg / Real.log 2 + 10 with hAM_def
  have hAM_pos : 0 < A_M := by positivity
  set C_left : ℝ := (16 * P29 / c) * A_M with hC_left_def
  have hC_left_pos : 0 < C_left := by positivity
  set C' : ℝ := max C_right C_left with hC'_def
  have hC'_pos : 0 < C' := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c', hc'_pos, C', hC'_pos, fun s hre_lo hre_hi => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have ht2_ge2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have ht2_pos : 0 < |t| + 2 := by linarith
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) ht2_ge2
  have hL_pos : 0 < L := hlog2_pos.trans_le hL_ge
  have hL9_pos : 0 < L ^ 9 := pow_pos hL_pos 9
  have hL10_pos : 0 < L ^ 10 := pow_pos hL_pos 10
  by_cases hright : 1 + c' / L ^ 9 ≤ s.re
  · 
    have hs_re_gt1 : 1 < s.re := by
      have : 0 < c' / L ^ 9 := div_pos hc'_pos hL9_pos
      linarith
    have hs_eq : (s.re : ℂ) + I * (t : ℂ) = s := by
      have := Complex.re_add_im s
      simpa only [t, mul_comm I] using this
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_re_gt1 t).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv_le : 1 / (s.re - 1) ≤ L ^ 9 / c' := by
      rw [div_le_div_iff₀ (by linarith) hc'_pos, one_mul]
      have h1 : c' / L ^ 9 ≤ s.re - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hL9_pos.le
      rw [div_mul_cancel₀ _ hL9_pos.ne'] at h2
      linarith
    have h1_le_L : 1 ≤ L / Real.log 2 := (one_le_div hlog2_pos).mpr hL_ge
    have h1_le_L10 : 1 ≤ L ^ 10 / (Real.log 2) ^ 10 :=
      (one_le_div (pow_pos hlog2_pos 10)).mpr (pow_le_pow_left₀ hlog2_pos.le hL_ge 10)
    have hterm1 : L ^ 9 / c' ≤ ((1 / c') / Real.log 2) * L ^ 10 := by
      have h := mul_le_mul_of_nonneg_left h1_le_L (show 0 ≤ L ^ 9 / c' by positivity)
      have hrhs : (L ^ 9 / c') * (L / Real.log 2) = ((1 / c') / Real.log 2) * L ^ 10 := by
        field_simp [hc'_pos.ne', hlog2_pos.ne']
      linarith
    have hterm2 : (1 : ℝ) ≤ (1 / (Real.log 2) ^ 10) * L ^ 10 := by
      have : (1 / (Real.log 2) ^ 10) * L ^ 10 = L ^ 10 / (Real.log 2) ^ 10 := by ring
      linarith
    calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ 1 / (s.re - 1) + 1 := hbd
      _ ≤ L ^ 9 / c' + 1 := by linarith
      _ ≤ ((1 / c') / Real.log 2) * L ^ 10 + (1 / (Real.log 2) ^ 10) * L ^ 10 := by linarith
      _ = C_right * L ^ 10 := by dsimp only [C_right]; ring
      _ ≤ C' * L ^ 10 := mul_le_mul_of_nonneg_right (le_max_left _ _) hL10_pos.le
  · 
    push Not at hright
    set η : ℝ := c / (8 * P29 * L ^ 9) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      have hpow_ge : (Real.log 2) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ hlog2_pos.le hL_ge 9
      have h1 : c / L ^ 9 ≤ 1 / 4 := by
        calc c / L ^ 9 ≤ ((Real.log 2) ^ 9 / 4) / L ^ 9 :=
              div_le_div_of_nonneg_right hc_le_qtr hL9_pos.le
          _ ≤ ((Real.log 2) ^ 9 / 4) / (Real.log 2) ^ 9 :=
              div_le_div_of_nonneg_left (by positivity) (pow_pos hlog2_pos 9) hpow_ge
          _ = 1 / 4 := by field_simp [(pow_pos hlog2_pos 9).ne']
      have hP29_ge1 : (1 : ℝ) ≤ P29 := by dsimp only [P29]; norm_num
      have hη_eq : η = (c / L ^ 9) / (8 * P29) := by dsimp only [η]; ring
      rw [hη_eq]
      calc (c / L ^ 9) / (8 * P29) ≤ (1 / 4) / (8 * 1) :=
            div_le_div₀ (by norm_num) h1 (by norm_num) (by linarith)
        _ = 1 / 32 := by norm_num
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le_half : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith [abs_nonneg t]
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hpow9_le : (Real.log (|z.im| + 2)) ^ 9 ≤ P29 * L ^ 9 := by
        have h1 := pow_le_pow_left₀ hlogz_pos.le hlog_le 9
        rwa [mul_pow] at h1
      have hdiv_ge : c / (P29 * L ^ 9) ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 := by
        calc c / (P29 * L ^ 9) ≤ c / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_left hc_pos.le (pow_pos hlogz_pos 9) hpow9_le
          _ ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right hc_le_zf (pow_nonneg hlogz_pos.le 9)
      have h4η : 4 * η ≤ c / (P29 * L ^ 9) := by
        have hEq : 4 * η = (c / (P29 * L ^ 9)) / 2 := by dsimp only [η]; ring
        have hnn : 0 ≤ c / (P29 * L ^ 9) := by positivity
        linarith
      have hz_re_ge : 1 - c_zf / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
        dsimp only [R_open] at hre_diff
        linarith
      exact hzf z hz_re_ge
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    
    set M : ℝ := A_M * L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hznz : DirichletCharacter.LFunction χ z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : DirichletCharacter.LFunction χ s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_hi : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 4 * (q : ℝ) * (|t| + 2) := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ (q : ℝ) * (2 + (|t| + 1 / 2)) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_left (by linarith) hq_pos.le) (by norm_num) hz_re_lo
          _ ≤ 4 * (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 16 * P29 * L ^ 9 / c := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) t).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
        rw [hs₀_eq'] at h
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
        have h3 : 2 / η = 16 * P29 * L ^ 9 / c := by
          dsimp only [η]; field_simp [hc_pos.ne', hP29_pos.ne', hL9_pos.ne']; ring
        linarith
      have hratio_le :
          ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
            K_arg * (|t| + 2) * L ^ 9 := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
              DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring,
          norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (4 * (q : ℝ) * (|t| + 2)) * (16 * P29 * L ^ 9 / c) :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = K_arg * (|t| + 2) * L ^ 9 := by dsimp only [K_arg]; ring
      have hre_eq : (Log z).re =
          Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        have hexp : Real.exp (Log z).re =
            ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      have hlogL_le : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith)
      have h1_le_L : 1 ≤ L / Real.log 2 := (one_le_div hlog2_pos).mpr hL_ge
      rw [hre_eq]
      calc Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖
          ≤ Real.log (K_arg * (|t| + 2) * L ^ 9) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (K_arg * (|t| + 2)) + Real.log (L ^ 9) :=
            Real.log_mul (by positivity) (by positivity)
        _ = Real.log K_arg + Real.log (|t| + 2) + 9 * Real.log L := by
            rw [Real.log_mul (by positivity) ht2_pos.ne', Real.log_pow]; push_cast; ring
        _ ≤ Real.log K_arg * (L / Real.log 2) + L + 9 * L := by
            have h1 : Real.log K_arg ≤ Real.log K_arg * (L / Real.log 2) := by
              nlinarith
            linarith
        _ = M := by dsimp only [M, A_M]; ring
    
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc'_eq : c' / L ^ 9 = η / 2 := by dsimp only [c', η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 16 * P29 * L ^ 9 / c := by
      dsimp only [R, r, η]
      field_simp [hc_pos.ne', hP29_pos.ne', hL9_pos.ne']
      ring
    rw [hcoeff] at hbc
    have hneg_norm :
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ (16 * P29 * L ^ 9 / c) * M := hbc
      _ = C_left * L ^ 10 := by dsimp only [C_left, M]; ring
      _ ≤ C' * L ^ 10 := mul_le_mul_of_nonneg_right (le_max_right _ _) hL10_pos.le

theorem perron_contour_shift_psi1Char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {x σ c T : ℝ} (hx : 0 < x)
    (hσ0 : 0 < σ) (hσc : σ < c) (hT : 0 < T)
    (hzf : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T → DirichletCharacter.LFunction χ z ≠ 0) :
    let F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
      ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  intro F
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ DirichletCharacter.LFunction χ z ≠ 0}
  have hU_open : IsOpen U := by
    have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous
    have hset : U = {z : ℂ | 0 < z.re} ∩ (DirichletCharacter.LFunction χ) ⁻¹' ({(0 : ℂ)}ᶜ) := by
      ext z; simp [U]
    rw [hset]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isClosed_singleton.isOpen_compl.preimage hL_cont)
  have hrect_sub : Set.uIcc σ c ×ℂ Set.uIcc (-T) T ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hσc.le,
      Set.uIcc_of_le (by linarith : -T ≤ T)] at hz
    exact ⟨lt_of_lt_of_le hσ0 hz.1.1, hzf z hz.1.1 hz.1.2 (abs_le.mpr hz.2)⟩
  have hF_diff_U : DifferentiableOn ℂ F U := by
    have hL_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    have hnd_diff : DifferentiableOn ℂ (Stage3ZeroFreeRegion.negLogDerivL χ) U := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      exact (hL_diff.deriv hU_open).neg.div hL_diff fun _ hz => hz.2
    have hW_diff : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ (s + 1) / (s * (s + 1))) U := by
      intro s hs
      have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (z + 1)) s := by
        have hEq : (fun z : ℂ => (x : ℂ) ^ (z + 1)) =
            fun z : ℂ => cexp (Complex.log (x : ℂ) * (z + 1)) :=
          funext fun z => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      have hs0 : s ≠ 0 := fun h => by have := hs.1; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
      have hs1 : s + 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hs.1]
      exact (hpow.div (differentiableAt_id.mul (differentiableAt_id.add (differentiableAt_const 1)))
        (mul_ne_zero hs0 hs1)).differentiableWithinAt
    have hF_eq : F = fun s => Stage3ZeroFreeRegion.negLogDerivL χ s *
        ((x : ℂ) ^ (s + 1) / (s * (s + 1))) := funext fun s => by dsimp only [F]; ring
    rw [hF_eq]
    exact hnd_diff.mul hW_diff
  
  set z₀ : ℂ := (σ : ℂ) + ((-T : ℝ) : ℂ) * I
  set w₀ : ℂ := (c : ℂ) + (T : ℂ) * I
  have hz₀_re : z₀.re = σ := by simp [z₀]
  have hz₀_im : z₀.im = -T := by simp [z₀]
  have hw₀_re : w₀.re = c := by simp [w₀]
  have hw₀_im : w₀.im = T := by simp [w₀]
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z₀ w₀
    (by simpa [hz₀_re, hz₀_im, hw₀_re, hw₀_im] using hF_diff_U.mono hrect_sub)
  simp only [hz₀_re, hz₀_im, hw₀_re, hw₀_im, smul_eq_mul] at hcauchy
  have hright_eq : Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) := by
    unfold Stage4ExplicitFormula.truncatedPerronPsi1
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [F]
    have harg : (c : ℂ) + I * (t : ℂ) = (c : ℂ) + (t : ℂ) * I := by ring
    have harg1 : (c : ℂ) + 1 + I * (t : ℂ) = ((c : ℂ) + (t : ℂ) * I) + 1 := by ring
    rw [harg, harg1]
  rw [hright_eq]
  have h2piI_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have h2pi_cast : (2 * Real.pi * I : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹) = I := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    push_cast
    field_simp [Real.pi_ne_zero]
  apply mul_left_cancel₀ h2piI_ne
  calc (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)))
      = I * (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) := by
        rw [← mul_assoc, h2pi_cast]
    _ = I * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
        (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
        linear_combination hcauchy
    _ = (2 * Real.pi * I : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
        rw [mul_sub, mul_add, ← mul_assoc, h2pi_cast, ← mul_assoc, ← mul_assoc,
          mul_inv_cancel₀ h2piI_ne, one_mul, one_mul]

private lemma pow_mul_exp_neg_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-(k : ℝ) * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ k * Real.exp (-(k : ℝ) * u) = (u * Real.exp (-u)) ^ k := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; ring
  rw [h2]
  exact pow_le_one₀ (mul_nonneg hu (Real.exp_pos (-u)).le) h1

private lemma exp_neg_rpow_le_of_le {p q c x : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hc : 0 < c) (hx : 2 ≤ x) :
    Real.exp (-c * (Real.log x) ^ q) ≤
      Real.exp c * Real.exp (-c * (Real.log x) ^ p) := by
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases hL1 : 1 ≤ Real.log x
  · have hpow : (Real.log x) ^ p ≤ (Real.log x) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hL1 hpq
    have hexp1 : Real.exp (-c * (Real.log x) ^ q) ≤ Real.exp (-c * (Real.log x) ^ p) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h1 : (1 : ℝ) ≤ Real.exp c := Real.one_le_exp hc.le
    nlinarith [Real.exp_pos (-c * (Real.log x) ^ p)]
  · push Not at hL1
    have hpow_le1 : (Real.log x) ^ p ≤ 1 :=
      Real.rpow_le_one hLx_pos.le hL1.le hp.le
    have hpow_nn : 0 ≤ (Real.log x) ^ q := Real.rpow_nonneg hLx_pos.le q
    have h1 : Real.exp (-c * (Real.log x) ^ q) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-c) ≤ Real.exp (-c * (Real.log x) ^ p) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hcancel : Real.exp c * Real.exp (-c) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 1 ≤ Real.exp c * Real.exp (-c * (Real.log x) ^ p) := by
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le
    linarith

set_option maxHeartbeats 2000000 in
theorem effective_psi1Char_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          C * x ^ 2 * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c_zf, hc_zf, hzf⟩ := LFunction_zeroFreeRegion_fixed_char hχ
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := negLogDerivL_zeroFree_bound_pow10 hχ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c_star : ℝ := min (min c_zf c₁) (1 / 4) with hc_star_def
  have hc_star_pos : 0 < c_star := by positivity
  have hc_star_le_zf : c_star ≤ c_zf := (min_le_left _ _).trans (min_le_left _ _)
  have hc_star_le_c₁ : c_star ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_star_le_qtr : c_star ≤ 1 / 4 := min_le_right _ _
  
  set α : ℝ := c_star ^ (1 / 10 : ℝ) / 2 with hα_def
  have hα_pos : 0 < α := by positivity
  have h2α_pow10 : (2 * α) ^ (10 : ℕ) = c_star := by
    have h1 : 2 * α = c_star ^ (1 / 10 : ℝ) := by dsimp only [α]; ring
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hc_star_pos.le]
    norm_num
  set c_fin : ℝ := α / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  
  set x₀ : ℝ := max 2 (Real.exp ((1 / α) ^ (10 : ℕ))) with hx₀_def
  have hx₀_ge2 : 2 ≤ x₀ := le_max_left _ _
  set K_large : ℝ :=
    (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) * (20 / α) ^ (10 : ℕ)
  have hK_large_pos : 0 < K_large := by positivity
  
  have hlarge : ∀ x : ℝ, x₀ ≤ x →
      ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        K_large * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
    intro x hx
    have hx2 : 2 ≤ x := hx₀_ge2.trans hx
    have hx0 : 0 < x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_ge_log2 : Real.log 2 ≤ Lx := Real.log_le_log (by norm_num) hx2
    have hLx_pos : 0 < Lx := hlog2_pos.trans_le hLx_ge_log2
    set u : ℝ := Lx ^ (1 / 10 : ℝ) with hu_def
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
    have hu_pow10 : u ^ (10 : ℕ) = Lx := by
      dsimp only [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLx_pos.le]
      norm_num
    have hLx_ge_inv : (1 / α) ^ (10 : ℕ) ≤ Lx := by
      have hexp : Real.exp ((1 / α) ^ (10 : ℕ)) ≤ x := (le_max_right _ _).trans hx
      exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hexp)
    have hαu_ge1 : 1 ≤ α * u := by
      have hpow : (1 : ℝ) ^ (10 : ℕ) ≤ (α * u) ^ (10 : ℕ) := by
        rw [one_pow, mul_pow, hu_pow10]
        have h := mul_le_mul_of_nonneg_left hLx_ge_inv (pow_nonneg hα_pos.le 10)
        rw [← mul_pow, mul_one_div_cancel hα_pos.ne', one_pow] at h
        exact h
      by_contra hlt
      push Not at hlt
      have : (α * u) ^ (10 : ℕ) < 1 ^ (10 : ℕ) :=
        pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      linarith
    set T : ℝ := Real.exp (α * u) with hT_def
    have hT_pos : 0 < T := Real.exp_pos _
    have hT_ge_e : Real.exp 1 ≤ T := Real.exp_le_exp.mpr hαu_ge1
    have hT_ge2 : 2 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlogT : Real.log T = α * u := Real.log_exp _
    set LT : ℝ := Real.log (T + 2) with hLT_def
    have hLT_ge1 : 1 ≤ LT := by
      have h : Real.exp 1 ≤ T + 2 := by linarith
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) h)
    have hLT_pos : 0 < LT := zero_lt_one.trans_le hLT_ge1
    have hLT_le : LT ≤ 2 * (α * u) := by
      have hle2T : T + 2 ≤ 2 * T := by linarith
      have h1 : LT ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hle2T
      rw [Real.log_mul (by norm_num) hT_pos.ne', hlogT] at h1
      have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    
    set c : ℝ := 1 + 1 / (2 * Lx) with hc_def
    have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (by linarith : 0 < 2 * Lx)]
    have hc_le2 : c ≤ 2 := by
      have h2Lx : 1 ≤ 2 * Lx := by linarith [Real.log_two_gt_d9]
      have : 1 / (2 * Lx) ≤ 1 := (div_le_one (by linarith)).mpr h2Lx
      dsimp only [c]; linarith
    have hx_pow_c : x ^ (c + 1) ≤ 2 * x ^ 2 := by
      have h1 : x ^ (c + 1) = x ^ 2 * x ^ (1 / (2 * Lx)) := by
        rw [show c + 1 = (2 : ℝ) + 1 / (2 * Lx) by dsimp only [c]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (1 / (2 * Lx)) = Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]
        congr 1; field_simp [hLx_pos.ne']
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
          linarith [Real.exp_one_lt_d9]
        nlinarith [Real.exp_pos (1 / 2)]
      rw [h1, h2]
      nlinarith [sq_nonneg x]
    set σ_T : ℝ := 1 - c_star / LT ^ 9 with hσ_def
    have hσ_lt1 : σ_T < 1 := by dsimp only [σ_T]; linarith [div_pos hc_star_pos (pow_pos hLT_pos 9)]
    have hσ_ge_half : 1 / 2 ≤ σ_T := by
      have hLT9_ge1 : (1 : ℝ) ≤ LT ^ 9 := one_le_pow₀ hLT_ge1
      have h1 : c_star / LT ^ 9 ≤ 1 / 4 := by
        calc c_star / LT ^ 9 ≤ c_star / 1 :=
              div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hLT9_ge1
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le_qtr
      dsimp only [σ_T]; linarith
    have hσ_pos : 0 < σ_T := by linarith
    
    have hzf_rect : ∀ z : ℂ, σ_T ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hlo _ him
      have hlog_le : Real.log (|z.im| + 2) ≤ LT :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
      have hlog_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith [abs_nonneg z.im])
      have hpow9 : (Real.log (|z.im| + 2)) ^ 9 ≤ LT ^ 9 :=
        pow_le_pow_left₀ hlog_pos.le hlog_le 9
      have h1 : c_star / LT ^ 9 ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 := by
        calc c_star / LT ^ 9 ≤ c_star / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_left hc_star_pos.le (pow_pos hlog_pos 9) hpow9
          _ ≤ c_zf / (Real.log (|z.im| + 2)) ^ 9 :=
              div_le_div_of_nonneg_right hc_star_le_zf (pow_nonneg hlog_pos.le 9)
      exact hzf z (by linarith)
    set F : ℂ → ℂ := fun s =>
      Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    
    have htrunc_err :
        ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (48 / Real.pi) * x ^ 2 * Lx / T := by
      have h0 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hx0 hc_gt1 hT_pos
      have hc_sub : c - 1 = 1 / (2 * Lx) := by dsimp only [c]; ring
      rw [hc_sub] at h0
      calc ‖Stage4ExplicitFormula.psi1Char χ x -
              Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖
          ≤ (6 * c / Real.pi) * x ^ (c + 1) / (1 / (2 * Lx) * T) := h0
        _ ≤ (6 * 2 / Real.pi) * (2 * x ^ 2) / (1 / (2 * Lx) * T) := by gcongr
        _ = (48 / Real.pi) * x ^ 2 * Lx / T := by
            field_simp [Real.pi_ne_zero, hLx_pos.ne', hT_pos.ne']; ring
    
    have hshift := perron_contour_shift_psi1Char hχ hx0 hσ_pos (by linarith : σ_T < c) hT_pos hzf_rect
    
    have hhoriz_bd : ∀ sgn : ℝ, |sgn| = 1 →
        ‖∫ v in σ_T..c, F ((v : ℂ) + ((sgn * T : ℝ) : ℂ) * I)‖ ≤
          2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      intro sgn hsgn
      have hle : σ_T ≤ c := by linarith
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2) fun v hv => ?_).trans ?_
      · rw [Set.uIoc_of_le hle] at hv
        set z : ℂ := (v : ℂ) + ((sgn * T : ℝ) : ℂ) * I
        have hz_re : z.re = v := by simp [z]
        have hz_im : z.im = sgn * T := by simp [z]
        have hz_abs_im : |z.im| = T := by
          rw [hz_im, abs_mul, hsgn, one_mul, abs_of_pos hT_pos]
        have hz_re_lo : 1 - c₁ / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
          rw [hz_re, hz_abs_im]
          have : c_star / LT ^ 9 ≤ c₁ / LT ^ 9 :=
            div_le_div_of_nonneg_right hc_star_le_c₁ (pow_nonneg hLT_pos.le 9)
          dsimp only [σ_T] at hv; linarith [hv.1]
        have hz_re_hi : z.re ≤ 2 := by rw [hz_re]; linarith [hv.2]
        have hnd := hbd₁ z hz_re_lo hz_re_hi
        rw [hz_abs_im] at hnd
        have hpow_norm : ‖(x : ℂ) ^ (z + 1)‖ ≤ x ^ (c + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre1 : (z + 1).re = v + 1 := by simp [hz_re]
          rw [hre1]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hv.2])
        have hden_ge : T ^ 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : T ≤ ‖z‖ := by rw [← hz_abs_im]; exact Complex.abs_im_le_norm z
          have h2 : T ≤ ‖z + 1‖ := by
            have := Complex.abs_im_le_norm (z + 1)
            simpa [hz_abs_im] using this
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                ‖(x : ℂ) ^ (z + 1)‖ / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 10) * x ^ (c + 1) / T ^ 2 := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hnd hpow_norm (norm_nonneg _) (by positivity))
                (sq_pos_of_pos hT_pos) hden_ge
          _ = C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by ring
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        have hlen : c - σ_T ≤ 2 := by linarith
        calc C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 * (c - σ_T)
            ≤ C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left hlen (by positivity)
          _ = 2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by ring
    have htop_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd 1 (by norm_num)
    have hbot_bd : ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 := by
      simpa using hhoriz_bd (-1) (by norm_num)
    
    have hleft_cont : ContinuousOn (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
      have hL_cont : Continuous (DirichletCharacter.LFunction χ) :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous
      have hL'_cont : Continuous (deriv (DirichletCharacter.LFunction χ)) :=
        continuousOn_univ.mp
          ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn.deriv isOpen_univ).continuousOn
      have hmap : Continuous (fun t : ℝ => (σ_T : ℂ) + (t : ℂ) * I) := by fun_prop
      have hnd_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ_T : ℂ) + (t : ℂ) * I))
          (Set.Icc (-T) T) := by
        unfold Stage3ZeroFreeRegion.negLogDerivL
        refine (hL'_cont.comp hmap).neg.continuousOn.div (hL_cont.comp hmap).continuousOn fun t ht => ?_
        exact hzf_rect _ (by simp) (by simp; linarith) (by simp [abs_le, ht.1, ht.2])
      have hpow_cont : Continuous (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) := by
        have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
        have hEq : (fun t : ℝ => (x : ℂ) ^ (((σ_T : ℂ) + (t : ℂ) * I) + 1)) =
            fun t : ℝ => cexp (Complex.log (x : ℂ) * (((σ_T : ℂ) + (t : ℂ) * I) + 1)) :=
          funext fun t => Complex.cpow_def_of_ne_zero hxC _
        rw [hEq]; fun_prop
      refine (hnd_cont.mul hpow_cont.continuousOn).div (by fun_prop) fun t _ => mul_ne_zero ?_ ?_
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hint_seg : ∀ a b : ℝ, -T ≤ a → a ≤ b → b ≤ T →
        IntervalIntegrable (fun t : ℝ => F ((σ_T : ℂ) + (t : ℂ) * I)) volume a b := by
      intro a b ha hab hb
      refine (hleft_cont.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
    have hsplit_left :
        ∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I) =
          (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith))
        (hint_seg (-1) 1 (by linarith) (by norm_num) (by linarith))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hint_seg (-T) 1 le_rfl (by linarith) (by linarith))
        (hint_seg 1 T (by linarith) (by linarith) le_rfl)
      rw [h1, h2]
    
    have hleft_nd : ∀ t : ℝ, |t| ≤ T →
        ‖-deriv (DirichletCharacter.LFunction χ) ((σ_T : ℂ) + (t : ℂ) * I) /
          DirichletCharacter.LFunction χ ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 10 := by
      intro t htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hlog_le : Real.log (|t| + 2) ≤ LT := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
      have hlog_pos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hpow9 : (Real.log (|t| + 2)) ^ 9 ≤ LT ^ 9 := pow_le_pow_left₀ hlog_pos.le hlog_le 9
      have hz_re_lo : 1 - c₁ / (Real.log (|z.im| + 2)) ^ 9 ≤ z.re := by
        rw [hz_re, hz_im]
        have h1 : c_star / LT ^ 9 ≤ c₁ / (Real.log (|t| + 2)) ^ 9 := by
          calc c_star / LT ^ 9 ≤ c_star / (Real.log (|t| + 2)) ^ 9 :=
                div_le_div_of_nonneg_left hc_star_pos.le (pow_pos hlog_pos 9) hpow9
            _ ≤ c₁ / (Real.log (|t| + 2)) ^ 9 :=
                div_le_div_of_nonneg_right hc_star_le_c₁ (pow_nonneg hlog_pos.le 9)
        dsimp only [σ_T]; linarith
      have hnd := hbd₁ z hz_re_lo (by rw [hz_re]; linarith)
      rw [hz_im] at hnd
      exact hnd.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog_pos.le hlog_le 10) hC₁.le)
    
    have hleft_tail_pt : ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
        ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) / t ^ 2 := by
      intro t ht1 htT
      set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
      have hz_re : z.re = σ_T := by simp [z]
      have hz_im : z.im = t := by simp [z]
      have hnd' := hleft_nd t htT
      have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
      have hden : t ^ 2 ≤ ‖z * (z + 1)‖ := by
        rw [norm_mul]
        have h1 : |t| ≤ ‖z‖ := by rw [← hz_im]; exact Complex.abs_im_le_norm z
        have h2 : |t| ≤ ‖z + 1‖ := by
          have := Complex.abs_im_le_norm (z + 1); simpa [hz_im] using this
        have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs, sq]
        rw [hsq]
        exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
      have ht2_pos : 0 < t ^ 2 := by
        have : t ≠ 0 := fun h => by rw [h, abs_zero] at ht1; linarith
        positivity
      dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
      rw [norm_div, norm_mul, hpow]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _))
        ht2_pos hden
    have hinv_sq_1T : ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.1])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      linarith [inv_nonneg.mpr hT_pos.le]
    have hinv_sq_neg : ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ ≤ 1 := by
      have hd : ∀ t ∈ Set.uIcc (-T) (-1 : ℝ), HasDerivAt (fun w : ℝ => -(w⁻¹)) (t ^ 2)⁻¹ t := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact ((hasDerivAt_inv (by linarith [ht.2] : t ≠ 0)).neg).congr_deriv (by ring)
      have hc_inv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (-T) (-1 : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (by linarith [ht.2])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc_inv.intervalIntegrable]
      simp only [inv_neg, neg_neg, inv_one]
      linarith [inv_nonneg.mpr hT_pos.le]
    have hleft_pos_bd : ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (1 : ℝ) T := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      calc ‖∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (1 : ℝ)..T, ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (1 : ℝ)..T, C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg 1 T (by linarith) (by linarith) le_rfl).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1)
              (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.2)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) * ∫ t in (1 : ℝ)..T, (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_1T (by positivity)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) := mul_one _
    have hleft_neg_bd : ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      have hint_dom : IntervalIntegrable (fun t : ℝ => C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹)
          volume (-T) (-1 : ℝ) := by
        refine (continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => ?_)).intervalIntegrable
        rw [Set.uIcc_of_le (by linarith)] at ht
        exact pow_ne_zero 2 (by linarith [ht.2])
      calc ‖∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)‖
          ≤ ∫ t in (-T)..(-1 : ℝ), ‖F ((σ_T : ℂ) + (t : ℂ) * I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ t in (-T)..(-1 : ℝ), C₁ * LT ^ 10 * x ^ (σ_T + 1) * (t ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (hint_seg (-T) (-1) le_rfl (by linarith) (by linarith)).norm hint_dom fun t ht => ?_
            rw [← div_eq_mul_inv]
            exact hleft_tail_pt t (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
              (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) * ∫ t in (-T)..(-1 : ℝ), (t ^ 2)⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ C₁ * LT ^ 10 * x ^ (σ_T + 1) * 1 :=
            mul_le_mul_of_nonneg_left hinv_sq_neg (by positivity)
        _ = C₁ * LT ^ 10 * x ^ (σ_T + 1) := mul_one _
    
    have hleft_mid_bd : ‖∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        4 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 2 * C₁ * LT ^ 10 * x ^ (σ_T + 1)) fun t ht => ?_).trans ?_
      · rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        set z : ℂ := (σ_T : ℂ) + (t : ℂ) * I
        have hz_re : z.re = σ_T := by simp [z]
        have htT : |t| ≤ T := by
          have : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
          linarith
        have hnd' := hleft_nd t htT
        have hpow : ‖(x : ℂ) ^ (z + 1)‖ = x ^ (σ_T + 1) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [hz_re]
        have hden : 1 / 2 ≤ ‖z * (z + 1)‖ := by
          rw [norm_mul]
          have h1 : 1 / 2 ≤ ‖z‖ := by
            have := Complex.abs_re_le_norm z; rw [hz_re, abs_of_pos hσ_pos] at this; linarith
          have h2 : 1 ≤ ‖z + 1‖ := by
            have := Complex.abs_re_le_norm (z + 1)
            have hre1 : (z + 1).re = σ_T + 1 := by simp [hz_re]
            rw [hre1, abs_of_pos (by linarith)] at this; linarith
          nlinarith
        dsimp only [F, Stage3ZeroFreeRegion.negLogDerivL]
        rw [norm_div, norm_mul, hpow]
        calc ‖-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ *
                x ^ (σ_T + 1) / ‖z * (z + 1)‖
            ≤ (C₁ * LT ^ 10) * x ^ (σ_T + 1) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hnd' (Real.rpow_nonneg hx0.le _)) (by norm_num) hden
          _ = 2 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by ring
      · norm_num
        linarith
    have hleft_bd : ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
        6 * C₁ * LT ^ 10 * x ^ (σ_T + 1) := by
      rw [hsplit_left]
      have htri1 := norm_add_le
        ((∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I)) +
          (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I)))
        (∫ t in (1 : ℝ)..T, F ((σ_T : ℂ) + (t : ℂ) * I))
      have htri2 := norm_add_le
        (∫ t in (-T)..(-1 : ℝ), F ((σ_T : ℂ) + (t : ℂ) * I))
        (∫ t in (-1 : ℝ)..1, F ((σ_T : ℂ) + (t : ℂ) * I))
      linarith
    
    have hshift_bd :
        ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) +
          (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
      rw [hshift]
      have hnorm_2pi : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnorm_2piI : ‖((2 * Real.pi * I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      have htri :
          ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤
          (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)‖ := by
        have h1 := norm_sub_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
            ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I)))
        have h2 := norm_add_le
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)))
          (((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)))
        simp only [norm_mul, hnorm_2pi, hnorm_2piI] at h1 h2
        linarith
      have hterm_left : (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖ ≤
          (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) := by
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)‖
            ≤ (2 * Real.pi)⁻¹ * (6 * C₁ * LT ^ 10 * x ^ (σ_T + 1)) :=
              mul_le_mul_of_nonneg_left hleft_bd (by positivity)
          _ = (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) := by field_simp [Real.pi_ne_zero]; ring
      have hterm_horiz : ∀ Ival : ℂ, ‖Ival‖ ≤ 2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2 →
          (2 * Real.pi)⁻¹ * ‖Ival‖ ≤ (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
        intro Ival hIval
        have hxc_div : x ^ (c + 1) / T ^ 2 ≤ x ^ 2 / T := by
          have h1 : x ^ (c + 1) / T ^ 2 ≤ (2 * x ^ 2) / T ^ 2 :=
            div_le_div_of_nonneg_right hx_pow_c (sq_nonneg T)
          have h2 : 2 * x ^ 2 / T ^ 2 ≤ x ^ 2 / T := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hT_pos) hT_pos]
            have hT2 : 2 * T ≤ T ^ 2 := by nlinarith
            nlinarith [sq_nonneg x]
          linarith
        calc (2 * Real.pi)⁻¹ * ‖Ival‖
            ≤ (2 * Real.pi)⁻¹ * (2 * C₁ * LT ^ 10 * x ^ (c + 1) / T ^ 2) :=
              mul_le_mul_of_nonneg_left hIval (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 10 * (x ^ (c + 1) / T ^ 2) := by
              field_simp [Real.pi_ne_zero, hT_pos.ne']
          _ ≤ (C₁ / Real.pi) * LT ^ 10 * (x ^ 2 / T) :=
              mul_le_mul_of_nonneg_left hxc_div (by positivity)
          _ = (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by ring
      have htop_h := hterm_horiz _ htop_bd
      have hbot_h := hterm_horiz _ hbot_bd
      change ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ_T : ℂ) + (t : ℂ) * I)) +
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + (T : ℂ) * I)) -
          ((2 * Real.pi * I : ℂ))⁻¹ * (∫ v in σ_T..c, F ((v : ℂ) + ((-T : ℝ) : ℂ) * I))‖ ≤ _
      have hsum2 : (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T + (C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T =
          (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by ring
      linarith
    
    have htotal : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
        (48 / Real.pi) * x ^ 2 * Lx / T +
        (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) +
        (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T := by
      have htri : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤
          ‖Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ +
          ‖Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
          (Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T)
      linarith
    have hLT_pow10 : LT ^ 10 ≤ c_star * Lx := by
      have h1 := pow_le_pow_left₀ hLT_pos.le hLT_le 10
      have h2 : (2 * (α * u)) ^ (10 : ℕ) = c_star * Lx := by
        rw [show 2 * (α * u) = (2 * α) * u by ring, mul_pow, h2α_pow10, hu_pow10]
      linarith
    have hx_left_exp : x ^ (σ_T + 1) ≤ x ^ 2 * Real.exp (-α * u) := by
      have h1 : x ^ (σ_T + 1) = x ^ 2 * x ^ (-(c_star / LT ^ 9)) := by
        rw [show σ_T + 1 = (2 : ℝ) + (-(c_star / LT ^ 9)) by dsimp only [σ_T]; ring,
          Real.rpow_add hx0, show x ^ (2 : ℝ) = x ^ (2 : ℕ) by norm_cast]
      have h2 : x ^ (-(c_star / LT ^ 9)) = Real.exp (-(c_star * Lx / LT ^ 9)) := by
        rw [Real.rpow_def_of_pos hx0, ← hLx_def]; congr 1; ring
      have hexp_le : -(c_star * Lx / LT ^ 9) ≤ -α * u := by
        have hdiv : α * u ≤ c_star * Lx / LT ^ 9 := by
          rw [le_div_iff₀ (pow_pos hLT_pos 9)]
          calc α * u * LT ^ 9
              ≤ α * u * (2 * (α * u)) ^ 9 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLT_pos.le hLT_le 9) (by positivity)
            _ = (1 / 2) * ((2 * α) ^ (10 : ℕ) * u ^ (10 : ℕ)) := by ring
            _ = (1 / 2) * (c_star * Lx) := by rw [h2α_pow10, hu_pow10]
            _ ≤ c_star * Lx := by nlinarith
        linarith
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (sq_nonneg x)
    have hinvT : (1 : ℝ) / T = Real.exp (-α * u) := by
      rw [hT_def, one_div, ← Real.exp_neg]; congr 1; ring
    
    have habsorb : Lx * Real.exp (-α * u) ≤ (20 / α) ^ (10 : ℕ) * Real.exp (-c_fin * u) := by
      have hsplit : Real.exp (-α * u) =
          Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u)) * Real.exp (-c_fin * u) := by
        rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; push_cast; ring
      rw [hsplit, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hv_nn : 0 ≤ (α / 20) * u := by positivity
      have hid : Lx * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u)) =
          (20 / α) ^ (10 : ℕ) * (((α / 20) * u) ^ (10 : ℕ) * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) := by
        have h1 : Lx = (20 / α) ^ (10 : ℕ) * ((α / 20) * u) ^ (10 : ℕ) := by
          rw [← mul_pow, show (20 / α) * ((α / 20) * u) = u by field_simp [hα_pos.ne'], hu_pow10]
        have h2 := congrArg (· * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) h1
        simpa only [mul_assoc] using h2
      calc Lx * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))
          = (20 / α) ^ (10 : ℕ) *
              (((α / 20) * u) ^ (10 : ℕ) * Real.exp (-((10 : ℕ) : ℝ) * ((α / 20) * u))) := hid
        _ ≤ (20 / α) ^ (10 : ℕ) * 1 :=
            mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_one 10 hv_nn) (by positivity)
        _ = (20 / α) ^ (10 : ℕ) := mul_one _
    have hterm1 : (48 / Real.pi) * x ^ 2 * Lx / T =
        (48 / Real.pi) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]; ring
    have hterm2 : (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1) ≤
        ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      calc (3 * C₁ / Real.pi) * LT ^ 10 * x ^ (σ_T + 1)
          ≤ (3 * C₁ / Real.pi) * (c_star * Lx) * (x ^ 2 * Real.exp (-α * u)) := by gcongr
        _ = ((3 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    have hterm3 : (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 / T ≤
        ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by
      rw [div_eq_mul_inv, ← one_div, hinvT]
      calc (2 * C₁ / Real.pi) * LT ^ 10 * x ^ 2 * Real.exp (-α * u)
          ≤ (2 * C₁ / Real.pi) * (c_star * Lx) * x ^ 2 * Real.exp (-α * u) := by gcongr
        _ = ((2 * C₁ / Real.pi) * c_star) * x ^ 2 * (Lx * Real.exp (-α * u)) := by ring
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * (Lx * Real.exp (-α * u)) := by linarith
      _ ≤ (48 / Real.pi + (3 * C₁ / Real.pi + 2 * C₁ / Real.pi) * c_star) *
            x ^ 2 * ((20 / α) ^ (10 : ℕ) * Real.exp (-c_fin * u)) := by gcongr
      _ = K_large * x ^ 2 * Real.exp (-c_fin * u) := by dsimp only [K_large]; ring
  
  set C_small : ℝ := 6 * Real.exp (c_fin * (Real.log x₀) ^ (1 / 10 : ℝ))
  set C_fin : ℝ := max K_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hK_large_pos (le_max_left _ _)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hge : x₀ ≤ x
  · exact (hlarge x hge).trans (by gcongr; exact le_max_left _ _)
  · push Not at hge
    have hpsi1_le : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ 6 * x ^ 2 := by
      have h1 : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ x * RHDirect.chebyshevPsi x := by
        unfold Stage4ExplicitFormula.psi1Char RHDirect.chebyshevPsi
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.norm_of_nonneg (le_max_right _ _)]
        have hmax : max (x - (n : ℝ)) 0 ≤ x :=
          max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
        have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
        calc Λ n * ‖χ n‖ * max (x - (n : ℝ)) 0
            ≤ Λ n * 1 * x := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
                hmax (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
          _ = x * Λ n := by ring
      have h2 := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith : 1 ≤ x)
      nlinarith
    have hexp_ge :
        Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) ≤
          Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log (by linarith) hge.le
      have hrpow : (Real.log x) ^ (1 / 10 : ℝ) ≤ (Real.log x₀) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog (by norm_num)
      nlinarith
    have hcancel : C_small * Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) = 6 := by
      dsimp only [C_small]
      rw [mul_assoc, ← Real.exp_add]
      have : c_fin * (Real.log x₀) ^ (1 / 10 : ℝ) + -c_fin * (Real.log x₀) ^ (1 / 10 : ℝ) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ 6 * x ^ 2 := hpsi1_le
      _ = C_small * x ^ 2 * Real.exp (-c_fin * (Real.log x₀) ^ (1 / 10 : ℝ)) := by
          rw [← hcancel]; ring
      _ ≤ C_small * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by gcongr
      _ ≤ C_fin * x ^ 2 * Real.exp (-c_fin * (Real.log x) ^ (1 / 10 : ℝ)) := by
          gcongr; exact le_max_right _ _

theorem norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
        (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
  have hfl_le : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊x + h⌋₊ + 1) := Finset.range_mono hfl_le
  
  have hpsi1_ext : Stage4ExplicitFormula.psi1Char χ x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ) := by
    unfold Stage4ExplicitFormula.psi1Char
    refine Finset.sum_subset hsub fun n _ hn => ?_
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hn
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    rw [max_eq_right (by linarith), Complex.ofReal_zero, mul_zero]
  have hchar_ext : (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * (h : ℂ) := by
    unfold Stage2DirichletAP.chebyshevPsiChar
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hdiff_eq :
      Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x =
        ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1) \ Finset.range (⌊x⌋₊ + 1),
          (Λ n : ℂ) * χ n * ((max (x + h - (n : ℝ)) 0 : ℝ) : ℂ) := by
    rw [hpsi1_ext, hchar_ext]
    unfold Stage4ExplicitFormula.psi1Char
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sdiff hsub]
    have hinner :
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
            ((Λ n : ℂ) * χ n * ((max (x + h - (n : ℝ)) 0 : ℝ) : ℂ) -
             (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ)) =
          ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ n * (h : ℂ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn_le : (n : ℝ) ≤ x :=
        le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) (Nat.floor_le hx)
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      push_cast; ring
    rw [hinner, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnot : n ∉ Finset.range (⌊x⌋₊ + 1) := (Finset.mem_sdiff.mp hn).2
    have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hnot
    have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
    have hm0 : max (x - (n : ℝ)) 0 = 0 := max_eq_right (by linarith)
    rw [hm0, Complex.ofReal_zero, mul_zero, sub_zero]
  have hpsi_diff :
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x =
        ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1) \ Finset.range (⌊x⌋₊ + 1), Λ n := by
    unfold RHDirect.chebyshevPsi
    exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
  rw [hdiff_eq, hpsi_diff, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hnot : n ∉ Finset.range (⌊x⌋₊ + 1) := (Finset.mem_sdiff.mp hn).2
  have hgt : ⌊x⌋₊ + 1 ≤ n := by simpa [Finset.mem_range] using hnot
  have hnx : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hgt)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Real.norm_of_nonneg (le_max_right _ _)]
  have hmax_le : max (x + h - (n : ℝ)) 0 ≤ h := max_le (by linarith) hh
  have hchi : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  calc Λ n * ‖χ n‖ * max (x + h - (n : ℝ)) 0
      ≤ Λ n * 1 * h := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg)
          hmax_le (le_max_right _ _) (by linarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)])
    _ = h * Λ n := by ring

theorem effective_chebyshevPsiChar_bound_one_tenth {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hpsi1⟩ := effective_psi1Char_bound hχ
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  set c_fin : ℝ := min (c₁ / 2) c_ψ with hc_fin_def
  have hc_fin_pos : 0 < c_fin := lt_min (by positivity) hc_ψ
  have hc_fin_le1 : c_fin ≤ c₁ / 2 := min_le_left _ _
  have hc_fin_le_ψ : c_fin ≤ c_ψ := min_le_right _ _
  set C_fin : ℝ := 5 * C₁ + 1 + 3 * C_ψ * Real.exp c_fin
  have hC_fin_pos : 0 < C_fin := by positivity
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  set u : ℝ := (Real.log x) ^ (1 / 10 : ℝ) with hu_def
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hLx_pos _
  set E : ℝ := Real.exp (-c_fin * u) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_le1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set h : ℝ := x * E with hh_def
  have hh_pos : 0 < h := by positivity
  have hh_le_x : h ≤ x := by nlinarith
  have hxph_ge2 : 2 ≤ x + h := by linarith
  have hxph_le2x : x + h ≤ 2 * x := by linarith
  
  have hexp_E2 : Real.exp (-c₁ * u) ≤ E ^ 2 := by
    rw [hE_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast; nlinarith
  have hexp_xh : Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) ≤ E ^ 2 := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    have hrpow : u ≤ (Real.log (x + h)) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow hLx_pos.le hlog (by norm_num)
    have h1 : Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) ≤ Real.exp (-c₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact h1.trans hexp_E2
  
  have hexp_psi : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp c_fin * E := by
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤ Real.exp (-c_fin * (Real.log x) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)]
    exact h1.trans (exp_neg_rpow_le_of_le (by norm_num) (by norm_num) hc_fin_pos hx2)
  have hexp_psi_xh : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ Real.exp c_fin * E := by
    have hlog : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx0 (by linarith)
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤ Real.exp (-c_ψ * Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_le_sqrt hlog])
    exact h1.trans hexp_psi
  
  have hdiff := norm_psi1Char_diff_sub_mul_chebyshevPsiChar_le χ hx0.le hh_pos.le
  have hnorm_mul : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ + ‖Stage4ExplicitFormula.psi1Char χ x‖ +
        h * (RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x) := by
    have h1 : ‖(h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x‖ +
        ‖Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
      have htri := norm_sub_le
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x)
        (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x -
          (h : ℂ) * Stage2DirichletAP.chebyshevPsiChar χ x)
      simpa [sub_sub_cancel] using htri
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh_pos.le] at h1
    linarith [norm_sub_le (Stage4ExplicitFormula.psi1Char χ (x + h)) (Stage4ExplicitFormula.psi1Char χ x)]
  have hbd_xh : ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖ ≤ 4 * C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ (x + h)‖
        ≤ C₁ * (x + h) ^ 2 * Real.exp (-c₁ * (Real.log (x + h)) ^ (1 / 10 : ℝ)) := hpsi1 (x + h) hxph_ge2
      _ ≤ C₁ * (2 * x) ^ 2 * E ^ 2 := by
          have hsq : (x + h) ^ 2 ≤ (2 * x) ^ 2 := by nlinarith
          gcongr
      _ = 4 * C₁ * x ^ 2 * E ^ 2 := by ring
  have hbd_x : ‖Stage4ExplicitFormula.psi1Char χ x‖ ≤ C₁ * x ^ 2 * E ^ 2 := by
    calc ‖Stage4ExplicitFormula.psi1Char χ x‖
        ≤ C₁ * x ^ 2 * Real.exp (-c₁ * u) := hpsi1 x hx2
      _ ≤ C₁ * x ^ 2 * E ^ 2 := by gcongr
  have hpsi_diff_le :
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x ≤
        (1 + 3 * C_ψ * Real.exp c_fin) * x * E := by
    have h1 := (abs_le.mp (hpsi (x + h) hxph_ge2)).2
    have h2 := (abs_le.mp (hpsi x hx2)).1
    have h3 : C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h))) ≤
        2 * C_ψ * Real.exp c_fin * x * E := by
      calc C_ψ * (x + h) * Real.exp (-c_ψ * Real.sqrt (Real.log (x + h)))
          ≤ C_ψ * (2 * x) * (Real.exp c_fin * E) := by gcongr
        _ = 2 * C_ψ * Real.exp c_fin * x * E := by ring
    have h4 : C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤
        C_ψ * Real.exp c_fin * x * E := by
      calc C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x))
          ≤ C_ψ * x * (Real.exp c_fin * E) := by gcongr
        _ = C_ψ * Real.exp c_fin * x * E := by ring
    dsimp only [h] at h1 h2 h3 ⊢
    linarith
  have hcomb : h * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ h * (C_fin * x * E) := by
    have hrhs1 : 5 * C₁ * x ^ 2 * E ^ 2 = h * (5 * C₁ * x * E) := by dsimp only [h]; ring
    have hmul_psi := mul_le_mul_of_nonneg_left hpsi_diff_le hh_pos.le
    have hrhs2 : h * (5 * C₁ * x * E) + h * ((1 + 3 * C_ψ * Real.exp c_fin) * x * E) =
        h * (C_fin * x * E) := by dsimp only [C_fin]; ring
    linarith
  exact le_of_mul_le_mul_left hcomb hh_pos

theorem effective_chebyshevPsiChar_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_chebyshevPsiChar_bound_one_tenth hχ
  refine ⟨c, hc, C * Real.exp c, by positivity, fun x hx => ?_⟩
  have hcmp := exp_neg_rpow_le_of_le (p := (1 / 20 : ℝ)) (q := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) hc hx
  calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
      ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 10 : ℝ)) := hbd x hx
    _ ≤ C * x * (Real.exp c * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ))) := by gcongr
    _ = (C * Real.exp c) * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by ring

private lemma exists_uniform_nonprincipal_char_bound {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ χ ∈ S, ∀ x : ℝ, 2 ≤ x →
        ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, zero_lt_one, 1, zero_lt_one, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert χ S' hnot ih =>
    have hχ : χ ≠ 1 := hS χ (Finset.mem_insert_self χ S')
    obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := effective_chebyshevPsiChar_bound hχ
    obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂⟩ := ih (fun ψ hψ => hS ψ (Finset.mem_insert_of_mem hψ))
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _),
      fun ψ hψ x hx => ?_⟩
    have hLx_nn : 0 ≤ (Real.log x) ^ (1 / 20 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    rcases Finset.mem_insert.mp hψ with hEq | hmem
    · rw [hEq]
      have hexp : Real.exp (-c₁ * (Real.log x) ^ (1 / 20 : ℝ)) ≤
          Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])
      calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
          ≤ C₁ * x * Real.exp (-c₁ * (Real.log x) ^ (1 / 20 : ℝ)) := hbd₁ x hx
        _ ≤ max C₁ C₂ * x * Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
              hexp (Real.exp_pos _).le (by positivity)
    · have hexp : Real.exp (-c₂ * (Real.log x) ^ (1 / 20 : ℝ)) ≤
          Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])
      calc ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
          ≤ C₂ * x * Real.exp (-c₂ * (Real.log x) ^ (1 / 20 : ℝ)) := hbd₂ ψ hmem x hx
        _ ≤ max C₁ C₂ * x * Real.exp (-min c₁ c₂ * (Real.log x) ^ (1 / 20 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
              hexp (Real.exp_pos _).le (by positivity)

private lemma sqrt_mul_log_le_mul_exp_neg_rpow {c p x : ℝ} (hc : 0 < c) (hc_le : c ≤ 1 / 4)
    (hp : 0 < p) (hp_le : p ≤ 1 / 2) (hx : 2 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * Real.exp c * x * Real.exp (-c * (Real.log x) ^ p) := by
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x with hLx_def
  have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
  have hsqrt_eq : Real.sqrt x = x * Real.exp (-(1 / 2) * Lx) := by
    have h1 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have h2 : x ^ (1 / 2 : ℝ) = x * x ^ (-(1 / 2 : ℝ)) := by
      calc x ^ (1 / 2 : ℝ) = x ^ ((1 : ℝ) + -(1 / 2 : ℝ)) := by norm_num
        _ = x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ)) := Real.rpow_add hx0 _ _
        _ = x * x ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    rw [h1, h2, Real.rpow_def_of_pos hx0, ← hLx_def]
    congr 2; ring
  have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by
    have h1_mul : (Lx / 4) * Real.exp (-(Lx / 4)) ≤ 1 := by
      have h := pow_mul_exp_neg_le_one 1 (show 0 ≤ Lx / 4 by positivity)
      simpa using h
    by_cases hL1 : 1 ≤ Lx
    · have hpow_le : Lx ^ (1 / 2 : ℝ) ≤ Lx := by
        calc Lx ^ (1 / 2 : ℝ) ≤ Lx ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          _ = Lx := Real.rpow_one Lx
      have hexp_le : Real.exp (-(1 / 2) * Lx) ≤ Real.exp (-(Lx / 4)) * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc Lx * Real.exp (-(1 / 2) * Lx)
          ≤ Lx * (Real.exp (-(Lx / 4)) * Real.exp (-c * Lx ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp_le hLx_pos.le
        _ = 4 * ((Lx / 4) * Real.exp (-(Lx / 4))) * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by ring
        _ ≤ 4 * 1 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by gcongr
        _ = 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by ring
    · push Not at hL1
      have hpow_le1 : Lx ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hLx_pos.le hL1.le (by norm_num)
      have h1 : Real.exp (-(1 / 2) * Lx) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-c * Lx ^ (1 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)])
      have h3 : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
      calc Lx * Real.exp (-(1 / 2) * Lx)
          ≤ 1 * 1 := mul_le_mul hL1.le h1 (Real.exp_pos _).le zero_le_one
        _ = 4 * (1 / 4) := by norm_num
        _ ≤ 4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ)) := by linarith
  have hcmp := exp_neg_rpow_le_of_le hp hp_le hc hx
  rw [hsqrt_eq]
  calc x * Real.exp (-(1 / 2) * Lx) * Lx
      = x * (Lx * Real.exp (-(1 / 2) * Lx)) := by ring
    _ ≤ x * (4 * Real.exp (-c * Lx ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hkey hx0.le
    _ ≤ x * (4 * (Real.exp c * Real.exp (-c * Lx ^ p))) := by gcongr
    _ = 4 * Real.exp c * x * Real.exp (-c * Lx ^ p) := by ring

theorem effective_pnt_psiAP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  classical
  obtain ⟨c_ψ, hc_ψ, C_ψ, hC_ψ, hpsi⟩ := Stage6EffectivePNT.effective_pnt_chebyshevPsi
  obtain ⟨c_χ, hc_χ, C_χ, hC_χ, hchar⟩ :=
    exists_uniform_nonprincipal_char_bound (Finset.univ.erase (1 : DirichletCharacter ℂ q))
      (fun χ hχ => (Finset.mem_erase.mp hχ).1)
  set c_fin : ℝ := min (min c_ψ c_χ) (1 / 4) with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  have hc_fin_le_ψ : c_fin ≤ c_ψ := (min_le_left _ _).trans (min_le_left _ _)
  have hc_fin_le_χ : c_fin ≤ c_χ := (min_le_left _ _).trans (min_le_right _ _)
  have hc_fin_le_qtr : c_fin ≤ 1 / 4 := min_le_right _ _
  set ω : ℝ := (q.primeFactors.card : ℝ)
  set C_fin : ℝ := C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin + C_χ
  have hC_fin_pos : 0 < C_fin := by positivity
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hphi_ge1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set E : ℝ := Real.exp (-c_fin * (Real.log x) ^ (1 / 20 : ℝ)) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  
  have hpsi_bd : |RHDirect.chebyshevPsi x - x| ≤ (C_ψ * Real.exp c_fin) * x * E := by
    have h1 : Real.exp (-c_ψ * Real.sqrt (Real.log x)) ≤
        Real.exp (-c_fin * (Real.log x) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 2 : ℝ)]
    have h2 := h1.trans (exp_neg_rpow_le_of_le (p := (1 / 20 : ℝ)) (q := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) hc_fin_pos hx2)
    calc |RHDirect.chebyshevPsi x - x|
        ≤ C_ψ * x * Real.exp (-c_ψ * Real.sqrt (Real.log x)) := hpsi x hx2
      _ ≤ C_ψ * x * (Real.exp c_fin * E) := by gcongr
      _ = (C_ψ * Real.exp c_fin) * x * E := by ring
  
  have hlog_bd : ω * Real.log x ≤ (4 * ω * Real.exp c_fin) * x * E := by
    have hsq_ge1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have h1 : Real.log x ≤ Real.sqrt x * Real.log x := by nlinarith
    have h2 := h1.trans (sqrt_mul_log_le_mul_exp_neg_rpow hc_fin_pos hc_fin_le_qtr
      (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (1 / 20 : ℝ) ≤ 1 / 2) hx2)
    have hω_nn : 0 ≤ ω := Nat.cast_nonneg _
    calc ω * Real.log x ≤ ω * (4 * Real.exp c_fin * x * E) := mul_le_mul_of_nonneg_left h2 hω_nn
      _ = (4 * ω * Real.exp c_fin) * x * E := by ring
  
  have hchar_bd : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤ C_χ * x * E := by
    intro χ hχ
    have hmem : χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
      Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ _⟩
    calc ‖Stage2DirichletAP.chebyshevPsiChar χ x‖
        ≤ C_χ * x * Real.exp (-c_χ * (Real.log x) ^ (1 / 20 : ℝ)) := hchar χ hmem x hx2
      _ ≤ C_χ * x * E := by
          dsimp only [E]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [Real.rpow_nonneg hLx_pos.le (1 / 20 : ℝ)]
  have htri := Stage2DirichletAP.abs_chebyshevPsiAP_sub_le_of_uniform_char_bound hcop
    (by linarith : 1 ≤ x) (by positivity : 0 ≤ C_χ * x * E) hpsi_bd hchar_bd
  have hdiv_le : ((C_ψ * Real.exp c_fin) * x * E + ω * Real.log x) / (q.totient : ℝ) ≤
      (C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin) * x * E := by
    calc ((C_ψ * Real.exp c_fin) * x * E + ω * Real.log x) / (q.totient : ℝ)
        ≤ ((C_ψ * Real.exp c_fin) * x * E + (4 * ω * Real.exp c_fin) * x * E) / 1 := by
          refine div_le_div₀ (by positivity) (by linarith) zero_lt_one hphi_ge1
      _ = (C_ψ * Real.exp c_fin + 4 * ω * Real.exp c_fin) * x * E := by ring
  dsimp only [C_fin]
  linarith

theorem effective_pnt_thetaAP {q a : ℕ} [NeZero q] (hcop : Nat.Coprime a q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
          C * x * Real.exp (-c * (Real.log x) ^ (1 / 20 : ℝ)) := by
  obtain ⟨c, hc, C, hC, hpsi⟩ := effective_pnt_psiAP hcop
  set c' : ℝ := min c (1 / 4) with hc'_def
  have hc'_pos : 0 < c' := lt_min hc (by norm_num)
  have hc'_le_c : c' ≤ c := min_le_left _ _
  have hc'_le_qtr : c' ≤ 1 / 4 := min_le_right _ _
  refine ⟨c', hc'_pos, C + 4 * Real.exp c', by positivity, fun x hx => ?_⟩
  have hdiff : |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| ≤
      Real.sqrt x * Real.log x := by
    have h1 := Stage2DirichletAP.chebyshevThetaAP_le_chebyshevPsiAP q a x
    have h2 := Stage2DirichletAP.chebyshevPsiAP_sub_chebyshevThetaAP_le q a (by linarith : 1 ≤ x)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact h2
  have hsqrt := sqrt_mul_log_le_mul_exp_neg_rpow hc'_pos hc'_le_qtr
    (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (1 / 20 : ℝ) ≤ 1 / 2) hx
  have hpsi' : |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤
      C * x * Real.exp (-c' * (Real.log x) ^ (1 / 20 : ℝ)) := by
    have hLx_nn : 0 ≤ (Real.log x) ^ (1 / 20 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    refine (hpsi x hx).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have htri : |Stage2DirichletAP.chebyshevThetaAP q a x - x / (q.totient : ℝ)| ≤
      |Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x| +
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      (Stage2DirichletAP.chebyshevThetaAP q a x - Stage2DirichletAP.chebyshevPsiAP q a x)
      (Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ))
  linarith

end RHDirect.Stage7PNTInAP
end

/-! ## From RHDirect/Stage10SiegelWalfiszFull.lean -/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage10SiegelWalfiszFull

private lemma sq_mul_exp_neg_two_le_one {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-2 * u) ≤ 1 := by
  have h1 : u * Real.exp (-u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos u)).mpr (by linarith)
  have h2 : u ^ 2 * Real.exp (-2 * u) = (u * Real.exp (-u)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h2]
  exact pow_le_one₀ (mul_nonneg hu (Real.exp_pos (-u)).le) h1

private lemma stepSum_primeLogAP_eq_thetaAP (q a : ℕ) (x : ℝ) :
    Stage3RealAnalyticLandau.stepSum
        (fun n => if n.Prime ∧ n ≡ a [MOD q] then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) x =
      (Stage2DirichletAP.chebyshevThetaAP q a x : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum Stage2DirichletAP.chebyshevThetaAP
  rw [Complex.ofReal_sum]
  have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [Nat.not_prime_zero, false_and, ↓reduceIte, Complex.ofReal_zero, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

private lemma intervalIntegral_stepSum_unit (a : ℕ → ℂ) (k : ℕ) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), Stage3RealAnalyticLandau.stepSum a t * φ' t =
      Stage3RealAnalyticLandau.stepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      Stage3RealAnalyticLandau.stepSum a t * φ' t =
        Stage3RealAnalyticLandau.stepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

private lemma intervalIntegrable_stepSum_mul_unit (a : ℕ → ℂ) (k : ℕ) {φ' : ℝ → ℂ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum a t * φ' t) volume
      (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum a (k : ℝ) * φ' t)
      volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    hc.intervalIntegrable.const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]

set_option maxHeartbeats 2000000 in
theorem primeCountAP_eq_abel_thetaAP (q a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (Stage2DirichletAP.primeCountAP q a x : ℝ) =
      Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x +
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) := by
  set f : ℕ → ℂ := fun n => if n.Prime ∧ n ≡ a [MOD q] then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0
  set φ : ℝ → ℂ := fun u => (((Real.log u)⁻¹ : ℝ) : ℂ)
  set φ' : ℝ → ℂ := fun u => ((-(1 / (u * (Real.log u) ^ 2)) : ℝ) : ℂ)
  have hd : ∀ t ∈ Set.Icc (2 : ℝ) x, HasDerivAt φ (φ' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlt0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hr : HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(1 / (t * (Real.log t) ^ 2))) t := by
      have h1 := (Real.hasDerivAt_log ht0).inv hlt0
      refine h1.congr_deriv ?_
      field_simp
    exact hr.ofReal_comp
  have hc : ContinuousOn φ' (Set.Icc (2 : ℝ) x) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.neg (continuousOn_const.div
      (continuousOn_id.mul ((Real.continuousOn_log.mono fun t ht =>
        (by linarith [ht.1] : (0 : ℝ) < t).ne').pow 2)) fun t ht => ?_)
    exact mul_ne_zero (by linarith [ht.1] : (0 : ℝ) < t).ne'
      (pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne')
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hint_nat : ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum f t * φ' t) volume (2 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 2 N, f n * φ (n : ℝ) =
        Stage3RealAnalyticLandau.stepSum f (N : ℝ) * φ (N : ℝ) -
          ∫ t in (2 : ℝ)..(N : ℝ), Stage3RealAnalyticLandau.stepSum f t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat, intervalIntegral.integral_same,
        sub_zero]
      have hf2 : Stage3RealAnalyticLandau.stepSum f 2 = f 2 := by
        unfold Stage3RealAnalyticLandau.stepSum
        rw [Nat.floor_ofNat]
        have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
        rw [hIcc, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
        have h1 : f 1 = 0 := by simp [f, Nat.not_prime_one]
        rw [h1, zero_add]
      rw [hf2]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (2 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact ⟨le_trans hm2R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit f m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit f m
        (fun t ht => hd t (hsub_u ht)) (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc2 : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hIcc1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hstep_succ : Stage3RealAnalyticLandau.stepSum f ((m + 1 : ℕ) : ℝ) =
          Stage3RealAnalyticLandau.stepSum f (m : ℝ) + f (m + 1) := by
        unfold Stage3RealAnalyticLandau.stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc1, Finset.sum_insert (by simp)]
        ring
      rw [hIcc2, Finset.sum_insert (by simp), heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN2 hfl_le
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (2 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (by exact_mod_cast hN2) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      Stage3RealAnalyticLandau.stepSum f t * φ' t =
        Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [Stage3RealAnalyticLandau.stepSum_const_on_Ico f ⌊x⌋₊ ht.1.le hlt]
  have hint_tail :
      IntervalIntegrable (fun t => Stage3RealAnalyticLandau.stepSum f t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul
      (Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t =
      Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : Stage3RealAnalyticLandau.stepSum f x = Stage3RealAnalyticLandau.stepSum f (⌊x⌋₊ : ℝ) := by
    unfold Stage3RealAnalyticLandau.stepSum; rw [Nat.floor_natCast]
  have hab : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ) =
      Stage3RealAnalyticLandau.stepSum f x * φ x -
        ∫ t in (2 : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N, hstep_x]
    ring
  have hLHS : (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ)).re = (Stage2DirichletAP.primeCountAP q a x : ℝ) := by
    have hsum_eq : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, f n * φ (n : ℝ) =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n.Prime ∧ n ≡ a [MOD q] then (1 : ℂ) else 0 := by
      have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (insert 1 (Finset.Icc 2 ⌊x⌋₊)) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      simp only [Nat.not_prime_zero, Nat.not_prime_one, false_and, ↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      simp only [f, φ]
      split_ifs
      · rw [← Complex.ofReal_mul, mul_inv_cancel₀ hlogn, Complex.ofReal_one]
      · simp
    rw [hsum_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp [Stage2DirichletAP.primeCountAP]
  have hRHS : (Stage3RealAnalyticLandau.stepSum f x * φ x -
        ∫ t in (2 : ℝ)..x, Stage3RealAnalyticLandau.stepSum f t * φ' t).re =
      Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x +
        ∫ t in (2 : ℝ)..x, Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2) := by
    have h1 : Stage3RealAnalyticLandau.stepSum f x * φ x =
        ((Stage2DirichletAP.chebyshevThetaAP q a x / Real.log x : ℝ) : ℂ) := by
      rw [stepSum_primeLogAP_eq_thetaAP]
      simp only [φ, ← Complex.ofReal_mul, div_eq_mul_inv]
    have h2 : (fun t : ℝ => Stage3RealAnalyticLandau.stepSum f t * φ' t) =
        fun t : ℝ => (((-(Stage2DirichletAP.chebyshevThetaAP q a t / (t * (Real.log t) ^ 2)) : ℝ) : ℂ)) := by
      funext t
      rw [stepSum_primeLogAP_eq_thetaAP]
      simp only [φ', ← Complex.ofReal_mul]
      congr 1; ring
    rw [h1, h2, intervalIntegral.integral_ofReal, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_re, intervalIntegral.integral_neg, sub_neg_eq_add]
  have hre := congrArg Complex.re hab
  rw [hLHS, hRHS] at hre
  exact hre

theorem integral_inv_log_eq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have hcont1 : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact (Real.log_pos (by linarith [ht.1])).ne'
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 2) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => u / Real.log u)
        (1 / Real.log t - 1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hd := (hasDerivAt_id' t).fun_div (Real.hasDerivAt_log ht0.ne') hlt0.ne'
    refine hd.congr_deriv ?_
    field_simp [ht0.ne', hlt0.ne']
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont1.sub hcont2).intervalIntegrable
  rw [intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable] at hftc
  linarith

lemma measurable_chebyshevThetaAP (q a : ℕ) :
    Measurable (Stage2DirichletAP.chebyshevThetaAP q a) := by
  have h : Stage2DirichletAP.chebyshevThetaAP q a =
      (fun k : ℕ => ∑ n ∈ Finset.range (k + 1),
        if n.Prime ∧ n ≡ a [MOD q] then Real.log (n : ℝ) else 0) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

end RHDirect.Stage10SiegelWalfiszFull
end

section
open Filter Real Finset MeasureTheory Set Asymptotics
open scoped Topology
namespace Partial323
lemma decay (c C : ℝ) (hc : 0<c) :
    ∀ᶠ t : ℝ in atTop, C*exp (-c*(log t)^(1/20:ℝ))*(log t)^2 ≤ 1 := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 40 c hc).comp
    ((tendsto_rpow_atTop (by norm_num : 0 < (1/20:ℝ))).comp tendsto_log_atTop)).const_mul C
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const zero_lt_one,tendsto_log_atTop.eventually_gt_atTop 0] with t ht hlog
  simp only [Function.comp_apply] at ht
  change C*((log t^(1/20:ℝ))^(40:ℝ)*exp (-c*(log t)^(1/20:ℝ)))<1 at ht
  rw [←rpow_mul hlog.le,show (1/20:ℝ)*40=2 by norm_num,rpow_two] at ht
  linarith only [ht]
lemma growth : Tendsto (fun x : ℝ => x/(log x)^3) atTop atTop := by
  apply ((tendsto_exp_div_pow_atTop 3).comp tendsto_log_atTop).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x h
  simp [exp_log h]
lemma abel_bound (θ pc : ℝ → ℝ) (meas : Measurable θ)
    (eff : ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ t : ℝ, 2≤t →
      |θ t - t/2| ≤ C*t*exp (-c*(log t)^(1/20:ℝ)))
    (abel : ∀ x : ℝ, 2≤x → pc x = θ x/log x + ∫ t in (2:ℝ)..x, θ t/(t*(log t)^2))
    (li : ∀ x : ℝ, 2≤x → (∫ t in (2:ℝ)..x, 1/log t) = x/log x-2/log 2+
      ∫ t in (2:ℝ)..x, 1/(log t)^2) :
    (fun x : ℝ => pc x - (1/2:ℝ)*(∫ t in (2:ℝ)..x,1/log t)) =O[atTop]
      (fun x => x/(log x)^3) := by
  obtain ⟨c,hc,C,hC,est⟩ := eff
  let E (t : ℝ) := (θ t-t/2)/(t*(log t)^2)
  let F (t : ℝ) := t/(log t)^3
  let G (t : ℝ) := (log t-3)/(log t)^4
  have log2 : 0<log 2 := log_pos one_lt_two
  have EI {a b : ℝ} (ha : 2≤a) (hab : a≤b) : IntervalIntegrable E volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    refine Integrable.mono' (integrableOn_const (C:=C/(log 2)^2) (hs:=measure_Ioc_lt_top.ne)) ?_ ?_
    · exact ((meas.sub (measurable_id.div_const _)).div (measurable_id.mul
        (Real.measurable_log.pow_const 2))).aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have t2 := ha.trans ht.1.le
    have tp : 0<t := by linarith
    have ll := log_le_log (by norm_num : (0:ℝ)<2) t2
    have lp := log2.trans_le ll
    have ex : exp (-c*(log t)^(1/20:ℝ)) ≤ 1 := exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (rpow_nonneg lp.le _))
    have h := (est t t2).trans (show C*t*exp (-c*(log t)^(1/20:ℝ)) ≤ C*t by
      simpa using mul_le_mul_of_nonneg_left ex (mul_nonneg hC.le tp.le))
    dsimp only [E]
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos tp (sq_pos_of_pos lp))]
    calc _ ≤ C*t/(t*(log 2)^2) := div_le_div₀ (by positivity) h (by positivity)
            (by gcongr)
         _ = _ := by field_simp
  have LI {a b : ℝ} (ha : 2≤a) (hab : a≤b) :
      IntervalIntegrable (fun t : ℝ => 1/(log t)^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine continuousOn_const.div ((continuousOn_log.mono ?_).pow 2) ?_
    · intro t ht; exact ne_of_gt (by linarith [ht.1])
    · intro t ht; exact pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
  obtain ⟨Y,hy⟩ := eventually_atTop.mp (((decay c C hc).and (eventually_ge_atTop (2:ℝ))).and
    (tendsto_log_atTop.eventually_ge_atTop 6))
  have y2 := (hy Y le_rfl).1.2
  have herr (t : ℝ) (ht : Y≤t) : |θ t-t/2| ≤ t/(log t)^2 := by
    obtain ⟨⟨dec,t2⟩,lg⟩ := hy t ht
    apply (est t t2).trans
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith))).mpr
    nlinarith only [mul_le_mul_of_nonneg_right dec (by linarith : 0≤t)]
  have tail (x : ℝ) (hx : Y≤x) : |∫ t in Y..x,E t| ≤ F x := by
    have dF (t : ℝ) (ht : t∈uIcc Y x) : HasDerivAt F (G t) t := by
      rw [uIcc_of_le hx] at ht
      have tp : 0<t := by linarith [ht.1]
      have lp : 0<log t := log_pos (by linarith [ht.1])
      have der := (hasDerivAt_id t).div ((Real.hasDerivAt_log tp.ne').pow 3) (pow_ne_zero 3 lp.ne')
      apply der.congr_deriv
      dsimp [G]
      field_simp <;> ring
    have gI : IntervalIntegrable G volume Y x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hx]
      have l : ContinuousOn log (Icc Y x) := continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [ht.1]))
      exact (l.sub (continuousOn_const (c:=3))).div (l.pow 4) fun t ht => pow_ne_zero 4 (log_pos (by linarith [ht.1])).ne'
    calc _ ≤ ∫ t in Y..x, |E t| := intervalIntegral.abs_integral_le_integral_abs hx
         _ ≤ ∫ t in Y..x, G t := by
           apply intervalIntegral.integral_mono_on hx (EI y2 hx).abs gI
           intro t ht
           have tp : 0<t := by linarith [ht.1]
           have lg := (hy t ht.1).2
           have lp : 0<log t := by linarith
           dsimp only [E]
           rw [abs_div,abs_of_pos (mul_pos tp (sq_pos_of_pos lp))]
           calc _ ≤ (t/(log t)^2)/(t*(log t)^2) := div_le_div_of_nonneg_right (herr t ht.1) (by positivity)
                _ = 1/(log t)^4 := by field_simp
                _ ≤ G t := div_le_div_of_nonneg_right (by linarith) (by positivity)
         _ = F x-F Y := intervalIntegral.integral_eq_sub_of_hasDerivAt dF gI
         _ ≤ F x := sub_le_self _ (by dsimp [F]; exact div_nonneg (by linarith) (pow_nonneg
                   (log_pos (by linarith : 1<Y)).le _))
  let B := |(1/log 2 : ℝ)|+|∫ t in (2:ℝ)..Y, E t|
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop Y,growth.eventually_ge_atTop B] with x hx hb
  have x2 := y2.trans hx
  have xp : 0<x := by linarith
  have lp : 0<log x := log_pos (by linarith)
  have split : (∫ t in (2:ℝ)..x,θ t/(t*(log t)^2)) =
      (1/2:ℝ)*(∫ t in (2:ℝ)..x,1/(log t)^2)+(∫ t in (2:ℝ)..x,E t) := by
    rw [← intervalIntegral.integral_const_mul,←intervalIntegral.integral_add ((LI le_rfl x2).const_mul _) (EI le_rfl x2)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le x2] at ht
    have tp : 0<t := by linarith [ht.1]
    have tl : 0<log t := log_pos (by linarith [ht.1])
    dsimp [E]
    field_simp
    ring
  have id : pc x-(1/2:ℝ)*(∫ t in (2:ℝ)..x,1/log t) =
      (θ x-x/2)/log x+1/log 2+(∫ t in (2:ℝ)..Y,E t)+(∫ t in Y..x,E t) := by
    rw [abel x x2,li x x2,split,← intervalIntegral.integral_add_adjacent_intervals (EI le_rfl y2) (EI y2 hx)]
    ring
  have bnd : |(θ x-x/2)/log x| ≤ F x := by
    rw [abs_div,abs_of_pos lp]
    calc _ ≤ (x/(log x)^2)/log x := div_le_div_of_nonneg_right (herr x hx) lp.le
         _ = _ := by dsimp [F]; ring
  simp only [Real.norm_eq_abs]
  rw [id, abs_of_pos (div_pos xp (pow_pos lp 3))]
  change _ ≤ 3*F x
  change B ≤ F x at hb
  dsimp [B] at hb
  linarith only [abs_add_le ((θ x-x/2)/log x+1/log 2+(∫ t in (2:ℝ)..Y,E t)) (∫ t in Y..x,E t),
    abs_add_le ((θ x-x/2)/log x+1/log 2) (∫ t in (2:ℝ)..Y,E t),abs_add_le ((θ x-x/2)/log x) (1/log 2),bnd,hb,tail x hx]
end Partial323
end

section
open Filter Finset Real Asymptotics
open scoped Topology
namespace Finish323
open RHDirect.Stage2DirichletAP RHDirect.Stage7PNTInAP RHDirect.Stage10SiegelWalfiszFull
lemma count (N : ℕ) (hn : 2≤N) :
    ({p : ℕ | p≤N ∧ p.Prime ∧ p%4≠3}.ncard : ℝ) = (primeCountAP 4 1 N : ℝ)+1 := by
  classical
  let S : Finset ℕ := (Finset.range (N+1)).filter fun p : ℕ => p.Prime ∧ p ≡ 1 [MOD 4]
  have eq : {p : ℕ | p≤N ∧ p.Prime ∧ p%4≠3} = ((insert 2 S : Finset ℕ) : Set ℕ) := by
    ext p
    change (p≤N ∧ p.Prime ∧ p%4≠3) ↔ p∈insert 2 S
    constructor
    · rintro ⟨hpN,pr,hp⟩
      apply Finset.mem_insert.mpr
      rcases pr.eq_two_or_odd with two|odd
      · exact Or.inl two
      · apply Or.inr
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega),pr,show p%4=1%4 by omega⟩
    · intro mem
      rcases Finset.mem_insert.mp mem with rfl|mem
      · exact ⟨hn,Nat.prime_two,by decide⟩
      · obtain ⟨h,pr,eq⟩ := Finset.mem_filter.mp mem
        have := Finset.mem_range.mp h
        change p%4=1%4 at eq
        exact ⟨by omega,pr,by omega⟩
  have h2 : 2 ∉ S := by simp [S,Nat.ModEq]
  rw [eq,Set.ncard_coe_finset,card_insert_of_notMem h2]
  simp only [primeCountAP,Nat.floor_natCast,Nat.cast_add,Nat.cast_one,S]
lemma result : OMA.R_Erdos323_erdos_323_variants_k_eq_2_R1.H2 := by
  have hφ : (4:ℕ).totient = 2 := by decide
  obtain ⟨c,hc,C,hC,bound⟩ := effective_pnt_thetaAP (q:=4) (a:=1) (by decide)
  have est := Partial323.abel_bound (chebyshevThetaAP 4 1) (fun x => (primeCountAP 4 1 x:ℝ))
    (measurable_chebyshevThetaAP 4 1) ⟨c,hc,C,hC,by simpa [hφ] using bound⟩
    (fun x hx => primeCountAP_eq_abel_thetaAP 4 1 hx) (fun _ hx => integral_inv_log_eq hx)
  obtain ⟨b,hb,he⟩ := (est.comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))).exists_pos
  apply IsBigO.of_bound (b+1)
  filter_upwards [he.bound,(Partial323.growth.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1,
      eventually_ge_atTop 2] with N h h1 hN
  change 1≤(N:ℝ)/(log N)^3 at h1
  simp only [Function.comp_apply,Real.norm_eq_abs] at h ⊢
  rw [count N hN]
  have a : 0≤(N:ℝ)/(log N)^3 := by linarith
  rw [abs_of_nonneg a] at h ⊢
  rw [show (primeCountAP 4 1 N : ℝ)+1-1/2*(∫ t in (2:ℝ)..(N:ℝ),1/log t) =
      ((primeCountAP 4 1 N:ℝ)-1/2*(∫ t in (2:ℝ)..(N:ℝ),1/log t))+1 by ring]
  calc _ ≤ |(primeCountAP 4 1 N:ℝ)-1/2*(∫ t in (2:ℝ)..(N:ℝ),1/log t)|+1 := by
         simpa using abs_add_le ((primeCountAP 4 1 N:ℝ)-1/2*(∫ t in (2:ℝ)..(N:ℝ),1/log t)) 1
       _ ≤ _ := by linarith
end Finish323
end

theorem OMA.solution : OMA.R_Erdos323_erdos_323_variants_k_eq_2_R1.H2 := Finish323.result
