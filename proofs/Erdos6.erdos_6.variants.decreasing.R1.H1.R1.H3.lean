import OMAReductions.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1
import Mathlib

/-!
# From primitive character sums to arithmetic progression errors

The arithmetic progression and conductor estimates are adapted from
@nil-commits, Arithmetica4, commit 023f6441c22a9ca0db1670e351e8ac44f00555ea,
under Apache-2.0. The source files are RHDirect/ElementaryEquiv,
Stage2DirichletAP, Stage5DirichletLZeroFree, Stage8BarbanDavenport and
Stage11BombieriVinogradov. Arithmetica4 builds on Mathlib4 under Apache-2.0.
The final summation below removes higher prime powers in each progression.
Credit: @marcusbuffett.
-/

noncomputable section

open Complex DirichletCharacter Filter Topology

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect

def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n

end RHDirect
end

noncomputable section

open Complex DirichletCharacter Finset RHDirect
open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage2DirichletAP

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

theorem two_pow_card_primeFactors_le {q : ℕ} (hq : 0 < q) :
    2 ^ q.primeFactors.card ≤ q := by
  have h1 : 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
    rw [Finset.prod_const]
  rw [h1]
  calc ∏ _p ∈ q.primeFactors, (2 : ℕ)
      ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

theorem card_primeFactors_le_log_div_log_two {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have hle : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast two_pow_card_primeFactors_le hq
  calc (q.primeFactors.card : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ q.primeFactors.card) := (Real.log_pow 2 q.primeFactors.card).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (by positivity) hle

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

theorem chebyshevPsi_sub_chebyshevPsiCoprime_le_log {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 1 ≤ x) :
    chebyshevPsi x - chebyshevPsiCoprime q x ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x :=
  (chebyshevPsi_sub_chebyshevPsiCoprime_bounds hq hx).2.trans
    (mul_le_mul_of_nonneg_right (card_primeFactors_le_log_div_log_two hq) (Real.log_nonneg hx))

open Classical in

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

end RHDirect.Stage5DirichletLZeroFree
end

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage8BarbanDavenport

theorem changeLevel_apply_nat_of_coprime {d q : ℕ} (hd : d ∣ q)
    (ψ : DirichletCharacter ℂ d) {n : ℕ} (hcop : Nat.Coprime n q) :
    DirichletCharacter.changeLevel hd ψ (n : ZMod q) = ψ (n : ZMod d) := by
  have hu : IsUnit (n : ZMod q) := Stage2DirichletAP.isUnit_zmod_of_coprime hcop
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd hu.unit
  have hspec : ((hu.unit : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) := hu.unit_spec
  rw [hspec, ZMod.cast_natCast hd] at h1
  exact h1

theorem three_le_conductor_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 3 ≤ χ.conductor := by
  have hne0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
  have hne1 : χ.conductor ≠ 1 := by
    intro h1
    apply hχ
    have hprim := χ.changeLevel_primitiveCharacter
    have hψ1 : χ.primitiveCharacter = 1 := by
      have : NeZero χ.conductor := ⟨hne0⟩
      have hcard : Fintype.card (ZMod χ.conductor)ˣ = 1 := by
        rw [ZMod.card_units_eq_totient, h1]; norm_num
      have hsub : Subsingleton (ZMod χ.conductor)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      ext u
      rw [Subsingleton.elim u 1]
      simp
    rw [← hprim, hψ1, map_one]
  have hne2 : χ.conductor ≠ 2 := by
    intro h2
    have hprim_is := χ.primitiveCharacter_isPrimitive
    have : NeZero χ.conductor := ⟨hne0⟩
    have hψ1 : χ.primitiveCharacter = 1 := by
      have hcard : Fintype.card (ZMod χ.conductor)ˣ = 1 := by
        rw [ZMod.card_units_eq_totient, h2]; norm_num
      have hsub : Subsingleton (ZMod χ.conductor)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      ext u
      rw [Subsingleton.elim u 1]
      simp
    have hc : χ.primitiveCharacter.conductor = χ.conductor := hprim_is
    rw [hψ1, DirichletCharacter.conductor_one] at hc
    omega
  omega

theorem card_primeFactors_not_dvd_le_log {q d : ℕ} (hq : 0 < q) (hd3 : 3 ≤ d) (hdq : d ∣ q) :
    ((q.primeFactors.filter (fun p => ¬ p ∣ d)).card : ℝ) ≤ Real.log (q : ℝ) := by
  set S : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ∣ d)
  have hS_cop : Nat.Coprime (∏ p ∈ S, p) d := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hmem := Finset.mem_filter.mp hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hmem.1
    exact (Nat.Prime.coprime_iff_not_dvd hpr).mpr hmem.2
  have hS_dvd : (∏ p ∈ S, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd q)
  have hmul_dvd : d * (∏ p ∈ S, p) ∣ q := (hS_cop.symm).mul_dvd_of_dvd_of_dvd hdq hS_dvd
  have hmul_le : ((d : ℝ) * ∏ p ∈ S, (p : ℝ)) ≤ (q : ℝ) := by
    have hnat : d * ∏ p ∈ S, p ≤ q := Nat.le_of_dvd hq hmul_dvd
    rw [← Nat.cast_prod, ← Nat.cast_mul]
    exact_mod_cast hnat
  have hprod_pos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) :=
    Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlog_ge : Real.log (d : ℝ) + ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    have h1 := Real.log_le_log (mul_pos hd_pos hprod_pos) hmul_le
    rw [Real.log_mul hd_pos.ne' hprod_pos.ne',
      Real.log_prod fun p hp => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos).ne'] at h1
    exact h1
  have hlog3_gt1 : (1 : ℝ) < Real.log (3 : ℝ) := by
    have he3 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) he3)
  have hlogd_ge1 : (1 : ℝ) ≤ Real.log (d : ℝ) :=
    hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hd3))
  by_cases h2 : 2 ∈ S
  · have hsum_split : ∑ p ∈ S, Real.log (p : ℝ) = Real.log 2 + ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
      rw [← Finset.add_sum_erase S (fun p => Real.log (p : ℝ)) h2]
      norm_num
    have herase_ge : ((S.erase 2).card : ℝ) ≤ ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
      calc ((S.erase 2).card : ℝ)
          = ∑ _p ∈ S.erase 2, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ S.erase 2, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
            have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).1
            have hp3 : 3 ≤ p := by have := hpr.two_le; omega
            exact hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hp3))
    have hcard_eq : (S.card : ℝ) = ((S.erase 2).card : ℝ) + 1 := by
      have hnat : (S.erase 2).card + 1 = S.card := Finset.card_erase_add_one h2
      exact_mod_cast hnat.symm
    have hlog2_nn : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  · have hsum_ge : (S.card : ℝ) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      calc (S.card : ℝ)
          = ∑ _p ∈ S, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hne2 : p ≠ 2 := fun h => h2 (h ▸ hp)
            have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hp3 : 3 ≤ p := by have := hpr.two_le; omega
            exact hlog3_gt1.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hp3))
    linarith

private lemma sum_biUnion_le_of_nonneg_local {α β : Type*} [DecidableEq β] (s : Finset α)
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

theorem norm_chebyshevPsiChar_sub_primitive_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖Stage2DirichletAP.chebyshevPsiChar χ x -
        Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤
      Real.log (q : ℝ) * Real.log x := by
  set d : ℕ := χ.conductor
  set ψ : DirichletCharacter ℂ d := χ.primitiveCharacter
  have hdq : d ∣ q := χ.conductor_dvd_level
  have hch : DirichletCharacter.changeLevel hdq ψ = χ := χ.changeLevel_primitiveCharacter
  have hd3 : 3 ≤ d := three_le_conductor_of_ne_one hχ
  have hdiff_eq :
      Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar ψ x =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (χ (n : ZMod q) - ψ (n : ZMod d)) * (Λ n : ℂ) := by
    unfold Stage2DirichletAP.chebyshevPsiChar
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hdiff_eq]
  set T : Finset ℕ :=
    (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ¬ Nat.Coprime n q ∧ Nat.Coprime n d ∧ IsPrimePow n)
  have hnorm_le :
      ‖∑ n ∈ Finset.range (⌊x⌋₊ + 1), (χ (n : ZMod q) - ψ (n : ZMod d)) * (Λ n : ℂ)‖ ≤
        ∑ n ∈ T, Λ n := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hpp : IsPrimePow n
    · by_cases hcopq : Nat.Coprime n q
      · have hval : χ (n : ZMod q) = ψ (n : ZMod d) := by
          rw [← hch]
          exact changeLevel_apply_nat_of_coprime hdq ψ hcopq
        rw [hval, sub_self, zero_mul, norm_zero]
        split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl]
      · by_cases hcopd : Nat.Coprime n d
        · rw [if_pos ⟨hcopq, hcopd, hpp⟩]
          have hχ0 : χ (n : ZMod q) = 0 :=
            MulChar.map_nonunit χ fun hu => hcopq ((ZMod.isUnit_iff_coprime n q).mp hu)
          rw [hχ0, zero_sub, norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact (mul_le_mul_of_nonneg_right (ψ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
        · have hχ0 : χ (n : ZMod q) = 0 :=
            MulChar.map_nonunit χ fun hu => hcopq ((ZMod.isUnit_iff_coprime n q).mp hu)
          have hψ0 : ψ (n : ZMod d) = 0 :=
            MulChar.map_nonunit ψ fun hu => hcopd ((ZMod.isUnit_iff_coprime n d).mp hu)
          rw [hχ0, hψ0, sub_self, zero_mul, norm_zero, if_neg (fun h => hcopd h.2.1)]
    · have h0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
      rw [h0, Complex.ofReal_zero, mul_zero, norm_zero, if_neg (fun h => hpp h.2.2)]
  set S : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ∣ d)
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hx)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hsub : T ⊆ S.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)) := by
    intro n hn
    simp only [T, S, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc] at hn ⊢
    obtain ⟨hnle, hncopq, hcopd, hpp⟩ := hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hndvd
      exact hncopq (((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).pow_left k)
    have hnpd : ¬ p ∣ d := by
      intro hpd
      have hdiv : p ∣ (p ^ k).gcd d := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpd
      rw [hcopd.gcd_eq_one] at hdiv
      exact hp.not_dvd_one hdiv
    refine ⟨p, ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩, hnpd⟩, k, ⟨hkpos, ?_⟩, rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by omega)
  have hT_le : ∑ n ∈ T, Λ n ≤ (S.card : ℝ) * Real.log x := by
    calc ∑ n ∈ T, Λ n
        ≤ ∑ n ∈ S.biUnion (fun p => (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k)), Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ ∑ p ∈ S, ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n :=
          sum_biUnion_le_of_nonneg_local _ _ (fun n => Λ n) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ ≤ ∑ _p ∈ S, Real.log x := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          calc ∑ n ∈ (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).image (fun k => p ^ k), Λ n
              ≤ ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Λ (p ^ k) :=
                Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
            _ = ∑ _k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log (p : ℝ) := by
                refine Finset.sum_congr rfl fun k hk => ?_
                have hk0 : k ≠ 0 := by rw [Finset.mem_Icc] at hk; omega
                rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
                  ArithmeticFunction.vonMangoldt_apply_prime hpr]
            _ = ((Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card : ℝ) * Real.log (p : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Nat.log p ⌊x⌋₊ : ℝ) * Real.log (p : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
                have hcard : (Finset.Icc 1 (Nat.log p ⌊x⌋₊)).card ≤ Nat.log p ⌊x⌋₊ := by
                  rw [Nat.card_Icc]; omega
                exact_mod_cast hcard
            _ = Real.log ((p : ℝ) ^ Nat.log p ⌊x⌋₊) := (Real.log_pow (p : ℝ) _).symm
            _ ≤ Real.log x := by
                have hpow : p ^ Nat.log p ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self p (by omega)
                exact Real.log_le_log (pow_pos (Nat.cast_pos.mpr hpr.pos) _)
                  ((by exact_mod_cast hpow : ((p : ℝ) ^ Nat.log p ⌊x⌋₊) ≤ (⌊x⌋₊ : ℝ)).trans hNx)
      _ = (S.card : ℝ) * Real.log x := by rw [Finset.sum_const, nsmul_eq_mul]
  exact (hnorm_le.trans hT_le).trans
    (mul_le_mul_of_nonneg_right (card_primeFactors_not_dvd_le_log (NeZero.pos q) hd3 hdq)
      (Real.log_nonneg hx))

theorem totient_mul_ge_mul_totient (d m : ℕ) : d.totient * m.totient ≤ (d * m).totient :=
  Nat.totient_super_multiplicative d m

theorem div_totient_eq_sum_powerset {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) =
      ∑ s ∈ m.primeFactors.powerset, ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
  have htot := Nat.totient_eq_mul_prod_factors m
  have htotR : (m.totient : ℝ) = (m : ℝ) * ∏ p ∈ m.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    have hq := congrArg (Rat.cast : ℚ → ℝ) htot
    simpa [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one] using hq
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hprod_eq : (m : ℝ) / (m.totient : ℝ) = ∏ p ∈ m.primeFactors, (1 + ((p : ℝ) - 1)⁻¹) := by
    rw [htotR, div_mul_eq_div_div, div_self hm_pos.ne', one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    field_simp [(by linarith : (p : ℝ) ≠ 0), (by linarith : (p : ℝ) - 1 ≠ 0)]
    ring
  rw [hprod_eq, Finset.prod_one_add]

private lemma sum_inv_mul_sub_one_le_one (M : ℕ) :
    ∑ k ∈ Finset.Icc 2 M, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ ≤ 1 := by
  by_cases hM : M < 2
  · have : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]; norm_num
  · push Not at hM
    have hstrong : ∀ n : ℕ, 2 ≤ n →
        ∑ k ∈ Finset.Icc 2 n, ((k : ℝ) * ((k : ℝ) - 1))⁻¹ = 1 - (n : ℝ)⁻¹ := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        have h2 : Finset.Icc 2 2 = {2} := by ext x; simp
        rw [h2, Finset.sum_singleton]; norm_num
      | succ k hk ih =>
        have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        push_cast
        have hsub1 : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
        rw [hsub1]
        field_simp [hk_pos.ne', (by linarith : (k : ℝ) + 1 ≠ 0)]
        ring
    rw [hstrong M hM]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) M)]

theorem sum_inv_totient_le_log {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (m.totient : ℝ)⁻¹ ≤ 6 * Real.log (2 * (M : ℝ)) := by
  set P : Finset ℕ := (Finset.Icc 1 M).filter Nat.Prime
  set H : ℝ := ∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹
  have hH_le : H ≤ 2 * Real.log (2 * (M : ℝ)) := by
    have h1 := Stage5DirichletLZeroFree.harmonic_sum_le_log_add_one hM
    have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hlog2M : Real.log (2 * (M : ℝ)) = Real.log 2 + Real.log (M : ℝ) :=
      Real.log_mul (by norm_num) hM_pos.ne'
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogM_nn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    linarith
  have hstep1 :
      ∑ m ∈ Finset.Icc 1 M, (m.totient : ℝ)⁻¹ =
        ∑ m ∈ Finset.Icc 1 M,
          ∑ s ∈ P.powerset,
            if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_le : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hmR_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hexp := div_totient_eq_sum_powerset hm_pos
    have hinv : (m.totient : ℝ)⁻¹ = ((m : ℝ))⁻¹ * ((m : ℝ) / (m.totient : ℝ)) := by
      field_simp [hmR_pos.ne']
    rw [hinv, hexp, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext s
    simp only [Finset.mem_powerset, Finset.mem_filter, P]
    constructor
    · intro hs
      refine ⟨fun p hp => ?_, ?_⟩
      · have hmem := hs hp
        have hpr : p.Prime := Nat.prime_of_mem_primeFactors hmem
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.pos, (Nat.le_of_dvd hm_pos hpm).trans hm_le⟩, hpr⟩
      · exact (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans (Nat.prod_primeFactors_dvd m)
    · rintro ⟨hsP, hdvd⟩ p hp
      have hpr : p.Prime := (Finset.mem_filter.mp (hsP hp)).2
      have hpm : p ∣ m := (Finset.dvd_prod_of_mem _ hp).trans hdvd
      exact Nat.mem_primeFactors.mpr ⟨hpr, hpm, hm_pos.ne'⟩
  rw [hstep1, Finset.sum_comm]
  have hinner : ∀ s ∈ P.powerset,
      ∑ m ∈ Finset.Icc 1 M,
          (if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0) ≤
        H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro s hs
    set r : ℕ := ∏ p ∈ s, p
    have hr_pos : 0 < r := Finset.prod_pos fun p hp =>
      (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2.pos
    have hrR_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_pos
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    have hbij :
        ∑ m ∈ (Finset.Icc 1 M).filter (fun m => r ∣ m), ((m : ℝ))⁻¹ =
          ((r : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / r) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
        obtain ⟨⟨hm1, hmM⟩, ⟨k, hk⟩⟩ := hm
        have hk1 : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0, mul_zero] at hk
          omega
        rw [hk, Nat.mul_div_cancel_left _ hr_pos]
        exact ⟨hk1, (Nat.le_div_iff_mul_le hr_pos).mpr (by rw [mul_comm]; omega)⟩
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [Finset.mem_filter] at hm₁ hm₂
        have h1 : r * (m₁ / r) = m₁ := Nat.mul_div_cancel' hm₁.2
        have h2 : r * (m₂ / r) = m₂ := Nat.mul_div_cancel' hm₂.2
        rw [← h1, ← h2, h]
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨r * k, ?_, Nat.mul_div_cancel_left k hr_pos⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos hr_pos hk.1, ?_⟩, dvd_mul_right r k⟩
        exact (Nat.le_div_iff_mul_le hr_pos).mp hk.2 |> fun h => by rwa [mul_comm] at h
      · intro m hm
        simp only [Finset.mem_filter] at hm
        have h1 : (r : ℝ) * ((m / r : ℕ) : ℝ) = (m : ℝ) := by
          exact_mod_cast Nat.mul_div_cancel' hm.2
        rw [← h1, mul_inv]
    have hHsub : ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹ ≤ H := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self M r)
    have hprod_nn : 0 ≤ ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ :=
      Finset.prod_nonneg fun p hp => by
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
        exact inv_nonneg.mpr (by linarith)
    have hprod_merge :
        ((r : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ = ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
      have hr_cast : (r : ℝ) = ∏ p ∈ s, (p : ℝ) := by simp [r]
      rw [hr_cast, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => (mul_inv _ _).symm
    calc (∑ m ∈ (Finset.Icc 1 M).filter (fun m => r ∣ m), ((m : ℝ))⁻¹) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹
        = (((r : ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by
          rw [hbij]
      _ ≤ (((r : ℝ))⁻¹ * H) * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ := by gcongr
      _ = H * (((r : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹) := by ring
      _ = H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by rw [hprod_merge]
  have hprod_le3 : ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) ≤ 3 := by
    calc ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹)
        ≤ ∏ p ∈ P, Real.exp (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
          · have hpr : p.Prime := (Finset.mem_filter.mp hp).2
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
            have hnn : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := inv_nonneg.mpr (by nlinarith)
            linarith
          · linarith [Real.add_one_le_exp (((p : ℝ) * ((p : ℝ) - 1))⁻¹)]
      _ = Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑ k ∈ Finset.Icc 2 M, ((k : ℝ) * ((k : ℝ) - 1))⁻¹) := by
          apply Real.exp_le_exp.mpr
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k hk _ => ?_
          · intro p hp
            have hmem := Finset.mem_filter.mp hp
            exact Finset.mem_Icc.mpr ⟨hmem.2.two_le, (Finset.mem_Icc.mp hmem.1).2⟩
          · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
            exact inv_nonneg.mpr (by nlinarith)
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (sum_inv_mul_sub_one_le_one M)
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc ∑ s ∈ P.powerset,
          ∑ m ∈ Finset.Icc 1 M,
            (if (∏ p ∈ s, p) ∣ m then ((m : ℝ))⁻¹ * ∏ p ∈ s, ((p : ℝ) - 1)⁻¹ else 0)
      ≤ ∑ s ∈ P.powerset, H * ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.sum_le_sum hinner
    _ = H * ∑ s ∈ P.powerset, ∏ p ∈ s, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := (Finset.mul_sum _ _ _).symm
    _ = H * ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by rw [Finset.prod_one_add]
    _ ≤ (2 * Real.log (2 * (M : ℝ))) * 3 :=
        mul_le_mul hH_le hprod_le3 (Finset.prod_nonneg fun p hp => by
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
          have hnn : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := inv_nonneg.mpr (by nlinarith)
          linarith) (by
          have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          have : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by linarith)
          linarith)
    _ = 6 * Real.log (2 * (M : ℝ)) := by ring

theorem sum_inv_totient_dvd_le {d Q : ℕ} (hd : 1 ≤ d) (hdQ : d ≤ Q) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ ≤
      (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
  have hd_pos : 0 < d := hd
  have hM : 1 ≤ Q / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)
  have hphi_d_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd_pos)
  have hbij :
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ =
        ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹ := by
    refine Finset.sum_bij (fun q _ => q / d) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      obtain ⟨⟨hq1, hqQ⟩, ⟨m, hm⟩⟩ := hq
      have hm1 : 1 ≤ m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        rw [hm0, mul_zero] at hm
        omega
      rw [hm, Nat.mul_div_cancel_left _ hd_pos]
      exact ⟨hm1, (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; omega)⟩
    · intro q₁ hq₁ q₂ hq₂ h
      simp only [Finset.mem_filter] at hq₁ hq₂
      rw [← Nat.mul_div_cancel' hq₁.2, ← Nat.mul_div_cancel' hq₂.2, h]
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m hd_pos⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hd_pos hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd_pos).mp hm.2
      rwa [mul_comm] at this
    · intro q hq
      simp only [Finset.mem_filter] at hq
      rw [Nat.mul_div_cancel' hq.2]
  rw [hbij]
  have hstep :
      ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹ ≤
        (d.totient : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 (Q / d), (m.totient : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hphi_m_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm_pos)
    have hmul : (d.totient : ℝ) * (m.totient : ℝ) ≤ ((d * m).totient : ℝ) := by
      exact_mod_cast totient_mul_ge_mul_totient d m
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hphi_d_pos hphi_m_pos) hmul
  have hlog_le : Real.log (2 * ((Q / d : ℕ) : ℝ)) ≤ Real.log (2 * (Q : ℝ) / (d : ℝ)) := by
    have hdiv_le : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hpos : (0 : ℝ) < 2 * ((Q / d : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((Q / d : ℕ) : ℝ) := by exact_mod_cast hM
      linarith
    exact Real.log_le_log hpos (by linarith [show 2 * ((Q : ℝ) / (d : ℝ)) = 2 * (Q : ℝ) / (d : ℝ) by ring])
  calc ∑ m ∈ Finset.Icc 1 (Q / d), ((d * m).totient : ℝ)⁻¹
      ≤ (d.totient : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 (Q / d), (m.totient : ℝ)⁻¹ := hstep
    _ ≤ (d.totient : ℝ)⁻¹ * (6 * Real.log (2 * ((Q / d : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_inv_totient_le_log hM) (inv_nonneg.mpr hphi_d_pos.le)
    _ ≤ (d.totient : ℝ)⁻¹ * (6 * Real.log (2 * (Q : ℝ) / (d : ℝ))) := by
        gcongr
    _ = (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := by ring

end RHDirect.Stage8BarbanDavenport
end

noncomputable section

open Complex DirichletCharacter Finset Set Filter Topology RHDirect
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage11BombieriVinogradov

def psiAPMaxError (q : ℕ) (x : ℝ) : ℝ :=
  if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
      (fun a => |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)|)
  else 0

private lemma chebyshevPsiAP_mod (q a : ℕ) (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiAP q a x = Stage2DirichletAP.chebyshevPsiAP q (a % q) x := by
  unfold Stage2DirichletAP.chebyshevPsiAP
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff : n ≡ a [MOD q] ↔ n ≡ a % q [MOD q] := by
    simp [Nat.ModEq]
  by_cases h : n ≡ a [MOD q]
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem abs_chebyshevPsiAP_sub_le_psiAPMaxError {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    (x : ℝ) :
    |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ psiAPMaxError q x := by
  have hmem : a % q ∈ (Finset.range q).filter (fun b => Nat.Coprime b q) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hq), ?_⟩
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hcop.gcd_eq_one
  unfold psiAPMaxError
  rw [dif_pos ⟨a % q, hmem⟩, chebyshevPsiAP_mod q a x]
  exact Finset.le_sup' (f := fun b =>
    |Stage2DirichletAP.chebyshevPsiAP q b x - x / (q.totient : ℝ)|) hmem

theorem psiAPMaxError_le_of_forall {q : ℕ} {x M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a : ℕ, Nat.Coprime a q →
      |Stage2DirichletAP.chebyshevPsiAP q a x - x / (q.totient : ℝ)| ≤ M) :
    psiAPMaxError q x ≤ M := by
  unfold psiAPMaxError
  split_ifs with hne
  · refine Finset.sup'_le hne _ fun a ha => h a (Finset.mem_filter.mp ha).2
  · exact hM

open Classical in

private lemma psiAPMaxError_le_prim_divisors {q Q : ℕ} [NeZero q] (hqQ : q ≤ Q)
    {x : ℝ} (hx : 3 ≤ x) (hQx : (Q : ℝ) ≤ x) :
    psiAPMaxError q x ≤
      (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Real.log x) ^ 2 +
      (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
  have hq1 : 1 ≤ q := NeZero.pos q
  have hx1 : 1 ≤ x := by linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1)
  have hRHS_nn : 0 ≤
      (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Real.log x) ^ 2 +
      (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hsum_nn : 0 ≤ ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  refine psiAPMaxError_le_of_forall hRHS_nn fun a hcop => ?_
  rw [Stage2DirichletAP.chebyshevPsiAP_eq_principal_add_nonprincipal_re hcop x]
  have hsplit_eq :
      Stage2DirichletAP.chebyshevPsiCoprime q x / (q.totient : ℝ) +
          (q.totient : ℝ)⁻¹ *
            ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re -
          x / (q.totient : ℝ) =
      (q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x) +
      (q.totient : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re := by
    ring
  rw [hsplit_eq]
  
  have hlogq : Real.log (q : ℝ) ≤ Real.log x :=
    Real.log_le_log (Nat.cast_pos.mpr hq1) ((by exact_mod_cast hqQ : (q : ℝ) ≤ (Q : ℝ)).trans hQx)
  have hprinc : |Stage2DirichletAP.chebyshevPsiCoprime q x - x| ≤
      |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2 := by
    have hcop_bd := Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_le_log hq1 hx1
    have hcop_nn := (Stage2DirichletAP.chebyshevPsi_sub_chebyshevPsiCoprime_bounds hq1 hx1).1
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiff_le : RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x ≤
        2 * (Real.log x) ^ 2 := by
      have h1 : Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log x := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]; nlinarith
      calc RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x
          ≤ (Real.log (q : ℝ) / Real.log 2) * Real.log x := hcop_bd
        _ ≤ (2 * Real.log x) * Real.log x := mul_le_mul_of_nonneg_right h1 hlogx_nn
        _ = 2 * (Real.log x) ^ 2 := by ring
    have heq : Stage2DirichletAP.chebyshevPsiCoprime q x - x =
        (RHDirect.chebyshevPsi x - x) - (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) := by
      ring
    rw [heq]
    calc |(RHDirect.chebyshevPsi x - x) - (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x)|
        ≤ |RHDirect.chebyshevPsi x - x| + |RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x| :=
          abs_sub _ _
      _ = |RHDirect.chebyshevPsi x - x| + (RHDirect.chebyshevPsi x - Stage2DirichletAP.chebyshevPsiCoprime q x) := by
          rw [abs_of_nonneg hcop_nn]
      _ ≤ |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2 := by linarith
  
  have hnonprinc :
      |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
        (q.totient : ℝ) * (Real.log x) ^ 2 +
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hstep1 :
        |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
          ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            (‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ + (Real.log x) ^ 2) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun χ hχ => ?_)
      have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      have hre : |(starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
          ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
        calc |(starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re|
            ≤ ‖starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x‖ :=
              Complex.abs_re_le_norm _
          _ = ‖χ (a : ZMod q)‖ * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := by
              rw [norm_mul, Complex.norm_conj]
          _ ≤ 1 * ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ :=
              mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
          _ = ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ := one_mul _
      have htr := Stage8BarbanDavenport.norm_chebyshevPsiChar_sub_primitive_le hχne hx1
      have hdiff : ‖Stage2DirichletAP.chebyshevPsiChar χ x -
          Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤ (Real.log x) ^ 2 := by
        calc _ ≤ Real.log (q : ℝ) * Real.log x := htr
          _ ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_right hlogq hlogx_nn
          _ = (Real.log x) ^ 2 := by ring
      have htri : ‖Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
          ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ +
            ‖Stage2DirichletAP.chebyshevPsiChar χ x -
              Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ := by
        simpa using norm_add_le (Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
          (Stage2DirichletAP.chebyshevPsiChar χ x - Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x)
      linarith
    
    set target : Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
      ((Finset.Icc 3 Q).filter (fun d => d ∣ q)).sigma fun d =>
        Finset.univ.filter fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive
    let toPrim : DirichletCharacter ℂ q → (Σ d : ℕ, DirichletCharacter ℂ d) :=
      fun χ => ⟨χ.conductor, χ.primitiveCharacter⟩
    let induceFrom : (Σ d : ℕ, DirichletCharacter ℂ d) → DirichletCharacter ℂ q :=
      fun p => if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1
    have hind_eq : ∀ χ : DirichletCharacter ℂ q, induceFrom (toPrim χ) = χ := fun χ => by
      dsimp only [induceFrom, toPrim]
      rw [dif_pos χ.conductor_dvd_level, χ.changeLevel_primitiveCharacter]
    have hinj : Set.InjOn toPrim ((Finset.univ.erase (1 : DirichletCharacter ℂ q)) : Set (DirichletCharacter ℂ q)) := by
      intro χ₁ _ χ₂ _ h
      rw [← hind_eq χ₁, ← hind_eq χ₂, h]
    have hmaps : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), toPrim χ ∈ target := by
      intro χ hχ
      have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
      have hd3 : 3 ≤ χ.conductor := Stage8BarbanDavenport.three_le_conductor_of_ne_one hχne
      have hdq : χ.conductor ∣ q := χ.conductor_dvd_level
      have hdle : χ.conductor ≤ Q := (Nat.le_of_dvd hq1 hdq).trans hqQ
      simp only [target, toPrim, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_univ, true_and]
      exact ⟨⟨⟨hd3, hdle⟩, hdq⟩, χ.primitiveCharacter_isPrimitive⟩
    have hprim_sum :
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖Stage2DirichletAP.chebyshevPsiChar χ.primitiveCharacter x‖ ≤
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
      have hsig :
          ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ =
            ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := Finset.sum_sigma _ _ _
      rw [← hsig]
      calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ‖Stage2DirichletAP.chebyshevPsiChar (toPrim χ).2 x‖
          = ∑ p ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).image toPrim,
              ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ :=
            (Finset.sum_image (f := fun p : Σ d : ℕ, DirichletCharacter ℂ d =>
              ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖) hinj).symm
        _ ≤ ∑ p ∈ target, ‖Stage2DirichletAP.chebyshevPsiChar p.2 x‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
              fun _ _ _ => norm_nonneg _
    have hcard_le : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ (q.totient : ℝ) := by
      have htot : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have hnat : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
        calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card (Finset.erase_subset _ _)
          _ = q.totient := by rw [Finset.card_univ, htot]
      exact_mod_cast hnat
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hstep1
    have herr := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg (Real.log x))
    linarith
  
  have h1 : |(q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x) +
      (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| ≤
      (q.totient : ℝ)⁻¹ * |Stage2DirichletAP.chebyshevPsiCoprime q x - x| +
      (q.totient : ℝ)⁻¹ * |∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| := by
    calc _ ≤ |(q.totient : ℝ)⁻¹ * (Stage2DirichletAP.chebyshevPsiCoprime q x - x)| +
            |(q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              (starRingEnd ℂ (χ (a : ZMod q)) * Stage2DirichletAP.chebyshevPsiChar χ x).re| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hphi_pos)]
  have h2 := mul_le_mul_of_nonneg_left hprinc (inv_nonneg.mpr hphi_pos.le)
  have h3 := mul_le_mul_of_nonneg_left hnonprinc (inv_nonneg.mpr hphi_pos.le)
  have hcancel : (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * (Real.log x) ^ 2 +
      ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
        ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
          ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖) =
      (Real.log x) ^ 2 + (q.totient : ℝ)⁻¹ *
        ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
          ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
            ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hphi_pos.ne', one_mul]
  linarith

open Classical in

theorem sum_psiAPMaxError_le_prim_sum {Q : ℕ} (hQ : 1 ≤ Q) {x : ℝ} (hx : 3 ≤ x)
    (hQx : (Q : ℝ) ≤ x) :
    ∑ q ∈ Finset.Icc 1 Q, psiAPMaxError q x ≤
      12 * Real.log x * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
      (Q : ℝ) * (Real.log x) ^ 2 +
      12 * Real.log x *
        ∑ k ∈ Finset.Ico 2 Q,
          (1 / (Nat.totient (k + 1) : ℝ)) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
  have hlog2Q : Real.log (2 * (Q : ℝ)) ≤ 2 * Real.log x := by
    have hle : 2 * (Q : ℝ) ≤ x ^ 2 := by nlinarith
    calc Real.log (2 * (Q : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hsum_inv : ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ ≤ 12 * Real.log x := by
    calc ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹
        ≤ 6 * Real.log (2 * (Q : ℝ)) := Stage8BarbanDavenport.sum_inv_totient_le_log hQ
      _ ≤ 12 * Real.log x := by linarith
  have hper : ∀ q ∈ Finset.Icc 1 Q,
      psiAPMaxError q x ≤
        (q.totient : ℝ)⁻¹ * (|RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2) +
        (Real.log x) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    have : NeZero q := ⟨by omega⟩
    exact psiAPMaxError_le_prim_divisors hqQ hx hQx
  have hsum_all := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum_all
  
  have hswap :
      ∑ q ∈ Finset.Icc 1 Q, (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ =
        ∑ d ∈ Finset.Icc 3 Q,
          (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have h1 : ∀ q ∈ Finset.Icc 1 Q,
        (q.totient : ℝ)⁻¹ *
          ∑ d ∈ (Finset.Icc 3 Q).filter (fun d => d ∣ q),
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ =
        ∑ d ∈ Finset.Icc 3 Q,
          if d ∣ q then
            (q.totient : ℝ)⁻¹ *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖
          else 0 := by
      intro q _
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hd_bound :
      ∑ d ∈ Finset.Icc 3 Q,
          (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
            ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
              ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
        12 * Real.log x *
          ∑ k ∈ Finset.Ico 2 Q,
            (1 / (Nat.totient (k + 1) : ℝ)) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ (k + 1) => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
    have hle1 :
        ∑ d ∈ Finset.Icc 3 Q,
            (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ ≤
          ∑ d ∈ Finset.Icc 3 Q,
            (12 * Real.log x * (1 / (d.totient : ℝ))) *
              ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ d => ψ.IsPrimitive),
                ‖Stage2DirichletAP.chebyshevPsiChar ψ x‖ := by
      refine Finset.sum_le_sum fun d hd => ?_
      have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
      have hdQ : d ≤ Q := (Finset.mem_Icc.mp hd).2
      have hdiv := Stage8BarbanDavenport.sum_inv_totient_dvd_le hd1 hdQ
      have hlog_le : Real.log (2 * (Q : ℝ) / (d : ℝ)) ≤ 2 * Real.log x := by
        have h1 : 2 * (Q : ℝ) / (d : ℝ) ≤ 2 * (Q : ℝ) :=
          div_le_self (by positivity) (by exact_mod_cast hd1)
        exact (Real.log_le_log (by positivity) h1).trans hlog2Q
      have hcoef : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (q.totient : ℝ)⁻¹ ≤
          12 * Real.log x * (1 / (d.totient : ℝ)) := by
        have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
        calc _ ≤ (6 / (d.totient : ℝ)) * Real.log (2 * (Q : ℝ) / (d : ℝ)) := hdiv
          _ ≤ (6 / (d.totient : ℝ)) * (2 * Real.log x) :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ = 12 * Real.log x * (1 / (d.totient : ℝ)) := by ring
      exact mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    refine hle1.trans_eq ?_
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢; omega
    · intro k₁ _ k₂ _ h; omega
    · intro d hd; simp only [Finset.mem_Icc] at hd
      exact ⟨d - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; ring
  have h1_le := mul_le_mul_of_nonneg_right hsum_inv (by positivity : 0 ≤ |RHDirect.chebyshevPsi x - x| + 2 * (Real.log x) ^ 2)
  linarith

end RHDirect.Stage11BombieriVinogradov
end

open Finset Real RHDirect RHDirect.Stage2DirichletAP RHDirect.Stage11BombieriVinogradov
open scoped Classical ArithmeticFunction.vonMangoldt

theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_decreasing_R1_H1_R1.H3 := by
  classical
  intro x hx Q hQ hQx a ha
  have hsum := sum_psiAPMaxError_le_prim_sum hQ hx hQx
  have per (q : ℕ) (hq : q ∈ Icc 1 Q) :
      |∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q), log p -
        x/(q.totient:ℝ)| ≤ sqrt x*log x + psiAPMaxError q x := by
    have heq : (∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q), log p) =
        chebyshevThetaAP q (a q) x := by
      simp only [chebyshevThetaAP, sum_filter, Nat.ModEq]
      apply sum_congr rfl
      intro p hp
      by_cases h : p.Prime ∧ p%q=a q%q <;> simp [h]
    rw [heq]
    calc
      _ ≤ |chebyshevThetaAP q (a q) x - chebyshevPsiAP q (a q) x| +
          |chebyshevPsiAP q (a q) x - x/(q.totient:ℝ)| := abs_sub_le _ _ _
      _ ≤ _ := by
        apply add_le_add
        · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (chebyshevThetaAP_le_chebyshevPsiAP _ _ _))]
          exact chebyshevPsiAP_sub_chebyshevThetaAP_le _ _ (by linarith)
        · exact abs_chebyshevPsiAP_sub_le_psiAPMaxError (mem_Icc.mp hq).1 (ha q) x
  have sum := sum_le_sum per
  rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at sum
  have hnn : 0 ≤ (Q:ℝ)*(sqrt x*log x) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sqrt_nonneg _) (log_nonneg (by linarith)))
  dsimp [RHDirect.chebyshevPsi,chebyshevPsiChar] at hsum
  linarith only [sum,hsum,hnn]
