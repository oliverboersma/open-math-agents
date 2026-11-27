import FormalConjectures.ErdosProblems.«1141»
import Mathlib

/-!
# Pollack's lower bound for small prime quadratic residues

For a quadratic character, the nonnegative coefficients of ζ(s)L(s,χ)
at prime powers simplify to a square-only factor when χ(p) = -1.
A finite Euler product and Rankin's inequality show that too few small
residue primes would force a power saving for their summatory function.
At the quarter-power scale the character-sum asymptotic and Siegel's
lower bound rule out this saving. The principal character is handled
directly.

Adapted from the Pollack17 development imported by Boris Alexeev in plby/lean-proofs,
revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos1141. The enclosing formalization credits GPT-5.4 Pro
and Yuta Oriike. The mathematical result is
Paul Pollack, Bounds for the first several prime character nonresidues,
Theorem 1.3. This port uses the Formal Conjectures residue-prime set.
-/

open Filter Erdos1141
open scoped BigOperators Classical

namespace OMA.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1

/-- The character-sum asymptotic with a power saving above the Burgess threshold. -/
def H1 : Prop :=
  ∀ c : ℝ, 1 / 4 < c → ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
    ∀ [NeZero m] (χ : DirichletCharacter ℂ m), χ.IsQuadratic → χ ≠ 1 →
      |(∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, (χ.zetaMul n).re) -
        (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re| ≤ (m : ℝ) ^ (c - τ)

/-- Siegel's lower bound at one, uniformly in the modulus. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
    ∀ [NeZero m] (χ : DirichletCharacter ℂ m), χ ≠ 1 → χ.IsQuadratic →
      (m : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction χ 1).re

section

open scoped BigOperators ComplexOrder
open ArithmeticFunction

variable {m : ℕ}

theorem divisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    0 ≤ (χ.zetaMul n).re :=
  (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).1

theorem ofReal_divisorCoefficient (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    ((χ.zetaMul n).re : ℂ) = χ.zetaMul n := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).2

@[simp] theorem divisorCoefficient_zero (χ : DirichletCharacter ℂ m) :
    (χ.zetaMul 0).re = 0 := by
  simp

@[simp] theorem divisorCoefficient_one (χ : DirichletCharacter ℂ m) :
    (χ.zetaMul 1).re = 1 := by
  simp [χ.isMultiplicative_zetaMul.map_one]

theorem divisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {a b : ℕ} (hab : a.Coprime b) :
    (χ.zetaMul (a * b)).re = (χ.zetaMul a).re * (χ.zetaMul b).re := by
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_divisorCoefficient χ hχ, ofReal_divisorCoefficient χ hχ,
    ofReal_divisorCoefficient χ hχ]
  exact χ.isMultiplicative_zetaMul.map_mul_of_coprime hab

theorem zetaMul_prime_pow_eq_sum (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    χ.zetaMul (p ^ e) = ∑ i ∈ Finset.range (e + 1), χ (p : ZMod m) ^ i := by
  calc
    χ.zetaMul (p ^ e) =
        ∑ d ∈ (p ^ e).divisors, toArithmeticFunction (χ ·) d :=
      coe_zeta_mul_apply (f := toArithmeticFunction (χ ·))
    _ = _ := by
      simp only [toArithmeticFunction, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]

theorem divisorCoefficient_prime_pow_of_eq_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 1) (e : ℕ) :
    (χ.zetaMul (p ^ e)).re = e + 1 := by
  simp [zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_zero (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 0) (e : ℕ) :
    (χ.zetaMul (p ^ e)).re = 1 := by
  simp [zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1) (e : ℕ) :
    (χ.zetaMul (p ^ e)).re = if Even e then 1 else 0 := by
  rw [zetaMul_prime_pow_eq_sum χ hp, h, neg_one_geom_sum]
  by_cases he : Even e
  · simp [he, Nat.even_add_one]
  · simp [he, Nat.even_add_one]

theorem divisorCoefficient_prime_pow_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (χ.zetaMul (p ^ e)).re ≤ e + 1 := by
  rcases hχ (p : ZMod m) with h | h | h
  · rw [divisorCoefficient_prime_pow_of_eq_zero χ hp h]
    linarith [Nat.cast_nonneg (α := ℝ) e]
  · exact (divisorCoefficient_prime_pow_of_eq_one χ hp h e).le
  · rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) e]

theorem hasSum_succ_mul_geometric {u : ℝ} (hu : ‖u‖ < 1) :
    HasSum (fun e : ℕ => (e + 1 : ℝ) * u ^ e) ((1 - u)⁻¹ ^ 2) := by
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
    one_div, inv_pow] using hasSum_choose_mul_geometric_of_norm_lt_one 1 hu

theorem summable_divisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun e : ℕ => (χ.zetaMul (p ^ e)).re * u ^ e) := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact Summable.of_nonneg_of_le
    (fun e => mul_nonneg (divisorCoefficient_nonneg χ hχ _) (pow_nonneg hu0 _))
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (hasSum_succ_mul_geometric hu).summable

theorem local_divisorCoefficient_sum_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' e : ℕ, (χ.zetaMul (p ^ e)).re * u ^ e) ≤ (1 - u)⁻¹ ^ 2 := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact (Summable.tsum_le_tsum
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1)
    (hasSum_succ_mul_geometric hu).summable).trans_eq
      (hasSum_succ_mul_geometric hu).tsum_eq

theorem hasSum_divisorCoefficient_of_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun e : ℕ => (χ.zetaMul (p ^ e)).re * u ^ e)
      (1 - u ^ 2)⁻¹ := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  have hnu : ‖-u‖ < 1 := by simpa only [norm_neg] using hu
  have hs := ((hasSum_geometric_of_norm_lt_one hu).add
    (hasSum_geometric_of_norm_lt_one hnu)).div_const 2
  have hterm (e : ℕ) :
      (χ.zetaMul (p ^ e)).re * u ^ e = (u ^ e + (-u) ^ e) / 2 := by
    rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h, neg_pow,
      neg_one_pow_eq_ite]
    split_ifs <;> ring
  have hvalue : ((1 - u)⁻¹ + (1 - -u)⁻¹) / 2 = (1 - u ^ 2)⁻¹ := by
    have hminus : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
    have hplus : 1 + u ≠ 0 := ne_of_gt (by linarith)
    have hsquare : 1 - u ^ 2 ≠ 0 := by
      have : 0 < (1 - u) * (1 + u) := mul_pos (sub_pos.mpr hu1) (by linarith)
      nlinarith
    rw [sub_neg_eq_add]
    field_simp [hminus, hplus, hsquare]
    ring
  simpa only [← hterm, hvalue] using hs

end

section

open scoped BigOperators

variable {m : ℕ}

theorem weightedDivisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) (n : ℕ) :
    0 ≤ ((χ.zetaMul n).re * (n : ℝ) ^ (-s)) :=
  mul_nonneg (divisorCoefficient_nonneg χ hχ n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

@[simp] theorem weightedDivisorCoefficient_one (χ : DirichletCharacter ℂ m)
    (s : ℝ) : ((χ.zetaMul 1).re * (1 : ℝ) ^ (-s)) = 1 := by
  simp

theorem weightedDivisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (s : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    ((χ.zetaMul (a * b)).re * ((a * b : ℕ) : ℝ) ^ (-s)) =
      ((χ.zetaMul a).re * (a : ℝ) ^ (-s)) * ((χ.zetaMul b).re * (b : ℝ) ^ (-s)) := by
  simp only [divisorCoefficient_mul χ hχ hab,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

theorem weightedDivisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (s : ℝ) (p e : ℕ) :
    ((χ.zetaMul (p ^ e)).re * ((p ^ e : ℕ) : ℝ) ^ (-s)) =
      (χ.zetaMul (p ^ e)).re * ((p : ℝ) ^ (-s)) ^ e := by
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
    mul_comm (e : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]

theorem summable_norm_weightedDivisorCoefficient_prime_pow
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => ‖((χ.zetaMul (p ^ e)).re * ((p ^ e : ℕ) : ℝ) ^ (-s))‖) := by
  have hu0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu1 : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  apply (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1).congr
  intro e
  rw [Real.norm_eq_abs,
    abs_of_nonneg (weightedDivisorCoefficient_nonneg χ hχ s _),
    weightedDivisorCoefficient_prime_pow]

/-- Rankin's inequality with all local factors left explicit. -/
theorem sum_divisorCoefficient_le_finiteEulerProduct
    (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {s : ℝ} (hs : 0 < s) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤
      (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow,
          ∑' e : ℕ, (χ.zetaMul (p ^ e)).re * ((p : ℝ) ^ (-s)) ^ e := by
  classical
  let f (n : ℕ) : ℝ := (χ.zetaMul n).re * (n : ℝ) ^ (-s)
  have hf0 (n : ℕ) : 0 ≤ f n := weightedDivisorCoefficient_nonneg χ hχ s n
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f := f)
    (by simp [f])
    (fun {_ _} hab => weightedDivisorCoefficient_mul χ hχ s hab)
    (fun {_} hp => summable_norm_weightedDivisorCoefficient_prime_pow χ hχ hs hp)
    (X + 1)
  let terms : Finset (X + 1).smoothNumbers := (Finset.Icc 1 X).attach.map
    { toFun := fun n => ⟨n.1, Nat.mem_smoothNumbers_of_lt
        (Finset.mem_Icc.mp n.2).1 (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.2).2)⟩
      inj' := by
        intro a b h
        exact Subtype.ext (congrArg (fun z : (X + 1).smoothNumbers => (z : ℕ)) h) }
  have hterms : (∑ z ∈ terms, f z) = ∑ n ∈ Finset.Icc 1 X, f n := by
    simp only [terms, Finset.sum_map]
    change (∑ z ∈ (Finset.Icc 1 X).attach, f z.1) = _
    exact Finset.sum_attach _ _
  have hsum : (∑ n ∈ Finset.Icc 1 X, f n) ≤
      ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) := by
    rw [← hterms]
    exact (hEuler.2.summable.sum_le_tsum terms (fun n _ => hf0 n)).trans_eq
      hEuler.2.tsum_eq
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      (χ.zetaMul n).re ≤ (X : ℝ) ^ s * f n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpow : (n : ℝ) ^ s ≤ (X : ℝ) ^ s :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hs.le
    calc
      (χ.zetaMul n).re = (n : ℝ) ^ s * f n := by
        dsimp [f]
        rw [mul_left_comm, ← Real.rpow_add hn0]
        simp
      _ ≤ (X : ℝ) ^ s * f n := mul_le_mul_of_nonneg_right hpow (hf0 n)
  calc
    (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤
        ∑ n ∈ Finset.Icc 1 X, (X : ℝ) ^ s * f n :=
      Finset.sum_le_sum hpoint
    _ = (X : ℝ) ^ s * ∑ n ∈ Finset.Icc 1 X, f n := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ s *
        ∏ p ∈ (X + 1).primesBelow, ∑' e : ℕ, f (p ^ e) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by simp only [f, weightedDivisorCoefficient_prime_pow]

end

section

open scoped BigOperators

theorem sum_Icc_rpow_sub_one_le (K : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
      (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (δ - 1)) ≤
        ∑ n ∈ Finset.Icc 1 K, (K : ℝ) ^ δ * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [Real.rpow_sub_one hn0.ne', div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hδ)
        (inv_nonneg.mpr hn0.le)
    _ = (K : ℝ) ^ δ * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) ^ δ * (1 + Real.log (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_rpow_sub_one_le_card (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by
  classical
  by_cases hK : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hK
    simp [hEmpty, Real.zero_rpow hδ0.ne']
  have hKpos : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  let T := S.filter fun n => n ≤ S.card
  let U := S.filter fun n => ¬ n ≤ S.card
  have hsmall : (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) ≤
      (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (s := T)
      (t := Finset.Icc 1 S.card) ?_ ?_).trans (sum_Icc_rpow_sub_one_le _ hδ0.le)
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨hS n hn'.1, hn'.2⟩
    · intro n _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlarge : (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤ (S.card : ℝ) ^ δ := by
    calc
      (∑ n ∈ U, (n : ℝ) ^ (δ - 1)) ≤
          ∑ _n ∈ U, (S.card : ℝ) ^ (δ - 1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hKn : S.card ≤ n := by
          have := (Finset.mem_filter.mp hn).2
          omega
        exact Real.rpow_le_rpow_of_nonpos hKpos
          (by exact_mod_cast hKn) (sub_nonpos.mpr hδ1)
      _ = (U.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by simp
      _ ≤ (S.card : ℝ) * (S.card : ℝ) ^ (δ - 1) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hKpos.le _)
        exact_mod_cast Finset.card_filter_le S (fun n => ¬ n ≤ S.card)
      _ = (S.card : ℝ) ^ δ := by
        rw [Real.rpow_sub_one hKpos.ne']
        field_simp
  calc
    (∑ n ∈ S, (n : ℝ) ^ (δ - 1)) =
        (∑ n ∈ T, (n : ℝ) ^ (δ - 1)) +
          ∑ n ∈ U, (n : ℝ) ^ (δ - 1) := by
      exact (Finset.sum_filter_add_sum_filter_not S
        (fun n => n ≤ S.card) (fun n => (n : ℝ) ^ (δ - 1))).symm
    _ ≤ (S.card : ℝ) ^ δ * (1 + Real.log (S.card : ℝ)) +
        (S.card : ℝ) ^ δ := add_le_add hsmall hlarge
    _ = (S.card : ℝ) ^ δ * (2 + Real.log (S.card : ℝ)) := by ring

end

section

open scoped BigOperators

theorem eulerLogConstant_pos : 0 < (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

theorem inv_one_sub_le_exp_eulerLogConstant {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ))) :
    (1 - u)⁻¹ ≤ Real.exp ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u) := by
  let c : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - u := sub_pos.mpr (hu.trans_lt hc)
  have hcden : 0 < 1 - c := sub_pos.mpr hc
  have hlog : -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hden]
  have hid : (1 - u)⁻¹ - 1 = u * (1 - u)⁻¹ := by
    field_simp
    ring
  have hinv : (1 - u)⁻¹ ≤ (1 - c)⁻¹ :=
    (inv_le_inv₀ hden hcden).2 (sub_le_sub_left hu 1)
  have hexp : -Real.log (1 - u) ≤ (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u := by
    calc
      -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := hlog
      _ = u * (1 - u)⁻¹ := hid
      _ ≤ u * (1 - c)⁻¹ := mul_le_mul_of_nonneg_left hinv hu0
      _ = (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u := by simp [c, mul_comm]
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by rw [Real.exp_neg, Real.exp_log hden]
    _ ≤ Real.exp ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u) := Real.exp_le_exp.mpr hexp

theorem prime_neg_rpow_le_half_reference {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 / 2 ≤ s) :
    (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (neg_le_neg hs)
    _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)

theorem local_divisorCoefficient_sum_le_squareFactor
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 / 2 ≤ s) :
    (∑' e : ℕ, (χ.zetaMul (p ^ e)).re * ((p : ℝ) ^ (-s)) ^ e) ≤
      (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹ *
        Real.exp (if χ (p : ZMod m) ≠ -1 then
          2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * (p : ℝ) ^ (-s) else 0) := by
  let u : ℝ := (p : ℝ) ^ (-s)
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have huref : u ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := prime_neg_rpow_le_half_reference hp hs
  have hu1 : u < 1 := huref.trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hbase : 1 ≤ (1 - u ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ hden]
    nlinarith
  by_cases h : χ (p : ZMod m) = -1
  · simpa [h, u] using (hasSum_divisorCoefficient_of_neg_one χ hp h hu0 hu1).tsum_eq.le
  · rw [if_pos h]
    calc
      (∑' e : ℕ, (χ.zetaMul (p ^ e)).re * u ^ e) ≤ (1 - u)⁻¹ ^ 2 :=
        local_divisorCoefficient_sum_le χ hχ hp hu0 hu1
      _ ≤ Real.exp ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr hu1.le))
          (inv_one_sub_le_exp_eulerLogConstant hu0 huref) 2
      _ = Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ (1 - u ^ 2)⁻¹ * Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * u) :=
        le_mul_of_one_le_left (Real.exp_nonneg _) hbase

theorem squareEulerProduct_le_tsum (X : ℕ) {s : ℝ} (hs : 1 / 2 < s) :
    (∏ p ∈ (X + 1).primesBelow, (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(2 * s)) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-(2 * s))
      map_one' := by simp
      map_mul' := fun a b => by simp [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)] }
  have hf : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hlocal (p : ℕ) : ((p : ℝ) ^ (-s)) ^ 2 = f p := by
    dsimp [f]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  simp_rw [hlocal]
  rw [EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hf]
  exact tsum_comp_le_tsum_of_inj hf (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Subtype.val_injective : Function.Injective (fun n : (X + 1).smoothNumbers => (n : ℕ)))

theorem finiteEulerProduct_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∏ p ∈ (X + 1).primesBelow,
      ∑' e : ℕ, (χ.zetaMul (p ^ e)).re * ((p : ℝ) ^ (-s)) ^ e) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ *
          ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
            (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card)) := by
  classical
  let S := (X + 1).primesBelow
  let B : ℕ → ℝ := fun p => (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹
  let E : ℕ → ℝ := fun p => if χ (p : ZMod m) ≠ -1 then
    2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * (p : ℝ) ^ (-s) else 0
  have hprod :
      (∏ p ∈ S, ∑' e : ℕ, (χ.zetaMul (p ^ e)).re * ((p : ℝ) ^ (-s)) ^ e) ≤
        (∏ p ∈ S, B p) * Real.exp (∑ p ∈ S, E p) := by
    calc
      _ ≤ ∏ p ∈ S, B p * Real.exp (E p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact tsum_nonneg fun e =>
            mul_nonneg (divisorCoefficient_nonneg χ hχ _)
              (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
        · intro p hp
          exact local_divisorCoefficient_sum_le_squareFactor χ hχ
            (Nat.prime_of_mem_primesBelow hp) hs0.le
      _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]
  have hsum : (∑ p ∈ S, E p) ≤
      2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
        (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card) := by
    have hmass := sum_rpow_sub_one_le_card ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1))
      (fun p hp => (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1).pos)
      (sub_pos.mpr hs1) (by linarith : 1 - s ≤ 1)
    have hmass' : (∑ p ∈ (((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1), (p : ℝ) ^ (-s)) ≤
        ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
          (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card) := by
      simpa only [sub_sub_cancel_left] using hmass
    calc
      (∑ p ∈ S, E p) =
          2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * ∑ p ∈ (((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1), (p : ℝ) ^ (-s) := by
        simp only [Finset.sum_filter, E, S, Finset.mul_sum,
          mul_ite, mul_zero]
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hmass'
            (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  exact hprod.trans (mul_le_mul (squareEulerProduct_le_tsum X hs0)
    (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _)
    (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))

theorem sum_divisorCoefficient_le_sparse_bound
    {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (X : ℕ) {s : ℝ} (hs0 : 1 / 2 < s) (hs1 : s < 1) :
    (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤
      (X : ℝ) ^ s * (∑' n : ℕ, (n : ℝ) ^ (-(2 * s))) *
        Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ *
          ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
            (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card)) := by
  have h := mul_le_mul_of_nonneg_left
    (finiteEulerProduct_le_sparse_bound χ hχ X hs0 hs1)
    (Real.rpow_nonneg (Nat.cast_nonneg X) s)
  exact (sum_divisorCoefficient_le_finiteEulerProduct χ hχ
    (by linarith : 0 < s) X).trans (by simpa only [mul_assoc] using h)

end

section

open Filter
open scoped BigOperators

theorem eventually_const_mul_rpow_le {C d a b : ℝ} (hd : 0 < d) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ d * x ^ b := by
  have hlarge := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually
    (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hratio : C ≤ d * x ^ (b - a) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hx
  calc
    C * x ^ a ≤ (d * x ^ (b - a)) * x ^ a :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hx0.le _)
    _ = d * x ^ b := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

theorem sparse_cost_le_double_rpow (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
  by_cases hK : K = 0
  · subst K
    simp [Real.zero_rpow hδ.ne', Real.zero_rpow (by positivity : 2 * δ ≠ 0)]
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hK
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans_le hK1
  have hpow : 1 ≤ (K : ℝ) ^ δ := Real.one_le_rpow hK1 hδ.le
  have hlog : Real.log (K : ℝ) ≤ (K : ℝ) ^ δ * δ⁻¹ := by
    simpa only [div_eq_mul_inv] using Real.log_natCast_le_rpow_div K hδ
  calc
    (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
        (K : ℝ) ^ δ * ((2 + δ⁻¹) * (K : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK0.le _)
      nlinarith
    _ = (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := by
      rw [mul_left_comm, ← Real.rpow_add hK0]
      congr 2
      ring

theorem eventually_sparse_exponential_le_rpow {B δ η C : ℝ}
    (_hB : 0 < B) (hδ : 0 < δ) (hsmall : 2 * B * δ < 1)
    (hη : 0 < η) (hC : 0 ≤ C) :
    ∀ᶠ m : ℕ in atTop, ∀ K : ℕ,
      (K : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        Real.exp (C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ))) ≤ (m : ℝ) ^ η := by
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := C * (2 + δ⁻¹)) hη hsmall)
  filter_upwards [hbound, eventually_ge_atTop 2] with m hm hm2
  intro K hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hL0 : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hmass : (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
    calc
      (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
          (2 + δ⁻¹) * (K : ℝ) ^ (2 * δ) := sparse_cost_le_double_rpow K hδ
      _ ≤ (2 + δ⁻¹) * ((Real.log (m : ℝ)) ^ B) ^ (2 * δ) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg K) hK (by positivity))
        positivity
      _ = (2 + δ⁻¹) * (Real.log (m : ℝ)) ^ (2 * B * δ) := by
        rw [← Real.rpow_mul hL0.le]
        congr 2
        ring
  have hexponent : C * (K : ℝ) ^ δ * (2 + Real.log (K : ℝ)) ≤
      Real.log (m : ℝ) * η := by
    have hmassC := mul_le_mul_of_nonneg_left hmass hC
    simp only [Real.rpow_one] at hm
    nlinarith
  rw [Real.rpow_def_of_pos hm0]
  exact Real.exp_le_exp.mpr hexponent

/-- A polylogarithmic number of exceptional primes forces a fixed power
saving in the divisor-coefficient sum, uniformly over the character. -/
theorem eventually_sparse_divisor_sum {c B : ℝ} (hc : 0 < c) (hB : 0 < B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ → ∀ X : ℕ,
        (X : ℝ) ≤ (m : ℝ) ^ c →
        (((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card : ℝ) ≤ (Real.log (m : ℝ)) ^ B →
        (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤ (m : ℝ) ^ (c - ρ) := by
  let δ : ℝ := 1 / (4 * (B + 1))
  let s : ℝ := 1 - δ
  let η : ℝ := c * δ / 4
  let ρ : ℝ := c * δ / 2
  let Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 * s))
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 / 4 := by
    exact one_div_lt_one_div_of_lt (by norm_num) (by nlinarith : 4 < 4 * (B + 1))
  have hδid : 4 * (B + 1) * δ = 1 := by
    exact mul_one_div_cancel (by positivity : (4 : ℝ) * (B + 1) ≠ 0)
  have hsmall : 2 * B * δ < 1 := by nlinarith
  have hs0 : 1 / 2 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hspos : 0 < s := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp := eventually_sparse_exponential_le_rpow (C := 2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹)
    hB hδ0 hsmall hη
    (mul_nonneg (by norm_num) eulerLogConstant_pos.le)
  have hZ : ∀ᶠ m : ℕ in atTop, Z ≤ (m : ℝ) ^ η := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_const_mul_rpow_le (C := Z) (d := 1) (a := 0) (by norm_num) hη)
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hexp, hZ, eventually_ge_atTop 1] with m hmExp hmZ hm1
  intro χ hχ X hX hK
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hXpow : (X : ℝ) ^ s ≤ (m : ℝ) ^ (c * s) := by
    calc
      (X : ℝ) ^ s ≤ ((m : ℝ) ^ c) ^ s :=
        Real.rpow_le_rpow (Nat.cast_nonneg X) hX hspos.le
      _ = (m : ℝ) ^ (c * s) := (Real.rpow_mul hm0.le c s).symm
  have hExp := hmExp ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card hK
  have hExp' :
      Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
        (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card)) ≤ (m : ℝ) ^ η := by
    simpa only [s, sub_sub_cancel] using hExp
  calc
    (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤
        (X : ℝ) ^ s * Z *
          Real.exp (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ^ (1 - s) *
            (2 + Real.log ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card)) :=
      sum_divisorCoefficient_le_sparse_bound χ hχ X hs0 hs1
    _ ≤ (m : ℝ) ^ (c * s) * (m : ℝ) ^ η * (m : ℝ) ^ η :=
      mul_le_mul
        (mul_le_mul hXpow hmZ hZ0 (Real.rpow_nonneg hm0.le _)) hExp'
        (Real.exp_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hm0.le _))
    _ = (m : ℝ) ^ (c - ρ) := by
      rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
      congr 1
      dsimp [s, η, ρ]
      ring

end

section

open scoped BigOperators

theorem mem_residuePrimesUpTo_iff {m p : ℕ} {ε : ℝ}
    {χ : DirichletCharacter ℂ m} :
    p ∈ residuePrimesUpTo m χ ε ↔ p.Prime ∧
      (p : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (p : ZMod m) = 1 := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    apply Nat.lt_succ_of_le
    exact_mod_cast h.2.1.trans (Nat.le_ceil (residuePrimeUpperBound m ε))

theorem exceptionalPrimes_subset {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    (((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1) ⊆ m.primeFactors ∪ residuePrimesUpTo m χ ε := by
  classical
  intro p hp
  obtain ⟨hpS, hpne⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpS
  rcases hχ (p : ZMod m) with hzero | hone | hneg
  · apply Finset.mem_union_left
    have hnonunit := MulChar.apply_eq_zero_iff.mp hzero
    have hdiv : p ∣ m := by
      simpa only [ZMod.isUnit_iff_coprime, hprime.coprime_iff_not_dvd, not_not] using hnonunit
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hm⟩
  · apply Finset.mem_union_right
    exact mem_residuePrimesUpTo_iff.mpr ⟨hprime,
      (show (p : ℝ) ≤ X by exact_mod_cast Nat.lt_succ_iff.mp hpX).trans hX, hone⟩
  · exact (hpne hneg).elim

theorem exceptionalPrimes_card_le {m X : ℕ} {ε : ℝ}
    (hm : m ≠ 0) (χ : DirichletCharacter ℂ m) (hχ : MulChar.IsQuadratic χ)
    (hX : (X : ℝ) ≤ residuePrimeUpperBound m ε) :
    ((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card ≤ m.primeFactors.card + (residuePrimesUpTo m χ ε).card :=
  (Finset.card_le_card (exceptionalPrimes_subset hm χ hχ hX)).trans
    (Finset.card_union_le _ _)

theorem primeFactors_card_le_log {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  have hpow : 2 ^ m.primeFactors.card ≤ m := by
    calc
      2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hcast : (2 : ℝ) ^ m.primeFactors.card ≤ (m : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos (by norm_num) _) hcast
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

end

section

open Filter
open scoped BigOperators

theorem eventually_few_residue_primes_divisor_sum
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A →
        ∀ X : ℕ, (X : ℝ) ≤ residuePrimeUpperBound m ε →
          (∑ n ∈ Finset.Icc 1 X, (χ.zetaMul n).re) ≤
            (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) := by
  have hc : 0 < (1 / 4 : ℝ) + ε := by linarith
  have hB : 0 < A + 2 := by linarith
  obtain ⟨ρ, hρ, hsum⟩ := eventually_sparse_divisor_sum hc hB
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hram := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := (Real.log 2)⁻¹) (d := 1 / 2)
      (a := 1) (b := A + 2) (by norm_num) (by linarith))
  have hres := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
      (a := A) (b := A + 2) (by norm_num) (by linarith))
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hsum, hram, hres, eventually_ge_atTop 1] with m hmSum hmRam hmRes hm1
  intro χ hχ hcount X hX
  apply hmSum χ hχ X hX
  have hmpos : 0 < m := hm1
  have hcard : (((((X + 1).primesBelow).filter fun (p : ℕ) => χ (p : ZMod m) ≠ -1)).card : ℝ) ≤
      (m.primeFactors.card : ℝ) + ((residuePrimesUpTo m χ ε).card : ℝ) := by
    exact_mod_cast exceptionalPrimes_card_le hmpos.ne' χ hχ hX
  have hram' : Real.log (m : ℝ) / Real.log 2 ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [Real.rpow_one, div_eq_mul_inv, mul_comm] using hmRam
  have hres' : (Real.log (m : ℝ)) ^ A ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [one_mul] using hmRes
  linarith [primeFactors_card_le_log hmpos]

end

open scoped BigOperators

theorem divisorCoefficient_eq_sum {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) :
    (χ.zetaMul n).re = ∑ d ∈ n.divisors, (χ (d : ℕ)).re := by
  have heq : χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ℕ) := by
    change (ArithmeticFunction.zeta * toArithmeticFunction (χ ·)) n = _
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [heq, Complex.re_sum]

theorem eventually_floor_rpow_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ a / 2 ≤ (⌊(q : ℝ) ^ a⌋₊ : ℝ) ∧
        (⌊(q : ℝ) ^ a⌋₊ : ℝ) ≤ (q : ℝ) ^ a := by
  have hlarge := ((tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with q hq
  change 2 ≤ (q : ℝ) ^ a at hq
  refine ⟨?_, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)⟩
  have hfloor := Nat.lt_floor_add_one ((q : ℝ) ^ a)
  linarith

open Filter
open scoped BigOperators

theorem one_le_principal_divisorCoefficient {m n : ℕ} (hn : 0 < n) :
    1 ≤ ((1 : DirichletCharacter ℂ m).zetaMul n).re := by
  rw [divisorCoefficient_eq_sum]
  have hnonneg (d : ℕ) : 0 ≤ ((1 : DirichletCharacter ℂ m) (d : ℕ)).re := by
    by_cases hd : IsUnit (d : ZMod m)
    · rw [MulChar.one_apply hd, Complex.one_re]
      norm_num
    · rw [MulChar.map_nonunit _ hd, Complex.zero_re]
  have h := Finset.single_le_sum (fun d _ => hnonneg d)
    (show 1 ∈ n.divisors from Nat.one_mem_divisors.mpr hn.ne')
  simpa only [Nat.cast_one, map_one, Complex.one_re] using h

theorem principal_divisor_sum_lower (m X : ℕ) :
    (X : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, ((1 : DirichletCharacter ℂ m).zetaMul n).re := by
  calc
    _ = ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun n hn =>
      one_le_principal_divisorCoefficient (Finset.mem_Icc.mp hn).1

theorem eventually_divisor_sum_lower_bound (asymptotic : H1) (siegel : H2) {c δ : ℝ} (hc : 1 / 4 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic →
      (m : ℝ) ^ (c - δ) ≤ ∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, (χ.zetaMul n).re := by
  have hc0 : 0 < c := by linarith
  obtain ⟨τ, hτ, hcomp⟩ := asymptotic c hc
  let u : ℝ := min δ τ / 4
  have hu : 0 < u := by dsimp [u]; positivity
  have huδ : u < δ := by
    have h := min_le_left δ τ
    dsimp [u] at hu ⊢
    linarith
  have huτ : u < τ := by
    have h := min_le_right δ τ
    dsimp [u] at hu ⊢
    linarith
  have herr := eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - τ) (b := c - u) (by norm_num) (by linarith)
  have htarget := eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - δ) (b := c - u) (by norm_num) (by linarith)
  have hprincipal := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c - δ) (b := c) (by norm_num) (by linarith)
  filter_upwards [hcomp, siegel u hu,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually herr,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually htarget,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hprincipal, eventually_floor_rpow_bounds hc0, eventually_ge_atTop 1]
    with m hcomp hL herr htarget hprincipal hfloor hm1
  intro χ hχ
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have : NeZero m := ⟨by omega⟩
  by_cases hχ1 : χ = 1
  · rw [hχ1]
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hprincipal]
    exact (htarget'.trans hfloor.1).trans (principal_divisor_sum_lower m _)
  · have hLv := hL χ hχ1 hχ
    have hmain : (1 / 2 : ℝ) * (m : ℝ) ^ (c - u) ≤
        (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re := by
      calc
        _ = ((m : ℝ) ^ c / 2) * (m : ℝ) ^ (-u) := by
          rw [sub_eq_add_neg, Real.rpow_add hm0]
          ring
        _ ≤ _ := mul_le_mul hfloor.1 hLv (Real.rpow_nonneg hm0.le _) (Nat.cast_nonneg _)
    have herror := (abs_le.mp (hcomp χ hχ hχ1)).1
    have herr' : (m : ℝ) ^ (c - τ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using herr
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using htarget
    linarith only [hmain, herror, herr', htarget']

theorem main : H1 → H2 → type_of% @Erdos1141.erdos_1141.variants.pollack_1_3 := by
  intro asymptotic siegel ε A hε hA
  obtain ⟨ρ, hρ, hupper⟩ := eventually_few_residue_primes_divisor_sum ε A hε hA
  have hlower := eventually_divisor_sum_lower_bound asymptotic siegel
    (c := (1 / 4 : ℝ) + ε) (δ := ρ / 2) (by linarith) (half_pos hρ)
  have hresult : ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        Real.rpow (Real.log (m : ℝ)) A ≤ ((residuePrimesUpTo m χ ε).card : ℝ) := by
    filter_upwards [hupper, hlower, eventually_ge_atTop 2] with m hu hl hm
    intro χ hχ
    by_contra hnot
    have hcount : ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A :=
      (lt_of_not_ge hnot).le
    have hX : (⌊(m : ℝ) ^ ((1 / 4 : ℝ) + ε)⌋₊ : ℝ) ≤ residuePrimeUpperBound m ε :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum := (hl χ hχ).trans (hu χ hχ hcount _ hX)
    have hstrict : (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) <
        (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < m by omega)) (by linarith)
    exact (not_le_of_gt hstrict) hsum
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hresult
  exact ⟨m0, fun m hm => hm0 m hm.le⟩

end OMA.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1
