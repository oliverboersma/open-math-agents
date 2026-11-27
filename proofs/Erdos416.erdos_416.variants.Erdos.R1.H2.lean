import OMAReductions.R_Erdos416_erdos_416_variants_Erdos_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.SumPrimeReciprocals

-- Step Erdos416.erdos_416.variants.Erdos.R1.H2: hypothesis H2 of reduction Erdos416.erdos_416.variants.Erdos.R1
-- Credit: @koolkao

/-!
# Erdős's upper bound `V(x) ≤ x (log x)^(-1+ε)` (step H2 of Erdos416.erdos_416.variants.Erdos.R1)

Original proof (no sieve). Every totient `n = φ(m) ≤ x` either has `Ω(n) ≥ 100 log log x`
(rare, by Rankin's trick and the Euler product of `(3/2)^Ω(n)/n`), or its preimage `m` satisfies
`m ≤ (ω(m)+1) φ(m) ≤ (100 log log x + 2) x` and `∑_{p | m} t(p) < 100 log log x`, where
`t(p) = #{q ∈ S : p ≡ 1 (mod q)}` for a fixed finite set `S` of small primes (because
`∏_{p | m} (p - 1) ∣ φ(m)`). Rankin with `g(m) = ∏_{p | m} w^{-t(p)}`, a Halberstam–Richert
inequality (Dirichlet convolution with `Λ` and Chebyshev's `ψ(t) ≤ C t`) and an Euler product
bound the second class by `≪ y / log y · exp (2 ∑_{p ≤ y} w^{-t(p)} / p)`.
The key input `∑_{p ≤ y} w^{-t(p)}/p ≤ δ log log y + O(1)` comes from Dirichlet's theorem for the
fixed moduli `∏ T`, `T ⊆ S` (Mathlib's `LFunctionResidueClassAux`, two-sided on `(1, 2]`), by
inclusion–exclusion, plus a dyadic choice of `s = 1 + 2^{-j}`; the case `S = ∅` gives the
Mertens-type bound `∑_{p ≤ y} 1/p ≤ C log log y + C'`.

Reused: Mathlib only (Apache-2.0); `residueClass_tsum_eq` follows the proof of Mathlib's
`LSeries_residueClass_lower_bound`.
-/

/-! Part 1: analytic input. Residue-class L-series bounds (from Mathlib's Dirichlet theorem),
the inclusion–exclusion weight `G`, and the dyadic conversion to sums over primes up to `N`. -/

noncomputable section Part1

open Finset Real
open ArithmeticFunction hiding log

namespace LaneC416

section residue

open ArithmeticFunction.vonMangoldt Complex LSeries

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- (Mathlib's `LSeries_residueClass_lower_bound` proof, first half.) -/
lemma residueClass_tsum_eq (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  refine ofReal_injective ?_
  simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
    ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx,
    eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
    LSeries, term]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
  · rfl

/-- Two-sided version: the L-series of `Λ` on a residue class minus its polar part is bounded
on `(1, 2]`. -/
lemma residueClass_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → x ≤ 2 →
      |∑' n, residueClass a n / (n : ℝ) ^ x - (q.totient : ℝ)⁻¹ / (x - 1)| ≤ C := by
  have hc : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨C, fun x hx1 hx2 => ?_⟩
  rw [residueClass_tsum_eq ha hx1, add_sub_cancel_right]
  simpa [Real.norm_eq_abs] using hC x ⟨hx1.le, hx2⟩

end residue

lemma summable_vonMangoldt_rpow {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => Λ n / (n : ℝ) ^ x := by
  have h := (LSeriesSummable_vonMangoldt (s := (x : ℂ)) (by simpa using hx)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, abs_of_nonneg vonMangoldt_nonneg]

/-- indicator of `n ≡ 1 (mod d)` -/
def ind (d n : ℕ) : ℝ := if (n : ZMod d) = 1 then 1 else 0

/-- the weight `∏_{q ∈ S} (1 - c [n ≡ 1 mod q])` -/
def G (S : Finset ℕ) (c : ℝ) (n : ℕ) : ℝ := ∏ q ∈ S, (1 - c * ind q n)

lemma natCast_eq_one_iff_dvd (d n : ℕ) : (n : ZMod d) = 1 ↔ (d : ℤ) ∣ (n : ℤ) - 1 := by
  rw [show (1 : ZMod d) = ((1 : ℕ) : ZMod d) by simp, ZMod.natCast_eq_natCast_iff,
    Nat.ModEq.comm, Nat.modEq_iff_dvd]
  simp

lemma ind_prod {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) (n : ℕ) :
    ∏ q ∈ T, ind q n = ind (∏ q ∈ T, q) n := by
  unfold ind
  rw [Finset.prod_boole]
  congr 1
  apply propext
  simp only [natCast_eq_one_iff_dvd]
  constructor
  · intro h
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hT i hi) (hT j hj)).mpr hij)
    · exact h
  · intro h q hq
    exact dvd_trans (by rw [Nat.cast_prod]; exact Finset.dvd_prod_of_mem _ hq) h

lemma G_expand (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (c : ℝ) (n : ℕ) :
    G S c n = ∑ T ∈ S.powerset, (-c) ^ T.card * ind (∏ q ∈ T, q) n := by
  unfold G
  have : ∀ q ∈ S, 1 - c * ind q n = (-c * ind q n) + 1 := fun _ _ => by ring
  rw [Finset.prod_congr rfl this, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
    ind_prod (fun q hq => hS q (Finset.mem_powerset.mp hT hq))]

lemma totient_prod_primes {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) :
    ((∏ q ∈ T, q).totient : ℝ) = ∏ q ∈ T, ((q : ℝ) - 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hp ih =>
    have hpp := hT p (Finset.mem_insert_self p T)
    have hcop : Nat.Coprime p (∏ q ∈ T, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hpp (hT q (Finset.mem_insert_of_mem hq))).mpr (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop, Nat.cast_mul,
      ih (fun q hq => hT q (Finset.mem_insert_of_mem hq)), Nat.totient_prime hpp,
      Nat.cast_sub hpp.one_le, Nat.cast_one]

lemma main_coeff (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (c : ℝ) :
    ∑ T ∈ S.powerset, (-c) ^ T.card * ((∏ q ∈ T, q).totient : ℝ)⁻¹ =
      ∏ q ∈ S, (1 - c / ((q : ℝ) - 1)) := by
  have : ∀ q ∈ S, 1 - c / ((q : ℝ) - 1) = -c / ((q : ℝ) - 1) + 1 := fun _ _ => by ring
  rw [Finset.prod_congr rfl this, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_powerset.mp hT hq)
  rw [Finset.prod_const_one, mul_one, totient_prod_primes hT', Finset.prod_div_distrib,
    Finset.prod_const, div_eq_mul_inv]

lemma ind_nonneg (d n : ℕ) : 0 ≤ ind d n := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (d n : ℕ) : ind d n ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma G_nonneg {S : Finset ℕ} {c : ℝ} (hc1 : c ≤ 1) (n : ℕ) : 0 ≤ G S c n :=
  Finset.prod_nonneg fun q _ => by
    unfold ind; split_ifs <;> linarith

lemma G_le_one {S : Finset ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) : G S c n ≤ 1 :=
  Finset.prod_le_one (fun q _ => by unfold ind; split_ifs <;> linarith)
    (fun q _ => by unfold ind; split_ifs <;> linarith)

lemma summable_weighted {h : ℕ → ℝ} (h0 : ∀ n, 0 ≤ h n) (h1 : ∀ n, h n ≤ 1) {x : ℝ}
    (hx : 1 < x) : Summable fun n : ℕ => Λ n * h n / (n : ℝ) ^ x :=
  (summable_vonMangoldt_rpow hx).of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg vonMangoldt_nonneg (h0 n)) (by positivity))
    (fun n => div_le_div_of_nonneg_right
      (mul_le_of_le_one_right vonMangoldt_nonneg (h1 n)) (by positivity))

lemma F_bound (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 < x → x ≤ 2 →
      ∑' n, Λ n * G S c n / (n : ℝ) ^ x ≤ (∏ q ∈ S, (1 - c / ((q : ℝ) - 1))) / (x - 1) + C := by
  have hb : ∀ T ∈ S.powerset, ∃ C : ℝ, ∀ x : ℝ, 1 < x → x ≤ 2 →
      |∑' n, vonMangoldt.residueClass (1 : ZMod (∏ q ∈ T, q)) n / (n : ℝ) ^ x
        - ((∏ q ∈ T, q).totient : ℝ)⁻¹ / (x - 1)| ≤ C := by
    intro T hT
    have hT' : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_powerset.mp hT hq)
    have : NeZero (∏ q ∈ T, q) := ⟨Finset.prod_ne_zero_iff.mpr fun q hq => (hT' q hq).ne_zero⟩
    exact residueClass_bound isUnit_one
  choose! C hC using hb
  refine ⟨∑ T ∈ S.powerset, |C T|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun x hx1 hx2 => ?_⟩
  have hsum : ∀ T ∈ S.powerset, Summable fun n : ℕ =>
      (-c) ^ T.card * (vonMangoldt.residueClass (1 : ZMod (∏ q ∈ T, q)) n / (n : ℝ) ^ x) := by
    intro T _
    refine Summable.mul_left _ ?_
    exact (summable_vonMangoldt_rpow hx1).of_nonneg_of_le
      (fun n => div_nonneg (vonMangoldt.residueClass_nonneg _ n) (by positivity))
      (fun n => div_le_div_of_nonneg_right (vonMangoldt.residueClass_le _ n) (by positivity))
  have hrw : ∀ n : ℕ, Λ n * G S c n / (n : ℝ) ^ x = ∑ T ∈ S.powerset,
      (-c) ^ T.card * (vonMangoldt.residueClass (1 : ZMod (∏ q ∈ T, q)) n / (n : ℝ) ^ x) := by
    intro n
    rw [G_expand S hS c n, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq, ind]
    split_ifs <;> ring
  rw [tsum_congr hrw, Summable.tsum_finsetSum hsum]
  simp_rw [tsum_mul_left]
  have hle : ∀ T ∈ S.powerset,
      (-c) ^ T.card * ∑' n, vonMangoldt.residueClass (1 : ZMod (∏ q ∈ T, q)) n / (n : ℝ) ^ x ≤
      (-c) ^ T.card * ((∏ q ∈ T, q).totient : ℝ)⁻¹ / (x - 1) + |C T| := by
    intro T hT
    have h1 := hC T hT x hx1 hx2
    set X := ∑' n, vonMangoldt.residueClass (1 : ZMod (∏ q ∈ T, q)) n / (n : ℝ) ^ x
    set M := ((∏ q ∈ T, q).totient : ℝ)⁻¹ / (x - 1)
    have hk : |(-c) ^ T.card| ≤ 1 := by
      rw [abs_pow, abs_neg, abs_of_nonneg hc0]; exact pow_le_one₀ hc0 hc1
    have h2 : (-c) ^ T.card * (X - M) ≤ |C T| := by
      calc _ ≤ |(-c) ^ T.card * (X - M)| := le_abs_self _
        _ = |(-c) ^ T.card| * |X - M| := abs_mul _ _
        _ ≤ 1 * |C T| := mul_le_mul hk (h1.trans (le_abs_self _)) (abs_nonneg _) zero_le_one
        _ = |C T| := one_mul _
    have h3 : (-c) ^ T.card * M = (-c) ^ T.card * ((∏ q ∈ T, q).totient : ℝ)⁻¹ / (x - 1) :=
      (mul_div_assoc _ _ _).symm
    have h4 : (-c) ^ T.card * X = (-c) ^ T.card * M + (-c) ^ T.card * (X - M) := by ring
    linarith
  calc _ ≤ ∑ T ∈ S.powerset, ((-c) ^ T.card * ((∏ q ∈ T, q).totient : ℝ)⁻¹ / (x - 1) + |C T|) :=
        Finset.sum_le_sum hle
    _ = (∑ T ∈ S.powerset, (-c) ^ T.card * ((∏ q ∈ T, q).totient : ℝ)⁻¹) / (x - 1)
          + ∑ T ∈ S.powerset, |C T| := by rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = _ := by rw [main_coeff S hS c]

/-- Dyadic conversion: an `L`-series bound with pole `a/(s-1)` gives `∑_{p ≤ N} h p / p ≪ a log log N`. -/
lemma dyadic {h : ℕ → ℝ} (h0 : ∀ n, 0 ≤ h n) (h1 : ∀ n, h n ≤ 1) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hF : ∀ x : ℝ, 1 < x → x ≤ 2 → ∑' n, Λ n * h n / (n : ℝ) ^ x ≤ a / (x - 1) + b)
    {N : ℕ} (hN : 3 ≤ N) :
    ∑ p ∈ Nat.primesBelow (N + 1), h p / p ≤
      2 * exp 1 * (a * (logb 2 (log N) + 2) + 2 * b) := by
  set J := ⌈logb 2 (log N)⌉₊ with hJ
  have hlogN : 1 ≤ log N := by
    rw [le_log_iff_exp_le (by positivity)]
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [exp_one_lt_d9]
  have hlb : 0 ≤ logb 2 (log N) := logb_nonneg (by norm_num) hlogN
  set term : ℕ → ℕ → ℝ := fun p j =>
    ((2 : ℝ) ^ j)⁻¹ * (Λ p * h p / (p : ℝ) ^ (1 + ((2 : ℝ) ^ j)⁻¹)) with hterm_def
  have term_nonneg : ∀ p j, 0 ≤ term p j := fun p j =>
    mul_nonneg (by positivity) (div_nonneg (mul_nonneg vonMangoldt_nonneg (h0 p)) (by positivity))
  have key : ∀ p ∈ Nat.primesBelow (N + 1), h p / p ≤
      2 * exp 1 * ∑ j ∈ Finset.range (J + 1), term p j := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hpN : p ≤ N := Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hp).1
    set t := log p with ht_def
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpos : (0 : ℝ) < p := by linarith
    have ht : log 2 ≤ t := log_le_log (by norm_num) hp2
    have ht0 : 0 < t := lt_of_lt_of_le (log_pos (by norm_num)) ht
    set j := ⌈logb 2 t⌉₊ with hj_def
    have hj1 : t ≤ 2 ^ j := by
      calc t = (2 : ℝ) ^ logb 2 t := (rpow_logb (by norm_num) (by norm_num) ht0).symm
        _ ≤ (2 : ℝ) ^ (j : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
        _ = 2 ^ j := rpow_natCast 2 j
    have hj2 : (2 : ℝ) ^ j < 2 * t := by
      rcases le_or_gt (logb 2 t) 0 with hneg | hpos'
      · have : j = 0 := Nat.ceil_eq_zero.mpr hneg
        rw [this, pow_zero]
        have := Real.log_two_gt_d9
        linarith
      · have hlt : (j : ℝ) < logb 2 t + 1 := Nat.ceil_lt_add_one hpos'.le
        calc (2 : ℝ) ^ j = (2 : ℝ) ^ (j : ℝ) := (rpow_natCast 2 j).symm
          _ < (2 : ℝ) ^ (logb 2 t + 1) := rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
          _ = 2 * t := by
            rw [rpow_add (by norm_num), rpow_logb (by norm_num) (by norm_num) ht0, rpow_one]; ring
    have hjJ : j ≤ J := Nat.ceil_mono (logb_le_logb_of_le (by norm_num) ht0
      (log_le_log hpos (by exact_mod_cast hpN)))
    have hΛ : Λ p = t := vonMangoldt_apply_prime hpp
    have hq : 0 < (p : ℝ) ^ ((2 : ℝ) ^ j)⁻¹ := by positivity
    have e1 : (p : ℝ) ^ ((2 : ℝ) ^ j)⁻¹ ≤ exp 1 := by
      rw [rpow_def_of_pos hpos]
      apply exp_le_exp.mpr
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hj1
    have hA : 1 / 2 < t / 2 ^ j := by rw [lt_div_iff₀ (by positivity)]; linarith
    have hB : (1 / 2) / exp 1 ≤ (t / 2 ^ j) / (p : ℝ) ^ ((2 : ℝ) ^ j)⁻¹ :=
      div_le_div₀ (by positivity) hA.le hq e1
    have hhp : 0 ≤ h p / p := div_nonneg (h0 p) hpos.le
    have hterm : h p / p ≤ 2 * exp 1 * term p j := by
      calc h p / p = 2 * exp 1 * ((1 / 2) / exp 1) * (h p / p) := by field_simp
        _ ≤ 2 * exp 1 * ((t / 2 ^ j) / (p : ℝ) ^ ((2 : ℝ) ^ j)⁻¹) * (h p / p) := by gcongr
        _ = 2 * exp 1 * term p j := by
          simp only [hterm_def, hΛ]
          rw [rpow_add hpos, rpow_one]
          ring
    calc h p / p ≤ 2 * exp 1 * term p j := hterm
      _ ≤ 2 * exp 1 * ∑ j' ∈ Finset.range (J + 1), term p j' := by
        gcongr
        exact Finset.single_le_sum (f := fun j' => term p j') (fun j' _ => term_nonneg p j')
          (Finset.mem_range.mpr (by omega))
  have hinner : ∀ j : ℕ, ∑ p ∈ Nat.primesBelow (N + 1), Λ p * h p / (p : ℝ) ^ (1 + ((2 : ℝ) ^ j)⁻¹)
      ≤ a * 2 ^ j + b := by
    intro j
    have hx1 : 1 < 1 + ((2 : ℝ) ^ j)⁻¹ := by
      have : 0 < ((2 : ℝ) ^ j)⁻¹ := by positivity
      linarith
    have hx2 : 1 + ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
      have : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith
    calc _ ≤ ∑' n, Λ n * h n / (n : ℝ) ^ (1 + ((2 : ℝ) ^ j)⁻¹) :=
          Summable.sum_le_tsum _ (fun n _ => div_nonneg (mul_nonneg vonMangoldt_nonneg (h0 n))
            (by positivity)) (summable_weighted h0 h1 hx1)
      _ ≤ a / ((1 + ((2 : ℝ) ^ j)⁻¹) - 1) + b := hF _ hx1 hx2
      _ = a * 2 ^ j + b := by rw [add_sub_cancel_left, div_inv_eq_mul]
  have hJle : (J : ℝ) + 1 ≤ logb 2 (log N) + 2 := by
    have := Nat.ceil_lt_add_one hlb
    linarith
  calc ∑ p ∈ Nat.primesBelow (N + 1), h p / p
      ≤ ∑ p ∈ Nat.primesBelow (N + 1), 2 * exp 1 * ∑ j ∈ Finset.range (J + 1), term p j :=
        Finset.sum_le_sum key
    _ = 2 * exp 1 * ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j)⁻¹ *
          ∑ p ∈ Nat.primesBelow (N + 1), Λ p * h p / (p : ℝ) ^ (1 + ((2 : ℝ) ^ j)⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hterm_def, Finset.mul_sum]
    _ ≤ 2 * exp 1 * ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j)⁻¹ * (a * 2 ^ j + b) := by
        gcongr with j hj
        exact hinner j
    _ = 2 * exp 1 * ((J + 1) * a + b * ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ)) ^ j) := by
        congr 1
        rw [Finset.mul_sum]
        have : ∀ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j)⁻¹ * (a * 2 ^ j + b) =
            a + b * (1 / (2 : ℝ)) ^ j := by
          intro j _
          rw [one_div_pow, mul_add, ← mul_assoc, mul_comm _ a, mul_assoc,
            inv_mul_cancel₀ (by positivity), mul_one, mul_comm, one_div]
        rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * exp 1 * ((J + 1) * a + b * 2) := by
        gcongr
        exact sum_geometric_two_le _
    _ ≤ 2 * exp 1 * (a * (logb 2 (log N) + 2) + 2 * b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hJle ha]

lemma exists_S {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∏ q ∈ S, (1 - c / ((q : ℝ) - 1)) ≤ δ := by
  have hns := not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => Set.indicator_apply_nonneg
    (fun _ => by positivity))] at hns
  obtain ⟨M, hM⟩ := (hns.eventually_ge_atTop (-Real.log δ / c)).exists
  refine ⟨Nat.primesBelow M, fun q hq => (Nat.mem_primesBelow.mp hq).2, ?_⟩
  have hsum : ∑ i ∈ Finset.range M, Set.indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) i =
      ∑ q ∈ Nat.primesBelow M, (1 : ℝ) / q := by
    rw [Nat.primesBelow, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Set.indicator_apply]
  rw [hsum] at hM
  calc ∏ q ∈ Nat.primesBelow M, (1 - c / ((q : ℝ) - 1))
      ≤ ∏ q ∈ Nat.primesBelow M, Real.exp (-(c * ((1 : ℝ) / q))) := by
        apply Finset.prod_le_prod
        · intro q hq
          have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.mem_primesBelow.mp hq).2.two_le
          have : c / ((q : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
          linarith
        · intro q hq
          have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.mem_primesBelow.mp hq).2.two_le
          have h1 : c * ((1 : ℝ) / q) ≤ c / ((q : ℝ) - 1) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_left hc.le (by linarith) (by linarith)
          have h2 := Real.add_one_le_exp (-(c * ((1 : ℝ) / q)))
          linarith
    _ = Real.exp (-(c * ∑ q ∈ Nat.primesBelow M, (1 : ℝ) / q)) := by
        rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤ Real.exp (Real.log δ) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_iff₀ hc] at hM
        linarith
    _ = δ := Real.exp_log hδ

end LaneC416

end Part1


/-! Part 2: elementary arithmetic. Halberstam–Richert, Euler-product bounds, Rankin for `Ω`,
and totient facts. -/

noncomputable section Part2

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace LaneC416

/-! ### Halberstam–Richert -/

/-- `g` as an arithmetic function. -/
def gA (g : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else g n, by simp⟩

lemma gA_apply (g : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) : gA g n = g n := by
  simp [gA, hn]

lemma sum_g_log_le {g : ℕ → ℝ} (g0 : ∀ n, 0 ≤ g n)
    (gmono : ∀ a b, 0 < a → 0 < b → g (a * b) ≤ g a) (N : ℕ) :
    ∑ m ∈ Ioc 0 N, g m * Real.log m ≤
      (Real.log 4 + 4) * N * ∑ k ∈ Ioc 0 N, g k / k := by
  have hpt : ∀ m ∈ Ioc 0 N, g m * Real.log m ≤ (gA g * Λ) m := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_Ioc.mp hm).1.ne'
    rw [mul_apply, ← vonMangoldt_sum, Finset.mul_sum]
    rw [← Nat.sum_divisorsAntidiagonal' (fun a b => g m * Λ b)]
    apply Finset.sum_le_sum
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : 0 < x.1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hx'; exact hm0 hx'.1.symm)
    have h2 : 0 < x.2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hx'; exact hm0 hx'.1.symm)
    rw [gA_apply g h1.ne']
    apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
    rw [← hx'.1]
    exact gmono _ _ h1 h2
  calc ∑ m ∈ Ioc 0 N, g m * Real.log m ≤ ∑ m ∈ Ioc 0 N, (gA g * Λ) m := Finset.sum_le_sum hpt
    _ = ∑ k ∈ Ioc 0 N, gA g k * ∑ d ∈ Ioc 0 (N / k), Λ d := sum_Ioc_mul_eq_sum_sum _ _ _
    _ ≤ ∑ k ∈ Ioc 0 N, g k * ((Real.log 4 + 4) * N / k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 := (Finset.mem_Ioc.mp hk).1.ne'
      rw [gA_apply g hk0]
      apply mul_le_mul_of_nonneg_left _ (g0 k)
      have hpsi : ∑ d ∈ Ioc 0 (N / k), Λ d = Chebyshev.psi ((N / k : ℕ) : ℝ) := by
        rw [Chebyshev.psi, Nat.floor_natCast]
      rw [hpsi]
      calc Chebyshev.psi ((N / k : ℕ) : ℝ) ≤ (Real.log 4 + 4) * ((N / k : ℕ) : ℝ) :=
            Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
        _ ≤ (Real.log 4 + 4) * ((N : ℝ) / k) := by
            gcongr
            exact Nat.cast_div_le
        _ = (Real.log 4 + 4) * N / k := by ring
    _ = (Real.log 4 + 4) * N * ∑ k ∈ Ioc 0 N, g k / k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring

lemma HR {g : ℕ → ℝ} (g0 : ∀ n, 0 ≤ g n) (g1 : ∀ n, g n ≤ 1)
    (gmono : ∀ a b, 0 < a → 0 < b → g (a * b) ≤ g a) {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ Ioc 0 N, g m ≤
      Real.sqrt N + 2 * (Real.log 4 + 4) * N / Real.log N * ∑ k ∈ Ioc 0 N, g k / k := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hpt : ∀ m ∈ Ioc 0 N, g m ≤ (if (m : ℝ) ≤ Real.sqrt N then 1 else 0) +
      2 / Real.log N * (g m * Real.log m) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
    have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
    split_ifs with hs
    · have : 0 ≤ 2 / Real.log N * (g m * Real.log m) :=
        mul_nonneg (by positivity) (mul_nonneg (g0 m) hlm)
      linarith [g1 m]
    · rw [not_le] at hs
      have hsq : Real.log (Real.sqrt N) < Real.log m :=
        Real.log_lt_log (Real.sqrt_pos.mpr (by linarith)) hs
      rw [Real.log_sqrt (by linarith)] at hsq
      have : 1 ≤ 2 / Real.log N * Real.log m := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlogN]; linarith
      calc g m = g m * 1 := (mul_one _).symm
        _ ≤ g m * (2 / Real.log N * Real.log m) := mul_le_mul_of_nonneg_left this (g0 m)
        _ = 0 + 2 / Real.log N * (g m * Real.log m) := by ring
  have hcard : ∑ m ∈ Ioc 0 N, (if (m : ℝ) ≤ Real.sqrt N then (1 : ℝ) else 0) ≤ Real.sqrt N := by
    rw [Finset.sum_boole]
    have hsub : (Ioc 0 N).filter (fun m : ℕ => (m : ℝ) ≤ Real.sqrt N) ⊆ Ioc 0 ⌊Real.sqrt N⌋₊ := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_Ioc]
      exact ⟨hm.1.1, Nat.le_floor hm.2⟩
    calc (((Ioc 0 N).filter (fun m : ℕ => (m : ℝ) ≤ Real.sqrt N)).card : ℝ)
        ≤ ((Ioc 0 ⌊Real.sqrt N⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = ⌊Real.sqrt N⌋₊ := by simp
      _ ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
  calc ∑ m ∈ Ioc 0 N, g m
      ≤ ∑ m ∈ Ioc 0 N, ((if (m : ℝ) ≤ Real.sqrt N then 1 else 0) +
          2 / Real.log N * (g m * Real.log m)) := Finset.sum_le_sum hpt
    _ = ∑ m ∈ Ioc 0 N, (if (m : ℝ) ≤ Real.sqrt N then (1 : ℝ) else 0) +
          2 / Real.log N * ∑ m ∈ Ioc 0 N, g m * Real.log m := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.sqrt N + 2 / Real.log N * ((Real.log 4 + 4) * N * ∑ k ∈ Ioc 0 N, g k / k) := by
        gcongr
        exact sum_g_log_le g0 gmono N
    _ = _ := by ring

/-! ### Euler-product bounds -/

/-- `∑_{k ≤ N} (∏_{p | k} G p)/k ≤ exp (2 ∑_{p ≤ N} G p / p)`. -/
lemma euler_bound {G : ℕ → ℝ} (G0 : ∀ p, 0 ≤ G p) (G1 : ∀ p, G p ≤ 1) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (∏ p ∈ k.primeFactors, G p) / k ≤
      Real.exp (2 * ∑ p ∈ Nat.primesBelow (N + 1), G p / p) := by
  set f : ℕ → ℝ := fun k => (∏ p ∈ k.primeFactors, G p) / k with hf
  have f0 : ∀ k, 0 ≤ f k := fun k => div_nonneg (Finset.prod_nonneg fun p _ => G0 p) (by positivity)
  have hf1 : f 1 = 1 := by simp [hf]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hf]
    rw [Nat.Coprime.primeFactors_mul hmn, Finset.prod_union hmn.disjoint_primeFactors,
      Nat.cast_mul, mul_div_mul_comm]
  have hpow : ∀ {p : ℕ}, p.Prime → ∀ n : ℕ, f (p ^ (n + 1)) = G p / p * (1 / (p : ℝ)) ^ n := by
    intro p hp n
    simp only [hf]
    rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero n) hp, Finset.prod_singleton, Nat.cast_pow]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hg : Summable (fun n : ℕ => (1 / (p : ℝ)) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)
    refine hg.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    rw [Real.norm_of_nonneg (f0 _)]
    rcases n with _ | n
    · simp [hf1]
    · rw [hpow hp]
      have : G p / p ≤ 1 / p := div_le_div_of_nonneg_right (G1 p) (by positivity)
      calc G p / p * (1 / (p : ℝ)) ^ n ≤ 1 / p * (1 / (p : ℝ)) ^ n := by gcongr
        _ = (1 / (p : ℝ)) ^ (n + 1) := by ring
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum (N + 1)
  have hsub : ∀ k ∈ Ioc 0 N, k ∈ (N + 1).smoothNumbers := fun k hk =>
    Nat.mem_smoothNumbers_of_lt (Finset.mem_Ioc.mp hk).1 (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2)
  have h1 : ∑ k ∈ Ioc 0 N, f k ≤ ∏ p ∈ Nat.primesBelow (N + 1), ∑' n : ℕ, f (p ^ n) := by
    rw [← Finset.sum_subtype_of_mem f hsub]
    exact sum_le_hasSum _ (fun i _ => f0 i) hS
  have h2 : ∀ p ∈ Nat.primesBelow (N + 1), ∑' n : ℕ, f (p ^ n) ≤ Real.exp (2 * (G p / p)) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlt : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hs : Summable (fun n : ℕ => f (p ^ n)) := by
      have := hsum hpp
      exact this.of_norm
    rw [hs.tsum_eq_zero_add, pow_zero, hf1]
    simp_rw [hpow hpp]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hlt]
    have hinv : (1 - 1 / (p : ℝ))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num), le_sub_comm, one_div_le (by linarith)
        (by norm_num)]
      linarith
    have hGp : 0 ≤ G p / p := div_nonneg (G0 p) (by linarith)
    calc 1 + G p / p * (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + G p / p * 2 := by gcongr
      _ = 2 * (G p / p) + 1 := by ring
      _ ≤ Real.exp (2 * (G p / p)) := Real.add_one_le_exp _
  calc ∑ k ∈ Ioc 0 N, (∏ p ∈ k.primeFactors, G p) / k = ∑ k ∈ Ioc 0 N, f k := rfl
    _ ≤ ∏ p ∈ Nat.primesBelow (N + 1), ∑' n : ℕ, f (p ^ n) := h1
    _ ≤ ∏ p ∈ Nat.primesBelow (N + 1), Real.exp (2 * (G p / p)) :=
        Finset.prod_le_prod (fun p _ => tsum_nonneg fun n => f0 _) h2
    _ = Real.exp (2 * ∑ p ∈ Nat.primesBelow (N + 1), G p / p) := by
        rw [← Real.exp_sum, Finset.mul_sum]

/-- the completely multiplicative function `n ↦ (3/2)^Ω(n) / n` -/
def f32 : ℕ →* ℝ where
  toFun n := (3 / 2 : ℝ) ^ (Ω n) / n
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [cardFactors_mul hm hn, pow_add, Nat.cast_mul, mul_div_mul_comm]

lemma f32_apply (n : ℕ) : f32 n = (3 / 2 : ℝ) ^ (Ω n) / n := rfl

lemma one_sub_ge_exp (p : ℕ) (hp : p.Prime) :
    Real.exp (-(3 / p)) ≤ 1 - f32 p := by
  rw [f32_apply, cardFactors_apply_prime hp, pow_one]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rcases eq_or_ne p 2 with rfl | hp3
  · -- exp(-3/2) ≤ 1/4
    norm_num
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have h2 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
    have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith
  · have hp3' : (3 : ℝ) ≤ p := by
      have : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h | h
        · exact absurd h hp3
        · have := hp.two_le; obtain ⟨k, hk⟩ := h; omega
      exact_mod_cast this
    set t := (3 : ℝ) / p with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by linarith)]; exact hp3'
    have hexp : Real.exp (-t) ≤ 1 / (1 + t) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
    have : 1 / (1 + t) ≤ 1 - t / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have he : (3 / 2 : ℝ) / p = t / 2 := by rw [ht]; ring
    rw [he]
    linarith

lemma sum_f32_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (3 / 2 : ℝ) ^ (Ω n) / n ≤
      Real.exp (3 * ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / p) := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖f32 p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [f32_apply, cardFactors_apply_prime hp, pow_one, Real.norm_of_nonneg (by positivity),
      div_lt_one (by linarith)]
    linarith
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    hlt (N + 1)
  have hsub : ∀ k ∈ Icc 1 N, k ∈ (N + 1).smoothNumbers := fun k hk =>
    Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp hk).1 (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
  have h1 : ∑ k ∈ Icc 1 N, f32 k ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 - f32 p)⁻¹ := by
    rw [← Finset.sum_subtype_of_mem (fun k => f32 k) hsub]
    exact sum_le_hasSum _ (fun i _ => by rw [f32_apply]; positivity) hS
  calc ∑ n ∈ Icc 1 N, (3 / 2 : ℝ) ^ (Ω n) / n = ∑ k ∈ Icc 1 N, f32 k := rfl
    _ ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 - f32 p)⁻¹ := h1
    _ ≤ ∏ p ∈ Nat.primesBelow (N + 1), Real.exp (3 / p) := by
        apply Finset.prod_le_prod
        · intro p hp
          have := one_sub_ge_exp p (Nat.mem_primesBelow.mp hp).2
          exact inv_nonneg.mpr ((Real.exp_pos _).le.trans this)
        · intro p hp
          have := one_sub_ge_exp p (Nat.mem_primesBelow.mp hp).2
          calc (1 - f32 p)⁻¹ ≤ (Real.exp (-(3 / p)))⁻¹ := inv_anti₀ (Real.exp_pos _) this
            _ = Real.exp (3 / p) := by rw [Real.exp_neg, inv_inv]
    _ = Real.exp (3 * ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / p) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

/-- Rankin: few `n ≤ N` have `Ω n ≥ K`. -/
lemma card_Omega_large (N : ℕ) (K : ℝ) :
    (((Icc 1 N).filter (fun n => K ≤ (Ω n : ℝ))).card : ℝ) ≤
      N / (3 / 2 : ℝ) ^ K * Real.exp (3 * ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / p) := by
  have hK : 0 < (3 / 2 : ℝ) ^ K := by positivity
  calc (((Icc 1 N).filter (fun n => K ≤ (Ω n : ℝ))).card : ℝ)
      = ∑ n ∈ (Icc 1 N).filter (fun n => K ≤ (Ω n : ℝ)), (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => K ≤ (Ω n : ℝ)), (3 / 2 : ℝ) ^ (Ω n) / (3 / 2 : ℝ) ^ K := by
        apply Finset.sum_le_sum
        intro n hn
        rw [le_div_iff₀ hK, one_mul, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ Icc 1 N, (3 / 2 : ℝ) ^ (Ω n) / (3 / 2 : ℝ) ^ K :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Icc 1 N, N / (3 / 2 : ℝ) ^ K * ((3 / 2 : ℝ) ^ (Ω n) / n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        rw [div_mul_div_comm, mul_comm (N : ℝ), ← div_mul_div_comm]
        rw [le_mul_iff_one_le_right (by positivity), one_le_div (by linarith)]
        exact hnN
    _ = N / (3 / 2 : ℝ) ^ K * ∑ n ∈ Icc 1 N, (3 / 2 : ℝ) ^ (Ω n) / n := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr; exact sum_f32_le N

/-! ### Totient facts -/

lemma prod_sub_one_dvd_totient (m : ℕ) : ∏ p ∈ m.primeFactors, (p - 1) ∣ m.totient := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [Nat.totient_eq_prod_factorization hm, Finsupp.prod, Nat.support_factorization]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Dvd.intro_left _ rfl

lemma cardFactors_prod {s : Finset ℕ} {f : ℕ → ℕ} (hf : ∀ i ∈ s, f i ≠ 0) :
    Ω (∏ i ∈ s, f i) = ∑ i ∈ s, Ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, cardFactors_mul (hf a (mem_insert_self a s))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma cardFactors_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : Ω a ≤ Ω b := by
  obtain ⟨c, rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hb
  have hc : c ≠ 0 := right_ne_zero_of_mul hb
  rw [cardFactors_mul ha hc]
  omega

lemma sum_cardFactors_le (m : ℕ) (hm : m ≠ 0) :
    ∑ p ∈ m.primeFactors, Ω (p - 1) ≤ Ω m.totient := by
  rw [← cardFactors_prod (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)]
  exact cardFactors_le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
    (prod_sub_one_dvd_totient m)

lemma card_primeFactors_le (m : ℕ) :
    m.primeFactors.card ≤ 1 + ∑ p ∈ m.primeFactors, Ω (p - 1) := by
  classical
  have h : ∀ p ∈ m.primeFactors.erase 2, 1 ≤ Ω (p - 1) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
    have h3 : 3 ≤ p := by have := hp'.two_le; omega
    have : p - 1 ≠ 1 := by omega
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [cardFactors_eq_zero_iff_eq_zero_or_one] at h0
    omega
  calc m.primeFactors.card ≤ 1 + (m.primeFactors.erase 2).card := by
        have := Finset.pred_card_le_card_erase (s := m.primeFactors) (a := 2)
        omega
    _ ≤ 1 + ∑ p ∈ m.primeFactors.erase 2, Ω (p - 1) := by
        have := Finset.card_nsmul_le_sum _ _ 1 h
        simp at this
        omega
    _ ≤ 1 + ∑ p ∈ m.primeFactors, Ω (p - 1) := by
        have := Finset.sum_le_sum_of_subset (f := fun p => Ω (p - 1))
          (Finset.erase_subset 2 m.primeFactors)
        omega

lemma prod_le_card_mul_prod {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    ∏ p ∈ P, p ≤ (P.card + 1) * ∏ p ∈ P, (p - 1) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert M P hlt ih =>
    have hM : M ∉ P := fun h => lt_irrefl M (hlt M h)
    have hP' : ∀ p ∈ P, 2 ≤ p := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hM2 : 2 ≤ M := hP M (Finset.mem_insert_self M P)
    have hcard : P.card + 2 ≤ M := by
      have hsub : P ⊆ Finset.Ico 2 M := fun p hp =>
        Finset.mem_Ico.mpr ⟨hP' p hp, hlt p hp⟩
      have := Finset.card_le_card hsub
      simp at this
      omega
    rw [Finset.prod_insert hM, Finset.prod_insert hM, Finset.card_insert_of_notMem hM]
    have ih' := ih hP'
    set A := ∏ p ∈ P, p
    set B := ∏ p ∈ P, (p - 1)
    calc M * A ≤ M * ((P.card + 1) * B) := Nat.mul_le_mul_left _ ih'
      _ ≤ (P.card + 1 + 1) * ((M - 1) * B) := by
        have : M * (P.card + 1) ≤ (P.card + 1 + 1) * (M - 1) := by
          zify [show 1 ≤ M by omega]
          push_cast
          nlinarith
        calc M * ((P.card + 1) * B) = (M * (P.card + 1)) * B := by ring
          _ ≤ ((P.card + 1 + 1) * (M - 1)) * B := Nat.mul_le_mul_right _ this
          _ = _ := by ring

lemma le_card_mul_totient (m : ℕ) : m ≤ (m.primeFactors.card + 1) * m.totient := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hkey := Nat.totient_mul_prod_primeFactors m
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) := Finset.prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have h2 := prod_le_card_mul_prod (P := m.primeFactors)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have : m * ∏ p ∈ m.primeFactors, (p - 1) ≤
      ((m.primeFactors.card + 1) * m.totient) * ∏ p ∈ m.primeFactors, (p - 1) := by
    rw [← hkey]
    calc m.totient * ∏ p ∈ m.primeFactors, p ≤
          m.totient * ((m.primeFactors.card + 1) * ∏ p ∈ m.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end LaneC416

end Part2


/-! Part 3: counting totients and the final asymptotic assembly. -/

noncomputable section Part3

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Omega

namespace LaneC416

/-- number of `q ∈ S` with `n ≡ 1 (mod q)` -/
def tcount (S : Finset ℕ) (n : ℕ) : ℕ := (S.filter fun q => (n : ZMod q) = 1).card

lemma G_eq_pow (S : Finset ℕ) (w : ℝ) (n : ℕ) : G S (1 - w⁻¹) n = w⁻¹ ^ tcount S n := by
  unfold G tcount
  have : ∀ q ∈ S, 1 - (1 - w⁻¹) * ind q n = if (n : ZMod q) = 1 then w⁻¹ else 1 := by
    intro q _
    unfold ind
    split_ifs <;> ring
  rw [Finset.prod_congr rfl this, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]

lemma tcount_le {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime) :
    tcount S p ≤ Ω (p - 1) := by
  unfold tcount
  calc _ ≤ (p - 1).primeFactors.card := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_filter] at hq
        have hq' := hS q hq.1
        rw [Nat.mem_primeFactors]
        refine ⟨hq', ?_, by have := hp.two_le; omega⟩
        have h := (natCast_eq_one_iff_dvd q p).mp hq.2
        have h1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
          have := hp.one_le; push_cast [this]; ring
        rw [← h1] at h
        exact Int.natCast_dvd_natCast.mp h
    _ ≤ Ω (p - 1) := by
        rw [cardFactors_apply, Nat.primeFactors]
        exact List.toFinset_card_le _

lemma prod_pf_mono {G : ℕ → ℝ} (G0 : ∀ p, 0 ≤ G p) (G1 : ∀ p, G p ≤ 1) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    ∏ p ∈ (a * b).primeFactors, G p ≤ ∏ p ∈ a.primeFactors, G p := by
  have hsub : a.primeFactors ⊆ (a * b).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_right a b) (Nat.mul_pos ha hb).ne'
  rw [← Finset.prod_sdiff hsub]
  apply mul_le_of_le_one_left (Finset.prod_nonneg fun p _ => G0 p)
  exact Finset.prod_le_one (fun p _ => G0 p) (fun p _ => G1 p)

/-- The totient values `≤ N` split into those with many prime factors and those whose preimage
`m` lies in the set `B`. -/
lemma card_totients_le (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {K : ℝ} {N Y : ℕ}
    (hY : (K + 2) * N ≤ Y) [DecidablePred (fun n : ℕ => ∃ m : ℕ, m.totient = n)] :
    ((Icc 1 N).filter (fun n => ∃ m : ℕ, m.totient = n)).card ≤
      ((Icc 1 N).filter (fun n => K ≤ (Ω n : ℝ))).card +
      ((Ioc 0 Y).filter (fun m => ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) < K)).card := by
  classical
  set s := (Icc 1 N).filter (fun n => ∃ m : ℕ, m.totient = n)
  rw [← Finset.card_filter_add_card_filter_not (s := s) (p := fun n => K ≤ (Ω n : ℝ))]
  apply add_le_add
  · apply Finset.card_le_card
    intro n hn
    simp only [s, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.2⟩
  · let f : ℕ → ℕ := fun n => if h : ∃ m : ℕ, m.totient = n then h.choose else 0
    have hf : ∀ n ∈ s, (f n).totient = n := by
      intro n hn
      have h : ∃ m : ℕ, m.totient = n := (Finset.mem_filter.mp hn).2
      simp only [f, dif_pos h]
      exact h.choose_spec
    apply Finset.card_le_card_of_injOn f
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hns := hn'.1
      have hΩ : (Ω n : ℝ) < K := not_le.mp hn'.2
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hns).1).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hns).1).2
      set m := f n
      have hm : m.totient = n := hf n hns
      have hm0 : m ≠ 0 := by
        intro h; rw [h, Nat.totient_zero] at hm; omega
      have h1 := sum_cardFactors_le m hm0
      rw [hm] at h1
      have h2 := card_primeFactors_le m
      have h3 := le_card_mul_totient m
      rw [hm] at h3
      have h4 : ∑ p ∈ m.primeFactors, tcount S p ≤ ∑ p ∈ m.primeFactors, Ω (p - 1) :=
        Finset.sum_le_sum fun p hp => tcount_le hS (Nat.prime_of_mem_primeFactors hp)
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc]
      refine ⟨⟨Nat.pos_of_ne_zero hm0, ?_⟩, ?_⟩
      · have : (m : ℝ) ≤ Y := by
          have e1 : (m : ℝ) ≤ ((m.primeFactors.card : ℝ) + 1) * n := by exact_mod_cast h3
          have e2 : (m.primeFactors.card : ℝ) ≤ 1 + Ω n := by exact_mod_cast h2.trans (by omega)
          have e3 : (n : ℝ) ≤ N := by exact_mod_cast hnN
          have e4 : (0 : ℝ) ≤ n := by positivity
          calc (m : ℝ) ≤ ((m.primeFactors.card : ℝ) + 1) * n := e1
            _ ≤ (K + 2) * n := mul_le_mul_of_nonneg_right (by linarith) e4
            _ ≤ (K + 2) * N := by
                apply mul_le_mul_of_nonneg_left e3
                have : (0 : ℝ) ≤ Ω n := by positivity
                linarith
            _ ≤ Y := hY
        exact_mod_cast this
      · have h5 : ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) ≤ (Ω n : ℝ) := by
          exact_mod_cast h4.trans h1
        exact lt_of_le_of_lt h5 hΩ
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).1
      have hb' := (Finset.mem_filter.mp hb).1
      rw [← hf a ha', ← hf b hb']
      rw [hab]

lemma core (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {w : ℝ} (hw : 1 < w) {K : ℝ}
    {x : ℝ} (hx : 3 ≤ x) {Y : ℕ} (hY : (K + 2) * ⌊x⌋₊ ≤ Y) (hY2 : 2 ≤ Y) :
    Erdos416.V x ≤ ⌊x⌋₊ / (3 / 2 : ℝ) ^ K *
        Real.exp (3 * ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p)
      + w ^ K * (Real.sqrt Y + 2 * (Real.log 4 + 4) * Y / Real.log Y *
          Real.exp (2 * ∑ p ∈ Nat.primesBelow (Y + 1), G S (1 - w⁻¹) p / p)) := by
  classical
  have hw0 : 0 < w := by linarith
  have hc0 : 0 ≤ 1 - w⁻¹ := by
    have : w⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw.le
    linarith
  have hc1 : 1 - w⁻¹ ≤ 1 := by have : 0 ≤ w⁻¹ := by positivity
                               linarith
  set G' : ℕ → ℝ := G S (1 - w⁻¹)
  have G0 : ∀ p, 0 ≤ G' p := fun p => G_nonneg hc1 p
  have G1 : ∀ p, G' p ≤ 1 := fun p => G_le_one hc0 hc1 p
  set g : ℕ → ℝ := fun m => ∏ p ∈ m.primeFactors, G' p
  have g0 : ∀ m, 0 ≤ g m := fun m => Finset.prod_nonneg fun p _ => G0 p
  have g1 : ∀ m, g m ≤ 1 := fun m => Finset.prod_le_one (fun p _ => G0 p) (fun p _ => G1 p)
  have gmono : ∀ a b, 0 < a → 0 < b → g (a * b) ≤ g a := fun a b ha hb =>
    prod_pf_mono G0 G1 a b ha hb
  have hV : Erdos416.V x ≤ (((Icc 1 ⌊x⌋₊).filter (fun n => K ≤ (Ω n : ℝ))).card : ℝ) +
      ((Ioc 0 Y).filter (fun m => ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) < K)).card := by
    unfold Erdos416.V
    exact_mod_cast card_totients_le S hS hY
  have hB : (((Ioc 0 Y).filter
      (fun m => ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) < K)).card : ℝ) ≤
      w ^ K * ∑ m ∈ Ioc 0 Y, g m := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    calc ∑ m ∈ (Ioc 0 Y).filter
          (fun m => ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) < K), (1 : ℝ)
        ≤ ∑ m ∈ (Ioc 0 Y).filter
          (fun m => ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ) < K), w ^ K * g m := by
          apply Finset.sum_le_sum
          intro m hm
          have hT := (Finset.mem_filter.mp hm).2
          have hg : g m = (w ^ ((∑ p ∈ m.primeFactors, tcount S p : ℕ) : ℝ))⁻¹ := by
            simp only [g, G']
            simp_rw [G_eq_pow]
            rw [Finset.prod_pow_eq_pow_sum, inv_pow, Real.rpow_natCast]
          rw [hg, ← Real.rpow_neg hw0.le, ← Real.rpow_add hw0]
          exact Real.one_le_rpow hw.le (by linarith)
      _ ≤ ∑ m ∈ Ioc 0 Y, w ^ K * g m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun m _ _ => mul_nonneg (by positivity) (g0 m))
  have hHR := HR g0 g1 gmono hY2
  have hE := euler_bound G0 G1 Y
  have hA := card_Omega_large ⌊x⌋₊ K
  have hY0 : (0 : ℝ) ≤ 2 * (Real.log 4 + 4) * Y / Real.log Y := by
    have : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
    positivity
  calc Erdos416.V x ≤ _ := hV
    _ ≤ _ := add_le_add hA hB
    _ ≤ _ := by
      gcongr
      calc ∑ m ∈ Ioc 0 Y, g m ≤ _ := hHR
        _ ≤ _ := by gcongr

end LaneC416

end Part3


/-! Part 4: the asymptotic assembly. -/

noncomputable section Part4

open Finset Filter Real

namespace LaneC416

lemma mertens : ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
    ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / p ≤ 2 * exp 1 * logb 2 (log N) + C := by
  obtain ⟨C, hC0, hF⟩ := F_bound ∅ (by simp) (le_refl (0 : ℝ)) zero_le_one
  refine ⟨2 * exp 1 * (2 + 2 * C), fun N hN => ?_⟩
  have h := dyadic (h := G ∅ 0) (fun n => G_nonneg zero_le_one n)
    (fun n => G_le_one le_rfl zero_le_one n) (by simp) hC0 hF hN
  simp only [G, Finset.prod_empty] at h
  calc _ ≤ _ := h
    _ = _ := by ring

lemma Gsum {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
      ∑ p ∈ Nat.primesBelow (N + 1), G S c p / p ≤ 2 * exp 1 * δ * logb 2 (log N) + C := by
  obtain ⟨S, hS, hP⟩ := exists_S hδ hc hc1
  obtain ⟨C, hC0, hF⟩ := F_bound S hS hc.le hc1
  have hP0 : 0 ≤ ∏ q ∈ S, (1 - c / ((q : ℝ) - 1)) := Finset.prod_nonneg fun q hq => by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hq).two_le
    have : c / ((q : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  refine ⟨S, hS, 2 * exp 1 * (2 * δ + 2 * C), fun N hN => ?_⟩
  have h := dyadic (fun n => G_nonneg hc1 n) (fun n => G_le_one hc.le hc1 n) hP0 hC0 hF hN
  have hlogN : 1 ≤ log N := by
    rw [le_log_iff_exp_le (by positivity)]
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [exp_one_lt_d9]
  have hl : 0 ≤ logb 2 (log N) + 2 := by
    have := logb_nonneg (b := 2) (by norm_num) hlogN
    linarith
  calc _ ≤ _ := h
    _ ≤ 2 * exp 1 * (δ * (logb 2 (log N) + 2) + 2 * C) := by gcongr
    _ = _ := by ring

lemma num_bound : 6 * exp 1 / log 2 + 3 ≤ 100 * log (3 / 2) := by
  have h1 : (1 : ℝ) / 3 ≤ log (3 / 2) := by
    have := one_sub_inv_le_log_of_pos (x := (3 / 2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have h2 := exp_one_lt_d9
  have h3 := log_two_gt_d9
  have h4 : 6 * exp 1 / log 2 ≤ 24 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

lemma T1_aux {x t ℓ K CM : ℝ} {N : ℕ} (hx0 : 0 < x) (ht0 : 0 < t) (hℓ : ℓ = log t)
    (hℓ0 : 0 ≤ ℓ) (hK : K = 100 * ℓ) (hNx : (N : ℝ) ≤ x) (S1 : ℝ)
    (hS1 : S1 ≤ 2 * exp 1 * (ℓ / log 2) + CM) :
    (N : ℝ) / (3 / 2 : ℝ) ^ K * exp (3 * S1) ≤ x * exp (3 * CM) / t ^ 3 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have h32 : (3 / 2 : ℝ) ^ K = exp (log (3 / 2) * K) := rpow_def_of_pos (by norm_num) K
  have ht3 : t ^ 3 = exp (3 * ℓ) := by
    rw [show (3 : ℝ) * ℓ = log t * 3 by rw [hℓ]; ring, ← rpow_def_of_pos ht0]
    norm_num
  rw [h32, ht3]
  have hnum := num_bound
  have hexp : exp (3 * S1) ≤ exp (3 * (2 * exp 1 * (ℓ / log 2) + CM)) :=
    exp_le_exp.mpr (by linarith)
  have hkey : 3 * (2 * exp 1 * (ℓ / log 2) + CM) - log (3 / 2) * K ≤ 3 * CM - 3 * ℓ := by
    have h1 : (6 * exp 1 / log 2 + 3) * ℓ ≤ 100 * log (3 / 2) * ℓ :=
      mul_le_mul_of_nonneg_right hnum hℓ0
    have e1 : 3 * (2 * exp 1 * (ℓ / log 2) + CM) = 6 * exp 1 / log 2 * ℓ + 3 * CM := by
      field_simp; ring
    rw [e1, hK]
    nlinarith
  calc (N : ℝ) / exp (log (3 / 2) * K) * exp (3 * S1)
      ≤ x / exp (log (3 / 2) * K) * exp (3 * (2 * exp 1 * (ℓ / log 2) + CM)) := by
        gcongr
    _ = x * exp (3 * (2 * exp 1 * (ℓ / log 2) + CM) - log (3 / 2) * K) := by
        rw [exp_sub]; ring
    _ ≤ x * exp (3 * CM - 3 * ℓ) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr hkey) hx0.le
    _ = x * exp (3 * CM) / exp (3 * ℓ) := by rw [exp_sub]; ring

lemma final_arith {x t u E K K1 Cψ : ℝ} (hx0 : 0 < x) (ht1 : 1 ≤ t) (hu1 : 1 ≤ u) (hut : u ≤ t)
    (hE1 : 3 * E ≤ t ^ 2) (hE4 : 9 * t ^ 5 ≤ x) (hc : 6 * Cψ * K1 * (K + 3) ≤ u ^ 2)
    (hCψ : 0 < Cψ) (hK1 : 0 < K1) (hK0 : 0 ≤ K) :
    x * E / t ^ 3 + u * (sqrt (t * x) + 2 * Cψ * ((K + 3) * x / t) * (K1 * u)) ≤
      x * (u ^ 4 / t) := by
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu1
  have ha : x * E / t ^ 3 ≤ x / (3 * t) := by
    calc x * E / t ^ 3 ≤ x * (t ^ 2 / 3) / t ^ 3 := by gcongr; linarith
      _ = x / (3 * t) := by field_simp
  have hsq : t * x ≤ (x / (3 * t ^ 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_right hE4 hx0.le
    calc t * x * (3 * t ^ 2) ^ 2 = 9 * t ^ 5 * x := by ring
      _ ≤ x * x := h
      _ = x ^ 2 := by ring
  have hs : sqrt (t * x) ≤ x / (3 * t ^ 2) :=
    (sqrt_le_sqrt hsq).trans_eq (sqrt_sq (by positivity))
  have hb : u * sqrt (t * x) ≤ x / (3 * t) := by
    calc u * sqrt (t * x) ≤ t * (x / (3 * t ^ 2)) :=
          mul_le_mul hut hs (sqrt_nonneg _) ht0.le
      _ = x / (3 * t) := by field_simp
  have hc' : u * (2 * Cψ * ((K + 3) * x / t) * (K1 * u)) ≤ x * u ^ 4 / (3 * t) := by
    have e2 : u * (2 * Cψ * ((K + 3) * x / t) * (K1 * u)) =
        ((6 * Cψ * K1 * (K + 3)) * u ^ 2) * x / (3 * t) := by field_simp; ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h2 : (6 * Cψ * K1 * (K + 3)) * u ^ 2 ≤ u ^ 2 * u ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    calc (6 * Cψ * K1 * (K + 3)) * u ^ 2 * x ≤ u ^ 2 * u ^ 2 * x :=
          mul_le_mul_of_nonneg_right h2 hx0.le
      _ = x * u ^ 4 := by ring
  have hd : x / (3 * t) ≤ x * u ^ 4 / (3 * t) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * u ^ 4 := mul_le_mul_of_nonneg_left hu4 hx0.le
  calc _ = x * E / t ^ 3 + u * sqrt (t * x) +
        u * (2 * Cψ * ((K + 3) * x / t) * (K1 * u)) := by ring
    _ ≤ x * u ^ 4 / (3 * t) + x * u ^ 4 / (3 * t) + x * u ^ 4 / (3 * t) := by linarith
    _ = x * (u ^ 4 / t) := by field_simp; ring

theorem erdos_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Erdos416.V x ≤ x * log x ^ (-1 + ε) := by
  set e := min ε 1 with he_def
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨CM, hCM⟩ := mertens
  set A : ℝ := 100 with hA_def
  set w : ℝ := 1 + e / (4 * A) with hw_def
  have hw : 1 < w := by
    have : 0 < e / (4 * A) := by positivity
    linarith
  set c : ℝ := 1 - w⁻¹ with hc_def
  have hc : 0 < c := by have := inv_lt_one_of_one_lt₀ hw; linarith
  have hc1 : c ≤ 1 := by have : 0 < w⁻¹ := by positivity
                         linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  set δ : ℝ := e * log 2 / (16 * exp 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS, CG, hCG⟩ := Gsum hδ hc hc1
  set Cψ : ℝ := log 4 + 4 with hCψ
  have hCψ0 : 0 < Cψ := by have := log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  set K1 : ℝ := exp (4 * exp 1 * δ + 2 * CG) with hK1
  have hK10 : 0 < K1 := exp_pos _
  -- eventual conditions in `t = log x`
  have ev1 : ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 3 * exp (3 * CM) ≤ t ^ 2 ∧ A * log t + 3 ≤ t ∧
      6 * Cψ * K1 * (A * log t + 3) ≤ t ^ (e / 2) := by
    have hlo1 := (isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / (2 * A) by positivity)
    have hlo2 := (isLittleO_log_rpow_atTop (show 0 < e / 2 by positivity)).bound
      (show (0 : ℝ) < 1 / (12 * Cψ * K1 * A) by positivity)
    have hr := (tendsto_rpow_atTop (show 0 < e / 2 by positivity)).eventually_ge_atTop
      (36 * Cψ * K1)
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop 6,
      (tendsto_pow_atTop two_ne_zero).eventually_ge_atTop (3 * exp (3 * CM)),
      hlo1, hlo2, hr] with t ht1 ht6 ht2 hl1 hl2 hr2
    have hlt : 0 ≤ log t := log_nonneg ht1
    rw [norm_of_nonneg hlt, id, norm_of_nonneg (by linarith)] at hl1
    rw [norm_of_nonneg hlt, norm_of_nonneg (by positivity)] at hl2
    refine ⟨ht1, ht2, ?_, ?_⟩
    · have : A * log t ≤ t / 2 := by
        calc A * log t ≤ A * (1 / (2 * A) * t) := by gcongr
          _ = t / 2 := by field_simp
      linarith
    · have h1 : 6 * Cψ * K1 * (A * log t) ≤ t ^ (e / 2) / 2 := by
        calc 6 * Cψ * K1 * (A * log t) ≤ 6 * Cψ * K1 * (A * (1 / (12 * Cψ * K1 * A) * t ^ (e / 2))) := by
              gcongr
          _ = t ^ (e / 2) / 2 := by field_simp; ring
      nlinarith
  have ev2 : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 9 * log x ^ 5 ≤ x := by
    have hlo := (isLittleO_pow_log_id_atTop (n := 5)).bound (show (0 : ℝ) < 1 / 9 by norm_num)
    filter_upwards [eventually_ge_atTop 3, hlo] with x hx3 hl
    refine ⟨hx3, ?_⟩
    have hlx : 0 ≤ log x := log_nonneg (by linarith)
    rw [norm_of_nonneg (by positivity), id, norm_of_nonneg (by linarith)] at hl
    linarith
  filter_upwards [tendsto_log_atTop.eventually ev1, ev2] with x ⟨ht1, hE1, hE2, hE3⟩ ⟨hx3, hE4⟩
  set t := log x with ht_def
  set ℓ := log t with hℓ_def
  set N := ⌊x⌋₊ with hN_def
  set K : ℝ := A * ℓ with hK_def
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t := by linarith
  have hℓ0 : 0 ≤ ℓ := log_nonneg ht1
  have hK0 : 0 ≤ K := by positivity
  have hN3 : 3 ≤ N := Nat.le_floor (by exact_mod_cast hx3)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hNx' : x - 1 < N := Nat.sub_one_lt_floor x
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  set Y := ⌈(K + 2) * N⌉₊ with hY_def
  have hY1 : (K + 2) * N ≤ Y := Nat.le_ceil _
  have hY1' : (Y : ℝ) < (K + 2) * N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hY6 : (6 : ℝ) ≤ Y := by nlinarith
  have hY3 : 3 ≤ Y := by exact_mod_cast (show (3 : ℝ) ≤ Y by linarith)
  have hY2 : 2 ≤ Y := by omega
  have hxY : x ≤ Y := by nlinarith
  have hYx : (Y : ℝ) ≤ (K + 3) * x := by nlinarith
  have htx : t ≤ x := (log_le_sub_one_of_pos hx0).trans (by linarith)
  have hK3 : K + 3 ≤ t := hE2
  have hcore := core S hS hw hx3 (K := K) (Y := Y) (by exact_mod_cast hY1) hY2
  -- T1
  have hlogN : 0 < log N := log_pos (by linarith)
  have hlb1 : logb 2 (log N) ≤ ℓ / log 2 := by
    unfold logb
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact log_le_log hlogN (log_le_log (by positivity) hNx)
  have hS1 := hCM N hN3
  have hS1' : ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / p ≤ 2 * exp 1 * (ℓ / log 2) + CM := by
    have : 2 * exp 1 * logb 2 (log N) ≤ 2 * exp 1 * (ℓ / log 2) := by gcongr
    linarith
  have hT1 := T1_aux hx0 ht0 hℓ_def hℓ0 hK_def hNx _ hS1'
  -- T2
  set u := t ^ (e / 4) with hu_def
  have hu1 : 1 ≤ u := one_le_rpow ht1 (by positivity)
  have hut : u ≤ t := by
    calc u ≤ t ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = t := rpow_one t
  have hu2 : u ^ 2 = t ^ (e / 2) := by
    rw [hu_def, ← rpow_natCast, ← rpow_mul ht0.le]; norm_num; ring_nf
  have hwK : w ^ K ≤ u := by
    rw [rpow_def_of_pos (by linarith), hu_def, rpow_def_of_pos ht0]
    apply exp_le_exp.mpr
    have hlw : log w ≤ e / (4 * A) := by
      have := log_le_sub_one_of_pos (show 0 < w by linarith); linarith
    calc log w * K ≤ e / (4 * A) * K := mul_le_mul_of_nonneg_right hlw hK0
      _ = ℓ * (e / 4) := by rw [hK_def]; field_simp
  have hlogY1 : t ≤ log Y := log_le_log hx0 hxY
  have hlogY2 : log Y ≤ 2 * t := by
    have : (Y : ℝ) ≤ x ^ 2 := by
      calc (Y : ℝ) ≤ (K + 3) * x := hYx
        _ ≤ t * x := by gcongr
        _ ≤ x * x := by gcongr
        _ = x ^ 2 := by ring
    calc log Y ≤ log (x ^ 2) := log_le_log (by linarith) this
      _ = 2 * t := by rw [log_pow]; push_cast; ring
  have hlb2 : logb 2 (log Y) ≤ (log 2 + ℓ) / log 2 := by
    unfold logb
    apply div_le_div_of_nonneg_right _ hlog2.le
    calc log (log Y) ≤ log (2 * t) := log_le_log (by linarith) hlogY2
      _ = log 2 + ℓ := log_mul (by norm_num) ht0.ne'
  have hSG := hCG Y hY3
  have hexpG : exp (2 * ∑ p ∈ Nat.primesBelow (Y + 1), G S (1 - w⁻¹) p / p) ≤ K1 * u := by
    have hu' : u = exp (ℓ * (e / 4)) := by rw [hu_def, rpow_def_of_pos ht0]
    rw [hu', hK1, ← exp_add]
    apply exp_le_exp.mpr
    have h1 : 2 * exp 1 * δ * logb 2 (log Y) ≤ 2 * exp 1 * δ * ((log 2 + ℓ) / log 2) := by
      gcongr
    have h2 : 2 * (2 * exp 1 * δ * ((log 2 + ℓ) / log 2) + CG) =
        4 * exp 1 * δ + 2 * CG + ℓ * (e / 4) := by
      rw [hδ_def]; field_simp; ring
    have h3 : (∑ p ∈ Nat.primesBelow (Y + 1), G S (1 - w⁻¹) p / p) ≤
        2 * exp 1 * δ * ((log 2 + ℓ) / log 2) + CG := by
      simp only [hc_def] at hSG
      linarith
    linarith
  have hYlog : (Y : ℝ) / log Y ≤ (K + 3) * x / t :=
    div_le_div₀ (by positivity) hYx ht0 hlogY1
  have hsqrt : sqrt Y ≤ sqrt (t * x) := sqrt_le_sqrt (hYx.trans (by gcongr))
  have hT2 : w ^ K * (sqrt Y + 2 * Cψ * Y / log Y *
      exp (2 * ∑ p ∈ Nat.primesBelow (Y + 1), G S (1 - w⁻¹) p / p)) ≤
      u * (sqrt (t * x) + 2 * Cψ * ((K + 3) * x / t) * (K1 * u)) := by
    have hlY : 0 < log Y := by linarith
    have e1 : 2 * Cψ * Y / log Y = 2 * Cψ * (Y / log Y) := by ring
    rw [e1]
    gcongr
  have hfin := final_arith hx0 ht1 hu1 hut hE1 hE4 (by rw [hu2]; exact hE3) hCψ0 hK10 hK0
  have hfinal : x * (u ^ 4 / t) ≤ x * t ^ (-1 + ε) := by
    apply mul_le_mul_of_nonneg_left _ hx0.le
    have : u ^ 4 / t = t ^ (-1 + e) := by
      rw [hu_def, ← rpow_natCast, ← rpow_mul ht0.le, rpow_add ht0, rpow_neg_one]
      norm_num
      field_simp
    rw [this]
    exact rpow_le_rpow_of_exponent_le ht1 (by linarith)
  calc Erdos416.V x ≤ _ := hcore
    _ ≤ x * exp (3 * CM) / t ^ 3 +
        u * (sqrt (t * x) + 2 * Cψ * ((K + 3) * x / t) * (K1 * u)) := by
        exact add_le_add hT1 hT2
    _ ≤ x * (u ^ 4 / t) := hfin
    _ ≤ x * t ^ (-1 + ε) := hfinal

end LaneC416

end Part4

theorem OMA.solution : OMA.R_Erdos416_erdos_416_variants_Erdos_R1.H2 :=
  fun ε hε => LaneC416.erdos_upper ε hε
