import FormalConjectures.ErdosProblems.«946»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.QuotientRing


/-!
# Equal divisor counts at consecutive integers

We formalize the upper bound of Erdős, Pomerance and Sárközy, On locally
repeated values of certain arithmetic functions III, Proc. Amer. Math.
Soc. 101 (1987), Theorem 2.1 and its divisor-function remarks.
https://www.renyi.hu/~p_erdos/1987-15.pdf

A smooth-prefix decomposition assigns the pair to a logarithmic bin.
Away from large prime squares, equality of divisor counts constrains
the two-adic valuations of the prefix divisor counts. Stirling's
estimate bounds each valuation's totient-weighted mass. A two-residue
Selberg sieve counts each prefix pair. We sum the bin estimates and
pass from cube endpoints to all real endpoints.

The general sieve code uses Arend Mellendijk's Apache-2.0
PrimeNumberTheoremAnd development (55270df807213fc3584523d09e0311d7dc073ff5),
as adapted to the pinned Mathlib in open-math-agents PR 2155.
The license is reproduced at the end of this file.
-/


open scoped ArithmeticFunction.sigma
open Finset ArithmeticFunction Filter Asymptotics

namespace OMA.Erdos946

/-- The exponent of two in the divisor count. -/
def divisorValuation (n : ℕ) : ℕ := padicValNat 2 (σ 0 n)

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem sigma_squarefree {n : ℕ} (hn : Squarefree n) :
    σ 0 n = 2 ^ n.primeFactors.card := by
  rw [sigma_zero_apply, Nat.card_divisors hn.ne_zero]
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun p hp => by
    rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]

theorem divisorValuation_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) :
    divisorValuation (m * n) = divisorValuation m + divisorValuation n := by
  unfold divisorValuation
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, padicValNat.mul]
  · exact (sigma_pos 0 m hm).ne'
  · exact (sigma_pos 0 n hn).ne'

theorem divisorValuation_squarefree {n : ℕ} (hn : Squarefree n) :
    divisorValuation n = n.primeFactors.card := by
  rw [divisorValuation, sigma_squarefree hn, padicValNat.prime_pow]

theorem divisorValuation_split {a b k l : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk : Squarefree k) (hl : Squarefree l) (hak : a.Coprime k) (hbl : b.Coprime l)
    (hσ : σ 0 (a * k) = σ 0 (b * l)) :
    divisorValuation a + k.primeFactors.card = divisorValuation b + l.primeFactors.card := by
  calc
    divisorValuation a + k.primeFactors.card = divisorValuation (a * k) := by
      rw [divisorValuation_mul ha hk.ne_zero hak, divisorValuation_squarefree hk]
    _ = divisorValuation (b * l) := congrArg (padicValNat 2) hσ
    _ = divisorValuation b + l.primeFactors.card := by
      rw [divisorValuation_mul hb hl.ne_zero hbl, divisorValuation_squarefree hl]

/-- Split an increasing prime list just before its running product would exceed the cutoff. -/
theorem exists_prefix_split {L : List ℕ} (hs : L.Pairwise (· ≤ ·))
    (hprime : ∀ p ∈ L, Nat.Prime p) {T : ℕ} (hT : 1 ≤ T) (hlarge : T < L.prod) :
    ∃ A : List ℕ, ∃ p : ℕ, ∃ B : List ℕ, L = A ++ p :: B ∧ A.prod ≤ T ∧
      T < A.prod * p ∧ (∀ q ∈ A, q ≤ p) ∧ (∀ q ∈ p :: B, p ≤ q) := by
  induction L generalizing T with
  | nil => simp at hlarge; omega
  | cons q L ih =>
    have hq : Nat.Prime q := hprime q (by simp)
    have hs' := List.pairwise_cons.mp hs
    simp only [List.prod_cons] at hlarge
    by_cases h : T < q
    · exact ⟨[], q, L, rfl, by simpa, by simpa, by simp,
        fun r hr => (List.mem_cons.mp hr).elim (fun he => he ▸ le_rfl) (hs'.1 r)⟩
    · have hqt : q ≤ T := le_of_not_gt h
      have hqT : 1 ≤ T / q := (Nat.le_div_iff_mul_le hq.pos).2 (by simpa)
      have htail : T / q < L.prod := (Nat.div_lt_iff_lt_mul hq.pos).2 (by simpa [mul_comm])
      obtain ⟨A, p, B, he, hA, hAp, hleft, hright⟩ :=
        ih hs'.2 (fun r hr => hprime r (by simp [hr])) hqT htail
      refine ⟨q :: A, p, B, by simp [he], ?_, ?_, ?_, hright⟩
      · simp only [List.prod_cons]
        simpa only [mul_comm q] using (Nat.le_div_iff_mul_le hq.pos).mp hA
      · simp only [List.prod_cons, Nat.mul_assoc]
        simpa [mul_comm, mul_left_comm, mul_assoc] using (Nat.div_lt_iff_lt_mul hq.pos).mp hAp
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hs'.1 p (by simp [he])
        · exact hleft _ hr


/-- A prime factor of the product of a prime list occurs in that list. -/
theorem prime_dvd_list_prod_iff {L : List ℕ} (hL : ∀ t ∈ L, Nat.Prime t)
    {q : ℕ} (hq : Nat.Prime q) : q ∣ L.prod ↔ q ∈ L := by
  have hpos : 0 < L.prod := by
    induction L with
    | nil => simp
    | cons a t ih =>
      rw [List.prod_cons]
      exact Nat.mul_pos (hL a (by simp)).pos (ih (fun x hx => hL x (by simp [hx])))
  have hp := Nat.primeFactorsList_unique rfl hL
  rw [hp.mem_iff, Nat.mem_primeFactorsList hpos.ne']
  exact ⟨fun hd => ⟨hq, hd⟩, And.right⟩

/-- Smooth prefix and rough suffix after the running product crosses the cutoff. -/
theorem exists_factor_split {n T : ℕ} (hT : 1 ≤ T) (hn : T < n) :
    ∃ a k p : ℕ, a * k = n ∧ a ≠ 0 ∧ k ≠ 0 ∧
      Nat.Prime p ∧ p ∣ k ∧ a ≤ T ∧ T < a * p ∧
      (∀ q : ℕ, Nat.Prime q → q ∣ a → q ≤ p) ∧
      (∀ q : ℕ, Nat.Prime q → q ∣ k → p ≤ q) := by
  have hn0 : n ≠ 0 := by omega
  have hnp := Nat.prod_primeFactorsList hn0
  obtain ⟨A,p,B,he,hAT,hAp,hleft,hright⟩ := exists_prefix_split
    (Nat.primeFactorsList_sorted n).pairwise
    (fun q hq => Nat.prime_of_mem_primeFactorsList hq) hT (by simpa only [hnp] using hn)
  have hA : ∀ q ∈ A, Nat.Prime q := fun q hq =>
    Nat.prime_of_mem_primeFactorsList (by rw [he]; exact List.mem_append_left _ hq)
  have hB : ∀ q ∈ p :: B, Nat.Prime q := fun q hq =>
    Nat.prime_of_mem_primeFactorsList (by rw [he]; exact List.mem_append_right _ hq)
  have hprod : A.prod * (p :: B).prod = n := by
    rw [← List.prod_append, ← he, hnp]
  refine ⟨A.prod,(p :: B).prod,p,hprod,?_,?_,hB p (by simp),?_,hAT,hAp,?_,?_⟩
  · intro h; rw [h,zero_mul] at hprod; exact hn0 hprod.symm
  · intro h; rw [h,mul_zero] at hprod; exact hn0 hprod.symm
  · exact (prime_dvd_list_prod_iff hB (hB p (by simp))).2 (by simp)
  · intro q hq hd; exact hleft q ((prime_dvd_list_prod_iff hA hq).1 hd)
  · intro q hq hd; exact hright q ((prime_dvd_list_prod_iff hB hq).1 hd)

/-- A rough suffix is squarefree and disjoint from the prefix when large prime squares are absent. -/
theorem coprime_squarefree_of_rough {a k y : ℕ}
    (hl : ∀ p : ℕ, Nat.Prime p → p ∣ k → y ≤ p)
    (hs : ∀ p : ℕ, Nat.Prime p → y ≤ p → ¬ p * p ∣ a * k) :
    a.Coprime k ∧ Squarefree k := by
  constructor
  · by_contra h
    obtain ⟨p,hp,ha,hk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact hs p hp (hl p hp hk) (Nat.mul_dvd_mul ha hk)
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp h
    have hpk : p ∣ k := (dvd_mul_right p p).trans h
    exact hs p hp (hl p hp hpk) (h.trans (dvd_mul_left k a))

/-- A rough squarefree factor has at most logarithmically many prime factors. -/
theorem rough_card_le {k : ℕ} {y X : ℝ} (hk : Squarefree k) (hy : 1 < y)
    (hX : (k : ℝ) ≤ X) (hrough : ∀ p ∈ k.primeFactors, y ≤ (p : ℝ)) :
    (k.primeFactors.card : ℝ) ≤ Real.log X / Real.log y := by
  have hprod : ∏ p ∈ k.primeFactors, p = k := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hk.ne_zero]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hk (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
    simp
  have hpow : y ^ k.primeFactors.card ≤ (k : ℝ) := calc
    _ = ∏ _ ∈ k.primeFactors, y := (Finset.prod_const y).symm
    _ ≤ ∏ p ∈ k.primeFactors, (p : ℝ) := Finset.prod_le_prod (by intros; positivity) hrough
    _ = k := by rw [← Nat.cast_prod, hprod]
  apply (le_div_iff₀ (Real.log_pos hy)).mpr
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (hpow.trans hX)

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Filter Asymptotics
open scoped ArithmeticFunction.sigma

/-- Numbers up to X divisible by a square of a prime at least the cutoff. -/
def squareExceptions (X Y : ℕ) : Finset ℕ :=
  (Icc Y X).biUnion fun p => (Ioc 0 X).filter (fun n => p*p ∣ n)

theorem mem_squareExceptions {X Y n p : ℕ} (hY : Y ≤ p)
    (hn0 : 0 < n) (hnX : n ≤ X) (hdiv : p*p ∣ n) :
    n ∈ squareExceptions X Y := by
  apply Finset.mem_biUnion.2
  have hp : p ≤ X :=
    (Nat.le_mul_of_pos_right p (by
      by_contra h
      have hp : p = 0 := by omega
      simp [hp,hn0.ne'] at hdiv)).trans
      ((Nat.le_of_dvd hn0 hdiv).trans hnX)
  exact ⟨p,Finset.mem_Icc.mpr ⟨hY,hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0,hnX⟩,hdiv⟩⟩

theorem sum_inv_sq_Icc_le {Y X : ℕ} (hY : 2 ≤ Y) :
    (∑ p ∈ Icc Y X, (1 : ℝ) / (p*p)) ≤ 1 / ((Y : ℝ)-1) := by
  by_cases hYX : Y ≤ X
  · calc
      _ ≤ ∑ p ∈ Icc Y X, ((1 : ℝ) / ((p : ℝ)-1) - (1 : ℝ) / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hY.trans (Finset.mem_Icc.mp hp).1
        have hp0 : 0 < (p : ℝ) := by linarith
        have hp1 : 0 < (p : ℝ)-1 := by linarith
        field_simp [hp0.ne',hp1.ne']
        nlinarith
      _ = (1 : ℝ) / ((Y : ℝ)-1) - (1 : ℝ) / X := by
        have hYX' : X = Y + (X-Y) := by omega
        rw [hYX']
        clear hYX hYX'
        induction (X-Y) with
        | zero => simp
        | succ k ih =>
          rw [← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega), ih]
          push_cast
          have h : (Y : ℝ) + k + 1 - 1 = Y + k := by ring
          rw [h]
          ring
      _ ≤ _ := sub_le_self _ (by positivity)
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hYX), Finset.sum_empty]
    have h : (2 : ℝ) ≤ Y := by exact_mod_cast hY
    exact div_nonneg zero_le_one (by linarith)

theorem squareExceptions_card_le {X Y : ℕ} (hY : 2 ≤ Y) :
    ((squareExceptions X Y).card : ℝ) ≤ X / ((Y : ℝ)-1) := by
  classical
  unfold squareExceptions
  have hcard : ((Finset.biUnion (Icc Y X) (fun p => (Ioc 0 X).filter (fun n => p*p ∣ n))).card : ℝ) ≤
      ∑ p ∈ Icc Y X, (((Ioc 0 X).filter (fun n => p*p ∣ n)).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Icc Y X)
      (t := fun p => (Ioc 0 X).filter (fun n => p*p ∣ n)))
  apply hcard.trans
  simp only [Nat.Ioc_filter_dvd_card_eq_div]
  calc
    _ ≤ ∑ p ∈ Icc Y X, (X : ℝ) * ((1 : ℝ) / (p*p)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [mul_one_div]
      simpa only [Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := X) (n := p*p))
    _ = (X : ℝ) * ∑ p ∈ Icc Y X, (1 : ℝ) / (p*p) := (Finset.mul_sum ..).symm
    _ ≤ _ := by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le hY) (by positivity)

end OMA.Erdos946

open Finset Nat
open scoped BigOperators

namespace OMA.Erdos946

/-- Compare a finite sum over factorizations to an independent product over exponents. -/
theorem sum_factorization_weights_le
    (S P : Finset ℕ) (B : ℕ) (w : ℕ → ℕ → ℝ)
    (h0 : ∀ p e, 0 ≤ w p e)
    (hs : ∀ n ∈ S, n ≠ 0 ∧ n.primeFactors ⊆ P ∧ ∀ p, n.factorization p ≤ B) :
    (∑ n ∈ S, ∏ p ∈ P, w p (n.factorization p)) ≤
      ∏ p ∈ P, ∑ e ∈ Finset.range (B + 1), w p e := by
  classical
  let E : ℕ → P → ℕ := fun n p => n.factorization p.1
  let W : (P → ℕ) → ℝ := fun f => ∏ p : P, w p.1 (f p)
  have hEinj : Set.InjOn E S := by
    intro a ha b hb h
    apply Nat.eq_of_factorization_eq (hs a ha).1 (hs b hb).1
    intro p
    by_cases hp : p ∈ P
    · exact congrFun h ⟨p,hp⟩
    · have ha' : p ∉ a.primeFactors := fun hpa => hp ((hs a ha).2.1 hpa)
      have hb' : p ∉ b.primeFactors := fun hpb => hp ((hs b hb).2.1 hpb)
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at ha' hb'
      exact ha'.trans hb'.symm
  have hsub : S.image E ⊆ Fintype.piFinset (fun _ : P => Finset.range (B+1)) := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hf
    apply Fintype.mem_piFinset.mpr
    intro p
    simpa [E] using (hs n hn).2.2 p.1
  calc
    _ = ∑ n ∈ S, W (E n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (Finset.prod_attach P fun p => w p (n.factorization p)).symm
    _ = ∑ f ∈ S.image E, W f := (Finset.sum_image hEinj).symm
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : P => Finset.range (B+1)), W f :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.prod_nonneg (by intros; apply h0))
    _ = _ := by
      rw [← Finset.prod_attach P (fun p => ∑ e ∈ Finset.range (B+1), w p e)]
      exact
        (Finset.prod_univ_sum (fun _ : P => Finset.range (B+1))
          (fun (p : P) e => w p.1 e)).symm

/-- A weighted sum over k-element subsets is bounded by the kth power sum divided by k!. -/
theorem sum_powersetCard_prod_le {α : Type*} [DecidableEq α]
    (S : Finset α) (k : ℕ) (u : α → ℝ) (hu : ∀ x ∈ S, 0 ≤ u x) :
    (∑ A ∈ S.powersetCard k, ∏ i ∈ A, u i) * k.factorial ≤
      (∑ i ∈ S, u i) ^ k := by
  classical
  induction k generalizing S with
  | zero => simp
  | succ k ih =>
    have hcount :
        ((k + 1 : ℕ) : ℝ) * (∑ A ∈ S.powersetCard (k+1), ∏ i ∈ A, u i) =
        ∑ i ∈ S, u i * (∑ A ∈ (S.erase i).powersetCard k, ∏ j ∈ A, u j) := by
      calc
        _ = ∑ A ∈ S.powersetCard (k+1), ∑ i ∈ A, ∏ j ∈ A, u j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A hA
          simp [sum_const, (Finset.mem_powersetCard.mp hA).2, nsmul_eq_mul]
        _ = ∑ i ∈ S, ∑ A ∈ (S.erase i).powersetCard k,
                u i * ∏ j ∈ A, u j := by
          have hsub (A : Finset α) (hA : A ∈ S.powersetCard (k+1)) :
              S.filter (fun i => i ∈ A) = A :=
            by
              ext i
              exact ⟨fun hi => (Finset.mem_filter.mp hi).2,
                fun hi => Finset.mem_filter.mpr ⟨(Finset.mem_powersetCard.mp hA).1 hi, hi⟩⟩
          calc
            _ = ∑ A ∈ S.powersetCard (k+1), ∑ i ∈ S,
                if i ∈ A then ∏ j ∈ A, u j else 0 := by
              apply Finset.sum_congr rfl
              intro A hA
              rw [← Finset.sum_filter, hsub A hA]
            _ = ∑ i ∈ S, ∑ A ∈ (S.powersetCard (k+1)).filter (fun A => i ∈ A),
                ∏ j ∈ A, u j := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              refine Finset.sum_bij (fun A _ => A.erase i) ?_ ?_ ?_ ?_
              · intro A hA
                rw [Finset.mem_filter, Finset.mem_powersetCard] at hA
                apply Finset.mem_powersetCard.mpr
                constructor
                · intro j hj
                  have hj' := Finset.mem_erase.mp hj
                  exact Finset.mem_erase.mpr ⟨hj'.1,hA.1.1 hj'.2⟩
                · have := Finset.card_erase_add_one hA.2
                  omega
              · intro A hA C hC he
                rw [Finset.mem_filter] at hA hC
                rw [← Finset.insert_erase hA.2, ← Finset.insert_erase hC.2, he]
              · intro A hA
                have hAi : i ∉ A := fun h => Finset.notMem_erase i S
                  ((Finset.mem_powersetCard.mp hA).1 h)
                refine ⟨insert i A, ?_, Finset.erase_insert hAi⟩
                rw [Finset.mem_filter, Finset.mem_powersetCard]
                refine ⟨⟨?_, by simp [Finset.card_insert_of_notMem hAi,
                  (Finset.mem_powersetCard.mp hA).2]⟩, by simp⟩
                exact Finset.insert_subset hi ((Finset.mem_powersetCard.mp hA).1.trans
                  (Finset.erase_subset _ _))
              · intro A hA
                exact (Finset.mul_prod_erase _ _ (Finset.mem_filter.mp hA).2).symm
        _ = _ := by simp [Finset.mul_sum]
    have hu' : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg hu
    calc
      _ = ((k+1 : ℕ) : ℝ) * (∑ A ∈ S.powersetCard (k+1), ∏ i ∈ A, u i) * k.factorial := by
        push_cast [Nat.factorial_succ]
        ring
      _ = ∑ i ∈ S, u i * ((∑ A ∈ (S.erase i).powersetCard k, ∏ j ∈ A, u j) * k.factorial) := by
        rw [hcount, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ∑ i ∈ S, u i * (∑ j ∈ S, u j) ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        have hnon : ∀ x ∈ S.erase i, 0 ≤ u x := fun x hx => hu x (Finset.mem_of_mem_erase hx)
        refine mul_le_mul_of_nonneg_left ((ih _ hnon).trans ?_) (hu i hi)
        exact pow_le_pow_left₀ (Finset.sum_nonneg hnon)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i S)
            (fun j hj _ => hu j hj)) _
      _ = _ := by rw [← Finset.sum_mul, ← _root_.pow_succ']

end OMA.Erdos946

open Real

namespace OMA.Erdos946

noncomputable def poissonTerm (z : ℝ) (k : ℕ) : ℝ := z ^ k / k.factorial

theorem poissonTerm_step (z : ℝ) (k : ℕ) :
    poissonTerm z (k + 1) = poissonTerm z k * (z / (k+1)) := by
  simp only [poissonTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp [show (k.factorial : ℝ) ≠ 0 by positivity, show ((k : ℝ) + 1) ≠ 0 by positivity]

theorem poissonTerm_le_mode {z : ℝ} (hz : 0 ≤ z) (k : ℕ) :
    poissonTerm z k ≤ poissonTerm z ⌊z⌋₊ := by
  let m := ⌊z⌋₊
  have hm : (m : ℝ) ≤ z := Nat.floor_le hz
  have hm' : z < (m : ℝ) + 1 := Nat.lt_floor_add_one z
  have hnon (i : ℕ) : 0 ≤ poissonTerm z i := by
    unfold poissonTerm
    positivity
  have hinc (i : ℕ) (hi : i < m) : poissonTerm z i ≤ poissonTerm z (i+1) := by
    rw [poissonTerm_step]
    nth_rw 1 [← mul_one (poissonTerm z i)]
    apply mul_le_mul_of_nonneg_left _ (hnon i)
    apply (le_div_iff₀ (by positivity)).mpr
    have hi' : ((i : ℝ)+1) ≤ (m : ℝ) := by exact_mod_cast hi
    linarith
  have hdec (i : ℕ) (hi : m ≤ i) : poissonTerm z (i+1) ≤ poissonTerm z i := by
    rw [poissonTerm_step]
    nth_rw 2 [← mul_one (poissonTerm z i)]
    apply mul_le_mul_of_nonneg_left _ (hnon i)
    apply (div_le_iff₀ (by positivity)).mpr
    have hi' : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  rcases le_total k m with hkm | hmk
  · let f := fun i : ℕ => poissonTerm z (min i m)
    have hf : Monotone f := monotone_nat_of_le_succ fun i => by
      by_cases hi : i < m
      · have hi' : i+1 ≤ m := by omega
        simpa [f, min_eq_left hi.le, min_eq_left hi'] using hinc i hi
      · simp [f, min_eq_right (by omega : m ≤ i), min_eq_right (by omega : m ≤ i+1)]
    simpa [f, min_eq_left hkm] using hf hkm
  · exact (antitoneOn_nat_Ici_of_succ_le hdec)
      (show m ∈ Set.Ici m by simp) (show k ∈ Set.Ici m by simpa) hmk

theorem poissonTerm_le {z : ℝ} (hz : 2 ≤ z) (k : ℕ) :
    poissonTerm z k ≤ exp z / sqrt z := by
  let m := ⌊z⌋₊
  have hm : (m : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hm' : z < (m : ℝ) + 1 := Nat.lt_floor_add_one z
  have hmpos : 0 < (m : ℝ) := by linarith
  have hzpos : 0 < z := by linarith
  have hfac : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hs : sqrt z ≤ sqrt (2 * π * (m : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hpi : 2 ≤ π := Real.two_le_pi
    nlinarith [mul_nonneg (show 0 ≤ π - 2 by linarith) hmpos.le]
  have hlog : (m : ℝ) * log (z / m) ≤ z - m := by
    calc
      _ ≤ (m : ℝ) * (z / m - 1) :=
        mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hzpos hmpos)) hmpos.le
      _ = _ := by field_simp
  have hr : (z / (m : ℝ) * exp 1) ^ m ≤ exp z := by
    have he := exp_le_exp.mpr (show (m : ℝ) * (log (z / m) + 1) ≤ z by linarith)
    rw [exp_nat_mul, exp_add, exp_log (div_pos hzpos hmpos)] at he
    exact he
  have hse : 0 < (m / exp 1) ^ m := by positivity
  have hcalc : z ^ m = (z / (m : ℝ) * exp 1) ^ m * (m / exp 1) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  refine (poissonTerm_le_mode hzpos.le k).trans ?_
  unfold poissonTerm
  apply (div_le_div_iff₀ hfac (Real.sqrt_pos.2 hzpos)).mpr
  rw [hcalc]
  calc
    _ ≤ (exp z * (m / exp 1) ^ m) * sqrt (2 * π * (m : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hr hse.le) hs (Real.sqrt_nonneg _) (by positivity)
    _ = exp z * (sqrt (2 * π * (m : ℝ)) * (m / exp 1) ^ m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Stirling.le_factorial_stirling m) (Real.exp_pos _).le

end OMA.Erdos946

open Finset Real Filter
open scoped Topology

namespace OMA.Erdos946

theorem factorial_factorization_ge_div (N p : ℕ) (hp : p.Prime) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p N + 2) (by omega)]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 2) := by simp
  simpa only [pow_one] using
    (Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1)

theorem factorial_factorization_log (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, (N.factorial.factorization p : ℝ) * Real.log (p : ℝ) := by
  nth_rw 1 [← Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero N)]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      rw [Nat.mem_primesLE]
      refine ⟨le_of_not_gt (fun h => ?_), hprime⟩
      have hn : p ∈ N.factorial.factorization.support := by
        rwa [Nat.support_factorization]
      rw [Finsupp.mem_support_iff] at hn
      exact hn (Nat.factorization_factorial_eq_zero_of_lt h)
    · intro p hp h
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at h
      simp [h]
  · intro p hp
    simp only [Nat.cast_pow, ne_eq]
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem sum_log_prime_div_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / p) ≤ 2 * Real.log N := by
  by_cases hN : 0 < N
  · have hnr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hlogfac : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow N)
    rw [factorial_factorization_log] at hlogfac
    have hsum : (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / p) ≤
        2 * ∑ p ∈ Nat.primesLE N, (N.factorial.factorization p : ℝ) * Real.log (p : ℝ) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
      have hq : 1 ≤ N / p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa)
      have hqN : N < p * (N / p + 1) := by
        simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hprime.pos).mp
          (Nat.lt_succ_self (N / p))
      have hqR : (1 : ℝ) ≤ (N / p : ℕ) := by exact_mod_cast hq
      have hqNR : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) + 1) := by exact_mod_cast hqN
      have hfrac : (N : ℝ) / p ≤ 2 * (N / p : ℕ) := by
        apply (div_le_iff₀ hpR).mpr
        nlinarith
      have hf : ((N / p : ℕ) : ℝ) ≤ N.factorial.factorization p := by
        exact_mod_cast factorial_factorization_ge_div N p hprime
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      calc
        _ = ((N : ℝ) / p) * Real.log p := by ring
        _ ≤ (2 * (N / p : ℕ)) * Real.log p :=
          mul_le_mul_of_nonneg_right hfrac hlogp
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hf hlogp]
    apply (mul_le_mul_iff_right₀ hnr).mp
    nlinarith only [hsum,hlogfac]
  · have : N = 0 := by omega
    subst N
    simp

end OMA.Erdos946
section

open Finset Real Filter Set
open scoped Topology

namespace OMA.Erdos946

noncomputable def natRpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' a b := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem tsum_nat_rpow_le {s : ℝ} (hs : s < -1) :
    (∑' n : ℕ, (n : ℝ) ^ s) ≤ 1 + 1 / (-s - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ s) := Real.summable_nat_rpow.2 hs
  rw [hsum.tsum_eq_zero_add]
  have hsplit := (hsum.comp_injective Nat.succ_injective).tsum_eq_zero_add
  change (∑' b : ℕ, ((b+1 : ℕ) : ℝ) ^ s) = _ at hsplit
  rw [hsplit]
  have ha : AntitoneOn (fun x : ℝ => x ^ s) (Set.Ici (1 : ℝ)) := by
    intro a ha b hb hab
    apply Real.rpow_le_rpow_of_nonpos (by linarith [show 1 ≤ a from ha]) hab
    linarith
  have hInt := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ s) 1
    (by exact_mod_cast ha) (integrableOn_Ioi_rpow_of_lt hs (by norm_num))
    (fun x hx => Real.rpow_nonneg (by
      have hx' : (1 : ℝ) < x := by exact_mod_cast hx
      linarith) s)
  norm_num only [Nat.cast_one] at hInt
  rw [integral_Ioi_rpow_of_lt hs zero_lt_one] at hInt
  simp only [Real.one_rpow, Nat.cast_zero, Real.zero_rpow (by linarith : s ≠ 0),
    zero_add] at *
  have hh : -1 / (s + 1) = 1 / (-s - 1) := by
    rw [show -s - 1 = -(s + 1) by ring, div_neg, neg_div]
  rw [hh] at hInt
  have h1 : ((fun n : ℕ => (n : ℝ) ^ s) ∘ Nat.succ) 0 = 1 := by simp
  rw [h1]
  exact add_le_add le_rfl hInt

theorem prod_inv_one_sub_rpow_le {s : ℝ} (hs : s < -1) (V : ℕ) :
    (∏ p ∈ Nat.primesLE V, (1 - (p : ℝ) ^ s)⁻¹) ≤ 1 + 1 / (-s - 1) := by
  have hsum : Summable (natRpowHom s) := Real.summable_nat_rpow.2 hs
  have he := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum (Nat.primesLE V)
  simp only [Finset.filter_eq_self.mpr (fun p hp => (Nat.mem_primesLE.mp hp).2)] at he
  unfold natRpowHom at he
  calc
    _ = ∑' n : Nat.factoredNumbers (Nat.primesLE V), (n.1 : ℝ) ^ s := by
      simpa [one_div] using he
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ s := by
      exact Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ s)
        (Nat.factoredNumbers (Nat.primesLE V))
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) s) hsum
    _ ≤ _ := tsum_nat_rpow_le hs

end OMA.Erdos946
end

namespace OMA.Erdos946

theorem inv_euler_at_one_le_shift {t p : ℝ} (ht : 0 ≤ t) (hp : 2 ≤ p) :
    (1 - p⁻¹)⁻¹ ≤ (1 - p ^ (-(1+t)))⁻¹ * Real.exp (2 * t * (Real.log p / p)) := by
  have hp0 : 0 < p := by linarith
  have hl := Real.log_nonneg (show 1 ≤ p by linarith)
  have hq0 : 0 ≤ p⁻¹ := by positivity
  have hq : p⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div]; gcongr
  let a := t * Real.log p
  have ha : 0 ≤ a := mul_nonneg ht hl
  have hdef : p ^ (-(1+t)) = p⁻¹ * Real.exp (-a) := by
    rw [show -(1+t) = -1 + -t by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      Real.rpow_def_of_pos hp0]
    congr 2
    dsimp [a]
    ring
  have hleft : 0 < 1 - p⁻¹ := by linarith
  have hright : 0 < 1 - p ^ (-(1+t)) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))
  rw [inv_eq_one_div (1-p⁻¹), inv_eq_one_div (1-p ^ (-(1+t))), div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hleft hright).mpr
  rw [hdef, one_mul]
  have h1 := Real.add_one_le_exp (-a)
  have h2 : p⁻¹ * (1 - Real.exp (-a)) ≤ p⁻¹ * a :=
    mul_le_mul_of_nonneg_left (by linarith) hq0
  have h3 : p⁻¹ * a ≤ (1-p⁻¹) * (2 * a * p⁻¹) := by
    have ha' : 0 ≤ a * p⁻¹ := mul_nonneg ha hq0
    nlinarith only [mul_nonneg (show 0 ≤ 1-2*p⁻¹ by linarith) ha']
  have h4 : 2 * a * p⁻¹ = 2 * t * (Real.log p / p) := by
    dsimp [a]
    ring
  rw [← h4]
  have h5 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*a*p⁻¹)) hleft.le
  nlinarith only [h2,h3,h5]

theorem primeEulerProduct_le {V : ℕ} (hV : 2 ≤ V) :
    (∏ p ∈ Nat.primesLE V, (1 - (p : ℝ)⁻¹)⁻¹) ≤ Real.exp 4 * (1 + Real.log V) := by
  let t := (Real.log V)⁻¹
  have hV' : (1 : ℝ) < V := by exact_mod_cast hV
  have hlog := Real.log_pos hV'
  have ht : 0 < t := by positivity
  have hterm (p : ℕ) (hp : p ∈ Nat.primesLE V) :
      (1 - (p : ℝ)⁻¹)⁻¹ ≤
        (1 - (p : ℝ) ^ (-(1+t)))⁻¹ * Real.exp (2*t*(Real.log p / p)) :=
    inv_euler_at_one_le_shift ht.le (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le)
  have hnon (p : ℕ) (hp : p ∈ Nat.primesLE V) : 0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀
      (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)))
  have hc := Finset.prod_le_prod hnon hterm
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum] at hc
  have hsum : 2*t*(∑ p ∈ Nat.primesLE V, Real.log p / p) ≤ 4 := by
    calc
      _ ≤ 2*t*(2*Real.log V) := mul_le_mul_of_nonneg_left
        (sum_log_prime_div_le V) (by positivity)
      _ = 4 := by dsimp [t]; field_simp; norm_num
  have heuler := prod_inv_one_sub_rpow_le (s := -(1+t)) (by linarith) V
  have ht' : - -(1+t) - 1 = t := by ring
  rw [ht'] at heuler
  have hlogt : 1 / t = Real.log V := by simp [t]
  rw [hlogt] at heuler
  exact hc.trans (by
    rw [mul_comm (Real.exp 4)]
    exact mul_le_mul heuler (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le (by positivity))

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real

theorem primeEulerProduct_ge (V : ℕ) :
    Real.log (V : ℝ) ≤ ∏ p ∈ Nat.primesLE V, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hgeom {p : ℕ} (hp : p.Prime) : ‖natRpowHom (-1) p‖ < 1 := by
    change ‖(p : ℝ) ^ (-1 : ℝ)‖ < 1
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (by positivity)]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hgeom (Nat.primesLE V)).2
  simp only [Finset.filter_eq_self.mpr (fun p hp => (Nat.mem_primesLE.mp hp).2)] at hsum
  have hT (n : ℕ) (hn : n ∈ Icc 1 V) : n ∈ Nat.factoredNumbers (Nat.primesLE V) := by
    obtain ⟨ha,hb⟩ := Finset.mem_Icc.mp hn
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (by omega)
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hb,
      Nat.prime_of_mem_primeFactors hp⟩
  let I : (↥(Icc 1 V) : Type) → Nat.factoredNumbers (Nat.primesLE V) :=
    fun i => ⟨i.1,hT i.1 i.2⟩
  have hi : Function.Injective I := fun x y h => Subtype.ext (congrArg (fun a : Nat.factoredNumbers (Nat.primesLE V) => a.1) h)
  have hpart : (∑ n ∈ Icc 1 V, (n : ℝ)⁻¹) ≤
      ∏ p ∈ Nat.primesLE V, (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hbound := hsum.summable.sum_le_tsum
      (Finset.univ.map ⟨I,hi⟩) (fun n _ => by change 0 ≤ (n.1 : ℝ)^(-1:ℝ); positivity)
    rw [hsum.tsum_eq, Finset.sum_map] at hbound
    change (∑ i : (Icc 1 V), ((i.1 : ℕ) : ℝ)^(-1:ℝ)) ≤
      ∏ p ∈ Nat.primesLE V, (1 - (p : ℝ)^(-1:ℝ))⁻¹ at hbound
    simp only [Real.rpow_neg_one] at hbound
    rw [← Finset.sum_attach (s := Icc 1 V) (fun n => (n : ℝ)⁻¹)]
    exact hbound
  apply le_trans _ hpart
  have hlog := log_add_one_le_harmonic V
  rw [harmonic_eq_sum_Icc] at hlog
  push_cast at hlog
  by_cases hV : V = 0
  · simp [hV]
  · refine (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hV) (by norm_cast; omega)).trans hlog

end OMA.Erdos946

/- We use the upper Selberg sieve for two nonproportional linear polynomials.

The general upper sieve proof below is adapted from Arend Mellendijk's Apache-2.0
formalization in PrimeNumberTheoremAnd, commit 55270df80721, as ported to this
Mathlib version in open-math-agents PR 2155. The use of the sieve for the
two-polynomial count is specific to this proof.
-/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP

end Aux
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)

abbrev selbergTerms := BoundingSieve.selbergTerms (s := s)

theorem selbergTerms_apply (d : ℕ) :
    (SelbergSieve.selbergTerms s) d = s.nu d * ∏ p ∈ d.primeFactors, 1/(1 - s.nu p) := by
  simpa only [selbergTerms, one_div] using BoundingSieve.selbergTerms_apply (s := s) d
section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < (SelbergSieve.selbergTerms s) l := by
  exact BoundingSieve.selbergTerms_pos hl
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  exact BoundingSieve.selbergTerms_isMultiplicative
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by
  exact BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ s.totalMass * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
  by simpa only [selbergTerms, one_div] using BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := s) w
end LambdaSquared

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
section
noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0

theorem selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]

  apply symm
  rw [sum_mul_subst d s.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * (s.nu d) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared (SelbergSieve.selbergWeights s)

theorem weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨(SelbergSieve.selbergMuPlus s), BoundingSieve.upperMoebius_lambdaSquared (SelbergSieve.selbergWeights s) (s.weight_one_of_selberg)⟩

theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms (s.toBoundingSieve)) l *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private theorem _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ s.level ↔
    (k * m) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k s.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |(SelbergSieve.selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| (SelbergSieve.selbergWeights s) d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := s.toBoundingSieve)) d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| (BoundingSieve.rem (s := s.toBoundingSieve)) d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      s.totalMass / (SelbergSieve.selbergBoundingSum s) +
        ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := s.toBoundingSieve)) d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ s.totalMass * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
end
end

namespace OMA.Erdos946

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.omega

noncomputable def residueDensity (K : ℕ → ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (K p : ℝ) / p)

theorem residueDensity_prime {K : ℕ → ℕ} {p : ℕ} (hp : p.Prime) :
    residueDensity K p = (K p : ℝ) / p := by
  rw [residueDensity, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,
    Nat.Prime.primeFactors hp, Finset.prod_singleton]

/-- An interval sieve with weights indexed by the part of the polynomial value
    supported on the sieving primes. -/
noncomputable def intervalSieve (F K : ℕ → ℕ) (N P : ℕ) (z : ℝ)
    (hP : Squarefree P) (hz : 1 ≤ z)
    (hK : ∀ p : ℕ, p.Prime → p ∣ P → 0 < K p ∧ K p < p) : SelbergSieve where
  support := P.divisors
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights d := ((range N).filter (fun n => (F n).gcd P = d)).card
  weights_nonneg _ := by positivity
  totalMass := N
  nu := residueDensity K
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp hd := by
    rw [residueDensity_prime hp]
    exact div_pos (by exact_mod_cast (hK p hp hd).1) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime p hp hd := by
    rw [residueDensity_prime hp]
    apply (div_lt_one (by exact_mod_cast hp.pos)).2
    exact_mod_cast (hK p hp hd).2
  level := z
  one_le_level := hz

theorem gcd_in_divisors {P : ℕ} (hP : Squarefree P) (n : ℕ) :
    n.gcd P ∈ P.divisors :=
  Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hP.ne_zero⟩

theorem intervalSieve_multSum (F K : ℕ → ℕ) (N P : ℕ) (z : ℝ)
    (hP : Squarefree P) (hz : 1 ≤ z) (hK)
    {d : ℕ} (hd : d ∣ P) :
    (intervalSieve F K N P z hP hz hK).multSum d =
      ((range N).filter (fun n => d ∣ F n)).card := by
  classical
  unfold BoundingSieve.multSum
  change (∑ k ∈ P.divisors, if d ∣ k then
    (((range N).filter (fun n => (F n).gcd P = k)).card : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  have hfilter (k : ℕ) (hk : k ∈ P.divisors.filter (fun k => d ∣ k)) :
      ((range N).filter (fun n => (F n).gcd P = k)) =
        (((range N).filter (fun n => d ∣ F n)).filter (fun n => (F n).gcd P = k)) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hn,he⟩
      exact ⟨⟨hn,((Finset.mem_filter.mp hk).2.trans (he ▸ Nat.gcd_dvd_left (F n) P))⟩,he⟩
    · rintro ⟨⟨hn,_⟩,he⟩
      exact ⟨hn,he⟩
  have hmap (n : ℕ) (hn : n ∈ (range N).filter (fun n => d ∣ F n)) :
      (F n).gcd P ∈ P.divisors.filter (fun k => d ∣ k) :=
    Finset.mem_filter.mpr ⟨gcd_in_divisors hP _, Nat.dvd_gcd (Finset.mem_filter.mp hn).2 hd⟩
  apply Eq.trans (Finset.sum_congr rfl (fun k hk => by rw [hfilter k hk]))
  norm_cast
  exact (Finset.card_eq_sum_card_fiberwise hmap).symm

theorem intervalSieve_siftedSum (F K : ℕ → ℕ) (N P : ℕ) (z : ℝ)
    (hP : Squarefree P) (hz : 1 ≤ z) (hK) :
    (intervalSieve F K N P z hP hz hK).siftedSum =
      ((range N).filter (fun n => P.Coprime (F n))).card := by
  classical
  unfold BoundingSieve.siftedSum
  change (∑ k ∈ P.divisors, if P.Coprime k then
    (((range N).filter (fun n => (F n).gcd P = k)).card : ℝ) else 0) = _
  have hfilter : P.divisors.filter (fun k => P.Coprime k) = {1} := by
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · intro ⟨⟨hk,_⟩,hc⟩
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_right hk] at hc
      exact hc
    · rintro rfl
      exact ⟨⟨one_dvd _,hP.ne_zero⟩,Nat.coprime_one_right _⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_singleton]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext n
  simp only [Finset.mem_filter, Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm P]

end OMA.Erdos946

namespace OMA.Erdos946

open Finset

theorem nat_quotient_roundoff (N d : ℕ) (hd : 0 < d) :
    ((N/d : ℕ) : ℝ) ≤ N / d ∧
      (N : ℝ) / d < ((N/d : ℕ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  · apply (div_lt_iff₀ hdR).mpr
    have h := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d))
    exact_mod_cast h

theorem modEq_card_roundoff (N d a : ℕ) (hd : 0 < d) :
    |((Finset.range N).filter (fun n => n ≡ a [MOD d])).card - ((N : ℝ) / d)| ≤ 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card N hd a]
  have h := nat_quotient_roundoff N d hd
  push_cast
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [h.1,h.2]

/-- A union of residue classes in a finite interval has rounding error at most
    the number of classes. -/
theorem residues_roundoff (R : Finset ℕ) {N d : ℕ} (hd : 0 < d)
    (hR : R ⊆ Finset.range d) :
    |(((Finset.range N).filter (fun n => n % d ∈ R)).card : ℝ) -
       (R.card : ℝ) * ((N : ℝ) / d)| ≤ R.card := by
  have hmap (n : ℕ) (hn : n ∈ (range N).filter (fun n => n%d ∈ R)) : n%d ∈ R :=
    (Finset.mem_filter.mp hn).2
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hterm (a : ℕ) (ha : a ∈ R) :
      ((range N).filter (fun n => n%d ∈ R) |>.filter (fun n => n%d = a)) =
        (range N).filter (fun n => n ≡ a [MOD d]) := by
    ext n
    have hd' : a < d := Finset.mem_range.mp (hR ha)
    simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hd']
    exact ⟨fun ⟨⟨hn,_⟩,he⟩ => ⟨hn,he⟩, fun ⟨hn,he⟩ => ⟨⟨hn,he.symm ▸ ha⟩,he⟩⟩
  rw [hcard]
  push_cast
  have hconst : (R.card : ℝ) * ((N : ℝ) / d) = ∑ _ ∈ R, (N : ℝ) / d := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hconst, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h := Finset.sum_le_sum (s := R)
    (g := fun _ => (1 : ℝ)) (f := fun a => |(((range N).filter (fun n => n%d ∈ R) |>.filter
      (fun n => n%d = a)).card : ℝ) - (N : ℝ) / d|) (fun a ha => by
        rw [hterm a ha]
        exact modEq_card_roundoff N d a hd)
  simpa using h

theorem intervalSieve_abs_rem_le (F K : ℕ → ℕ) (N P : ℕ) (z : ℝ)
    (hP : Squarefree P) (hz : 1 ≤ z) (hK)
    {d : ℕ} (hd : d ∣ P) (R : Finset ℕ) (hR : R ⊆ Finset.range d)
    (hclasses : ∀ n : ℕ, d ∣ F n ↔ n % d ∈ R)
    (hRcard : R.card = ∏ p ∈ d.primeFactors, K p) :
    |(intervalSieve F K N P z hP hz hK).rem d| ≤ R.card := by
  have hdsq := hP.squarefree_of_dvd hd
  rw [BoundingSieve.rem, intervalSieve_multSum _ _ _ _ _ _ _ _ hd]
  change |(((range N).filter (fun n => d ∣ F n)).card : ℝ) - residueDensity K d * N| ≤ _
  simp_rw [hclasses, residueDensity, ArithmeticFunction.prodPrimeFactors_apply hdsq.ne_zero]
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod, ← hRcard,
    Nat.prod_primeFactors_of_squarefree hdsq]
  have he : ((R.card : ℝ) / d) * N = (R.card : ℝ) * ((N : ℝ) / d) := by ring
  rw [he]
  exact residues_roundoff R (Nat.pos_of_ne_zero hdsq.ne_zero) hR

end OMA.Erdos946

namespace OMA.Erdos946

open Finset
open scoped Function

def residues (F : ℕ → ℕ) (d : ℕ) : Finset ℕ :=
  (range d).filter (fun n => d ∣ F n)

theorem prime_modEq_imp_modEq {a b d : ℕ} (hd : Squarefree d)
    (h : ∀ p ∈ d.primeFactors, a ≡ b [MOD p]) :
    a ≡ b [MOD d] := by
  have hcop : d.primeFactorsList.Pairwise Nat.Coprime :=
    hd.nodup_primeFactorsList.pairwise_of_forall_ne (fun x hx y hy hne =>
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactorsList hx)
        (Nat.prime_of_mem_primeFactorsList hy)).mpr hne)
  rw [← Nat.prod_primeFactorsList hd.ne_zero]
  exact (Nat.modEq_list_prod_iff hcop).mpr
    (fun i => h _ (List.mem_toFinset.mpr (List.get_mem ..)))

theorem dvd_iff_prime_dvd {n d : ℕ} (hd : Squarefree d) :
    d ∣ n ↔ ∀ p ∈ d.primeFactors, p ∣ n := by
  simp only [← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h p hp => h.of_dvd (Nat.dvd_of_mem_primeFactors hp),
    fun h => prime_modEq_imp_modEq hd h⟩

/-- Chinese remaindering identifies the allowed residue classes for a squarefree
    modulus with the independent choices for its prime factors. -/
theorem residues_card_crt (F : ℕ → ℕ)
    (hper : ∀ p a b : ℕ, a ≡ b [MOD p] → (p ∣ F a ↔ p ∣ F b))
    {d : ℕ} (hd : Squarefree d) :
    (residues F d).card = ∏ p ∈ d.primeFactors, (residues F p).card := by
  classical
  let P := d.primeFactors
  let R := Fintype.piFinset (fun p : P => residues F p.1)
  have hpos (p : ℕ) (hp : p ∈ P) : p ≠ 0 :=
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hcop : Set.Pairwise (P : Set ℕ) (Nat.Coprime on id) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hne
  let small (n : ℕ) (p : P) := n % p.val
  suffices hh : (residues F d).card = R.card by
    rw [hh]
    rw [Fintype.card_piFinset, ← Finset.prod_attach P (fun p => (residues F p).card)]
    rfl
  refine Finset.card_bij (fun n _ => small n) ?_ ?_ ?_
  · intro n hn
    apply Fintype.mem_piFinset.mpr
    intro p
    have h := ((dvd_iff_prime_dvd hd).mp (Finset.mem_filter.mp hn).2) p.1 p.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero (hpos p.1 p.2))),
      (hper p.1 n (n % p.1) (by simp [Nat.ModEq])).mp h⟩
  · intro a ha b hb he
    have hab := prime_modEq_imp_modEq hd (fun p hp => congrFun he ⟨p,hp⟩)
    exact hab.eq_of_lt_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
  · intro f hf
    let A := fun p => if h : p ∈ P then f ⟨p,h⟩ else 0
    let c := Nat.chineseRemainderOfFinset A id P hpos hcop
    have hc : c.val < d := by
      simpa [P, Nat.prod_primeFactors_of_squarefree hd] using
        (Nat.chineseRemainderOfFinset_lt_prod A id hpos hcop)
    have hmod (p : P) : c.val ≡ f p [MOD p.val] := by
      simpa [A] using c.property p.1 p.2
    have hf' := Fintype.mem_piFinset.mp hf
    refine ⟨c.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, ?_⟩, ?_⟩
    · apply (dvd_iff_prime_dvd hd).mpr
      intro p hp
      exact (hper p c.val (f ⟨p,hp⟩) (hmod ⟨p,hp⟩)).mpr
        (Finset.mem_filter.mp (hf' ⟨p,hp⟩)).2
    · funext p
      exact Eq.trans (hmod p : c.val % p.val = f p % p.val) (Nat.mod_eq_of_lt
        (Finset.mem_range.mp (Finset.mem_filter.mp (hf' p)).1))

end OMA.Erdos946

namespace OMA.Erdos946

open Finset

def linearPair (a b c e t : ℕ) : ℕ := (a*t+c)*(b*t+e)

theorem linearPair_periodic (a b c e p r s : ℕ) (h : r ≡ s [MOD p]) :
    p ∣ linearPair a b c e r ↔ p ∣ linearPair a b c e s := by
  have hh : linearPair a b c e r ≡ linearPair a b c e s [MOD p] :=
    ((h.mul_left a).add_right c).mul ((h.mul_left b).add_right e)
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h0 => hh.symm.trans h0, fun h0 => hh.trans h0⟩

/-- The unique root of a nonconstant linear polynomial modulo a prime. -/
theorem linear_root_nat {p a c : ℕ} (hp : p.Prime) (ha : ¬p ∣ a) :
    ∃ r : ℕ, r < p ∧ ∀ t : ℕ, t < p → (p ∣ a*t+c ↔ t = r) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let y : ZMod p := -(c : ZMod p) / a
  have ha' : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  refine ⟨y.val, ZMod.val_lt y, ?_⟩
  intro t ht
  have hy : ((y.val : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
  simp only [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_add]
  constructor
  · intro h
    have h' : (t : ZMod p) = y := by
      apply (eq_div_iff ha').mpr
      linear_combination h
    exact (ZMod.val_natCast_of_lt ht).symm.trans (congrArg ZMod.val h')
  · intro h
    rw [h,hy,show (a : ZMod p) * y = -(c : ZMod p) by dsimp [y]; field_simp]
    abel

/-- A pair of linear polynomials with determinant a unit has one or two
    roots modulo a prime, according as one or both coefficients are units. -/
theorem linearPair_residues_card {p a b c e : ℕ} (hp : p.Prime)
    (hdet : a*e + 1 = b*c ∨ b*c + 1 = a*e) :
    (residues (linearPair a b c e) p).card =
      if p ∣ a*b then 1 else 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hD : (a : ZMod p)*(e : ZMod p)+1 = (b : ZMod p)*(c : ZMod p) ∨
      (b : ZMod p)*(c : ZMod p)+1 = (a : ZMod p)*(e : ZMod p) := by
    rcases hdet with h | h
    · left
      simpa using congrArg (fun n : ℕ => (n : ZMod p)) h
    · right
      simpa using congrArg (fun n : ℕ => (n : ZMod p)) h
  have hdet' : (a : ZMod p)*(e : ZMod p) ≠ (b : ZMod p)*(c : ZMod p) := by
    intro h
    rcases hD with hh | hh <;> rw [h] at hh <;> exact one_ne_zero (add_left_cancel
      (show ((b : ZMod p)*(c : ZMod p))+1 = ((b : ZMod p)*(c : ZMod p))+0 from by simpa using hh))
  by_cases ha : p ∣ a
  · have ha' := (ZMod.natCast_eq_zero_iff a p).mpr ha
    have hbc : (b : ZMod p) * (c : ZMod p) ≠ 0 := by simpa [ha'] using hdet'.symm
    have hb : ¬p∣b := fun hb => hbc (by simp [(ZMod.natCast_eq_zero_iff b p).mpr hb])
    have hc : ¬p∣c := fun hc => hbc (by simp [(ZMod.natCast_eq_zero_iff c p).mpr hc])
    obtain ⟨r,hr,hroot⟩ := linear_root_nat hp hb (c := e)
    have hres : residues (linearPair a b c e) p = {r} := by
      ext t
      have hfirst : ¬p ∣ a*t+c := fun h => hc (by simpa using Nat.dvd_sub h (dvd_mul_of_dvd_left ha t))
      simp only [residues, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, linearPair,
        hp.dvd_mul, hfirst, false_or]
      exact ⟨fun ⟨ht,h⟩ => (hroot t ht).mp h, fun h => h ▸ ⟨hr,(hroot r hr).mpr rfl⟩⟩
    simp [hres,dvd_mul_of_dvd_left ha b]
  · by_cases hb : p ∣ b
    · have hb' := (ZMod.natCast_eq_zero_iff b p).mpr hb
      have hae : (a : ZMod p) * (e : ZMod p) ≠ 0 := by simpa [hb'] using hdet'
      have he : ¬p∣e := fun he => hae (by simp [(ZMod.natCast_eq_zero_iff e p).mpr he])
      obtain ⟨r,hr,hroot⟩ := linear_root_nat hp ha (c := c)
      have hres : residues (linearPair a b c e) p = {r} := by
        ext t
        have hsecond : ¬p ∣ b*t+e := fun h => he (by simpa using Nat.dvd_sub h (dvd_mul_of_dvd_left hb t))
        simp only [residues, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, linearPair,
          hp.dvd_mul, hsecond, or_false]
        exact ⟨fun ⟨ht,h⟩ => (hroot t ht).mp h, fun h => h ▸ ⟨hr,(hroot r hr).mpr rfl⟩⟩
      simp [hres,dvd_mul_of_dvd_right hb a]
    · obtain ⟨r,hr,hrroot⟩ := linear_root_nat hp ha (c := c)
      obtain ⟨s,hs,hsroot⟩ := linear_root_nat hp hb (c := e)
      have hrs : r ≠ s := by
        intro h
        have h1 := (ZMod.natCast_eq_zero_iff (a*r+c) p).mpr ((hrroot r hr).mpr rfl)
        have h2 := (ZMod.natCast_eq_zero_iff (b*r+e) p).mpr ((hsroot r hr).mpr h)
        push_cast at h1 h2
        exact hdet' (by linear_combination (a : ZMod p)*h2 - (b : ZMod p)*h1)
      have hres : residues (linearPair a b c e) p = {r,s} := by
        ext t
        simp only [residues, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton, linearPair, hp.dvd_mul]
        constructor
        · rintro ⟨ht,h|h⟩
          · exact Or.inl ((hrroot t ht).mp h)
          · exact Or.inr ((hsroot t ht).mp h)
        · rintro (h|h)
          · rw [h]; exact ⟨hr,Or.inl ((hrroot r hr).mpr rfl)⟩
          · rw [h]; exact ⟨hs,Or.inr ((hsroot s hs).mpr rfl)⟩
      simp [hres,hrs,hp.dvd_mul,ha,hb]

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real

/-- Divisors of a squarefree positive integer enumerate its subsets of primes. -/
theorem sum_divisors_prime_product {P : ℕ} (hP : Squarefree P)
    (g : ℕ → ℝ) :
    (∑ d ∈ P.divisors, ∏ p ∈ d.primeFactors, g p) =
      ∏ p ∈ P.primeFactors, (1 + g p) := by
  rw [Finset.prod_one_add]
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ (by simp)
  · intro d hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero)
  · intro d hd e he hex
    rw [← Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)),
      ← Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)), hex]
  · intro T hT
    have ht := Finset.mem_powerset.mp hT
    refine ⟨∏ p ∈ T, p, Nat.mem_divisors.mpr ⟨?_,hP.ne_zero⟩, ?_⟩
    · rw [← Nat.prod_primeFactors_of_squarefree hP]
      exact Finset.prod_dvd_prod_of_subset _ _ _ ht
    · exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))

/-- The upper sieve can use the full local Euler product whenever the
    omitted divisor weights are collectively at most half that product. -/
theorem selberg_product_lower_of_tail (s : SelbergSieve) (g : ℕ → ℝ)
    (hg : ∀ d ∈ s.prodPrimes.divisors, SelbergSieve.selbergTerms s.toBoundingSieve d =
      ∏ p ∈ d.primeFactors, g p)
    (htail : (∑ d ∈ s.prodPrimes.divisors,
      if (d : ℝ)^2 ≤ s.level then 0 else ∏ p ∈ d.primeFactors, g p) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 + g p)) / 2) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 + g p)) / 2 ≤ s.selbergBoundingSum := by
  unfold SelbergSieve.selbergBoundingSum
  have hsum := sum_divisors_prime_product s.prodPrimes_squarefree g
  have hsplit :
      (∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ)^2 ≤ s.level then SelbergSieve.selbergTerms s.toBoundingSieve d else 0) +
      (∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ)^2 ≤ s.level then 0 else ∏ p ∈ d.primeFactors, g p) =
      ∑ d ∈ s.prodPrimes.divisors, ∏ p ∈ d.primeFactors, g p := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hg d hd]
    split_ifs <;> simp
  linarith

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    Real.exp x - 1 ≤ 2 * x := by
  apply sub_le_iff_le_add.mpr
  refine (Real.exp_le_two_add_div_two_sub hx0 (by linarith)).trans ?_
  apply (div_le_iff₀ (by linarith : 0 < 2-x)).mpr
  nlinarith [mul_nonneg hx0 (show 0 ≤ 1-x by linarith)]

theorem selberg_terms_prime_product (s : SelbergSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    SelbergSieve.selbergTerms s.toBoundingSieve d =
      ∏ p ∈ d.primeFactors, s.nu p / (1 - s.nu p) := by
  rw [SelbergSieve.selbergTerms_apply, ← s.toBoundingSieve.prod_primeFactors_nu hd,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p hp => by ring

/-- The sieve denominator retains a positive fraction of the local Euler product
    when the sieve level is a fixed sufficiently large power of the prime cutoff. -/
theorem selberg_product_lower (s : SelbergSieve) {V : ℕ} (hV : 2 ≤ V)
    (hlevel : s.level = (V : ℝ)^128)
    (hP : s.prodPrimes.primeFactors ⊆ Nat.primesLE V)
    (hnu : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ 2/(p : ℝ)) :
    (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹) / 2 ≤
      s.selbergBoundingSum := by
  classical
  let P := s.prodPrimes
  let g := fun p => s.nu p / (1 - s.nu p)
  let t := (2 * Real.log (V : ℝ))⁻¹
  have hlog : 0 < Real.log (V : ℝ) := Real.log_pos (by exact_mod_cast hV)
  have ht : 0 < t := by positivity
  have hpos (p : ℕ) (hp : p ∈ P.primeFactors) : 0 < s.nu p :=
    s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hlt (p : ℕ) (hp : p ∈ P.primeFactors) : s.nu p < 1 :=
    s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hg (p : ℕ) (hp : p ∈ P.primeFactors) : 0 ≤ g p :=
    div_nonneg (hpos p hp).le (sub_nonneg.mpr (hlt p hp).le)
  have hiden (p : ℕ) (hp : p ∈ P.primeFactors) : 1+g p = (1-s.nu p)⁻¹ := by
    dsimp [g]
    field_simp [(sub_pos.mpr (hlt p hp)).ne']
    ring
  rw [show (∏ p ∈ P.primeFactors, (1-s.nu p)⁻¹) = ∏ p ∈ P.primeFactors, (1+g p) from
    Finset.prod_congr rfl fun p hp => (hiden p hp).symm]
  apply selberg_product_lower_of_tail s g
  · intro d hd
    exact selberg_terms_prime_product s (Nat.dvd_of_mem_divisors hd)
  let u := fun p : ℕ => t * Real.log (p : ℝ)
  have hu (p : ℕ) (hp : p ∈ P.primeFactors) : 0 ≤ u p ∧ u p ≤ 1/2 := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have hpV : (p : ℝ) ≤ V := by exact_mod_cast (Nat.mem_primesLE.mp (hP hp)).1
    refine ⟨mul_nonneg ht.le (Real.log_nonneg hpR), ?_⟩
    calc
      _ ≤ t * Real.log V := mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith) hpV) ht.le
      _ = _ := by dsimp [t]; field_simp
  have hloc (p : ℕ) (hp : p ∈ P.primeFactors) :
      1+g p * Real.exp (u p) ≤ (1+g p) * Real.exp (2 * s.nu p * u p) := by
    have hgap : 0 < 1-s.nu p := sub_pos.mpr (hlt p hp)
    have hid : 1 + g p * Real.exp (u p) =
        (1+g p) * (1+s.nu p * (Real.exp (u p)-1)) := by
      dsimp [g]
      field_simp [hgap.ne']
      ring
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ (by linarith [hg p hp])
    refine (show 1+s.nu p*(Real.exp (u p)-1) ≤ 2*s.nu p*u p+1 by
      nlinarith only [mul_le_mul_of_nonneg_left
        (exp_sub_one_le_two_mul (hu p hp).1 (hu p hp).2) (hpos p hp).le]).trans
      (Real.add_one_le_exp _)
  have htot : ∑ p ∈ P.primeFactors, 2*s.nu p*u p ≤ 4 := by
    calc
      _ ≤ ∑ p ∈ P.primeFactors, (4*t) * (Real.log (p : ℝ) / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi := mul_le_mul_of_nonneg_left (hnu p hp) (show 0 ≤ 2*u p by linarith [(hu p hp).1])
        dsimp [u] at hi
        convert hi using 1 <;> ring
      _ ≤ ∑ p ∈ Nat.primesLE V, (4*t) * (Real.log (p : ℝ) / p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hP
        intro p hp _
        have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
        exact mul_nonneg (by positivity) (div_nonneg (Real.log_nonneg hpR) (by positivity))
      _ ≤ (4*t) * (2*Real.log V) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_log_prime_div_le V) (by positivity)
      _ = 4 := by dsimp [t]; field_simp
  have hexp : ∏ p ∈ P.primeFactors, (1+g p * Real.exp (u p)) ≤
      (∏ p ∈ P.primeFactors, (1+g p)) * Real.exp 4 := by
    have h := Finset.prod_le_prod
      (fun p hp => add_nonneg zero_le_one (mul_nonneg (hg p hp) (Real.exp_pos _).le)) hloc
    rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htot)
      (Finset.prod_nonneg (fun p hp => by linarith [hg p hp])))
  have h32 : t * (64 * Real.log (V : ℝ)) = 32 := by dsimp [t]; field_simp; norm_num
  have hterm (d : ℕ) (hd : d ∈ P.divisors) :
      (if (d : ℝ)^2 ≤ s.level then 0 else ∏ p ∈ d.primeFactors, g p) ≤
      Real.exp (-32) * ∏ p ∈ d.primeFactors, (g p * Real.exp (u p)) := by
    have hdsq := s.prodPrimes_squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    have dsub := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) s.prodPrimes_squarefree.ne_zero
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    have hnon : 0 ≤ ∏ p ∈ d.primeFactors, g p :=
      Finset.prod_nonneg fun p hp => hg p (dsub hp)
    split_ifs with hdlev
    · positivity
    · rw [show Real.exp (-32) * ((∏ p ∈ d.primeFactors, g p) *
          Real.exp (∑ p ∈ d.primeFactors, u p)) =
          (∏ p ∈ d.primeFactors, g p) * Real.exp ((∑ p ∈ d.primeFactors, u p)-32) by
        rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]; ring]
      conv_lhs => rw [← mul_one (∏ p ∈ d.primeFactors, g p)]
      apply mul_le_mul_of_nonneg_left _ hnon
      rw [Real.one_le_exp_iff]
      have hpr : ∑ p ∈ d.primeFactors, Real.log (p : ℝ) = Real.log d := by
        rw [← Real.log_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdsq]
        exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hdsq.ne_zero
      have hVpos : (0 : ℝ) < V := by positivity
      have hdlog : 64*Real.log (V : ℝ) ≤ Real.log d := by
        have H := Real.log_le_log (pow_pos hVpos 128) (lt_of_not_ge (hlevel ▸ hdlev)).le
        rw [Real.log_pow, Real.log_pow] at H
        norm_num at H
        linarith
      dsimp [u]
      rw [← Finset.mul_sum, hpr]
      linarith only [mul_le_mul_of_nonneg_left hdlog ht.le,h32]
  calc
    _ ≤ ∑ d ∈ P.divisors, Real.exp (-32) * ∏ p ∈ d.primeFactors, (g p * Real.exp (u p)) :=
      Finset.sum_le_sum hterm
    _ = Real.exp (-32) * ∏ p ∈ P.primeFactors, (1+g p * Real.exp (u p)) := by
      rw [← Finset.mul_sum, sum_divisors_prime_product s.prodPrimes_squarefree]
    _ ≤ Real.exp (-32) * ((∏ p ∈ P.primeFactors, (1+g p)) * Real.exp 4) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← mul_assoc, mul_comm (Real.exp (-32)), mul_assoc, ← Real.exp_add]
      have he : Real.exp ((-32) + 4) ≤ 1/2 := by
        have h := Real.add_one_le_exp 28
        rw [show ((-32) + 4 : ℝ) = -28 by norm_num, Real.exp_neg]
        apply (inv_le_comm₀ (Real.exp_pos _) (by positivity)).2
        norm_num at *
        linarith
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left he
        (Finset.prod_nonneg (fun p hp => by linarith [hg p hp]))

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

noncomputable def reciprocalTotient (n : ℕ) : ℝ := (n.totient : ℝ)⁻¹

def Squarefull (n : ℕ) : Prop := ∀ p : ℕ, n.factorization p ≠ 1

noncomputable def squarefreePartOne (n : ℕ) : ℕ :=
  (n.factorization.filter (fun p => n.factorization p = 1)).prod (· ^ ·)

noncomputable def squarefullPart (n : ℕ) : ℕ :=
  (n.factorization.filter (fun p => n.factorization p ≠ 1)).prod (· ^ ·)

theorem parts_factorization (n : ℕ) :
    (squarefreePartOne n).factorization = n.factorization.filter (fun p => n.factorization p = 1) ∧
    (squarefullPart n).factorization = n.factorization.filter (fun p => n.factorization p ≠ 1) := by
  classical
  constructor <;> apply Nat.factorization_prod_pow_eq_self_of_le_factorization (n := n)
  · intro p; rw [Finsupp.filter_apply]; split_ifs <;> omega
  · intro p; rw [Finsupp.filter_apply]; split_ifs <;> omega

theorem parts_ne_zero (n : ℕ) : squarefreePartOne n ≠ 0 ∧ squarefullPart n ≠ 0 := by
  classical
  exact ⟨Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero⟩

theorem squarefree_squarefull_parts {n : ℕ} (hn : n ≠ 0) :
    Squarefree (squarefreePartOne n) ∧ Squarefull (squarefullPart n) ∧
    (squarefreePartOne n).Coprime (squarefullPart n) ∧
    squarefreePartOne n * squarefullPart n = n := by
  classical
  have hf := parts_factorization n
  have hnz := parts_ne_zero n
  refine ⟨?_,?_,?_,?_⟩
  · apply Nat.squarefree_of_factorization_le_one hnz.1
    intro p
    rw [hf.1,Finsupp.filter_apply]
    split_ifs <;> omega
  · intro p
    rw [hf.2,Finsupp.filter_apply]
    split_ifs <;> omega
  · by_contra h
    obtain ⟨p,hp,ha,hb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have ha' := (hp.dvd_iff_one_le_factorization hnz.1).mp ha
    have hb' := (hp.dvd_iff_one_le_factorization hnz.2).mp hb
    simp only [hf.1,hf.2,Finsupp.filter_apply] at ha' hb'
    split_ifs at ha' hb' <;> omega
  · apply Nat.eq_of_factorization_eq (mul_ne_zero hnz.1 hnz.2) hn
    intro p
    rw [Nat.factorization_mul hnz.1 hnz.2,Finsupp.add_apply,hf.1,hf.2]
    simp only [Finsupp.filter_apply]
    split_ifs <;> omega

theorem reciprocalTotient_nonneg (n : ℕ) : 0 ≤ reciprocalTotient n := by
  unfold reciprocalTotient
  positivity

theorem reciprocalTotient_mul {a b : ℕ} (hab : a.Coprime b) :
    reciprocalTotient (a*b) = reciprocalTotient a * reciprocalTotient b := by
  simp only [reciprocalTotient,Nat.totient_mul hab,Nat.cast_mul,mul_inv]

theorem reciprocalTotient_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    reciprocalTotient (p^e) = ((1-(p : ℝ)⁻¹) * (p : ℝ)^e)⁻¹ := by
  have hcast : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by simpa using Nat.cast_sub (R := ℝ) hp.one_lt.le
  rw [reciprocalTotient,Nat.totient_prime_pow hp he,Nat.cast_mul,Nat.cast_pow,hcast]
  congr 1
  have h : e = e-1+1 := by omega
  conv_rhs => rw [h,pow_succ]
  field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero] <;> ring

theorem reciprocalTotient_factorization {n : ℕ} (hn : n ≠ 0)
    {P : Finset ℕ} (hP : n.primeFactors ⊆ P) :
    reciprocalTotient n = ∏ p ∈ P, reciprocalTotient (p ^ n.factorization p) := by
  unfold reciprocalTotient
  rw [Nat.multiplicative_factorization Nat.totient (@Nat.totient_mul) Nat.totient_one hn,
      Finsupp.prod_of_support_subset _ hP _ (by intros; simp), Nat.cast_prod]
  simp [Finset.prod_inv_distrib]

open scoped Classical in
theorem sum_squarefull_reciprocalTotient_le (X V : ℕ) :
    (∑ n ∈ (Icc 1 X).filter (fun n => Squarefull n ∧ n.primeFactors ⊆ Nat.primesLE V),
      reciprocalTotient n) ≤ Real.exp 4 := by
  classical
  let P := Nat.primesLE V
  let S := (Icc 1 X).filter (fun n => Squarefull n ∧ n.primeFactors ⊆ P)
  let w := fun p e : ℕ => if e = 1 then 0 else reciprocalTotient (p^e)
  have hflags (n : ℕ) (hn : n ∈ S) :
      n ≠ 0 ∧ n.primeFactors ⊆ P ∧ ∀ p, n.factorization p ≤ X := by
    obtain ⟨hnx,_,hsub⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1,hx⟩ := Finset.mem_Icc.mp hnx
    have hn0 : n ≠ 0 := by omega
    exact ⟨hn0,hsub,fun p => (Nat.factorization_lt p hn0).le.trans hx⟩
  have hterm (n : ℕ) (hn : n ∈ S) : reciprocalTotient n = ∏ p ∈ P, w p (n.factorization p) := by
    rw [reciprocalTotient_factorization (hflags n hn).1 (hflags n hn).2.1]
    exact Finset.prod_congr rfl fun p hp => by simp [w,(Finset.mem_filter.mp hn).2.1 p]
  have hmain := sum_factorization_weights_le S P X w (fun p e => by
    unfold w; split_ifs <;> simp [reciprocalTotient_nonneg]) hflags
  have hlocal (p : ℕ) (hp : p ∈ P) : (∑ e ∈ range (X+1), w p e) ≤ 1+4/((p : ℝ)^2) := by
    have hpr := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hinv : (p : ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; gcongr
    have hh (e : ℕ) : w p (e+2) ≤ 2 * (p : ℝ)⁻¹ ^ (e+2) := by
      simp only [w, show e+2 ≠ 1 by omega, if_false]
      have hgap : (1/2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by linarith
      rw [reciprocalTotient_prime_pow hpr (by omega), mul_inv, inv_pow]
      exact mul_le_mul_of_nonneg_right
        (by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1/2) hgap) (by positivity)
    cases X with
    | zero => simp [w,reciprocalTotient]; positivity
    | succ X =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [w,zero_ne_one,if_false,if_true,pow_zero,reciprocalTotient,Nat.totient_one,
        Nat.cast_one,inv_one,add_zero]
      have hgeom : (∑ e ∈ range X, 2 * (p : ℝ)⁻¹ ^ (e+2)) ≤ 4 / (p : ℝ)^2 := by
        calc
          _ = (2 * (p : ℝ)⁻¹ ^ 2) * ∑ e ∈ range X, (p : ℝ)⁻¹ ^ e := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            rw [pow_add]
            ring
          _ ≤ (2 * (p : ℝ)⁻¹ ^ 2) * (1 - (p : ℝ)⁻¹)⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← tsum_geometric_of_lt_one (by positivity) (by linarith : (p : ℝ)⁻¹ < 1)]
            exact (summable_geometric_of_lt_one (by positivity)
              (by linarith : (p : ℝ)⁻¹ < 1)).sum_le_tsum _ (by intros; positivity)
          _ ≤ (2 * (p : ℝ)⁻¹ ^ 2) * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have h := inv_anti₀ (by norm_num : (0:ℝ)<1/2) (by linarith : (1/2:ℝ) ≤ 1-(p:ℝ)⁻¹)
            norm_num at h ⊢
            exact h
          _ = _ := by ring
      have hh' : (∑ e ∈ range X, w p (e+2)) ≤ 4 / (p : ℝ)^2 :=
        (Finset.sum_le_sum fun e _ => hh e).trans hgeom
      simpa [w,show ∀ e : ℕ, e + 1 + 1 ≠ 1 by omega,reciprocalTotient,add_assoc,add_comm,
        add_left_comm] using add_le_add_right hh' 1
  calc
    _ = ∑ n ∈ S, ∏ p ∈ P, w p (n.factorization p) := Finset.sum_congr rfl hterm
    _ ≤ ∏ p ∈ P, ∑ e ∈ range (X+1), w p e := hmain
    _ ≤ ∏ p ∈ P, (1+4/((p : ℝ)^2)) :=
      Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun e _ => by
        unfold w; split_ifs <;> simp [reciprocalTotient_nonneg]) hlocal
    _ ≤ Real.exp (∑ p ∈ P, 4 / ((p : ℝ)^2)) :=
      Real.prod_one_add_le_exp_sum P (by intros; positivity)
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      have hsub : P ⊆ Icc 2 V := fun p hp =>
        Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.two_le,(Nat.mem_primesLE.mp hp).1⟩
      have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 4 / ((p : ℝ)^2))
        hsub (by intros; positivity)
      apply h.trans
      have hrewrite : (∑ p ∈ Icc 2 V, 4 / ((p : ℝ)^2)) = 4 * ∑ p ∈ Icc 2 V, (1 : ℝ)/(p*p) := by
        rw [Finset.mul_sum]
        simp only [sq,mul_one_div]
      rw [hrewrite]
      exact (mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le (X := V) (Y := 2) (by decide)) (by norm_num)).trans (by norm_num)

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

noncomputable def singlePrimeWeight (p : ℕ) : ℝ := ((p - 1 : ℕ) : ℝ)⁻¹

theorem singlePrimeWeight_nonneg (p : ℕ) : 0 ≤ singlePrimeWeight p := by
  unfold singlePrimeWeight
  positivity

theorem sum_singlePrimeWeight_le {V : ℕ} (hV : 2 ≤ V) :
    (∑ p ∈ Nat.primesLE V, singlePrimeWeight p) ≤ Real.log (1+Real.log V) + 6 := by
  let P := Nat.primesLE V
  have hmain : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ Real.log (1+Real.log V)+4 := by
    have hpos (p : ℕ) (hp : p ∈ P) : (0:ℝ) < 1-(p:ℝ)⁻¹ := by
      apply sub_pos.mpr
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hc := Real.log_le_log (Finset.prod_pos (fun p hp => inv_pos.mpr (hpos p hp)))
      (primeEulerProduct_le hV)
    have hpV : (1:ℝ) < V := by exact_mod_cast hV
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_prod] at hc
    · have hbound : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, Real.log ((1-(p:ℝ)⁻¹)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Real.log_inv]
        linarith [Real.log_le_sub_one_of_pos (hpos p hp)]
      linarith
    · exact fun p hp => (inv_pos.mpr (hpos p hp)).ne'
  have htail : (∑ p ∈ P, 2 / ((p : ℝ)^2)) ≤ 2 := by
    have hsub : P ⊆ Icc 2 V := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.two_le,(Nat.mem_primesLE.mp hp).1⟩
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 2 / ((p : ℝ)^2))
      hsub (by intros; positivity)
    refine h.trans ?_
    have hrewrite : (∑ p ∈ Icc 2 V, 2 / (p : ℝ)^2) =
        2 * ∑ p ∈ Icc 2 V, (1 : ℝ)/(p*p) := by
      rw [Finset.mul_sum]
      simp only [sq,mul_one_div]
    rw [hrewrite]
    have hh := mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le (X := V) (Y := 2) (by decide))
      (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hc : (∑ p ∈ P, singlePrimeWeight p) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) + ∑ p ∈ P, 2 / ((p : ℝ)^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hp1 : (0:ℝ) < (p:ℝ)-1 := by linarith
    rw [singlePrimeWeight, Nat.cast_sub (by exact_mod_cast (show (1:ℝ) ≤ p by linarith)), Nat.cast_one]
    field_simp [hp0.ne',hp1.ne']
    nlinarith
  linarith

theorem reciprocalTotient_squarefree {n : ℕ} (hn : Squarefree n) :
    reciprocalTotient n = ∏ p ∈ n.primeFactors, singlePrimeWeight p := by
  rw [reciprocalTotient_factorization hn.ne_zero Finset.Subset.rfl]
  apply Finset.prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  rw [Nat.factorization_eq_one_of_squarefree hn hpr (Nat.dvd_of_mem_primeFactors hp),
    pow_one, reciprocalTotient, Nat.totient_prime hpr]
  rfl

theorem sum_squarefree_fixed_card {X V k : ℕ} (hV : 2 ≤ V)
    (hbig : 1 < Real.log (V : ℝ)) :
    (∑ n ∈ (Icc 1 X).filter (fun n => Squarefree n ∧ n.primeFactors ⊆ Nat.primesLE V ∧
        n.primeFactors.card = k), reciprocalTotient n) ≤
      (2 * Real.exp 6) * Real.log V / Real.sqrt (Real.log (Real.log V)) := by
  classical
  let P := Nat.primesLE V
  let S := (Icc 1 X).filter (fun n => Squarefree n ∧ n.primeFactors ⊆ P ∧
    n.primeFactors.card = k)
  let z := Real.log (1+Real.log V)+6
  have hz : 2 ≤ z := by dsimp [z]; linarith [Real.log_nonneg (by linarith : 1 ≤ 1+Real.log (V:ℝ))]
  have hsum := sum_singlePrimeWeight_le hV
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro a ha b hb h
    have ha' := (Finset.mem_filter.mp ha).2.1
    have hb' := (Finset.mem_filter.mp hb).2.1
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb',h]
  have hsub : S.image Nat.primeFactors ⊆ P.powersetCard k := by
    intro a ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_powersetCard.mpr (Finset.mem_filter.mp hn).2.2
  have hlog : 0 < Real.log (V : ℝ) := by linarith
  have hlogs : 0 < Real.log (Real.log (V : ℝ)) := Real.log_pos hbig
  have hfac : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  calc
    _ = ∑ n ∈ S, ∏ p ∈ n.primeFactors, singlePrimeWeight p := by
      exact Finset.sum_congr rfl fun n hn => reciprocalTotient_squarefree (Finset.mem_filter.mp hn).2.1
    _ = ∑ T ∈ S.image Nat.primeFactors, ∏ p ∈ T, singlePrimeWeight p :=
      (Finset.sum_image (f := fun T => ∏ p ∈ T, singlePrimeWeight p) hinj).symm
    _ ≤ ∑ T ∈ P.powersetCard k, ∏ p ∈ T, singlePrimeWeight p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun T hT _ => Finset.prod_nonneg fun p hp => singlePrimeWeight_nonneg p)
    _ ≤ poissonTerm z k := by
      apply (le_div_iff₀ hfac).mpr
      refine (sum_powersetCard_prod_le P k singlePrimeWeight
        (fun p _ => singlePrimeWeight_nonneg p)).trans ?_
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => singlePrimeWeight_nonneg p) hsum k
    _ ≤ Real.exp z / Real.sqrt z := poissonTerm_le hz k
    _ ≤ _ := by
      have he : Real.exp z ≤ 2 * Real.exp 6 * Real.log V := by
        dsimp [z]
        rw [Real.exp_add, Real.exp_log (by linarith : 0 < 1+Real.log (V:ℝ))]
        nlinarith [Real.exp_pos 6]
      have hs : Real.sqrt (Real.log (Real.log (V : ℝ))) ≤ Real.sqrt z := by
        apply Real.sqrt_le_sqrt
        dsimp [z]
        linarith [Real.log_le_log hlog (show Real.log (V:ℝ) ≤ 1 + Real.log (V:ℝ) by linarith)]
      exact div_le_div₀ (by positivity) he (Real.sqrt_pos.mpr hlogs) hs

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

open scoped Classical in
theorem sum_valuation_reciprocalTotient_le {X V j : ℕ} (hV : 2 ≤ V)
    (hbig : 1 < Real.log (V : ℝ)) :
    (∑ n ∈ (Icc 1 X).filter (fun n => n.primeFactors ⊆ Nat.primesLE V ∧ divisorValuation n = j),
        reciprocalTotient n) ≤
      (2 * Real.exp 10) * Real.log V / Real.sqrt (Real.log (Real.log V)) := by
  classical
  let P := Nat.primesLE V
  let S := (Icc 1 X).filter (fun n => n.primeFactors ⊆ P ∧ divisorValuation n = j)
  let T := (Icc 1 X).filter (fun n => Squarefull n ∧ n.primeFactors ⊆ P)
  let U (b : ℕ) := (Icc 1 X).filter (fun n => Squarefree n ∧ n.primeFactors ⊆ P ∧
    n.primeFactors.card = j - divisorValuation b)
  let F (n : ℕ) : Σ b : ℕ, ℕ := ⟨squarefullPart n,squarefreePartOne n⟩
  let w (t : Σ b : ℕ, ℕ) := reciprocalTotient t.1 * reciprocalTotient t.2
  have hpair (n : ℕ) (hn : n ∈ S) :
      F n ∈ T.sigma U ∧ reciprocalTotient n = w (F n) ∧
        (F n).2 * (F n).1 = n := by
    obtain ⟨hnX,hsub,hval⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnX).1
    obtain ⟨ha,hb,hcop,hab⟩ := squarefree_squarefull_parts hnpos.ne'
    have hnz := parts_ne_zero n
    have hadvd : squarefreePartOne n ∣ n := ⟨squarefullPart n,hab.symm⟩
    have hbdvd : squarefullPart n ∣ n := ⟨squarefreePartOne n,by rw [mul_comm,hab]⟩
    have haX : squarefreePartOne n ∈ Icc 1 X := Finset.mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero hnz.1,(Nat.le_of_dvd hnpos hadvd).trans (Finset.mem_Icc.mp hnX).2⟩
    have hbX : squarefullPart n ∈ Icc 1 X := Finset.mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero hnz.2,(Nat.le_of_dvd hnpos hbdvd).trans (Finset.mem_Icc.mp hnX).2⟩
    have hv := divisorValuation_mul hnz.1 hnz.2 hcop
    rw [hab, hval, divisorValuation_squarefree ha] at hv
    refine ⟨Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hbX,hb,
        (Nat.primeFactors_mono hbdvd hnpos.ne').trans hsub⟩,
      Finset.mem_filter.mpr ⟨haX,ha,(Nat.primeFactors_mono hadvd hnpos.ne').trans hsub,by dsimp [F]; omega⟩⟩,?_,hab⟩
    change reciprocalTotient n = reciprocalTotient (squarefullPart n) * reciprocalTotient (squarefreePartOne n)
    rw [mul_comm, ← reciprocalTotient_mul hcop,hab]
  have hinj : Set.InjOn F S := by
    intro a ha b hb h
    rw [← (hpair a ha).2.2, h, (hpair b hb).2.2]
  have hsub : S.image F ⊆ T.sigma U := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    exact (hpair n hn).1
  let C := (2 * Real.exp 6) * Real.log V / Real.sqrt (Real.log (Real.log V))
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Real.log_pos (by exact_mod_cast hV : (1:ℝ) < V)
    positivity
  calc
    _ = ∑ n ∈ S, w (F n) := Finset.sum_congr rfl fun n hn => (hpair n hn).2.1
    _ = ∑ t ∈ S.image F, w t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ T.sigma U, w t := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t ht _ => mul_nonneg (reciprocalTotient_nonneg _) (reciprocalTotient_nonneg _))
    _ = ∑ b ∈ T, reciprocalTotient b * ∑ a ∈ U b, reciprocalTotient a := by
      rw [Finset.sum_sigma T U w]
      apply Finset.sum_congr rfl
      intro b hb
      simp [w,Finset.mul_sum]
    _ ≤ ∑ b ∈ T, reciprocalTotient b * C := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (sum_squarefree_fixed_card hV hbig) (reciprocalTotient_nonneg _)
    _ = (∑ b ∈ T, reciprocalTotient b) * C := (Finset.sum_mul ..).symm
    _ ≤ Real.exp 4 * C := mul_le_mul_of_nonneg_right (sum_squarefull_reciprocalTotient_le _ _) hC
    _ = _ := by
      dsimp [C]
      rw [show (10:ℝ) = 4+6 by norm_num,Real.exp_add]
      ring

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.omega

def oddPrimesLE (V : ℕ) := (Nat.primesLE V).erase 2
def oddPrimorial (V : ℕ) := ∏ p ∈ oddPrimesLE V, p
def pairRootCount (a b p : ℕ) : ℕ := if p ∣ a*b then 1 else 2

theorem oddPrimorial_sqfree (V : ℕ) : Squarefree (oddPrimorial V) := by
  apply (squarefree_primorial V).squarefree_of_dvd
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)

theorem oddPrimorial_factors (V : ℕ) :
    (oddPrimorial V).primeFactors = oddPrimesLE V :=
  Nat.primeFactors_prod fun p hp => (Nat.mem_primesLE.mp (Finset.mem_of_mem_erase hp)).2

theorem pairRootCount_bounds (a b V : ℕ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ oddPrimorial V) : 0 < pairRootCount a b p ∧ pairRootCount a b p < p := by
  have hpm := Nat.mem_primeFactors.mpr ⟨hp,hd,(oddPrimorial_sqfree V).ne_zero⟩
  rw [oddPrimorial_factors] at hpm
  have h2 := (Finset.mem_erase.mp hpm).1
  have hp2 := hp.two_le
  unfold pairRootCount
  split_ifs <;> omega

noncomputable def primeEulerFactor (p : ℕ) : ℝ := 1-(p : ℝ)⁻¹

theorem primeEulerFactor_bounds {p : ℕ} (hp : p.Prime) :
    0 < primeEulerFactor p ∧ primeEulerFactor p ≤ 1 := by
  unfold primeEulerFactor
  constructor
  · apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  · exact sub_le_self _ (by positivity)

theorem totient_cast_euler (n : ℕ) :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, primeEulerFactor p := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simpa [primeEulerFactor,Rat.cast_sum,Rat.cast_prod] using h

theorem pairEulerProduct_ge {a b V : ℕ} (hab : (a*b) ≠ 0) (hV : 2 ≤ V) :
    (Real.log (V : ℝ))^2 * ((a*b).totient : ℝ) / ((a*b : ℕ) : ℝ) / 4 ≤
      ∏ p ∈ oddPrimesLE V, (1 - (pairRootCount a b p : ℝ) / p)⁻¹ := by
  let P := oddPrimesLE V
  let α := primeEulerFactor
  let δ := fun p : ℕ => if p ∣ a*b then α p else 1
  have hp (p : ℕ) (h : p ∈ P) : p.Prime ∧ 3 ≤ p := by
    obtain ⟨hn2,hm⟩ := Finset.mem_erase.mp h
    have hp := (Nat.mem_primesLE.mp hm).2
    have hp2 := hp.two_le
    exact ⟨hp,by omega⟩
  have hα (p : ℕ) (h : p ∈ P) : 0 < α p ∧ α p ≤ 1 := primeEulerFactor_bounds (hp p h).1
  have hprod :
      (∏ p ∈ P, (α p)⁻¹)^2 * ∏ p ∈ P, δ p ≤
        ∏ p ∈ P, (1 - (pairRootCount a b p : ℝ) / p)⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p h; dsimp [δ]; split_ifs <;> positivity [(hα p h).1]
    · intro p h
      have hpR : (3:ℝ) ≤ p := by exact_mod_cast (hp p h).2
      have hp0 : (0:ℝ)<p := by linarith
      by_cases hpab : p ∣ a*b
      · simp only [pairRootCount,δ,if_pos hpab,Nat.cast_one]
        rw [inv_pow, show 1-(1:ℝ)/p = α p by simp only [α,primeEulerFactor,one_div]]
        field_simp [(hα p h).1.ne'] <;> rfl
      · simp only [pairRootCount,δ,if_neg hpab,Nat.cast_ofNat,mul_one,inv_pow]
        have hgap : 0 < 1-(2:ℝ)/p := sub_pos.mpr ((div_lt_one hp0).mpr (by linarith))
        apply inv_anti₀ hgap
        dsimp [α,primeEulerFactor]
        rw [div_eq_mul_inv]
        nlinarith [sq_nonneg ((p:ℝ)⁻¹)]
  have hδ : (∏ p ∈ (a*b).primeFactors, α p) ≤ ∏ p ∈ P, δ p := by
    have he : P.filter (fun p => p ∣ a*b) = P ∩ (a*b).primeFactors := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter,Nat.mem_primeFactors,hab,and_true]
      exact ⟨fun ⟨h,hpab⟩ => ⟨h,(hp p h).1,hpab,hab⟩,fun ⟨h,_,hpab,_⟩ => ⟨h,hpab⟩⟩
    dsimp [δ]
    rw [← Finset.prod_filter,he]
    apply Finset.prod_le_prod_of_subset_of_le_one Finset.inter_subset_right
    · intro p hp; exact (primeEulerFactor_bounds (Nat.prime_of_mem_primeFactors hp)).1.le
    · intro p hp _; exact (primeEulerFactor_bounds (Nat.prime_of_mem_primeFactors hp)).2
  have h2mem : 2 ∈ Nat.primesLE V := Nat.mem_primesLE.mpr ⟨hV,Nat.prime_two⟩
  have he2 : (α 2)⁻¹ * ∏ p ∈ P, (α p)⁻¹ =
      ∏ p ∈ Nat.primesLE V, (α p)⁻¹ := Finset.mul_prod_erase _ (fun p => (α p)⁻¹) h2mem
  have hh : (α 2)⁻¹ = 2 := by norm_num [α,primeEulerFactor]
  have hpl : Real.log (V : ℝ) / 2 ≤ ∏ p ∈ P, (α p)⁻¹ := by
    have h := primeEulerProduct_ge V
    change Real.log (V : ℝ) ≤ ∏ p ∈ Nat.primesLE V, (α p)⁻¹ at h
    rw [← he2,hh] at h
    linarith
  have hlog : 0 ≤ Real.log (V : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ V by omega))
  have hmain : (Real.log (V : ℝ)/2)^2 * (∏ p ∈ (a*b).primeFactors, α p) ≤
      (∏ p ∈ P, (α p)⁻¹)^2 * ∏ p ∈ P, δ p := by
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) hpl _) hδ
    · exact Finset.prod_nonneg (fun _ hp => (primeEulerFactor_bounds (Nat.prime_of_mem_primeFactors hp)).1.le)
    · positivity
  refine le_trans ?_ (hmain.trans hprod)
  rw [totient_cast_euler]
  have hne : (((a*b : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hab
  field_simp
  dsimp [α]
  apply le_of_eq
  ring

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.omega

theorem linearPair_sieve_bound {a b c e V N : ℕ} (hV : 2 ≤ V)
    (hab : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdet : a*e + 1 = b*c ∨ b*c + 1 = a*e) :
    (((range N).filter (fun n => (oddPrimorial V).Coprime (linearPair a b c e n))).card : ℝ) ≤
      8 * N * (a : ℝ) * b * reciprocalTotient a * reciprocalTotient b /
        (Real.log (V : ℝ))^2 + (V : ℝ)^640 := by
  classical
  let F := linearPair a b c e
  let K := pairRootCount a b
  let P := oddPrimorial V
  let Z := (V : ℝ)^128
  have hP := oddPrimorial_sqfree V
  have hZ : 1 ≤ Z := one_le_pow₀ (by exact_mod_cast (show 1 ≤ V by omega))
  have hK (p : ℕ) (hp : p.Prime) (hpdvd : p ∣ P) : 0 < K p ∧ K p < p :=
    pairRootCount_bounds a b V hp hpdvd
  let s := intervalSieve F K N P Z hP hZ hK
  have hbound := SelbergSieve.selberg_bound_simple s
  have hprime : P.primeFactors ⊆ Nat.primesLE V := by
    rw [oddPrimorial_factors]
    exact Finset.erase_subset _ _
  have hnu (p : ℕ) (hp : p ∈ P.primeFactors) : s.nu p ≤ 2/(p:ℝ) := by
    change residueDensity K p ≤ _
    rw [residueDensity_prime (Nat.prime_of_mem_primeFactors hp)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [K,pairRootCount]
    split_ifs <;> norm_num
  have hprod := selberg_product_lower s hV rfl hprime hnu
  have hprod0 := pairEulerProduct_ge (mul_ne_zero ha hb) hV
  have hprod' : (Real.log (V:ℝ))^2 * ((a*b).totient : ℝ) /
        ((a*b:ℕ):ℝ) / 8 ≤ s.selbergBoundingSum := by
    change (∏ p ∈ P.primeFactors, (1-s.nu p)⁻¹) / 2 ≤ s.selbergBoundingSum at hprod
    refine le_trans ?_ hprod
    have hh :
        (∏ p ∈ P.primeFactors, (1-s.nu p)⁻¹) =
        ∏ p ∈ oddPrimesLE V, (1-(K p : ℝ)/p)⁻¹ := by
      have he : P.primeFactors = oddPrimesLE V := oddPrimorial_factors V
      rw [← he]
      apply Finset.prod_congr rfl
      intro p hp
      change (1-residueDensity K p)⁻¹ = _
      rw [residueDensity_prime (Nat.prime_of_mem_primeFactors hp)]
    rw [hh]
    linarith only [hprod0]
  have htota : 0 < (a.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)
  have htotb : 0 < (b.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hlog : 0 < Real.log (V:ℝ) := Real.log_pos (by exact_mod_cast hV)
  have ht : 0 < (Real.log (V:ℝ))^2 * ((a*b).totient:ℝ) / ((a*b:ℕ):ℝ) / 8 := by
    rw [Nat.totient_mul hab,Nat.cast_mul,Nat.cast_mul]
    positivity
  have hmain : s.totalMass / s.selbergBoundingSum ≤
      8 * N * (a : ℝ) * b * reciprocalTotient a * reciprocalTotient b /
        (Real.log (V : ℝ))^2 := by
    calc
      _ ≤ s.totalMass /
          ((Real.log (V:ℝ))^2 * ((a*b).totient:ℝ) / ((a*b:ℕ):ℝ) / 8) :=
        div_le_div_of_nonneg_left (by change (0:ℝ) ≤ N; positivity) ht hprod'
      _ = _ := by
        change (N:ℝ) / _ = _
        rw [Nat.totient_mul hab,Nat.cast_mul,Nat.cast_mul,reciprocalTotient,reciprocalTotient]
        field_simp [hlog.ne',htota.ne',htotb.ne'] <;> ring
  have herror :
      (∑ d ∈ P.divisors, if (d:ℝ) ≤ Z then (3:ℝ)^ω d * |s.rem d| else 0) ≤ (V:ℝ)^640 := by
    rw [← Finset.sum_filter]
    let D := P.divisors.filter (fun d : ℕ => (d:ℝ) ≤ Z)
    have hrem (d : ℕ) (hd : d ∈ D) : |s.rem d| ≤ Z := by
      obtain ⟨hdiv,hle⟩ := Finset.mem_filter.mp hd
      have hdP := Nat.dvd_of_mem_divisors hdiv
      have hdsq := hP.squarefree_of_dvd hdP
      let R := residues F d
      have hR : R ⊆ range d := Finset.filter_subset _ _
      have hclasses (n : ℕ) : d ∣ F n ↔ n%d ∈ R := by
        have hdpos : 0 < d := Nat.pos_of_ne_zero hdsq.ne_zero
        change d ∣ F n ↔ n%d ∈ (range d).filter (fun x => d ∣ F x)
        simp only [Finset.mem_filter,Finset.mem_range,Nat.mod_lt _ hdpos,true_and]
        exact linearPair_periodic a b c e d n (n%d) (by simp [Nat.ModEq])
      have hRcard : R.card = ∏ p ∈ d.primeFactors, K p := by
        rw [residues_card_crt F (linearPair_periodic a b c e) hdsq]
        exact Finset.prod_congr rfl fun p hp =>
          linearPair_residues_card (Nat.prime_of_mem_primeFactors hp) hdet
      exact (intervalSieve_abs_rem_le F K N P Z hP hZ hK hdP R hR hclasses hRcard).trans
        ((by exact_mod_cast (Finset.card_le_card hR).trans_eq (Finset.card_range d) :
          (R.card : ℝ) ≤ d).trans hle)
    calc
      _ ≤ ∑ d ∈ D, (3:ℝ)^ω d * Z := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hrem d hd) (by positivity)
      _ ≤ Z * (Z * (1+Real.log Z)^3) := by
        rw [← Finset.sum_mul,mul_comm Z]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [D]
        rw [Finset.sum_filter]
        exact Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (h := 3) Z hZ hP
      _ ≤ Z * (Z * Z^3) := by
        have h1 : 0 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ]
        have h2 : 1+Real.log Z ≤ Z := by linarith [Real.log_le_sub_one_of_pos (show 0 < Z by positivity)]
        gcongr
      _ = _ := by dsimp [Z]; ring
  rw [intervalSieve_siftedSum F K N P Z hP hZ hK] at hbound
  exact hbound.trans (add_le_add hmain herror)

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

theorem rpow_shift_selberg {t p : ℝ} (hp : 2 ≤ p) (ht0 : 0 ≤ t) (ht : t * Real.log p ≤ 1/4) :
    p ^ (-1+t) ≤ (3/2) * p⁻¹ ∧
    (1 - p ^ (-1+t))⁻¹ ≤ (1 - p⁻¹)⁻¹ * Real.exp (8*t * (Real.log p / p)) := by
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ t * Real.log p := mul_nonneg ht0 (Real.log_nonneg (by linarith))
  have hexp := exp_sub_one_le_two_mul ha (by linarith)
  have hq0 : 0 ≤ p⁻¹ := by positivity
  have hq : p⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; gcongr
  have hdef : p ^ (-1+t) = p⁻¹ * Real.exp (t * Real.log p) := by
    rw [Real.rpow_add hp0,Real.rpow_neg_one,Real.rpow_def_of_pos hp0]
    rw [mul_comm t]
  have hr : p ^ (-1+t) ≤ (3/2) * p⁻¹ := by
    rw [hdef,mul_comm (p⁻¹)]
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith
  have h1 : 0 < 1 - p ^ (-1+t) := by linarith
  have h2 : 0 < 1 - p⁻¹ := by linarith
  refine ⟨hr,?_⟩
  rw [inv_eq_one_div (1-p^(-1+t)), inv_eq_one_div (1-p⁻¹),div_mul_eq_mul_div,one_mul]
  apply (div_le_div_iff₀ h1 h2).mpr
  rw [one_mul]
  have hu : 0 ≤ 2 * (p⁻¹ * (t * Real.log p)) := by positivity
  have hdiff : p ^ (-1+t) - p⁻¹ ≤ 2 * (p⁻¹ * (t * Real.log p)) := by
    rw [hdef]
    nlinarith only [mul_le_mul_of_nonneg_left hexp hq0]
  have hquarter : 1/4 ≤ 1 - p ^ (-1+t) := by linarith
  have ha' : 8*t*(Real.log p / p) = 4*(2*(p⁻¹*(t*Real.log p))) := by ring
  rw [ha']
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4*(2*(p⁻¹*(t*Real.log p))))) h1.le
  nlinarith only [hm,hdiff,mul_nonneg (show 0 ≤ (1-p^(-1+t))-1/4 by linarith) hu]

theorem smooth_euler_shift_le {V : ℕ} (hV : 2 ≤ V) :
    (∏ p ∈ Nat.primesLE V, (1 - (p : ℝ) ^ (-1 + (4 * Real.log (V : ℝ))⁻¹))⁻¹) ≤
      Real.exp 8 * (1 + Real.log V) := by
  let t := (4 * Real.log (V : ℝ))⁻¹
  have hlog : 0 < Real.log (V : ℝ) := Real.log_pos (by exact_mod_cast hV)
  have ht : 0 < t := by positivity
  have hi (p : ℕ) (hp : p ∈ Nat.primesLE V) : t*Real.log (p:ℝ) ≤ 1/4 := by
    have hpR : (0:ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hpV : (p:ℝ) ≤ V := by exact_mod_cast (Nat.mem_primesLE.mp hp).1
    calc
      _ ≤ t*Real.log V := mul_le_mul_of_nonneg_left (Real.log_le_log hpR hpV) ht.le
      _ = _ := by dsimp [t]; field_simp
  have hlocal (p : ℕ) (hp : p ∈ Nat.primesLE V) :
      (1-(p:ℝ)^(-1+t))⁻¹ ≤ ((1-(p:ℝ)⁻¹)⁻¹) * Real.exp (8*t*(Real.log p/p)) :=
    (rpow_shift_selberg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) ht.le (hi p hp)).2
  have hnon (p : ℕ) (hp : p ∈ Nat.primesLE V) : 0 ≤ (1-(p:ℝ)^(-1+t))⁻¹ := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have h := (rpow_shift_selberg hp2 ht.le (hi p hp)).1
    have h' : (p:ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; gcongr
    exact inv_nonneg.mpr (by linarith)
  have h := Finset.prod_le_prod hnon hlocal
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum] at h
  have hsum : 8*t * (∑ p ∈ Nat.primesLE V, Real.log p / p) ≤ 4 := by
    calc
      _ ≤ 8*t*(2*Real.log V) := mul_le_mul_of_nonneg_left (sum_log_prime_div_le _) (by positivity)
      _ = _ := by dsimp [t]; field_simp; norm_num
  refine h.trans ?_
  calc
    _ ≤ (Real.exp 4 * (1 + Real.log V)) * Real.exp 4 :=
      mul_le_mul (primeEulerProduct_le hV) (Real.exp_le_exp.mpr hsum) (by positivity) (by positivity)
    _ = _ := by rw [show (8:ℝ) = 4+4 by norm_num,Real.exp_add]; ring

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

theorem smooth_totient_moment {X V : ℕ} (hV : 2 ≤ V) :
    (∑ n ∈ (Icc 1 X).filter (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE V),
        reciprocalTotient n * (n : ℝ)^((4*Real.log (V:ℝ))⁻¹)) ≤
      Real.exp 11 * (1+Real.log (V:ℝ)) := by
  classical
  let P := Nat.primesLE V
  let S := (Icc 1 X).filter (fun n => n.primeFactors ⊆ P)
  let t := (4*Real.log (V:ℝ))⁻¹
  have hlog : 0 < Real.log (V:ℝ) := Real.log_pos (by exact_mod_cast hV)
  have ht : 0 < t := by positivity
  let w := fun p e : ℕ => reciprocalTotient (p^e) * ((p:ℝ)^e)^t
  have hflags (n : ℕ) (hn : n ∈ S) :
      n ≠ 0 ∧ n.primeFactors ⊆ P ∧ ∀ p, n.factorization p ≤ X := by
    obtain ⟨hnX,hsub⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1,hX⟩ := Finset.mem_Icc.mp hnX
    have hn0 : n ≠ 0 := by omega
    exact ⟨hn0,hsub,fun p => (Nat.factorization_lt p hn0).le.trans hX⟩
  have hterm (n : ℕ) (hn : n ∈ S) :
      reciprocalTotient n * (n : ℝ)^t = ∏ p ∈ P, w p (n.factorization p) := by
    have h := hflags n hn
    have he : (∏ p ∈ P, p ^ n.factorization p) = n := by
      rw [← Finsupp.prod_of_support_subset n.factorization h.2.1 (· ^ ·) (by intros; simp),
        Nat.prod_factorization_pow_eq_self h.1]
    rw [reciprocalTotient_factorization h.1 h.2.1]
    dsimp [w]
    rw [Finset.prod_mul_distrib]
    congr 1
    nth_rw 1 [← he]
    rw [Nat.cast_prod, ← Real.finsetProd_rpow P]
    · simp
    · intros; positivity
  have h0 (p e : ℕ) : 0 ≤ w p e :=
    mul_nonneg (reciprocalTotient_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hmain := sum_factorization_weights_le S P X w h0 hflags
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (∑ e ∈ range (X+1), w p e) ≤
        (1-(p:ℝ)^(-1+t))⁻¹ * (1+3/(p:ℝ)^2) := by
    let r := (p:ℝ)^(-1+t)
    let u := (p:ℝ)⁻¹
    let A := (1-u)⁻¹
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu : u ≤ 1/2 := by dsimp [u]; rw [inv_eq_one_div]; gcongr
    have hpV : (p:ℝ) ≤ V := by exact_mod_cast (Nat.mem_primesLE.mp hp).1
    have htp : t*Real.log p ≤ 1/4 := by
      calc
        _ ≤ t * Real.log V := mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpV) ht.le
        _ = _ := by dsimp [t]; field_simp
    have hr : r ≤ 3/2*u := (rpow_shift_selberg hp2 ht.le htp).1
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    have hr1 : r < 1 := by linarith
    have hA0 : 0 ≤ A := by dsimp [A]; apply inv_nonneg.mpr; linarith
    have hw (e : ℕ) :
        w p (e+1) = A * r^(e+1) := by
      dsimp [w,A,u,r]
      rw [reciprocalTotient_prime_pow (Nat.mem_primesLE.mp hp).2 (by omega),mul_inv]
      rw [mul_assoc, ← Real.rpow_neg_one ((p:ℝ)^(e+1)),
        ← Real.rpow_add (pow_pos hp0 _), ← Real.rpow_natCast_mul hp0.le,
        mul_comm ((e+1 : ℕ) : ℝ), Real.rpow_mul_natCast hp0.le]
    have hg : (∑ e ∈ range X, r^e) ≤ (1-r)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hr0 hr1]
      exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (by intros; positivity)
    rw [Finset.sum_range_succ']
    have hw0 : w p 0 = 1 := by simp [w,reciprocalTotient]
    rw [hw0]
    simp_rw [hw,pow_succ]
    have he : (∑ e ∈ range X, A * (r^e * r)) = A*r * ∑ e ∈ range X, r^e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    rw [he]
    have huA : A-1 ≤ 2*u := by
      dsimp [A]
      rw [inv_eq_one_div]
      have h1 : 1≤(2*u+1)*(1-u) := by nlinarith [mul_nonneg hu0 (show 0≤1-2*u by linarith)]
      linarith [(div_le_iff₀ (by linarith : 0 < 1-u)).mpr h1]
    have hAu : 0 ≤ A-1 := by
      have hgap : 0 < 1-u := by linarith
      dsimp [A]
      rw [inv_eq_one_div]
      have h := (le_div_iff₀ hgap).mpr (show (1:ℝ)*(1-u) ≤ 1 by linarith)
      linarith
    have hAr : (A-1)*r ≤ 3/(p:ℝ)^2 := calc
      _ ≤ (2*u)*(3/2*u) := mul_le_mul huA hr hr0 (by positivity)
      _ = _ := by dsimp [u]; ring
    rw [add_comm (A*r*(∑ e ∈ range X, r^e)) 1]
    simp only [pow_zero, one_mul]
    rw [← sq (p:ℝ)]
    change 1 + A*r*(∑ e ∈ range X, r^e) ≤ (1-r)⁻¹ * (1+3/(p:ℝ)^2)
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg (by positivity))).trans ?_
    have hgap : 0 < 1-r := by linarith
    rw [inv_eq_one_div,one_div_mul_eq_div, ← div_eq_mul_one_div]
    apply (le_div_iff₀ hgap).mpr
    rw [add_mul, div_mul_cancel₀ _ hgap.ne']
    nlinarith only [hAr]
  have htail : (∏ p ∈ P, (1+3/(p:ℝ)^2)) ≤ Real.exp 3 := by
    refine (Real.prod_one_add_le_exp_sum P (by intros; positivity)).trans ?_
    apply Real.exp_le_exp.mpr
    have hsub : P ⊆ Icc 2 V := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.two_le,(Nat.mem_primesLE.mp hp).1⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans ?_
    have hm : (∑ p ∈ Icc 2 V, 3/(p:ℝ)^2) = 3 * ∑ p ∈ Icc 2 V, (1:ℝ)/(p*p) := by
      rw [Finset.mul_sum]
      simp only [sq,mul_one_div]
    rw [hm]
    have h := mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le (X := V) (Y := 2) (by decide))
      (by norm_num : (0:ℝ)≤3)
    norm_num at h ⊢
    exact h
  calc
    _ = ∑ n ∈ S, ∏ p ∈ P, w p (n.factorization p) := Finset.sum_congr rfl hterm
    _ ≤ ∏ p ∈ P, ∑ e ∈ range (X+1), w p e := hmain
    _ ≤ ∏ p ∈ P, (1-(p:ℝ)^(-1+t))⁻¹*(1+3/(p:ℝ)^2) :=
      Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun e _ => h0 p e) hlocal
    _ ≤ (Real.exp 8 * (1+Real.log V)) * Real.exp 3 := by
      rw [Finset.prod_mul_distrib]
      apply mul_le_mul (smooth_euler_shift_le hV) htail
      · positivity
      · positivity
    _ = _ := by rw [show (11:ℝ) = 8+3 by norm_num,Real.exp_add]; ring

open scoped Classical in
theorem smooth_totient_tail {X V : ℕ} (hV : 2 ≤ V) {u : ℝ} (hu : 0 < u) :
    (∑ n ∈ (Icc 1 X).filter (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE V ∧ u ≤ (n:ℝ)),
        reciprocalTotient n) ≤
      Real.exp 11 * (1+Real.log V) * Real.exp (- Real.log u / (4*Real.log V)) := by
  classical
  let t := (4*Real.log (V:ℝ))⁻¹
  have ht : 0 < t := by dsimp [t]; have := Real.log_pos (by exact_mod_cast hV : (1:ℝ)<V); positivity
  have ht' : t * Real.log u = Real.log u / (4*Real.log (V:ℝ)) := by dsimp [t]; ring
  let S := (Icc 1 X).filter (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE V ∧ u ≤ (n:ℝ))
  let T := (Icc 1 X).filter (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE V)
  have hsub : S ⊆ T := fun n hn => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
    (Finset.mem_filter.mp hn).2.1⟩
  have hU : 0 < u^t := Real.rpow_pos_of_pos hu _
  have hc := smooth_totient_moment (X := X) hV
  calc
    _ ≤ ∑ n ∈ S, reciprocalTotient n * ((n:ℝ)^t / u^t) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (Finset.mem_filter.mp hn).2.2
      conv_lhs => rw [← mul_one (reciprocalTotient n)]
      exact mul_le_mul_of_nonneg_left
        ((le_div_iff₀ hU).mpr (by simpa using Real.rpow_le_rpow hu.le hn' ht.le))
        (reciprocalTotient_nonneg _)
    _ ≤ ∑ n ∈ T, reciprocalTotient n * ((n:ℝ)^t / u^t) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n _ _
      exact mul_nonneg (reciprocalTotient_nonneg _) (by positivity)
    _ = (∑ n ∈ T, reciprocalTotient n * (n:ℝ)^t) / u^t := by
      simp_rw [← mul_div_assoc]
      rw [Finset.sum_div]
    _ ≤ (Real.exp 11 * (1+Real.log V)) / u^t := div_le_div_of_nonneg_right hc (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos hu,mul_comm (Real.log u),ht',div_eq_mul_inv, ← Real.exp_neg];
                congr 2; ring

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Nat Real

def Rough (y : ℝ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, y ≤ (p : ℝ)

theorem rough_prime {y : ℝ} {n p : ℕ} (hn : n ≠ 0) (h : Rough y n)
    (hp : p.Prime) (hd : p ∣ n) : y ≤ (p : ℝ) :=
  h p (Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩)

open scoped Classical in
noncomputable def pairFiber (X a b s t : ℕ) (y : ℝ) : Finset ℕ :=
  (range X).filter fun n =>
    a ∣ n+s ∧ b ∣ n+t ∧ 0 < n ∧ Rough y ((n+s)/a) ∧ Rough y ((n+t)/b)

theorem adjacent_coprime_shifts {n s t : ℕ} (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0) :
    (n+s).Coprime (n+t) := by
  rcases hst with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simpa using Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)
  · simpa using (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)).symm

theorem pairFiber_bound {X a b s t V : ℕ} {y : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (habX : a*b ≤ X)
    (hV : 2 ≤ V) (hVy : (V:ℝ) < y)
    (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0) :
    ((pairFiber X a b s t y).card : ℝ) ≤
      16 * X * reciprocalTotient a * reciprocalTotient b / (Real.log (V:ℝ))^2 +
        (V:ℝ)^640 := by
  classical
  let A := pairFiber X a b s t y
  by_cases hA : A.Nonempty
  · obtain ⟨n₀,hn₀⟩ := hA
    have hn₀' := (Finset.mem_filter.mp hn₀).2
    have hcop : a.Coprime b :=
      (adjacent_coprime_shifts (n := n₀) hst).coprime_dvd_left hn₀'.1 |>.coprime_dvd_right hn₀'.2.1
    let r := n₀ % (a*b)
    let c := (r+s)/a
    let e := (r+t)/b
    have hdiva : a ∣ r+s := by
      have hr : n₀ ≡ r [MOD a] := (show n₀ ≡ r [MOD a*b] by simp [Nat.ModEq,r]).of_dvd (dvd_mul_right _ _)
      exact Nat.modEq_zero_iff_dvd.mp ((hr.add_right s).symm.trans (Nat.modEq_zero_iff_dvd.mpr hn₀'.1))
    have hdivb : b ∣ r+t := by
      have hr : n₀ ≡ r [MOD b] := (show n₀ ≡ r [MOD a*b] by simp [Nat.ModEq,r]).of_dvd (dvd_mul_left _ _)
      exact Nat.modEq_zero_iff_dvd.mp ((hr.add_right t).symm.trans (Nat.modEq_zero_iff_dvd.mpr hn₀'.2.1))
    have hc : a*c = r+s := Nat.mul_div_cancel' hdiva
    have he : b*e = r+t := Nat.mul_div_cancel' hdivb
    have hdet : b*e + 1 = a*c ∨ a*c + 1 = b*e := by
      rcases hst with ⟨hs,ht⟩|⟨hs,ht⟩
      · right; omega
      · left; omega
    let N := X/(a*b) + 1
    let f := fun n : ℕ => n/(a*b)
    have hnform (n : ℕ) (hn : n ∈ A) : n = a*b*(f n)+r := by
      have hn' := (Finset.mem_filter.mp hn).2
      have hmoda : n+s ≡ n₀+s [MOD a] :=
        (Nat.modEq_zero_iff_dvd.mpr hn'.1).trans (Nat.modEq_zero_iff_dvd.mpr hn₀'.1).symm
      have hmodb : n+t ≡ n₀+t [MOD b] :=
        (Nat.modEq_zero_iff_dvd.mpr hn'.2.1).trans (Nat.modEq_zero_iff_dvd.mpr hn₀'.2.1).symm
      have hmod := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨Nat.ModEq.add_right_cancel' s hmoda,Nat.ModEq.add_right_cancel' t hmodb⟩
      change n % (a*b) = r at hmod
      have h := Nat.mod_add_div n (a*b)
      dsimp [f]; omega
    have hinj : Set.InjOn f A := fun n hn m hm h => by
      rw [hnform n hn, hnform m hm,h]
    have hf (n : ℕ) (hn : n ∈ A) :
        f n ∈ (range N).filter (fun m => (oddPrimorial V).Coprime (linearPair b a c e m)) := by
      obtain ⟨hnX, hda,hdb,hn0,hka,hkb⟩ := Finset.mem_filter.mp hn
      have hnX' := Finset.mem_range.mp hnX
      have h1 : (n+s)/a = b*(f n)+c := by
        calc
          _ = ((b*(f n)+c)*a)/a := by
            congr 1
            nth_rw 1 [hnform n hn]
            nlinarith only [hc]
          _ = _ := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ha)
      have h2 : (n+t)/b = a*(f n)+e := by
        calc
          _ = ((a*(f n)+e)*b)/b := by
            congr 1
            nth_rw 1 [hnform n hn]
            nlinarith only [he]
          _ = _ := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb)
      have ha0 : (n+s)/a ≠ 0 := by
        have hh := Nat.mul_div_cancel' hda
        intro hz
        simp [hz] at hh
        omega
      have hb0 : (n+t)/b ≠ 0 := by
        have hh := Nat.mul_div_cancel' hdb
        intro hz
        simp [hz] at hh
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right hnX'.le)),?_⟩
      by_contra hbad
      obtain ⟨p,hp,hpP,hplin⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
      have hpV := (Nat.mem_primeFactors.mpr ⟨hp,hpP,(oddPrimorial_sqfree V).ne_zero⟩)
      rw [oddPrimorial_factors] at hpV
      have hpV' : (p:ℝ) ≤ V := by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_of_mem_erase hpV)).1
      unfold linearPair at hplin
      rw [← h1,← h2] at hplin
      rcases hp.dvd_mul.mp hplin with h | h
      · linarith [rough_prime ha0 hka hp h]
      · linarith [rough_prime hb0 hkb hp h]
    have hcard : (A.card:ℝ) ≤
        (((range N).filter (fun m => (oddPrimorial V).Coprime (linearPair b a c e m))).card:ℝ) := by
      have hh : A.image f ⊆ (range N).filter (fun m => (oddPrimorial V).Coprime (linearPair b a c e m)) := by
        intro w hw
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hw
        exact hf n hn
      exact_mod_cast (Finset.card_image_of_injOn hinj).symm.trans_le (Finset.card_le_card hh)
    have hN : (N:ℝ)*(a:ℝ)*b ≤ 2*X := by
      have hN' : N*(a*b) ≤ X + a*b := by
        dsimp [N]
        rw [Nat.add_mul,one_mul]
        exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
      have hN1 : (N:ℝ)*((a:ℝ)*b) ≤ X + (a:ℝ)*b := by exact_mod_cast hN'
      have hxr : (a:ℝ)*b ≤ X := by exact_mod_cast habX
      nlinarith only [hN1,hxr]
    refine hcard.trans ((linearPair_sieve_bound hV hcop.symm hb ha hdet).trans ?_)
    refine add_le_add ?_ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hw : 0 ≤ reciprocalTotient a * reciprocalTotient b :=
      mul_nonneg (reciprocalTotient_nonneg _) (reciprocalTotient_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hN hw
    nlinarith only [hh]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hA
    change (A.card:ℝ) ≤ _
    rw [he,Finset.card_empty]
    norm_num only [Nat.cast_zero]
    have ha0 := reciprocalTotient_nonneg a
    have hb0 := reciprocalTotient_nonneg b
    positivity

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat
open scoped ArithmeticFunction.sigma

noncomputable def alphaBlock (T V : ℕ) (u : ℝ) : Finset ℕ :=
  (Icc 1 T).filter fun a => a.primeFactors ⊆ Nat.primesLE V ∧ u ≤ (a:ℝ)

def betaBlock (T a m : ℕ) : Finset ℕ :=
  (Icc 1 T).filter fun b =>
    divisorValuation b ∈ Icc (divisorValuation a - m) (divisorValuation a + m)

noncomputable def blockCover (X T V m s t : ℕ) (u y : ℝ) : Finset ℕ :=
  (alphaBlock T V u).biUnion (fun a =>
    (betaBlock T a m).biUnion (fun b => pairFiber X a b s t y))

theorem primeFactors_le_of_le {n V : ℕ} (hn : n ≤ V) : n.primeFactors ⊆ Nat.primesLE V :=
  fun p hp => Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hn,
    Nat.prime_of_mem_primeFactors hp⟩

theorem betaBlock_weight {T X a m : ℕ} (hTX : T ≤ X) (hX : 2 ≤ X)
    (hlog : 1 < Real.log (X:ℝ)) :
    (∑ b ∈ betaBlock T a m, reciprocalTotient b) ≤
      (2*m+1) * ((2*Real.exp 10)*Real.log X / Real.sqrt (Real.log (Real.log X))) := by
  classical
  let J := Icc (divisorValuation a-m) (divisorValuation a+m)
  let S := betaBlock T a m
  have hmap : ∀ b ∈ S, divisorValuation b ∈ J := fun b hb => (Finset.mem_filter.mp hb).2
  have hsum := Finset.sum_fiberwise_of_maps_to (g := divisorValuation) hmap reciprocalTotient
  rw [← hsum]
  have hJ : J.card ≤ 2*m+1 := by
    dsimp [J]
    rw [Nat.card_Icc]
    omega
  let C := (2*Real.exp 10)*Real.log X / Real.sqrt (Real.log (Real.log X))
  have hC : 0 ≤ C := by dsimp [C]; have := Real.log_pos (by exact_mod_cast hX : (1:ℝ)<X); positivity
  calc
    _ ≤ ∑ j ∈ J, C := by
      apply Finset.sum_le_sum
      intro j hj
      have hsub : S.filter (fun b => divisorValuation b = j) ⊆
        (Icc 1 X).filter (fun b => b.primeFactors ⊆ Nat.primesLE X ∧ divisorValuation b = j) := by
        intro b hb
        obtain ⟨hbJ,hv⟩ := Finset.mem_filter.mp hb
        obtain ⟨hbt,_⟩ := Finset.mem_filter.mp hbJ
        obtain ⟨hb1,hbT⟩ := Finset.mem_Icc.mp hbt
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb1,hbT.trans hTX⟩,
          primeFactors_le_of_le (hbT.trans hTX),hv⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun b _ _ => reciprocalTotient_nonneg b)).trans (sum_valuation_reciprocalTotient_le hX hlog)
    _ = (J.card:ℝ)*C := by simp [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hJR : (J.card:ℝ) ≤ 2*(m:ℝ)+1 := by exact_mod_cast hJ
      exact mul_le_mul_of_nonneg_right hJR hC

theorem blockCover_card_le {X T V W m s t : ℕ} {u y : ℝ}
    (hX : 2 ≤ X) (hT : 1 ≤ T) (hTX : T^2 ≤ X)
    (hlog : 1 < Real.log (X:ℝ)) (hV : 2 ≤ V) (hW : 2 ≤ W)
    (hWy : (W:ℝ) < y) (hu : 0 < u) (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0) :
    ((blockCover X T V m s t u y).card : ℝ) ≤
      (16*(X:ℝ)/(Real.log (W:ℝ))^2) *
        ((2*(m:ℝ)+1)*((2*Real.exp 10)*Real.log X / Real.sqrt (Real.log (Real.log X)))) *
        (Real.exp 11*(1+Real.log V)*Real.exp (-Real.log u/(4*Real.log V))) +
      (T:ℝ)^2 * (W:ℝ)^640 := by
  classical
  let A := alphaBlock T V u
  let B (a : ℕ) := betaBlock T a m
  let C := (2*(m:ℝ)+1)*((2*Real.exp 10)*Real.log X / Real.sqrt (Real.log (Real.log X)))
  let F := 16*(X:ℝ)/(Real.log (W:ℝ))^2
  let E := (W:ℝ)^640
  have hT' : T ≤ X := (by simpa [sq] using (Nat.le_mul_of_pos_left T (show 0<T by omega)) : T ≤ T^2).trans hTX
  have hF : 0 ≤ F := by unfold F; positivity
  have hC : 0 ≤ C := by dsimp [C]; have := Real.log_pos (by exact_mod_cast hX : (1:ℝ)<X); positivity
  have hE : 0 ≤ E := by unfold E; positivity
  have hA : A.card ≤ T :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Nat.card_Icc])
  have hB (a : ℕ) : (B a).card ≤ T :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Nat.card_Icc])
  have hpair (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ B a) :
      ((pairFiber X a b s t y).card:ℝ) ≤
        F*reciprocalTotient a*reciprocalTotient b+E := by
    have ha' := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    have h := pairFiber_bound (by omega : a≠0) (by omega : b≠0)
      ((Nat.mul_le_mul ha'.2 hb'.2).trans (by simpa [sq] using hTX))
      hW hWy hst
    refine h.trans_eq ?_
    dsimp [F,E]
    ring
  have hcard : ((blockCover X T V m s t u y).card : ℝ) ≤
      ∑ a ∈ A, ∑ b ∈ B a, ((pairFiber X a b s t y).card:ℝ) := by
    calc
      _ ≤ ∑ a ∈ A, (((B a).biUnion (fun b => pairFiber X a b s t y)).card:ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := A)
          (t := fun a => (B a).biUnion (fun b => pairFiber X a b s t y)))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast (Finset.card_biUnion_le (s := B a) (t := fun b => pairFiber X a b s t y))
  refine hcard.trans ?_
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B a, (F*reciprocalTotient a*reciprocalTotient b+E) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (hpair a ha))
    _ ≤ ∑ a ∈ A, (F*reciprocalTotient a*C+(T:ℝ)*E) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (betaBlock_weight hT' hX hlog) (mul_nonneg hF (reciprocalTotient_nonneg _)))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hB a) hE)
    _ = F*C*(∑ a ∈ A,reciprocalTotient a)+(A.card:ℝ)*(T*E) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ F*C*(Real.exp 11*(1+Real.log V)*Real.exp (-Real.log u/(4*Real.log V)))+
        T*(T*E) := add_le_add
      (mul_le_mul_of_nonneg_left (smooth_totient_tail hV hu) (mul_nonneg hF hC))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (mul_nonneg (by positivity) hE))
    _ = _ := by dsimp [C,F,E]; ring

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat
open scoped ArithmeticFunction.sigma

theorem mem_blockCover_of_split {X T V m s t n a b k l q Y : ℕ} {u y : ℝ}
    (hn0 : 0 < n) (hnX : n < X) (hsX : n+s ≤ X) (htX : n+t ≤ X)
    (ha : a ≠ 0) (hb : b ≠ 0) (hk0 : k ≠ 0) (hl0 : l ≠ 0)
    (has : a*k = n+s) (hbt : b*l = n+t)
    (haT : a ≤ T) (hbT : b ≤ T) (hua : u ≤ (a:ℝ)) (hay : a.primeFactors ⊆ Nat.primesLE V)
    (hy : 1 < y) (hY : Y ≤ q) (hyq : y ≤ (q:ℝ))
    (hk : ∀ p : ℕ, p.Prime → p∣k → q ≤ p)
    (hl : ∀ p : ℕ, p.Prime → p∣l → q ≤ p)
    (hS : n+s ∉ squareExceptions X Y) (hR : n+t ∉ squareExceptions X Y)
    (hσ : σ 0 (n+s) = σ 0 (n+t))
    (hm : ⌊Real.log (X:ℝ)/ Real.log y⌋₊ = m) :
    n ∈ blockCover X T V m s t u y := by
  classical
  have hs0 : 0 < n+s := by omega
  have ht0 : 0 < n+t := by omega
  have hnoS (p : ℕ) (hp : p.Prime) (hqp : q ≤ p) : ¬ p*p ∣ a*k := by
    rw [has]
    exact fun h => hS (mem_squareExceptions (hY.trans hqp) hs0 hsX h)
  have hnoT (p : ℕ) (hp : p.Prime) (hqp : q ≤ p) : ¬ p*p ∣ b*l := by
    rw [hbt]
    exact fun h => hR (mem_squareExceptions (hY.trans hqp) ht0 htX h)
  obtain ⟨hcopA,hsqk⟩ := coprime_squarefree_of_rough hk hnoS
  obtain ⟨hcopB,hsql⟩ := coprime_squarefree_of_rough hl hnoT
  have hv := divisorValuation_split ha hb hsqk hsql hcopA hcopB (has ▸ hbt ▸ hσ)
  have hkr : Rough y k := fun p hp =>
    hyq.trans (by exact_mod_cast hk p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hlr : Rough y l := fun p hp =>
    hyq.trans (by exact_mod_cast hl p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hkX : k ≤ X := (Nat.le_of_dvd hs0 ⟨a,by rw [mul_comm,has]⟩).trans hsX
  have hlX : l ≤ X := (Nat.le_of_dvd ht0 ⟨b,by rw [mul_comm,hbt]⟩).trans htX
  have hkm : k.primeFactors.card ≤ m := by
    rw [← hm]
    apply Nat.le_floor
    exact rough_card_le hsqk hy (by exact_mod_cast hkX) hkr
  have hlm : l.primeFactors.card ≤ m := by
    rw [← hm]
    apply Nat.le_floor
    exact rough_card_le hsql hy (by exact_mod_cast hlX) hlr
  have hak : (n+s)/a = k := by rw [← has,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)]
  have hbl : (n+t)/b = l := by rw [← hbt,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb)]
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,haT⟩,hay,hua⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hbT⟩,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnX,⟨k,has.symm⟩,⟨l,hbt.symm⟩,
    hn0,hak.symm ▸ hkr,hbl.symm ▸ hlr⟩

open scoped Classical in
noncomputable def smallPrimeCover (X T V s : ℕ) (u : ℝ) : Finset ℕ :=
  (alphaBlock T V u).biUnion fun a => (range X).filter (fun n => 0 < n ∧ n+s ≤ X ∧ a ∣ n+s)

theorem smallPrimeCover_bound {X T V s : ℕ} {u : ℝ} (hV : 2 ≤ V) (hu : 0 < u) :
    ((smallPrimeCover X T V s u).card : ℝ) ≤
      X * (Real.exp 11*(1+Real.log V)*Real.exp (-Real.log u/(4*Real.log V))) := by
  classical
  let A := alphaBlock T V u
  have hcnt (a : ℕ) (ha : a ∈ A) :
      (((range X).filter (fun n => 0 < n ∧ n+s ≤ X ∧ a ∣ n+s)).card : ℝ) ≤
      X * reciprocalTotient a := by
    let S := (range X).filter (fun n => 0 < n ∧ n+s ≤ X ∧ a ∣ n+s)
    have hI : Set.InjOn (fun n : ℕ => n+s) S := fun _ _ _ _ h => Nat.add_right_cancel h
    have hsub : (S.image (fun n => n+s)) ⊆ (Ioc 0 X).filter (fun v => a ∣ v) := by
      intro v hv
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hv
      have h := (Finset.mem_filter.mp hn).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,h.2.1⟩,h.2.2⟩
    have hcard := (Finset.card_image_of_injOn hI).symm.trans_le (Finset.card_le_card hsub)
    rw [Nat.Ioc_filter_dvd_card_eq_div] at hcard
    have ha0 : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hf : 0 < (a.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr ha0
    calc
      _ ≤ ((X/a : ℕ):ℝ) := by exact_mod_cast hcard
      _ ≤ (X:ℝ)/a := Nat.cast_div_le
      _ ≤ X*reciprocalTotient a := by
        rw [reciprocalTotient,div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left (inv_anti₀ hf (by exact_mod_cast Nat.totient_le a)) (by positivity)
  calc
    _ ≤ ∑ a ∈ A, (((range X).filter (fun n => 0 < n ∧ n+s ≤ X ∧ a ∣ n+s)).card:ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, X*reciprocalTotient a := Finset.sum_le_sum hcnt
    _ = X*(∑ a ∈ A,reciprocalTotient a) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (smooth_totient_tail hV hu) (by positivity)

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

noncomputable def binLog (X j : ℕ) : ℝ := Real.log (X:ℝ)/((2:ℝ)^(j+1))
noncomputable def binCut (X j : ℕ) : ℝ := Real.exp (binLog X j)
noncomputable def squareCut (X : ℕ) : ℕ := ⌊Real.exp (Real.sqrt (Real.log (X:ℝ)))⌋₊
noncomputable def binPrimes (X j : ℕ) : ℕ := ⌊(binCut X j)^2⌋₊
noncomputable def sievePrimes (X j : ℕ) : ℕ := ⌊Real.exp (binLog X j/8192)⌋₊
noncomputable def numBins (X : ℕ) : ℕ := ⌈Real.log (X:ℝ)⌉₊ + 1

theorem floor_ge_sqrt {z : ℝ} (hz : 4 ≤ z) : Real.sqrt z ≤ (⌊z⌋₊ : ℝ) := by
  have hz0 : 0 ≤ z := by linarith
  have hs : 2 ≤ Real.sqrt z := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : Real.sqrt z ≤ z-1 := by nlinarith [Real.sq_sqrt hz0]
  linarith [Nat.lt_floor_add_one z]

theorem squareCut_log_bounds {X : ℕ} (hX : 4 ≤ Real.sqrt (Real.log (X:ℝ))) :
    2 ≤ squareCut X ∧
    Real.sqrt (Real.log (X:ℝ))/2 ≤ Real.log ((squareCut X : ℕ):ℝ) ∧
    Real.log ((squareCut X : ℕ):ℝ) ≤ Real.sqrt (Real.log (X:ℝ)) := by
  let z := Real.sqrt (Real.log (X:ℝ))
  have hz : 4 ≤ z := hX
  have hex : 4 ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  have hf := floor_ge_sqrt hex
  have hs : (2:ℝ) ≤ (squareCut X:ℝ) := by
    change _ ≤ (⌊Real.exp z⌋₊:ℝ)
    apply le_trans _ hf
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hfpos : (0:ℝ) < (squareCut X:ℝ) := by linarith
  refine ⟨by exact_mod_cast hs, ?_, ?_⟩
  · have hh := Real.log_le_log (Real.sqrt_pos.mpr (Real.exp_pos z)) hf
    rw [Real.log_sqrt (Real.exp_pos _).le,Real.log_exp] at hh
    exact hh
  · have h := Real.log_le_log hfpos (Nat.floor_le (Real.exp_pos z).le)
    rwa [Real.log_exp] at h

theorem exists_bin {X q : ℕ} (hX : 4 ≤ Real.sqrt (Real.log (X:ℝ)))
    (hq0 : squareCut X ≤ q) (hqX : q ≤ X) :
    ∃ j ∈ range (numBins X),
      binLog X j ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ 2*binLog X j := by
  have hy := squareCut_log_bounds hX
  have hqpos : (0:ℝ) < q := by exact_mod_cast (show 0<q by omega)
  have hqR : (q:ℝ) ≤ X := by exact_mod_cast hqX
  have hlog := hqpos.trans_le hqR
  have hq2 : (squareCut X:ℝ) ≤ q := by exact_mod_cast hq0
  have hqlog : 1 ≤ Real.log (q:ℝ) := by
    have hs : (0:ℝ) < (squareCut X:ℝ) := by exact_mod_cast (show 0 < squareCut X by omega)
    linarith [Real.log_le_log hs hq2,hy.2.1]
  let N := ⌈Real.log (X:ℝ)⌉₊
  have hN : Real.log (X:ℝ) ≤ (N:ℝ) := Nat.le_ceil _
  have hp (k : ℕ) : (k:ℝ)+1 ≤ (2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ,Nat.cast_succ]
      linarith only [ih,show 0 ≤ (k:ℝ) by positivity]
  have hsat : ∃ j : ℕ, binLog X j ≤ Real.log (q:ℝ) := by
    refine ⟨N,?_⟩
    unfold binLog
    have hc : Real.log (X:ℝ) / (2:ℝ)^(N+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have h := hp (N+1)
      push_cast at h
      linarith [show 0 ≤ (N:ℝ) by positivity]
    exact hc.trans hqlog
  let j := Nat.find hsat
  have hj : j ≤ N := by
    have hc : Real.log (X:ℝ) / (2:ℝ)^(N+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have h := hp (N+1)
      push_cast at h
      linarith [show 0 ≤ (N:ℝ) by positivity]
    exact Nat.find_min' hsat (hc.trans hqlog)
  refine ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),Nat.find_spec hsat,?_⟩
  have htop : 2 * binLog X j = Real.log (X:ℝ)/(2:ℝ)^j := by
    unfold binLog
    rw [pow_succ]
    field_simp
  rw [htop]
  by_cases hj0 : j = 0
  · simpa [hj0] using Real.log_le_log hqpos hqR
  · apply le_of_lt
    have hb := Nat.find_min hsat (show j-1 < j by omega)
    push Not at hb
    simpa [binLog, show j-1+1=j by omega] using hb

theorem exp_suppress {U : ℝ} (hU : 0 < U) :
    U^2 * Real.exp (-U/24) ≤ (6*24^3 : ℝ)/U := by
  have h := Real.pow_div_factorial_le_exp (U/24) (show 0 ≤ U / 24 by positivity) 3
  norm_num at h
  rw [show -U/24 = -(U/24) by ring,Real.exp_neg]
  apply (le_div_iff₀ hU).mpr
  have hz := mul_le_mul_of_nonneg_right h ((Real.exp_pos (U/24)).le)
  have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ (Real.exp (U/24))⁻¹ by positivity)
  rw [mul_inv_cancel₀ (Real.exp_pos (U/24)).ne'] at hh
  nlinarith only [hh]

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat

noncomputable def activeBins (X : ℕ) : Finset ℕ :=
  (range (numBins X)).filter (fun j => Real.log (squareCut X:ℝ) ≤ 2*binLog X j)

noncomputable def binnedCover (X T j s t : ℕ) : Finset ℕ :=
  blockCover X T (binPrimes X j) ⌊Real.log (X:ℝ)/Real.log (binCut X j)⌋₊
    s t ((T:ℝ) / (binCut X j)^2) (binCut X j)

noncomputable def epsConstant : ℝ := (16*16384^2)*(6*3)*Real.exp (43/2)*(6*24^3)

theorem binnedCover_estimate {T j s t : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ))
    (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0) (hj : j ∈ activeBins (T^3)) :
    ((binnedCover (T^3) T j s t).card:ℝ) ≤
      epsConstant * ((T:ℝ)^3 / Real.sqrt (Real.log (Real.log ((T:ℝ)^3)))) /
        (2:ℝ)^(j+1) + (T:ℝ)^2 * Real.sqrt T := by
  let X := T^3
  let H := Real.log (X:ℝ)
  let U := (2:ℝ)^(j+1)
  let L := binLog X j
  let y := binCut X j
  let W := sievePrimes X j
  let V := binPrimes X j
  let m := ⌊Real.log (X:ℝ)/Real.log y⌋₊
  let u := (T:ℝ) / y^2
  let S := Real.sqrt (Real.log H)
  have hT0 : (0:ℝ) < T := by
    by_contra h
    have hz : T=0 := by exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg T) : (T:ℝ)=0)
    norm_num [hz] at hT
  have hT1 : (1:ℝ) < T := by
    by_contra h
    linarith [Real.log_nonpos hT0.le (le_of_not_gt h)]
  have hT2 : 2 ≤ T := by exact_mod_cast hT1
  have hTlog : 0 < Real.log (T:ℝ) := Real.log_pos hT1
  have hXlog : H = 3 * Real.log (T:ℝ) := by dsimp [H,X]; rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hH : 1 < H := by norm_num at hT; linarith
  have hHbig : (2:ℝ)^40 ≤ H := by norm_num at hT ⊢; linarith
  have hS : 0 < S := Real.sqrt_pos.mpr (Real.log_pos hH)
  have hU : 0 < U := by positivity
  have hU1 : 1 ≤ U := one_le_pow₀ (by norm_num)
  have hU2 : 2 ≤ U := by dsimp [U]; rw [pow_succ]; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)]
  have hL : L = H/U := rfl
  have hyL : Real.log y = L := Real.log_exp L
  have hL0 : 0 < L := by rw [hL]; positivity
  have hLbig : 16384 ≤ L := by
    have Hsqrt : (65536:ℝ) ≤ Real.sqrt H := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 65536)]
      exact Real.sqrt_le_sqrt (by norm_num at hHbig ⊢; linarith)
    have hx : 4 ≤ Real.sqrt H := by linarith
    have hQ := (squareCut_log_bounds (X:=X) hx).2.1
    have hj' := (Finset.mem_filter.mp hj).2
    change Real.log (squareCut X:ℝ) ≤ 2*L at hj'
    linarith
  have hy2 : 2 ≤ y := by
    dsimp [y,binCut]
    linarith [Real.add_one_le_exp L]
  have hy0 : 0 < y := by linarith
  have hV3 : (y:ℝ) ≤ V := by
    change y ≤ (⌊y^2⌋₊:ℝ)
    have hv := floor_ge_sqrt (show (4:ℝ) ≤ y^2 by nlinarith)
    rwa [Real.sqrt_sq hy0.le] at hv
  have hV2 : 2 ≤ V := by exact_mod_cast hy2.trans hV3
  have logVlo : L ≤ Real.log (V:ℝ) := by
    rw [←hyL]; exact Real.log_le_log hy0 hV3
  have logVhi : Real.log (V:ℝ) ≤ 2*L := by
    have hh := Real.log_le_log (show 0 < (V:ℝ) by linarith)
      (Nat.floor_le (show 0 ≤ y^2 by positivity))
    rwa [Real.log_pow,hyL] at hh
  have logV0 : 0 < Real.log (V:ℝ) := hL0.trans_le logVlo
  have hWfloor : Real.sqrt (Real.exp (L/8192)) ≤ (W:ℝ) := by
    apply floor_ge_sqrt
    have he := Real.exp_le_exp.mpr (show (2:ℝ) ≤ L/8192 by linarith)
    have h4 : (4:ℝ) ≤ Real.exp 2 := by
      have hh := Real.pow_div_factorial_le_exp 2 (show 0≤(2:ℝ) by norm_num) 3
      have hh' := Real.exp_one_gt_two
      rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
      nlinarith
    exact h4.trans he
  have hW2 : 2 ≤ W := by
    have hw : (2:ℝ) ≤ W := by
      refine le_trans ?_ hWfloor
      rw [← Real.sqrt_sq (show (0:ℝ)≤2 by norm_num)]
      apply Real.sqrt_le_sqrt
      have h := Real.exp_le_exp.mpr (show (2:ℝ) ≤ L/8192 by linarith)
      have h2 := Real.exp_one_gt_two
      rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add] at h
      nlinarith
    exact_mod_cast hw
  have hWpos : (0:ℝ)<W := by exact_mod_cast (show 0<W by omega)
  have hWle : (W:ℝ) ≤ Real.exp (L/8192) := Nat.floor_le (Real.exp_pos _).le
  have hWy : (W:ℝ) < y :=
    hWle.trans_lt (Real.exp_lt_exp.mpr (by linarith))
  have logWlo : L/16384 ≤ Real.log (W:ℝ) := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr (Real.exp_pos _)) hWfloor
    rw [Real.log_sqrt (Real.exp_pos _).le,Real.log_exp] at h
    linarith
  have logW0 : 0 < Real.log (W:ℝ) := by linarith
  have hu : 0 < u := by positivity
  have hY : 2 ≤ X := hT2.trans (Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) T)
  have hm : (m:ℝ) ≤ U := by
    change (⌊H/Real.log y⌋₊:ℝ) ≤ U
    rw [hyL,hL,div_div_cancel₀ (show H ≠ 0 by linarith)]
    exact Nat.floor_le (by positivity)
  have hTsq : T^2 ≤ X := by
    dsimp [X]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB := blockCover_card_le (m := m) hY (by omega : 1≤T) hTsq hH hV2 hW2 hWy hu hst
  have hBoundLog : ((Real.log (W:ℝ))^2)⁻¹ ≤ (16384:ℝ)^2 / L^2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ L/16384 by positivity) logWlo 2
    have hh := inv_anti₀ (show 0 < (L/16384)^2 by positivity) h
    refine hh.trans_eq ?_
    field_simp <;> ring
  have hExp : Real.exp (-Real.log u/(4*Real.log V)) ≤ Real.exp (1/2) * Real.exp (-U/24) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlogu : Real.log u = Real.log (T:ℝ)-2*L := by
      dsimp [u]
      rw [Real.log_div hT0.ne' (by positivity),Real.log_pow,hyL]
      norm_num
    rw [hlogu]
    have hl : L/(2*Real.log V) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have hr : U/24 ≤ Real.log (T:ℝ)/(4*Real.log V) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_left logVhi (show 0 ≤ U by positivity)
      have hl2 : L*U=H := by rw [hL]; field_simp
      nlinarith only [h,hl2,hXlog]
    have hend : -(Real.log (T:ℝ)-2*L)/(4*Real.log V) =
        L/(2*Real.log V)-Real.log (T:ℝ)/(4*Real.log V) := by ring
    rw [hend]
    linarith
  have hF : 16*(X:ℝ)/(Real.log (W:ℝ))^2 ≤ (16*16384^2)*(X:ℝ)/L^2 := by
    have h := mul_le_mul_of_nonneg_left hBoundLog (show 0 ≤ 16*(X:ℝ) by positivity)
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  have hC : (2*(m:ℝ)+1)*((2*Real.exp 10)*H/S) ≤ 6*Real.exp 10*U*H/S := by
    have hh := mul_le_mul_of_nonneg_right (show 2*(m:ℝ)+1≤3*U by linarith)
      (show 0 ≤ (2*Real.exp 10)*H/S by positivity)
    exact hh.trans_eq (by ring)
  have hA : Real.exp 11*(1+Real.log V)*Real.exp (-Real.log u/(4*Real.log V)) ≤
      (3*Real.exp (23/2))*L*Real.exp (-U/24) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left (show 1+Real.log V≤3*L by linarith)
      (Real.exp_pos 11).le) hExp (Real.exp_pos _).le (by positivity)
    exact hh.trans_eq (by
      rw [show (23/2:ℝ)=11+1/2 by norm_num,Real.exp_add]
      ring)
  have hMul :
      (16*(X:ℝ)/(Real.log (W:ℝ))^2) *
        ((2*(m:ℝ)+1)*((2*Real.exp 10)*H/S)) *
        (Real.exp 11*(1+Real.log V)*Real.exp (-Real.log u/(4*Real.log V))) ≤
      epsConstant*((X:ℝ)/S)/U := by
    have h := mul_le_mul (mul_le_mul hF hC (by positivity) (by positivity)) hA
      (by positivity) (by positivity)
    refine h.trans ?_
    calc
      _ = ((16*16384^2)*(6*3)*Real.exp (43/2))*((X:ℝ)/S)*
          (U^2*Real.exp (-U/24)) := by
        have hHU : H=U*L := by rw [hL]; field_simp
        rw [hHU,show (43/2:ℝ)=10+23/2 by norm_num,Real.exp_add]
        field_simp <;> ring
      _ ≤ ((16*16384^2)*(6*3)*Real.exp (43/2))*((X:ℝ)/S)*
          ((6*24^3:ℝ)/U) := mul_le_mul_of_nonneg_left (exp_suppress hU) (by positivity)
      _ = _ := by unfold epsConstant; ring
  have hWE : (W:ℝ)^640 ≤ Real.sqrt T := by
    have hLog : Real.log W ≤ L/8192 := by
      have h := Real.log_le_log hWpos hWle
      rwa [Real.log_exp] at h
    have hLx : L ≤ H/2 := by rw [hL]; gcongr
    rw [← Real.exp_log (pow_pos hWpos _), Real.log_pow,
      ← Real.exp_log (Real.sqrt_pos.mpr hT0), Real.log_sqrt hT0.le]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith only [hLog,hLx,hXlog,hTlog]
  have hR := hB.trans (add_le_add hMul (mul_le_mul_of_nonneg_left hWE (by positivity : 0 ≤ (T:ℝ)^2)))
  simpa only [binnedCover,X,Nat.cast_pow,H,U,S,m,y,W,V,u] using hR

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat
open scoped ArithmeticFunction.sigma

noncomputable def smallPrimeU (X T : ℕ) : ℝ :=
  (T:ℝ)/Real.exp (Real.sqrt (Real.log (X:ℝ)))

noncomputable def shiftedSquareCover (X Y s : ℕ) : Finset ℕ :=
  (range X).filter (fun n => n+s ∈ squareExceptions X Y)

noncomputable def directionCover (X T s t : ℕ) : Finset ℕ :=
  (shiftedSquareCover X (squareCut X) s ∪
    smallPrimeCover X T (squareCut X) s (smallPrimeU X T)) ∪
    (activeBins X).biUnion (fun j => binnedCover X T j s t)

theorem shiftedSquareCover_card_le {X Y s : ℕ} (hY : 2 ≤ Y) :
    ((shiftedSquareCover X Y s).card:ℝ) ≤ X/((Y:ℝ)-1) := by
  let S := shiftedSquareCover X Y s
  have hi : Set.InjOn (fun n : ℕ => n+s) S := fun a ha b hb h => Nat.add_right_cancel h
  have hsub : S.image (fun n => n+s) ⊆ squareExceptions X Y := by
    intro v hv
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hn).2
  have h := (Finset.card_image_of_injOn hi).symm.trans_le (Finset.card_le_card hsub)
  exact (by exact_mod_cast h : (S.card:ℝ) ≤ (squareExceptions X Y).card).trans (squareExceptions_card_le hY)

theorem finset_card_union_real {A B : Finset ℕ} :
    (((A∪B).card : ℕ) : ℝ) ≤ (A.card:ℝ)+(B.card:ℝ) := by
  exact_mod_cast Finset.card_union_le A B

theorem cube_good_cover {T n : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ))
    (hnX : n < T^3) (hσ : σ 0 n = σ 0 (n+1)) :
    n ∈ range (T+1) ∪ (directionCover (T^3) T 0 1 ∪ directionCover (T^3) T 1 0) := by
  classical
  let X := T^3
  let Y := squareCut X
  by_cases hnT : n ≤ T
  · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  apply Finset.mem_union_right
  have hT1 : 1 ≤ T := by
    by_contra h
    have hz : T=0 := by omega
    norm_num [hz] at hT
  by_cases hS : n ∈ squareExceptions X Y
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnX,by simpa using hS⟩
  by_cases hR : n+1 ∈ squareExceptions X Y
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnX,hR⟩
  have hTlog : 0 < Real.log (T:ℝ) := (by positivity : 0 < (2:ℝ)^40).trans_le hT
  have hH : Real.log (X:ℝ) = 3 * Real.log (T:ℝ) := by dsimp [X]; rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hX : 4 ≤ Real.sqrt (Real.log (X:ℝ)) := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ)≤4)]
    apply Real.sqrt_le_sqrt
    norm_num at hT
    linarith
  have hY : 2 ≤ Y := (squareCut_log_bounds (X:=X) hX).1
  have hchoose {s t a b k l q : ℕ}
      (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0)
      (has : a*k=n+s) (hbt : b*l=n+t)
      (ha : a≠0) (hb : b≠0) (hk0 : k≠0) (hl0 : l≠0)
      (hq : q.Prime) (hqk : q ∣ k) (haT : a≤T) (hbT : b≤T) (haq : T<a*q)
      (hA : ∀ p : ℕ, p.Prime → p∣a → p≤q)
      (hK : ∀ p : ℕ, p.Prime → p∣k → q≤p)
      (hL : ∀ p : ℕ, p.Prime → p∣l → q≤p) :
      n ∈ directionCover X T s t := by
    have hn0 : 0<n := by omega
    have hsX : n+s ≤ X := by rcases hst with ⟨h,_⟩|⟨h,_⟩ <;> omega
    have htX : n+t ≤ X := by rcases hst with ⟨_,h⟩|⟨_,h⟩ <;> omega
    have hSa : n+s ∉ squareExceptions X Y := by
      rcases hst with ⟨hs,_⟩|⟨hs,_⟩
      · simpa [hs] using hS
      · simpa [hs] using hR
    have hTb : n+t ∉ squareExceptions X Y := by
      rcases hst with ⟨_,ht⟩|⟨_,ht⟩
      · simpa [ht] using hR
      · simpa [ht] using hS
    have hσ' : σ 0 (n+s) = σ 0 (n+t) := by
      rcases hst with ⟨hs,ht⟩|⟨hs,ht⟩
      · simpa [hs,ht] using hσ
      · simpa [hs,ht] using hσ.symm
    have hql (C : ℝ) (hC : 0<C) (h : (q:ℝ) ≤ C) : (T:ℝ)/C ≤ a := by
      have h' : (T:ℝ) < (a:ℝ)*q := by exact_mod_cast haq
      have hf := mul_le_mul_of_nonneg_left h (show 0 ≤ (a:ℝ) by positivity)
      apply (div_le_iff₀ hC).mpr
      linarith
    by_cases hqY : q < Y
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      have hqE : (q:ℝ) ≤ Real.exp (Real.sqrt (Real.log (X:ℝ))) :=
        (by exact_mod_cast hqY.le : (q:ℝ) ≤ Y).trans (Nat.floor_le (Real.exp_pos _).le)
      refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,haT⟩,?_ ,
        hql _ (Real.exp_pos _) hqE⟩, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnX,hn0,hsX,⟨k,has.symm⟩⟩⟩
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(hA p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)).trans hqY.le, Nat.prime_of_mem_primeFactors hp⟩
    · have hqX : q ≤ X := (Nat.le_of_dvd (by omega : 0 < n+s)
        (hqk.trans ⟨a,by rw [mul_comm,has]⟩)).trans hsX
      obtain ⟨j,hj,hlo,hhi⟩ := exists_bin hX (le_of_not_gt hqY) hqX
      let y := binCut X j
      have hy0 : 0 < y := Real.exp_pos _
      have hy : 1 < y := by
        dsimp [y,binCut]
        rw [← Real.exp_zero]
        apply Real.exp_lt_exp.mpr
        unfold binLog
        have hx : 0<Real.log (X:ℝ) := by linarith [hH]
        positivity
      have hqy : (q:ℝ) ≤ y^2 := by
        apply (Real.log_le_log_iff (by exact_mod_cast hq.pos) (pow_pos hy0 _)).mp
        rw [Real.log_pow,show Real.log y=binLog X j from Real.log_exp _]
        norm_num
        exact hhi
      have hyq : y ≤ (q:ℝ) := by
        dsimp [y,binCut]
        rw [← Real.exp_log (show (0:ℝ)<q by exact_mod_cast hq.pos)]
        exact Real.exp_le_exp.mpr hlo
      have hV : a.primeFactors ⊆ Nat.primesLE (binPrimes X j) := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpq : (p:ℝ) ≤ q := by exact_mod_cast hA p hpp (Nat.dvd_of_mem_primeFactors hp)
        exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpq.trans hqy),hpp⟩
      have hj' : j ∈ activeBins X := Finset.mem_filter.mpr ⟨hj,by
        have hypos : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
        have hyq' : (Y:ℝ)≤q := by exact_mod_cast le_of_not_gt hqY
        exact (Real.log_le_log hypos hyq').trans hhi⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j,hj',mem_blockCover_of_split hn0 hnX hsX htX ha hb hk0 hl0 has hbt haT hbT
        (hql _ (pow_pos hy0 _) hqy) hV hy (le_of_not_gt hqY) hyq hK hL hSa hTb hσ' rfl⟩
  obtain ⟨a,k,p,has,ha,hk,hp,hpk,haT,haq,hA,hK⟩ :=
    exists_factor_split hT1 (show T < n by omega)
  obtain ⟨b,l,q,hbt,hb,hl,hq,hql,hbT,hbq,hB,hL⟩ :=
    exists_factor_split hT1 (show T < n+1 by omega)
  have has' : a*k=n+0 := by simpa using has
  rcases le_total p q with h | h
  · exact Finset.mem_union_left _ (hchoose (Or.inl ⟨rfl,rfl⟩) has' hbt ha hb hk hl
      hp hpk haT hbT haq hA hK (fun r hr hd => h.trans (hL r hr hd)))
  · exact Finset.mem_union_right _ (hchoose (Or.inr ⟨rfl,rfl⟩) hbt has' hb ha hl hk
      hq hql hbT haT hbq hB hL (fun r hr hd => h.trans (hK r hr hd)))

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat
open scoped ArithmeticFunction.sigma

theorem cube_log_bounds {T : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ)) :
    let H := Real.log ((T^3 : ℕ):ℝ)
    let S := Real.sqrt (Real.log H)
    (0:ℝ)<T ∧ 1<H ∧ 4 ≤ Real.sqrt H ∧ 0 < S ∧ S ≤ H ∧
      (numBins (T^3):ℝ)*S ≤ Real.sqrt T ∧
      S ≤ ((squareCut (T^3):ℕ):ℝ)-1 := by
  dsimp
  let X := T^3
  let H := Real.log (X:ℝ)
  let L := Real.log (T:ℝ)
  let S := Real.sqrt (Real.log H)
  have hT0 : (0:ℝ)<T := by
    by_contra hn
    have h : T=0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg T) : (T:ℝ)=0)
    norm_num [h] at hT
  have hL : (2:ℝ)^40 ≤ L := hT
  have hH : H=3*L := by dsimp [H,X,L]; rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hHbig : 1024 ≤ H := by norm_num at hL; linarith
  have hHs : 4 ≤ Real.sqrt H := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ)≤4)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hH1 : 1 < H := by linarith
  have hS0 : 0 < S := Real.sqrt_pos.mpr (Real.log_pos hH1)
  have hSH : S ≤ Real.sqrt H := Real.sqrt_le_sqrt (by linarith [Real.log_le_sub_one_of_pos (show 0<H by linarith)])
  have hS' : Real.sqrt H ≤ H := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith,by nlinarith [mul_nonneg (show 0≤H by linarith) (show 0≤H-1 by linarith)]⟩
  refine ⟨hT0,hH1,hHs,hS0,hSH.trans hS',?_,?_⟩
  · have hN : (numBins X:ℝ) ≤ H+2 := by
      have hc := Nat.ceil_lt_add_one (show 0 ≤ H by linarith)
      dsimp [numBins]
      push_cast
      linarith
    have hpow := Real.pow_div_factorial_le_exp (L/2) (by positivity) 3
    have hh : Real.exp (L/2) = Real.sqrt T := by
      rw [← Real.exp_log (Real.sqrt_pos.mpr hT0),Real.log_sqrt hT0.le]
    rw [hh] at hpow
    have h' : (H+2)*H ≤ (L/2)^3 / ((3:ℕ).factorial : ℝ) := by
      rw [hH]
      norm_num at hL ⊢
      nlinarith only [mul_nonneg (show 0 ≤ L-1000 by linarith) (sq_nonneg L),
        mul_nonneg (show 0 ≤ L-1000 by linarith) (show 0 ≤ L by positivity)]
    exact (mul_le_mul hN (hSH.trans hS') hS0.le (by positivity)).trans (h'.trans hpow)
  · have hc := (squareCut_log_bounds (X:=X) hHs).2.1
    have hcut : Real.exp (Real.sqrt H/2) ≤ (squareCut X:ℝ) := by
      have hY := (squareCut_log_bounds (X:=X) hHs).1
      exact (Real.le_log_iff_exp_le (by exact_mod_cast (show 0<squareCut X by omega))).mp hc
    have hp := Real.pow_div_factorial_le_exp (Real.sqrt H/2) (by positivity) 2
    have hs2 := Real.sq_sqrt (show 0≤H by linarith)
    have hHs2 : 32 ≤ Real.sqrt H := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ)≤32)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    norm_num at hp
    nlinarith only [hp,hcut,hSH,hs2,hHs2,
      mul_nonneg (show 0 ≤ Real.sqrt H - 32 by linarith) (Real.sqrt_nonneg H)]

theorem bin_geom_sum (J : Finset ℕ) :
    (∑ j ∈ J, ((2:ℝ)^(j+1))⁻¹) ≤ 1 := by
  have haux : (fun j : ℕ => ((2:ℝ)^(j+1))⁻¹) = fun j => (1/2:ℝ)*(1/2:ℝ)^j := by
    funext j
    rw [← inv_pow, _root_.pow_succ']
    norm_num
  rw [haux,← Finset.mul_sum]
  have hsum := (summable_geometric_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).sum_le_tsum J (by intros; positivity)
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hsum
  norm_num at hsum
  linarith

noncomputable def epsSmallConstant : ℝ := 576*Real.exp (23/2)

theorem smallPrimeCube_bound {T s : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ)) :
    ((smallPrimeCover (T^3) T (squareCut (T^3)) s (smallPrimeU (T^3) T)).card:ℝ) ≤
      epsSmallConstant * (((T^3:ℕ):ℝ) / Real.sqrt (Real.log (Real.log ((T^3:ℕ):ℝ)))) := by
  let X := T^3
  let H := Real.log (X:ℝ)
  let S := Real.sqrt (Real.log H)
  let Z := Real.sqrt H
  let V := squareCut X
  let u := smallPrimeU X T
  obtain ⟨hT0,hH,hZ,hS,hSH,_,_⟩ := cube_log_bounds hT
  have hXlog : H=3*Real.log (T:ℝ) := by dsimp [H,X]; rw [Nat.cast_pow,Real.log_pow]; norm_num
  have hH0 : 0 < H := by linarith
  have hZ0 : 0 < Z := by dsimp [Z]; positivity
  have hu : 0<u := by dsimp [u,smallPrimeU]; positivity
  obtain ⟨hV, hVlo,hVhi⟩ := squareCut_log_bounds (X:=X) hZ
  have ht : 0 < Real.log (V:ℝ) := by
    change Z/2 ≤ Real.log (V:ℝ) at hVlo
    linarith
  have htail : -Real.log u / (4*Real.log (V:ℝ)) ≤ 1/2-Z/12 := by
    have hlogu : Real.log u = Real.log (T:ℝ)-Z := by
      dsimp [u,smallPrimeU,Z,H]
      rw [Real.log_div hT0.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogu]
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hVhi (show 0 ≤ Z by positivity)
    nlinarith only [hVlo,hm,Real.sq_sqrt hH0.le,hXlog]
  have hS' : S ≤ Z := Real.sqrt_le_sqrt (by linarith [Real.log_le_sub_one_of_pos hH0])
  have hb := smallPrimeCover_bound (X:=X) (T:=T) (s:=s) hV hu
  refine hb.trans ?_
  have hv : 1+Real.log (V:ℝ) ≤ 2*Z := by linarith
  have he := Real.exp_le_exp.mpr htail
  rw [Real.exp_sub] at he
  have hp := Real.pow_div_factorial_le_exp (Z/12) (by positivity) 2
  norm_num at hp
  have he2 : Real.exp 11*(1+Real.log (V:ℝ))*Real.exp (-Real.log u/(4*Real.log V)) * S ≤ epsSmallConstant := by
    calc
      _ ≤ Real.exp 11*(2*Z)*(Real.exp (1/2)/Real.exp (Z/12))*Z := by
        have hv' := mul_le_mul_of_nonneg_left hv (Real.exp_pos 11).le
        have hm := mul_le_mul hv' he (Real.exp_pos _).le (by positivity)
        exact mul_le_mul hm hS' hS.le (by positivity)
      _ = Real.exp (23/2) * (2*Z^2 / Real.exp (Z/12)) := by
        rw [show (23/2:ℝ)=11+1/2 by norm_num, Real.exp_add]
        ring
      _ ≤ _ := by
        unfold epsSmallConstant
        rw [mul_comm 576]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply (div_le_iff₀ (Real.exp_pos _)).mpr
        nlinarith only [hp]
  have hTcast : 0 ≤ (X:ℝ) := by positivity
  have hz := mul_le_mul_of_nonneg_left he2 hTcast
  unfold epsSmallConstant at hz ⊢
  have h' := (le_div_iff₀ hS).mpr (show (X:ℝ)*(Real.exp 11*(1+Real.log (V:ℝ))*
    Real.exp (-Real.log u/(4*Real.log V)))*Real.sqrt (Real.log H) ≤
      (X:ℝ)*(576*Real.exp (23/2)) by nlinarith only [hz])
  convert h' using 1 <;> ring

theorem directionCube_bound {T s t : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ))
    (hst : s=0 ∧ t=1 ∨ s=1 ∧ t=0) :
    ((directionCover (T^3) T s t).card:ℝ) ≤
      (epsConstant+epsSmallConstant+2) *
       (((T^3:ℕ):ℝ) / Real.sqrt (Real.log (Real.log ((T^3:ℕ):ℝ)))) := by
  let X := T^3
  let Y := squareCut X
  let H := Real.log (X:ℝ)
  let S := Real.sqrt (Real.log H)
  let G := (X:ℝ)/S
  obtain ⟨hT0,hH,hZ,hS,hSH,hN,hy⟩ := cube_log_bounds hT
  have hY := (squareCut_log_bounds (X:=X) hZ).1
  have hsq : ((shiftedSquareCover X Y s).card:ℝ) ≤ G := by
    exact (shiftedSquareCover_card_le hY).trans (div_le_div_of_nonneg_left (by positivity) hS hy)
  have hsmall := smallPrimeCube_bound (T:=T) (s:=s) hT
  have hbin : ((((activeBins X).biUnion (fun j => binnedCover X T j s t)).card:ℝ)) ≤
      (epsConstant+1)*G := by
    have hc : ((((activeBins X).biUnion (fun j => binnedCover X T j s t)).card:ℝ)) ≤
        ∑ j ∈ activeBins X, ((binnedCover X T j s t).card:ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine hc.trans ?_
    have hM : ((activeBins X).card:ℝ) ≤ numBins X := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range (numBins X))
    have hnon : 0 ≤ epsConstant*G := by unfold epsConstant G; positivity
    have hsum (j : ℕ) (hj : j ∈ activeBins X) : ((binnedCover X T j s t).card:ℝ) ≤
        epsConstant * G * ((2:ℝ)^(j+1))⁻¹ + (T:ℝ)^2 * Real.sqrt T := by
      simpa [X,G,S,H,Nat.cast_pow,div_eq_mul_inv] using binnedCover_estimate hT hst hj
    have herr : ((activeBins X).card:ℝ) * ((T:ℝ)^2*Real.sqrt T) ≤ G := by
      apply (le_div_iff₀ hS).mpr
      change ((activeBins X).card:ℝ) * ((T:ℝ)^2*Real.sqrt T) * S ≤ (X:ℝ)
      have hsq := Real.sq_sqrt hT0.le
      have hcast : (X:ℝ) = (T:ℝ)^3 := by simp [X]
      rw [hcast]
      change (numBins X:ℝ)*S ≤ Real.sqrt T at hN
      have hhN : ((activeBins X).card:ℝ)*S ≤ Real.sqrt T :=
        (mul_le_mul_of_nonneg_right hM hS.le).trans hN
      calc
        _ = ((activeBins X).card:ℝ)*S*((T:ℝ)^2*Real.sqrt T) := by ring
        _ ≤ Real.sqrt T*((T:ℝ)^2*Real.sqrt T) :=
          mul_le_mul_of_nonneg_right hhN (by positivity)
        _ = (T:ℝ)^2*(Real.sqrt T)^2 := by ring
        _ = _ := by rw [hsq]; ring
    calc
      _ ≤ ∑ j ∈ activeBins X, (epsConstant*G*((2:ℝ)^(j+1))⁻¹ + (T:ℝ)^2*Real.sqrt T) :=
        Finset.sum_le_sum hsum
      _ = epsConstant*G*(∑ j ∈ activeBins X, ((2:ℝ)^(j+1))⁻¹) +
          ((activeBins X).card:ℝ)*((T:ℝ)^2*Real.sqrt T) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      _ ≤ epsConstant*G*1+G := add_le_add (mul_le_mul_of_nonneg_left (bin_geom_sum _) hnon) herr
      _ = _ := by ring
  have hc := finset_card_union_real
    (A := shiftedSquareCover X Y s ∪ smallPrimeCover X T Y s (smallPrimeU X T))
    (B := (activeBins X).biUnion (fun j => binnedCover X T j s t))
  have hd := finset_card_union_real (A := shiftedSquareCover X Y s)
    (B := smallPrimeCover X T Y s (smallPrimeU X T))
  have he := hc.trans (add_le_add (hd.trans (add_le_add hsq hsmall)) hbin)
  change ((directionCover X T s t).card:ℝ) ≤ _ at he
  exact he.trans_eq (by dsimp [G,S,H,X]; ring)

end OMA.Erdos946

namespace OMA.Erdos946

open Finset Real Nat Filter Asymptotics
open scoped ArithmeticFunction.sigma

noncomputable def epsTotalConstant : ℝ := 1 + 2*(epsConstant+epsSmallConstant+2)

theorem cube_divisor_count {T : ℕ} (hT : (2:ℝ)^40 ≤ Real.log (T:ℝ)) :
    (((Finset.range (T^3)).filter (fun n => σ 0 n = σ 0 (n+1))).card:ℝ) ≤
      epsTotalConstant * (((T^3:ℕ):ℝ) / Real.sqrt (Real.log (Real.log ((T^3:ℕ):ℝ)))) := by
  let X := T^3
  let S := Real.sqrt (Real.log (Real.log (X:ℝ)))
  let D := directionCover X T 0 1
  let E := directionCover X T 1 0
  have hsub : ((Finset.range X).filter (fun n => σ 0 n = σ 0 (n+1))) ⊆
       Finset.range (T+1) ∪ (D ∪ E) := by
    intro n hn
    obtain ⟨hnX,hσ⟩ := Finset.mem_filter.mp hn
    exact cube_good_cover hT (Finset.mem_range.mp hnX) hσ
  obtain ⟨hT0,hH,hZ,hS,hSH,hN,hy⟩ := cube_log_bounds hT
  have hT1 : (1:ℝ)<T := by
    by_contra h
    linarith [Real.log_nonpos hT0.le (le_of_not_gt h)]
  have hT2 : 2 ≤ T := by exact_mod_cast hT1
  have hS' : S ≤ Real.sqrt T := by
    have hN1 : (1:ℝ)≤numBins X := by
      exact_mod_cast (show 1≤numBins X by unfold numBins; omega)
    linarith only [hN,mul_le_mul_of_nonneg_right hN1 hS.le]
  have hfirst : ((Finset.range (T+1)).card:ℝ) ≤ (X:ℝ)/S := by
    rw [Finset.card_range,Nat.cast_add,Nat.cast_one]
    apply (le_div_iff₀ hS).mpr
    have hTsqrt : Real.sqrt (T:ℝ) ≤ T := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hT0.le,by nlinarith [mul_nonneg hT0.le (show 0≤(T:ℝ)-1 by linarith)]⟩
    have hS2 : S≤(T:ℝ) := hS'.trans hTsqrt
    have hT2' : (2:ℝ)≤T := by exact_mod_cast hT2
    have h1 : (T:ℝ)+1 ≤ (T:ℝ)^2 := by nlinarith
    calc
      _ ≤ (T:ℝ)^2*(T:ℝ) := mul_le_mul h1 hS2 hS.le (by positivity)
      _ = _ := by dsimp [X]; push_cast; ring
  have hD := directionCube_bound hT (s:=0) (t:=1) (Or.inl ⟨rfl,rfl⟩)
  have hE := directionCube_bound hT (s:=1) (t:=0) (Or.inr ⟨rfl,rfl⟩)
  have hcard : ((((Finset.range X).filter (fun n => σ 0 n = σ 0 (n+1))).card):ℝ) ≤
      (((Finset.range (T+1)) ∪ (D∪E)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hf := finset_card_union_real (A := Finset.range (T+1)) (B := D ∪ E)
  have hg := finset_card_union_real (A := D) (B := E)
  have hd := hg.trans (add_le_add hD hE)
  exact (hcard.trans (hf.trans (add_le_add hfirst hd))).trans_eq (by
    dsimp [epsTotalConstant,S,X]
    ring)

theorem real_to_cube {x : ℝ} (hx : 1 ≤ x) :
    ∃ T : ℕ, x < ((T^3 : ℕ):ℝ) ∧ ((T^3:ℕ):ℝ) ≤ 27*x ∧ 0 < (T:ℝ) := by
  let y := (x+1)^(1/3:ℝ)
  let T := ⌈y⌉₊
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hy : y ≤ (T:ℝ) := Nat.le_ceil _
  have hT : (T:ℝ) ≤ y+1 := (Nat.ceil_lt_add_one hy0.le).le
  have hyv : y^3=x+1 := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast (by positivity : 0≤x+1)]
    norm_num
  refine ⟨T, ?_,?_,hy0.trans_le hy⟩
  · rw [Nat.cast_pow, ← sub_zero x]
    linarith only [pow_le_pow_left₀ hy0.le hy 3,hyv]
  · have hxy : y ≤ 2*x^(1/3:ℝ) := by
      calc
        _ ≤ (2*x)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ ≤ _ := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0.le]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1:ℝ)≤2) (by norm_num : (1/3:ℝ)≤1)
    have hxrt : 1 ≤ x^(1/3:ℝ) := Real.one_le_rpow hx (by norm_num)
    have hTall : (T:ℝ) ≤ 3*x^(1/3:ℝ) := by linarith
    have hh := pow_le_pow_left₀ (show (0:ℝ)≤T by positivity) hTall 3
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hh
    norm_num at hh
    exact_mod_cast hh

theorem eps_bound : Erdos946.erdos946Count =O[atTop]
    (fun x : ℝ => x / Real.sqrt (Real.log (Real.log x))) := by
  refine Asymptotics.IsBigO.of_bound (27*epsTotalConstant) ?_
  filter_upwards [eventually_ge_atTop (Real.exp (3 * (2:ℝ)^40))] with x hx
  have he : (1:ℝ) < Real.exp (3*(2:ℝ)^40) := Real.one_lt_exp_iff.mpr (by positivity)
  have hx1 : (1:ℝ) < x := he.trans_le hx
  have hx0 : 0 < x := by linarith
  obtain ⟨T,hX,hX',hT0⟩ := real_to_cube hx1.le
  have hX0 : (0:ℝ) < ((T^3 : ℕ):ℝ) := hx0.trans hX
  have hT : (2:ℝ)^40 ≤ Real.log (T:ℝ) := by
    have hl := Real.log_le_log (Real.exp_pos _) (hx.trans hX.le)
    rw [Real.log_exp,Nat.cast_pow,Real.log_pow] at hl
    norm_num at hl ⊢
    linarith
  have hlog : 1 < Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rw [Real.log_exp] at h
    norm_num at h
    linarith
  have hlogs : 0 < Real.log (Real.log x) := Real.log_pos hlog
  have hD : Real.sqrt (Real.log (Real.log x)) ≤
      Real.sqrt (Real.log (Real.log ((T^3:ℕ):ℝ))) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (Real.log_le_log hx0 hX.le))
  have hbound := cube_divisor_count hT
  unfold Erdos946.erdos946Count
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hsub : (((Finset.range (⌊x⌋₊+1)).filter (fun n => σ 0 n = σ 0 (n+1)))) ⊆
      (Finset.range (T^3)).filter (fun n => σ 0 n = σ 0 (n+1)) := by
    apply Finset.filter_subset_filter
    apply Finset.range_mono
    have hf : (⌊x⌋₊ : ℝ) < ((T^3:ℕ):ℝ) := (Nat.floor_le hx0.le).trans_lt hX
    exact Nat.succ_le_iff.mpr (by exact_mod_cast hf)
  have hcard : ((((Finset.range (⌊x⌋₊+1)).filter (fun n => σ 0 n = σ 0 (n+1))).card):ℝ) ≤
      (((Finset.range (T^3)).filter (fun n => σ 0 n = σ 0 (n+1))).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply hcard.trans (hbound.trans ?_)
  have hreal : (((T^3 : ℕ):ℝ) / Real.sqrt (Real.log (Real.log ((T^3:ℕ):ℝ)))) ≤
      (27*x) / Real.sqrt (Real.log (Real.log x)) :=
    div_le_div₀ (by positivity) hX' (Real.sqrt_pos.mpr hlogs) hD
  exact (mul_le_mul_of_nonneg_left hreal (by unfold epsTotalConstant epsConstant epsSmallConstant; positivity)).trans_eq
    (by ring)

end OMA.Erdos946

/-- Erdős, Pomerance and Sárközy, 1987, Theorem 2.1 and its remarks for the divisor function. -/
theorem OMA.solution : type_of% @Erdos946.erdos_946.variants.upper_bound := by
  exact OMA.Erdos946.eps_bound

/-
License for the adapted PrimeNumberTheoremAnd code

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
