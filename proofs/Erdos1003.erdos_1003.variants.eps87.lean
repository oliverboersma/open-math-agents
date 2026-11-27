import FormalConjectures.ErdosProblems.«1003»
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
SPDX-License-Identifier: Apache-2.0

Theorem 2 of P. Erdős, C. Pomerance and A. Sárközy,
On locally repeated values of certain arithmetic functions. II,
Acta Math. Hungar. 49 (1987), 251–259, §4.
Generic smooth-number and counting lemmas are adapted from the
companion amicable-pair formalization by amp2600 and Codex.
-/

open Finset Filter Real
open scoped Nat BigOperators Topology

namespace EqualTotientCount

private theorem card_divisor_fiber {n d : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ n ∧ d ∣ m) :
    (S.card : ℝ) ≤ (n : ℝ) / d := by
  have hc : S.card ≤ (Icc 1 (n / d)).card := by
    apply card_le_card_of_injOn (fun m => m / d)
    · intro m hm
      obtain ⟨hm0, hmn, hmd⟩ := hS m hm
      exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hd).mpr (by simpa using Nat.le_of_dvd hm0 hmd),
        Nat.div_le_div_right hmn⟩
    · intro a ha b hb hab
      exact Nat.ext_div_modEq hab ((Nat.modEq_zero_iff_dvd.mpr (hS a ha).2.2).trans
        (Nat.modEq_zero_iff_dvd.mpr (hS b hb).2.2).symm)
  simp [Nat.card_Icc] at hc
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast (Nat.le_div_iff_mul_le hd).mp hc

private theorem card_congruence_fiber {n d r : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≤ n ∧ m ≡ r [MOD d]) :
    (S.card : ℝ) ≤ 1 + (n : ℝ) / d := by
  have hc : S.card ≤ (range (n / d + 1)).card := by
    apply card_le_card_of_injOn (fun m => m / d)
    · intro m hm
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hS m hm).1))
    · intro a ha b hb hab
      exact Nat.ext_div_modEq hab ((hS a ha).2.trans (hS b hb).2.symm)
  simp only [card_range] at hc
  have hh : S.card ≤ n / d + 1 := hc
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := by
    rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self n d
  have hc' : (S.card : ℝ) ≤ ((n / d : ℕ) : ℝ) + 1 := by exact_mod_cast hh
  linarith

private theorem card_linear_congruence {n c d r : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≤ n ∧ c * m ≡ r [MOD d]) :
    (S.card : ℝ) ≤ 1 + (n : ℝ) * d.gcd c / d := by
  have hgd := Nat.gcd_dvd_left d c
  have hgd0 := Nat.gcd_pos_of_pos_left c hd
  have hdiv : 0 < d / d.gcd c :=
    Nat.div_pos (Nat.le_of_dvd hd hgd) hgd0
  have hk : ((d / d.gcd c : ℕ) : ℝ) * ((d.gcd c : ℕ) : ℝ) = (d : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hgd
  by_cases hempty : S.Nonempty
  · obtain ⟨m₀, hm₀⟩ := hempty
    have hh := card_congruence_fiber hdiv S (r := m₀) (fun m hm =>
      ⟨(hS m hm).1, ((hS m hm).2.trans (hS m₀ hm₀).2.symm).cancel_left_div_gcd hd⟩)
    convert hh using 2
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hdiv' : (0 : ℝ) < ((d / d.gcd c : ℕ) : ℝ) := by exact_mod_cast hdiv
    apply (div_eq_iff hd'.ne').2
    rw [← hk]
    field_simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [hempty]
    positivity

private theorem card_of_fiber_bounds {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (w : β → ℝ)
    (hT : ∀ x ∈ S, f x ∈ T)
    (hw : ∀ y ∈ T, ((S.filter fun x => f x = y).card : ℝ) ≤ w y) :
    (S.card : ℝ) ≤ ∑ y ∈ T, w y := by
  rw [card_eq_sum_card_fiberwise hT, Nat.cast_sum]
  exact sum_le_sum hw

private theorem card_of_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (F : β → Finset α) (w : β → ℝ)
    (hCover : ∀ x ∈ S, ∃ y ∈ T, x ∈ F y)
    (hBound : ∀ y ∈ T, ((F y).card : ℝ) ≤ w y) :
    (S.card : ℝ) ≤ ∑ y ∈ T, w y := by
  have hsub : S ⊆ T.biUnion F := fun x hx => mem_biUnion.mpr (hCover x hx)
  calc
    (S.card : ℝ) ≤ ((T.biUnion F).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ y ∈ T, ((F y).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ _ := sum_le_sum hBound

private theorem harmonic_bound_finset {N : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 N) :
    ∑ n ∈ S, (n : ℝ)⁻¹ ≤ 1 + log N := by
  calc
    ∑ n ∈ S, (n : ℝ)⁻¹ ≤ ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity
    _ = harmonic N := by simp [harmonic_eq_sum_Icc]
    _ ≤ _ := harmonic_le_one_add_log N

private noncomputable def naturalPower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' m n := by push_cast; exact Real.mul_rpow (by positivity) (by positivity)

private noncomputable def smoothEuler (N : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-s))⁻¹

private theorem smoothEuler_hasSum (N : ℕ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : N.smoothNumbers => ((m : ℕ) : ℝ) ^ (-s)) (smoothEuler N s) := by
  refine (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := naturalPower (-s)) ?_ N).2
  intro p hp
  change ‖(p : ℝ) ^ (-s)‖ < 1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

private theorem sum_smooth_rpow_le {N : ℕ} {s : ℝ} (hs : 0 < s) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ∈ N.smoothNumbers) :
    ∑ n ∈ S, (n : ℝ) ^ (-s) ≤ smoothEuler N s := by
  classical
  let e : S → ↥N.smoothNumbers := fun n => ⟨n.val, hS n.val n.prop⟩
  let T : Finset N.smoothNumbers := S.attach.map ⟨e,
    fun a b h => Subtype.ext (congrArg (fun x : N.smoothNumbers => x.val) h)⟩
  have h := smoothEuler_hasSum N hs
  rw [← h.tsum_eq]
  calc
    ∑ n ∈ S, (n : ℝ) ^ (-s) = ∑ n ∈ T, ((n : ℕ) : ℝ) ^ (-s) := by
      rw [show ∑ n ∈ T, ((n : ℕ) : ℝ) ^ (-s) = ∑ n ∈ S.attach, ((n : ℕ) : ℝ) ^ (-s) by
        simp only [T, Finset.sum_map]; rfl]
      exact (Finset.sum_attach S (fun k : ℕ => (k : ℝ) ^ (-s))).symm
    _ ≤ _ := h.summable.sum_le_tsum T fun _ _ => Real.rpow_nonneg (by positivity) _

private theorem rpow_series_bound {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ 1 + 1 / (s - 1) := by
  have hsum := (Real.summable_nat_rpow (p := -s)).mpr (by linarith)
  have hAnti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Set.Ici 1) := by
    intro m hm n hn hmn
    exact Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp hm]) hmn (by linarith)
  have hint : ∫ x in Set.Ioi (1 : ℝ), x ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one, Real.one_rpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hAnti)
    (by simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one)
    (fun t ht => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) (-s))
  have ht : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-s)) ≤ 1 / (s - 1) := by
    simpa [hint, Nat.add_assoc] using htail
  rw [← hsum.sum_add_tsum_nat_add 2]
  simpa [Finset.sum_range_succ, Real.zero_rpow (by linarith : -s ≠ 0)] using
    add_le_add_left ht (1 : ℝ)

private theorem smoothEuler_base_le (N : ℕ) {s : ℝ} (hs : 1 < s) :
    smoothEuler N s ≤ 1 + 1 / (s - 1) := by
  have h := smoothEuler_hasSum N (zero_lt_one.trans hs)
  rw [← h.tsum_eq]
  apply le_trans _ (rpow_series_bound hs)
  exact h.summable.tsum_le_tsum_of_inj (fun n : N.smoothNumbers => n.val) Subtype.val_injective
    (fun _ _ => Real.rpow_nonneg (by positivity) _) (fun _ => le_rfl)
    ((Real.summable_nat_rpow (p := -s)).2 (by linarith))

private theorem smoothEuler_pos {N : ℕ} {s : ℝ} (hs : 0 < s) : 0 < smoothEuler N s := by
  apply Finset.prod_pos
  intro p hp
  have hp' := (Nat.mem_primesBelow.mp hp).2
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp'.one_lt) (by linarith)))

private theorem sum_log_primes_div_le (N : ℕ) :
    ∑ p ∈ N.primesLE, log p / p ≤ log N + log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactor : log (N.factorial : ℝ) =
      ∑ p ∈ N.primesLE, ((N.factorial.factorization p : ℕ) : ℝ) * log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp.1).mp hp.2.1, hp.1⟩
    · intro p _
      simp
  have hterm (p : ℕ) (hp : p ∈ N.primesLE) : (N : ℝ) / p - 1 ≤ N.factorial.factorization p := by
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hquot : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add (a := N) hpp.pos
    have hfloor : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
      rw [div_sub_one hpR.ne', div_le_iff₀ hpR]
      linarith
    refine hfloor.trans ?_
    norm_cast
    rw [Nat.factorization_factorial hpp (Nat.lt_add_one (Nat.log p N))]
    have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      exact mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_of_le (Nat.log_pos hpp.one_lt hpN)⟩
    simpa using (Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1)
  have hsum : (∑ p ∈ N.primesLE, log p * ((N : ℝ) / p - 1)) ≤ log (N.factorial : ℝ) := by
    rw [hfactor]
    exact sum_le_sum (fun p hp => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hterm p hp)
        (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)))
  have hsplit : ∑ p ∈ N.primesLE, log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ N.primesLE, log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl (fun p _ => by ring)
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf : log (N.factorial : ℝ) ≤ N * log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) (by exact_mod_cast Nat.factorial_le_pow N)
  rw [hsplit] at hsum
  apply le_of_mul_le_mul_left _ hNr
  linarith only [hf, hth, hsum]

private theorem neg_log_one_sub_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 3 / 4) :
    -log (1 - b) - -log (1 - a) ≤ 4 * (b - a) := by
  have hb₀ : 0 < 1 - b := by linarith
  have ha₀ : 0 < 1 - a := by linarith
  have hd : log ((1 - a) / (1 - b)) ≤ (1 - a) / (1 - b) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha₀ hb₀)
  rw [Real.log_div ha₀.ne' hb₀.ne'] at hd
  have hdiv : (1 - a) / (1 - b) - 1 = (b - a) / (1 - b) := by field_simp; ring
  rw [hdiv] at hd
  have hle : (b - a) / (1 - b) ≤ 4 * (b - a) := by
    rw [div_le_iff₀ hb₀]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 3 / 4 - b by linarith)]
  linarith

private theorem rpow_neg_le_three_quarters {p s : ℝ} (hp : 2 ≤ p) (hs : 1 / 2 ≤ s) :
    p ^ (-s) ≤ 3 / 4 := by
  have htwo : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos : 0 < Real.sqrt (2 : ℝ) := by positivity
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  calc
    p ^ (-s) ≤ p ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
    _ ≤ _ := htwo

private theorem rpow_difference_le {p y s a : ℝ} (hp : 2 ≤ p) (hpy : p ≤ y)
    (hs : s ≤ 1) (ha : 0 ≤ a) :
    p ^ (-s) - p ^ (-(1 + a)) ≤ (1 - s + a) * y ^ (1 - s) * (log p / p) := by
  have hp₀ : 0 < p := by linarith
  have hlog : 0 ≤ log p := Real.log_nonneg (by linarith)
  let u := (1 - s + a) * log p
  have hu : 1 - exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  have hrew : p ^ (-s) * exp (-u) = p ^ (-(1 + a)) := by
    rw [Real.rpow_def_of_pos hp₀, Real.rpow_def_of_pos hp₀, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  have hrew' : p ^ (-s) = p ^ (1 - s) / p := by
    conv_lhs => rw [show -s = (1 - s) - 1 by ring]
    rw [Real.rpow_sub hp₀, Real.rpow_one]
  calc
    p ^ (-s) - p ^ (-(1 + a)) = p ^ (-s) * (1 - exp (-u)) := by rw [← hrew]; ring
    _ ≤ p ^ (-s) * u := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (1 - s + a) * p ^ (1 - s) * (log p / p) := by rw [hrew']; dsimp [u]; ring
    _ ≤ _ := by gcongr

private theorem smoothEuler_log_le {N : ℕ} (hN : 2 ≤ N) {s : ℝ} (hs : 1 / 2 ≤ s) (hs₁ : s ≤ 1) :
    log (smoothEuler N s) ≤ log (1 + log N) +
      12 * (1 + (1 - s) * log N) * (N : ℝ) ^ (1 - s) := by
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 < log (N : ℝ) := Real.log_pos (by linarith)
  let a : ℝ := (log (N : ℝ))⁻¹
  have ha : 0 < a := inv_pos.mpr hlN
  have hs₀ : 0 < s := by linarith
  have hL (v : ℝ) (hv : 0 < v) : log (smoothEuler N v) =
      ∑ p ∈ N.primesBelow, -log (1 - (p : ℝ) ^ (-v)) := by
    unfold smoothEuler
    rw [Real.log_prod]
    · exact sum_congr rfl (fun p _ => Real.log_inv _)
    · intro p hp
      exact inv_ne_zero (sub_ne_zero.mpr (Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt) (by linarith)).ne')
  have hsum : ∑ p ∈ N.primesBelow, log p / (p : ℝ) ≤ log N + log 4 := by
    apply le_trans _ (sum_log_primes_div_le N)
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpn, hpp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpn.le, hpp⟩
    · intro p hp _
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)) (by positivity)
  have hcmp : log (smoothEuler N s) - log (smoothEuler N (1 + a)) ≤
      4 * (1 - s + a) * (N : ℝ) ^ (1 - s) * (log N + log 4) := by
    rw [hL s hs₀, hL (1 + a) (by linarith), ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ N.primesBelow, 4 * (1 - s + a) * (N : ℝ) ^ (1 - s) * (log p / p) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpn, hpp⟩ := Nat.mem_primesBelow.mp hp
        have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hpy : (p : ℝ) ≤ N := by exact_mod_cast hpn.le
        have hpow := rpow_difference_le hp₂ hpy hs₁ ha.le
        have hab : (p : ℝ) ^ (-(1 + a)) ≤ (p : ℝ) ^ (-s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        have hterm := neg_log_one_sub_le hab (rpow_neg_le_three_quarters hp₂ hs)
        linarith only [hterm, mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 4 by norm_num)]
      _ ≤ _ := by rw [← mul_sum]; gcongr
  have hbase : smoothEuler N (1 + a) ≤ 1 + log N := by
    convert smoothEuler_base_le N (show 1 < 1 + a by linarith) using 1
    rw [add_sub_cancel_left, one_div, show a = (log (N : ℝ))⁻¹ from rfl, inv_inv]
  have hlog := Real.log_le_log (smoothEuler_pos (N := N) (s := 1 + a) (by linarith)) hbase
  have hl4 : log 4 ≤ 2 * log N := by
    have h := Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hN₂
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have he : 4 * (1 - s + a) * (N : ℝ) ^ (1 - s) * (log N + log 4) ≤
      12 * (1 + (1 - s) * log N) * (N : ℝ) ^ (1 - s) := by
    calc
      _ ≤ 4 * (1 - s + a) * (N : ℝ) ^ (1 - s) * (3 * log N) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by
        have haN : a * log (N : ℝ) = 1 := inv_mul_cancel₀ hlN.ne'
        linear_combination 12 * (N : ℝ) ^ (1 - s) * haN
  linarith only [hcmp, hlog, he]

private theorem recip_sum_congruence {N r a : ℕ} (hr : 0 < r) (S : Finset ℕ)
    (hS : ∀ n ∈ S, r ≤ n ∧ n ≤ N ∧ n ≡ a [MOD r]) :
    ∑ n ∈ S, (n : ℝ)⁻¹ ≤ (1 + log N) / r := by
  have hinj : Set.InjOn (fun n : ℕ => n / r) S := by
    intro n hn m hm he
    exact Nat.ext_div_modEq he ((hS n hn).2.2.trans (hS m hm).2.2.symm)
  have hsub : S.image (fun n => n / r) ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    obtain ⟨hmr, hmN, -⟩ := hS m hm
    exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hr).mpr (by simpa using hmr),
      (Nat.div_le_self _ _).trans hmN⟩
  have hsum := harmonic_bound_finset _ hsub
  calc
    ∑ n ∈ S, (n : ℝ)⁻¹ ≤ ∑ n ∈ S, (r : ℝ)⁻¹ * ((n / r : ℕ) : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hr.trans_le (hS n hn).1
      have hnr : (0 : ℝ) < ((n / r : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (hS n hn).1 hr
      rw [← mul_inv]
      exact inv_anti₀ (mul_pos (by exact_mod_cast hr) hnr) (by
        exact_mod_cast (Nat.mul_comm r (n / r)) ▸ Nat.div_mul_le_self n r)
    _ = (r : ℝ)⁻¹ * ∑ z ∈ S.image (fun n => n / r), (z : ℝ)⁻¹ := by
      rw [← mul_sum, sum_image hinj]
    _ ≤ _ := by rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem count_has_divisor {N : ℕ} (D S : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ d ∈ D, d ∣ n) :
    (S.card : ℝ) ≤ (N : ℝ) * ∑ d ∈ D, (d : ℝ)⁻¹ := by
  rw [mul_sum]
  refine card_of_cover S D (fun d => S.filter fun n => d ∣ n) (fun d => (N : ℝ) * (d : ℝ)⁻¹) ?_ ?_
  · intro n hn
    obtain ⟨d, hd, hdn⟩ := (hS n hn).2.2
    exact ⟨d, hd, mem_filter.mpr ⟨hn, hdn⟩⟩
  · intro d hd
    rw [← div_eq_mul_inv]
    apply card_divisor_fiber (hD d hd)
    intro n hn
    obtain ⟨hs, hnd⟩ := mem_filter.mp hn
    exact ⟨(hS n hs).1, (hS n hs).2.1, hnd⟩

private theorem shifted_rpow_tail {z w t : ℝ} (hz : 0 < z) (hzw : z ≤ w) (ht : 0 ≤ t) :
    w⁻¹ ≤ z ^ (-t) * w ^ (-(1 - t)) := by
  have hw := hz.trans_le hzw
  calc
    w⁻¹ = w ^ (-t) * w ^ (-(1 - t)) := by
      rw [← Real.rpow_add hw, show -t + -(1 - t) = -1 by ring, Real.rpow_neg_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hz hzw (by linarith)) (by positivity)

private theorem shifted_prime_recip_log {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ ≤ exp 1 * log (1 + log N) := by
  let t := (log (N : ℝ))⁻¹
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < log (N : ℝ) := Real.log_pos (by linarith)
  have ht : 0 < t := inv_pos.mpr hL
  have htx : (N : ℝ) ^ t = exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    have h : log (N : ℝ) * t = 1 := mul_inv_cancel₀ hL.ne'
    rw [h]
  have hkind (p) (hp : p ∈ N.primesBelow) : (p : ℝ)⁻¹ ≤ exp 1 * -log (1 - (p : ℝ) ^ (-(1 + t))) := by
    obtain ⟨hpN, hP⟩ := Nat.mem_primesBelow.mp hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hP.one_lt
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith : -(1 + t) < 0)
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hlt)
    calc
      (p : ℝ)⁻¹ = (p : ℝ) ^ t * (p : ℝ) ^ (-(1 + t)) := by
        rw [← Real.rpow_add (by linarith), show t + -(1 + t) = -1 by ring, Real.rpow_neg_one]
      _ ≤ exp 1 * (p : ℝ) ^ (-(1 + t)) := by
        rw [← htx]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpN.le) ht.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
  have hb : smoothEuler N (1 + t) ≤ 1 + log N := by
    convert smoothEuler_base_le N (show 1 < 1 + t by linarith) using 1
    rw [add_sub_cancel_left, one_div, show t = (log (N : ℝ))⁻¹ from rfl, inv_inv]
  calc
    _ ≤ ∑ p ∈ N.primesBelow, exp 1 * -log (1 - (p : ℝ) ^ (-(1 + t))) := sum_le_sum hkind
    _ = exp 1 * log (smoothEuler N (1 + t)) := by
      rw [← mul_sum]
      unfold smoothEuler
      rw [Real.log_prod]
      · simp only [Real.log_inv]
      · intro p hp
        exact inv_ne_zero (sub_ne_zero.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt) (by linarith)).ne')
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.log_le_log (smoothEuler_pos (N := N) (by linarith : 0 < 1 + t)) hb) (by positivity)

private theorem shifted_prime_weight {N K T : ℕ} (hT : 2 ≤ T)
    {s s' : ℝ} (hs' : 0 < s') (hss : s' ≤ s) (hs : s ≤ 1) :
    ∑ p ∈ N.primesLE.filter (fun p => p - 1 ∈ K.smoothNumbers), (p : ℝ) ^ (-s) ≤
      (T : ℝ) ^ (1 - s) * (exp 1 * log (1 + log T)) +
        2 * (T : ℝ) ^ (-(s - s')) * smoothEuler K s' := by
  let P := N.primesLE.filter (fun p => p - 1 ∈ K.smoothNumbers)
  let S := P.filter (· < T)
  let B := P.filter (fun p => T ≤ p)
  have hsplit : S ∪ B = P := by
    ext p
    by_cases hp : p < T
    · simp [S, B, hp, not_le_of_gt hp]
    · simp [S, B, hp, le_of_not_gt hp]
  have hdisj : Disjoint S B := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    exact (not_le_of_gt (mem_filter.mp hp).2) (mem_filter.mp hq).2
  have hsmall : ∑ p ∈ S, (p : ℝ) ^ (-s) ≤
      (T : ℝ) ^ (1 - s) * (exp 1 * log (1 + log T)) := by
    have hsub : S ⊆ T.primesBelow := by
      intro p hp
      obtain ⟨hp, hpT⟩ := mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨hpT, (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2⟩
    have he (p : ℕ) (hp : p ∈ S) : (p : ℝ) ^ (-s) ≤ (T : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ := by
      have hpr := (Nat.mem_primesBelow.mp (hsub hp)).2
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      have hpT := (Nat.mem_primesBelow.mp (hsub hp)).1
      calc
        (p : ℝ) ^ (-s) = (p : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hp₀]
          congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hp₀.le (by exact_mod_cast hpT.le) (by linarith)) (by positivity)
    calc
      _ ≤ ∑ p ∈ S, (T : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ := sum_le_sum he
      _ ≤ _ := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (shifted_prime_recip_log hT)
  have hbig : ∑ p ∈ B, (p : ℝ) ^ (-s) ≤ 2 * (T : ℝ) ^ (-(s - s')) * smoothEuler K s' := by
    let D := B.image (· - 1)
    have hinj : Set.InjOn (fun p : ℕ => p - 1) B := by
      intro a ha b hb h
      change a - 1 = b - 1 at h
      have haT := (mem_filter.mp ha).2
      have hbT := (mem_filter.mp hb).2
      omega
    have hDs (p) (hp : p ∈ D) : p ∈ K.smoothNumbers := by
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp (mem_filter.mp ha).1).2
    have hterm (p) (hp : p ∈ B) : (p : ℝ) ^ (-s) ≤
        2 * (T : ℝ) ^ (-(s - s')) * ((p - 1 : ℕ) : ℝ) ^ (-s') := by
      have hT₀ : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
      have hpT := (mem_filter.mp hp).2
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hm₀ : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
      have hdec : (p : ℝ) ^ (-(s - s')) ≤ (T : ℝ) ^ (-(s - s')) :=
        Real.rpow_le_rpow_of_nonpos hT₀ (by exact_mod_cast hpT) (by linarith)
      have hmono : (p : ℝ) ^ (-s') ≤ ((p - 1 : ℕ) : ℝ) ^ (-s') :=
        Real.rpow_le_rpow_of_nonpos hm₀ (by exact_mod_cast Nat.sub_le p 1) (by linarith)
      calc
        (p : ℝ) ^ (-s) = (p : ℝ) ^ (-(s - s')) * (p : ℝ) ^ (-s') := by
          rw [← Real.rpow_add hp₀]; congr 1; ring
        _ ≤ (T : ℝ) ^ (-(s - s')) * ((p - 1 : ℕ) : ℝ) ^ (-s') := by gcongr
        _ ≤ _ := by nlinarith [show 0 ≤ (T : ℝ) ^ (-(s - s')) * ((p - 1 : ℕ) : ℝ) ^ (-s') by positivity]
    calc
      _ ≤ ∑ p ∈ B, 2 * (T : ℝ) ^ (-(s - s')) * ((p - 1 : ℕ) : ℝ) ^ (-s') := sum_le_sum hterm
      _ ≤ _ := by
        have he : (∑ d ∈ D, (d : ℝ) ^ (-s')) = ∑ p ∈ B, ((p - 1 : ℕ) : ℝ) ^ (-s') := by
          unfold D; rw [sum_image hinj]
        rw [← mul_sum, ← he]
        exact mul_le_mul_of_nonneg_left (sum_smooth_rpow_le hs' D hDs) (by positivity)
  change ∑ p ∈ P, (p : ℝ) ^ (-s) ≤ _
  rw [← hsplit, sum_union hdisj]
  exact add_le_add hsmall hbig

private theorem recip_square_tail {Y : ℝ} (hY : 0 < Y) {D : Finset ℕ} {N : ℕ}
    (hD : ∀ d ∈ D, Y < (d : ℝ) ∧ d ≤ N) :
    ∑ d ∈ D, ((d : ℝ) ^ 2)⁻¹ ≤ 2 / Y := by
  have hs : D ⊆ Ioo ⌊Y⌋₊ (N + 1) := by
    intro d hd
    obtain ⟨hdY, hdN⟩ := hD d hd
    exact mem_Ioo.mpr ⟨Nat.floor_lt (by positivity) |>.mpr hdY, Nat.lt_succ_of_le hdN⟩
  calc
    _ ≤ ∑ d ∈ Ioo ⌊Y⌋₊ (N + 1), ((d : ℝ) ^ 2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ ≤ 2 / ((⌊Y⌋₊ : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le _ _
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hY (Nat.lt_floor_add_one Y).le

private def cofactor (n : ℕ) : ℕ := n / n.maxPrimeFac

private theorem factor_eq (n : ℕ) : cofactor n * n.maxPrimeFac = n :=
  Nat.div_mul_cancel Nat.maxPrimeFac_dvd

private theorem cofactor_pos {n : ℕ} (hn : 0 < n) : 0 < cofactor n := by
  by_contra! h
  have hz : cofactor n = 0 := by omega
  exact hn.ne' (by simpa [hz] using (factor_eq n).symm)

private theorem cofactor_dvd (n : ℕ) : cofactor n ∣ n := ⟨n.maxPrimeFac, (factor_eq n).symm⟩

private theorem cofactor_le {N L n : ℕ} (hn : n ≤ N) (hp : L ≤ n.maxPrimeFac) (hL : 0 < L) :
    cofactor n ≤ N / L := by
  apply (Nat.le_div_iff_mul_le hL).2
  exact (Nat.mul_le_mul_left _ hp).trans ((factor_eq n).le.trans hn)

private theorem large_maxPrimeFac {P n : ℕ} (hn : n ≠ 0) (h : n ∉ P.smoothNumbers) :
    P ≤ n.maxPrimeFac := by
  by_contra! hp
  apply h
  exact Nat.mem_smoothNumbers_iff_forall_le.mpr
    ⟨hn, fun q _ hq hd => (Nat.le_maxPrimeFac hn hq hd).trans_lt hp⟩

private def HasLargeSquare (K n : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ K ≤ p ∧ p ^ 2 ∣ n

private theorem maxPrimeFac_not_dvd_cofactor {K n : ℕ} (hn : 1 < n)
    (hpK : K ≤ n.maxPrimeFac) (hs : ¬ HasLargeSquare K n) :
    ¬ n.maxPrimeFac ∣ cofactor n := by
  intro hd
  apply hs
  refine ⟨n.maxPrimeFac, Nat.prime_maxPrimeFac_of_one_lt n hn, hpK, ?_⟩
  rw [pow_two]
  calc
    n.maxPrimeFac * n.maxPrimeFac ∣ cofactor n * n.maxPrimeFac := Nat.mul_dvd_mul_right hd _
    _ = n := factor_eq n

private theorem totient_factor_eq {K n : ℕ} (hn : 1 < n)
    (hpK : K ≤ n.maxPrimeFac) (hs : ¬ HasLargeSquare K n) :
    φ n = φ (cofactor n) * (n.maxPrimeFac - 1) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hc := maxPrimeFac_not_dvd_cofactor hn hpK hs
  have he := Nat.totient_mul_of_prime_of_not_dvd hp hc
  rw [mul_comm, factor_eq, mul_comm] at he
  exact he

private theorem prime_dvd_sub_one_of_dvd_totient {K n r : ℕ} (hn : 0 < n)
    (hr : r.Prime) (hrK : K ≤ r) (hs : ¬ HasLargeSquare K n) (hd : r ∣ φ n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ r ∣ q - 1 := by
  rw [Nat.totient_eq_prod_factorization hn.ne', Finsupp.prod, Nat.support_factorization] at hd
  obtain ⟨q, hq, hdiv⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hqn := Nat.dvd_of_mem_primeFactors hq
  have hpos := hqP.factorization_pos_of_dvd hn.ne' hqn
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [ha, Nat.succ_sub_one] at hdiv
  refine ⟨q, hqP, hqn, ?_⟩
  rcases hr.dvd_mul.mp hdiv with hbad | hgood
  · have hrq := (Nat.prime_dvd_prime_iff_eq hr hqP).mp (hr.dvd_of_dvd_pow hbad)
    exfalso
    subst q
    apply hs
    refine ⟨r, hr, hrK, ?_⟩
    have ha0 : a ≠ 0 := by
      intro he
      simp [he, hr.not_dvd_one] at hbad
    exact (pow_dvd_pow r (by omega : 2 ≤ n.factorization r)).trans
      (Nat.ordProj_dvd n r)
  · exact hgood

private theorem prime_sub_one_dvd_totient {q m : ℕ} (hq : q.Prime) (hm : q ∣ m) :
    q - 1 ∣ φ m := by
  simpa [Nat.totient_prime hq] using Nat.totient_dvd_of_dvd hm

private theorem cofactor_succ_nonunit {n : ℕ} (hn : 2 < n) (he : φ n = φ (n + 1)) :
    1 < cofactor (n + 1) := by
  have hn1 := cofactor_pos (show 0 < n + 1 by omega)
  by_contra! h
  have hc : cofactor (n + 1) = 1 := by omega
  have hp : (n + 1).Prime := by
    have hh := factor_eq (n + 1)
    simp only [hc, one_mul] at hh
    exact hh ▸ Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hz := Nat.totient_lt n (by omega)
  rw [Nat.totient_prime hp] at he
  omega
-- The two equations for the largest primes have a nonzero determinant.
private theorem cofactor_pair_inj {K P : ℕ} (hKP : K ≤ P) {a b : ℕ}
    (ha : 2 < a) (hb : 2 < b) (hap : P ≤ a.maxPrimeFac)
    (hap' : P ≤ (a + 1).maxPrimeFac) (hbp : P ≤ b.maxPrimeFac)
    (hbp' : P ≤ (b + 1).maxPrimeFac)
    (hsa : ¬ HasLargeSquare K a) (hsa' : ¬ HasLargeSquare K (a + 1))
    (hsb : ¬ HasLargeSquare K b) (hsb' : ¬ HasLargeSquare K (b + 1))
    (hta : φ a = φ (a + 1)) (htb : φ b = φ (b + 1))
    (hf : cofactor a = cofactor b) (hf' : cofactor (a + 1) = cofactor (b + 1)) :
    a = b := by
  have hcop : (cofactor a).Coprime (cofactor (a + 1)) :=
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right a)).of_dvd (cofactor_dvd a) (cofactor_dvd (a + 1))
  have hc := cofactor_succ_nonunit ha hta
  have hu := Nat.totient_pos.mpr (by omega : 0 < cofactor (a + 1))
  have hut := Nat.totient_lt _ hc
  have hdet : cofactor (a + 1) * φ (cofactor a) ≠ cofactor a * φ (cofactor (a + 1)) := by
    intro h
    have hdiv : cofactor (a + 1) ∣ cofactor a * φ (cofactor (a + 1)) :=
      h ▸ dvd_mul_right _ _
    have hdiv' := hcop.symm.dvd_of_dvd_mul_left hdiv
    exact (not_le_of_gt hut) (Nat.le_of_dvd hu hdiv')
  have ed : (cofactor (a + 1) : ℤ) * (φ (cofactor a) : ℤ) -
      (cofactor a : ℤ) * (φ (cofactor (a + 1)) : ℤ) ≠ 0 := by
    intro h
    apply hdet
    exact_mod_cast sub_eq_zero.mp h
  have e1 : (cofactor a : ℤ) * (a.maxPrimeFac : ℤ) + 1 =
      (cofactor (a + 1) : ℤ) * ((a + 1).maxPrimeFac : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, factor_eq, factor_eq]; norm_cast
  have e2 : (cofactor a : ℤ) * (b.maxPrimeFac : ℤ) + 1 =
      (cofactor (a + 1) : ℤ) * ((b + 1).maxPrimeFac : ℤ) := by
    rw [hf, hf', ← Nat.cast_mul, ← Nat.cast_mul, factor_eq, factor_eq]; norm_cast
  have ea1 := totient_factor_eq (by omega : 1 < a) (hKP.trans hap) hsa
  have ea2 := totient_factor_eq (by omega : 1 < a + 1) (hKP.trans hap') hsa'
  have eb1 := totient_factor_eq (by omega : 1 < b) (hKP.trans hbp) hsb
  have eb2 := totient_factor_eq (by omega : 1 < b + 1) (hKP.trans hbp') hsb'
  have pa := Nat.prime_maxPrimeFac_of_one_lt a (by omega)
  have pa' := Nat.prime_maxPrimeFac_of_one_lt (a + 1) (by omega)
  have pb := Nat.prime_maxPrimeFac_of_one_lt b (by omega)
  have pb' := Nat.prime_maxPrimeFac_of_one_lt (b + 1) (by omega)
  have e3 : (φ (cofactor a) : ℤ) * ((a.maxPrimeFac : ℤ) - 1) =
      (φ (cofactor (a + 1)) : ℤ) * (((a + 1).maxPrimeFac : ℤ) - 1) := by
    rw [← Nat.cast_one, ← Nat.cast_sub pa.one_lt.le, ← Nat.cast_sub pa'.one_lt.le,
      ← Nat.cast_mul, ← Nat.cast_mul, ← ea1, ← ea2, hta]
  have e4 : (φ (cofactor a) : ℤ) * ((b.maxPrimeFac : ℤ) - 1) =
      (φ (cofactor (a + 1)) : ℤ) * (((b + 1).maxPrimeFac : ℤ) - 1) := by
    rw [hf, hf', ← Nat.cast_one, ← Nat.cast_sub pb.one_lt.le, ← Nat.cast_sub pb'.one_lt.le,
      ← Nat.cast_mul, ← Nat.cast_mul, ← eb1, ← eb2, htb]
  have eqp : (a.maxPrimeFac : ℤ) - (b.maxPrimeFac : ℤ) = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left ed
    linear_combination (cofactor (a + 1) : ℤ) * (e3 - e4) -
      (φ (cofactor (a + 1)) : ℤ) * (e1 - e2)
  have eqp' : a.maxPrimeFac = b.maxPrimeFac := by exact_mod_cast sub_eq_zero.mp eqp
  calc
    a = cofactor a * a.maxPrimeFac := (factor_eq a).symm
    _ = cofactor b * b.maxPrimeFac := by rw [hf, eqp']
    _ = b := factor_eq b

private structure Regular (K P n : ℕ) : Prop where
  large : 2 < n
  equal : φ n = φ (n + 1)
  primeLeft : P ≤ n.maxPrimeFac
  primeRight : P ≤ (n + 1).maxPrimeFac
  squareLeft : ¬ HasLargeSquare K n
  squareRight : ¬ HasLargeSquare K (n + 1)

private theorem count_regular_box {K P A B : ℕ} (hKP : K ≤ P) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Regular K P n ∧ cofactor n ≤ A ∧ cofactor (n + 1) ≤ B) :
    (S.card : ℝ) ≤ (A : ℝ) * B := by
  have hcard : S.card ≤ ((Icc 1 A) ×ˢ (Icc 1 B)).card := by
    apply card_le_card_of_injOn (fun n => (cofactor n, cofactor (n + 1)))
    · intro n hn
      obtain ⟨h, ha, hb⟩ := hS n hn
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨cofactor_pos (by have := h.large; omega), ha⟩,
        mem_Icc.mpr ⟨cofactor_pos (by omega), hb⟩⟩
    · intro a ha b hb h
      have hA := (hS a ha).1
      have hB := (hS b hb).1
      exact cofactor_pair_inj hKP hA.large hB.large hA.primeLeft hA.primeRight hB.primeLeft
        hB.primeRight hA.squareLeft hA.squareRight hB.squareLeft hB.squareRight hA.equal hB.equal
        (congrArg Prod.fst h) (congrArg Prod.snd h)
  simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel] at hcard
  exact_mod_cast hcard

private theorem count_regular_small {K L N : ℕ} (hKP : K ≤ L ^ 2) (hL : 0 < L)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n + 1 ≤ N ∧ Regular K (L ^ 2) n ∧
      (cofactor n ≤ L ∨ cofactor (n + 1) ≤ L)) :
    (S.card : ℝ) ≤ 2 * (N : ℝ) / L := by
  classical
  let S₁ := S.filter fun n => cofactor n ≤ L
  let S₂ := S.filter fun n => cofactor (n + 1) ≤ L
  have hs : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    rcases (hS n hn).2.2 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, h⟩)
  have h₁ := count_regular_box hKP S₁ (A := L) (B := N / L^2) (by
    intro n hn
    obtain ⟨hn, hl⟩ := mem_filter.mp hn
    obtain ⟨hN, hR, -⟩ := hS n hn
    exact ⟨hR, hl, cofactor_le hN hR.primeRight (pow_pos hL _)⟩)
  have h₂ := count_regular_box hKP S₂ (A := N / L^2) (B := L) (by
    intro n hn
    obtain ⟨hn, hl⟩ := mem_filter.mp hn
    obtain ⟨hN, hR, -⟩ := hS n hn
    exact ⟨hR, cofactor_le (by omega) hR.primeLeft (pow_pos hL _), hl⟩)
  have h₀ : (S.card : ℝ) ≤ (S₁.card : ℝ) + S₂.card := by
    exact_mod_cast (card_le_card hs).trans (card_union_le S₁ S₂)
  have hdiv : ((N / L^2 : ℕ) : ℝ) ≤ (N : ℝ) / (L : ℝ)^2 := by
    rw [le_div_iff₀ (by exact_mod_cast pow_pos hL 2)]
    exact_mod_cast Nat.div_mul_le_self N (L^2)
  have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ L)
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have heq : (L : ℝ) * ((N : ℝ) / (L : ℝ)^2) = N / L := by
    field_simp
  rw [heq] at hmul
  rw [mul_comm] at h₂
  calc
    _ ≤ (N : ℝ) / L + (N : ℝ) / L := h₀.trans (add_le_add (h₁.trans hmul) (h₂.trans hmul))
    _ = _ := by ring

private theorem count_large_square {K N : ℕ} (hK : 2 ≤ K) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ HasLargeSquare K n) :
    (S.card : ℝ) ≤ 4 * (N : ℝ) / K := by
  let D := (Icc K N).filter Nat.Prime
  have hcount : (S.card : ℝ) ≤ (N : ℝ) * ∑ p ∈ D, ((p : ℝ)^2)⁻¹ := by
    rw [mul_sum]
    refine card_of_cover S D (fun p => S.filter fun n => p^2 ∣ n) _ ?_ ?_
    · intro n hn
      obtain ⟨hn0, hnN, p, hp, hpK, hd⟩ := hS n hn
      have hp2 := Nat.le_of_dvd hn0 hd
      have hpp : p ≤ p^2 := by nlinarith [hp.one_lt]
      exact ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hpK, hpp.trans (hp2.trans hnN)⟩, hp⟩,
        mem_filter.mpr ⟨hn, hd⟩⟩
    · intro p hp
      have hp0 := (mem_filter.mp hp).2.pos
      simpa [div_eq_mul_inv] using card_divisor_fiber (pow_pos hp0 2)
        (S.filter fun n => p^2 ∣ n) (fun n hn =>
          ⟨(hS n (mem_filter.mp hn).1).1, (hS n (mem_filter.mp hn).1).2.1, (mem_filter.mp hn).2⟩)
  have hk : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hsum := recip_square_tail (Y := (K : ℝ) - 1) (N := N) (D := D) (by linarith)
    (by intro p hp; obtain ⟨hKp, hpN⟩ := mem_Icc.mp (mem_filter.mp hp).1
        exact ⟨by linarith [show (K : ℝ) ≤ p by exact_mod_cast hKp], hpN⟩)
  have hle : 2 / ((K : ℝ) - 1) ≤ 4 / K := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    linarith [show (2 : ℝ) ≤ K by exact_mod_cast hK]
  exact hcount.trans ((mul_le_mul_of_nonneg_left (hsum.trans hle)
    (Nat.cast_nonneg N)).trans_eq (by ring))

private theorem count_smooth {N P : ℕ} {d : ℝ} (hN : 0 < N) (hd : d < 1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≤ N ∧ n ∈ P.smoothNumbers) :
    (S.card : ℝ) ≤ (N : ℝ) ^ (1-d) * smoothEuler P (1-d) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (N : ℝ) ^ (1-d) * (n : ℝ) ^ (-(1-d)) := by
      apply sum_le_sum
      intro n hn
      have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hS n hn).2.1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (hS n hn).1
      calc
        1 = (n : ℝ) ^ (1-d) * (n : ℝ) ^ (-(1-d)) := by
          rw [← Real.rpow_add hn₀, add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := by gcongr
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_smooth_rpow_le (by linarith) S
        (fun n hn => (hS n hn).2)) (by positivity)

private theorem factoredEuler_bound {s : ℝ} (hs : 1/2 ≤ s) (P D : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ n ∈ D, n ∈ Nat.factoredNumbers P) :
    ∑ n ∈ D, (n : ℝ) ^ (-s) ≤ exp (4 * ∑ p ∈ P, (p : ℝ) ^ (-s)) := by
  have hs0 : 0 < s := by linarith
  let term := fun p : ℕ => ((1 - (p : ℝ) ^ (-s))⁻¹ : ℝ)
  have hf : P.filter Nat.Prime = P := filter_eq_self.mpr hP
  have hHas : HasSum (fun m : Nat.factoredNumbers P => ((m : ℕ) : ℝ) ^ (-s))
      (∏ p ∈ P, term p) := by
    have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := naturalPower (-s)) (by
        intro p hp
        change ‖(p : ℝ) ^ (-s)‖ < 1
        rw [Real.norm_of_nonneg (by positivity)]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)) P).2
    rw [hf] at h
    exact h
  let e : D → ↥(Nat.factoredNumbers P) := fun n => ⟨n.val, hD n.val n.prop⟩
  let T : Finset (Nat.factoredNumbers P) := D.attach.map ⟨e,
    fun a b h => Subtype.ext (congrArg (fun x : Nat.factoredNumbers P => x.val) h)⟩
  have hsum : ∑ n ∈ D, (n : ℝ) ^ (-s) ≤ ∏ p ∈ P, term p := by
    rw [← hHas.tsum_eq]
    calc
      ∑ n ∈ D, (n : ℝ) ^ (-s) = ∑ n ∈ T, ((n : ℕ) : ℝ) ^ (-s) := by
        rw [show ∑ n ∈ T, ((n : ℕ) : ℝ) ^ (-s) =
          ∑ n ∈ D.attach, ((n : ℕ) : ℝ) ^ (-s) by simp only [T, Finset.sum_map]; rfl]
        exact (Finset.sum_attach D (fun k : ℕ => (k : ℝ) ^ (-s))).symm
      _ ≤ _ := hHas.summable.sum_le_tsum T fun _ _ => by positivity
  refine hsum.trans ?_
  rw [mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    dsimp [term]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact inv_nonneg.mpr (by linarith [rpow_neg_le_three_quarters hp2 hs])
  · intro p hp
    dsimp [term]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp3 := rpow_neg_le_three_quarters hp2 hs
    have hl := neg_log_one_sub_le (a := 0) (by positivity : 0 ≤ (p : ℝ)^(-s)) hp3
    simp only [sub_zero, log_one, neg_zero] at hl
    rw [← Real.exp_log (inv_pos.mpr (by linarith : 0 < 1 - (p : ℝ)^(-s))), Real.log_inv]
    exact Real.exp_le_exp.mpr hl

-- Every prime dividing a cofactor with smooth totient has a smooth predecessor.
private theorem count_smooth_totient_divisor {N K T L : ℕ} {d s' : ℝ} (hL : 0 < L)
    (hT : 2 ≤ T) (hd : 0 ≤ d) (hd₁ : d ≤ 1/2)
    (hs' : 0 < s') (hss : s' ≤ 1 - d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ m, m ∣ n ∧ L < m ∧ φ m ∈ K.smoothNumbers) :
    (S.card : ℝ) ≤ (N : ℝ) * ((L : ℝ)^(-d) *
      exp (4 * ((T : ℝ)^d * (exp 1 * log (1 + log T)) +
        2 * (T : ℝ)^(-(1-d-s')) * smoothEuler K s'))) := by
  let D := (Icc 1 N).filter fun m => L < m ∧ φ m ∈ K.smoothNumbers
  let P := N.primesLE.filter fun p => p - 1 ∈ K.smoothNumbers
  have h₁ := count_has_divisor D S (fun m hm => (mem_Icc.mp (mem_filter.mp hm).1).1) (by
    intro n hn
    obtain ⟨hn0, hnN, m, hmn, hLm, hm⟩ := hS n hn
    have hm0 : 0 < m := by omega
    exact ⟨hn0, hnN, m, mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0,
      (Nat.le_of_dvd hn0 hmn).trans hnN⟩, hLm, hm⟩, hmn⟩)
  have hD : ∀ m ∈ D, m ∈ Nat.factoredNumbers P := by
    intro m hm
    obtain ⟨hmI, hLm, hmS⟩ := mem_filter.mp hm
    have hm0 : 0 < m := (mem_Icc.mp hmI).1
    apply Nat.mem_factoredNumbers_of_primeFactors_subset hm0.ne'
    intro p hp
    obtain ⟨hP, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hm0 hdvd).trans
      (mem_Icc.mp hmI).2, hP⟩, Nat.mem_smoothNumbers_of_dvd hmS (prime_sub_one_dvd_totient hP hdvd)⟩
  have hB := factoredEuler_bound (s := 1-d) (by linarith) P D
    (fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2) hD
  have hw := shifted_prime_weight (N := N) (K := K) hT hs' hss (by linarith : 1-d ≤ 1)
  rw [show 1 - (1 - d) = d by ring] at hw
  refine h₁.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc
    ∑ m ∈ D, (m : ℝ)⁻¹ ≤ ∑ m ∈ D, (L : ℝ)^(-d) * (m : ℝ)^(-(1-d)) := by
      apply sum_le_sum
      intro m hm
      exact shifted_rpow_tail (by exact_mod_cast hL)
        (by exact_mod_cast (mem_filter.mp hm).2.1.le) hd
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hB.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw (by norm_num)))


private def progression (N r : ℕ) : Finset ℕ :=
  (Icc (r + 1) N).filter fun q => r ∣ q - 1

private theorem progression_recip {N r : ℕ} (hr : 0 < r) :
    ∑ q ∈ progression N r, (q : ℝ)⁻¹ ≤ (1 + log N) / r := by
  apply recip_sum_congruence hr (a := 1)
  intro q hq
  obtain ⟨h, hd⟩ := mem_filter.mp hq
  obtain ⟨h₁, h₂⟩ := mem_Icc.mp h
  have hm := (Nat.modEq_zero_iff_dvd.mpr hd).add (Nat.ModEq.refl (n := r) 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q), zero_add] at hm
  exact ⟨by omega, h₂, hm⟩

private def ResidueCase (N r : ℕ) (k : ℕ → ℕ) (a : ℕ) : Prop :=
  ∃ q ∈ progression N r, ∃ q' ∈ progression N r,
    q ∣ cofactor a ∧ q' ≤ a.maxPrimeFac ∧ (cofactor a).Coprime q' ∧
      a ≡ k q' [MOD q']

-- For fixed cofactor m, the largest prime occupies one residue class modulo q'.
private theorem fixed_residue_count {N q q' k : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ N ∧ q ∣ cofactor a ∧
      q' ≤ a.maxPrimeFac ∧ (cofactor a).Coprime q' ∧ a ≡ k [MOD q']) :
    (S.card : ℝ) ≤ 2 * (N : ℝ) * (1 + log N) / ((q : ℝ) * q') := by
  let M := (Icc q N).filter fun m => q ∣ m
  have hmrecip : ∑ m ∈ M, (m : ℝ)⁻¹ ≤ (1 + log N) / q := by
    apply recip_sum_congruence hq (a := 0)
    intro m hm
    obtain ⟨hmI, hd⟩ := mem_filter.mp hm
    exact ⟨(mem_Icc.mp hmI).1, (mem_Icc.mp hmI).2, Nat.modEq_zero_iff_dvd.mpr hd⟩
  have hcount : (S.card : ℝ) ≤ ∑ m ∈ M, (2 * (N : ℝ) / q') * (m : ℝ)⁻¹ := by
    apply card_of_fiber_bounds S M cofactor
    · intro a ha
      obtain ⟨ha₀, haN, had, -⟩ := hS a ha
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨Nat.le_of_dvd (cofactor_pos ha₀) had, (Nat.div_le_self _ _).trans haN⟩, had⟩
    · intro m hm
      let F := S.filter fun a => cofactor a = m
      let A := F.image Nat.maxPrimeFac
      have hAinj : Set.InjOn Nat.maxPrimeFac F := by
        intro a ha b hb h
        have hma := (mem_filter.mp ha).2
        have hmb := (mem_filter.mp hb).2
        rw [← factor_eq a, ← factor_eq b, hma, hmb, h]
      have hcard : F.card = A.card := (card_image_of_injOn hAinj).symm
      change (F.card : ℝ) ≤ _
      rw [hcard]
      have hm0 : 0 < m := hq.trans_le (mem_Icc.mp (mem_filter.mp hm).1).1
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
      have hqr : (0 : ℝ) < q' := by exact_mod_cast hq'
      by_cases hempty : A.Nonempty
      · obtain ⟨j, hj⟩ := hempty
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hj
        obtain ⟨haS, hma⟩ := mem_filter.mp ha
        obtain ⟨ha0, haN, haq, haq', hacop, hamod⟩ := hS a haS
        have hcop : q'.gcd m = 1 := by
          rw [← hma]
          exact hacop.symm.gcd_eq_one
        have hdiv_nat : q' ≤ N / m := by
          refine haq'.trans ((Nat.le_div_iff_mul_le hm0).2 ?_)
          rw [← hma, mul_comm, factor_eq]
          exact haN
        have hcnt := card_linear_congruence (n := N / m) (c := m) (r := k) hq' A
          (by
            intro p hp
            obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
            obtain ⟨hbS, hmb⟩ := mem_filter.mp hb
            obtain ⟨hb0, hbN, hbq, hbq', hbcop, hbmod⟩ := hS b hbS
            refine ⟨(Nat.le_div_iff_mul_le hm0).2 ?_, ?_⟩
            · rwa [← hmb, mul_comm, factor_eq]
            · rwa [← hmb, factor_eq])
        simp only [hcop, Nat.cast_one, mul_one] at hcnt
        have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
          rw [le_div_iff₀ hmr]
          exact_mod_cast Nat.div_mul_le_self N m
        have h1 : 1 ≤ ((N / m : ℕ) : ℝ) / q' := by
          rw [le_div_iff₀ hqr, one_mul]
          exact_mod_cast hdiv_nat
        have hle := div_le_div_of_nonneg_right hdiv hqr.le
        calc
          _ ≤ 1 + ((N / m : ℕ) : ℝ) / q' := hcnt
          _ ≤ 2 * ((N : ℝ) / m / q') := by linarith
          _ = _ := by ring
      · rw [not_nonempty_iff_eq_empty.mp hempty, card_empty, Nat.cast_zero]
        positivity
  apply hcount.trans
  rw [← mul_sum]
  calc
    _ ≤ (2 * (N : ℝ) / q') * ((1 + log N) / q) :=
      mul_le_mul_of_nonneg_left hmrecip (by positivity)
    _ = _ := by ring

private theorem residue_count {N r : ℕ} (hN : 1 ≤ N) (hr : 0 < r) (k : ℕ → ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ N ∧ ResidueCase N r k a) :
    (S.card : ℝ) ≤ 2 * (N : ℝ) * (1 + log N)^3 * ((r : ℝ)^2)⁻¹ := by
  let Q := progression N r
  let F := fun z : ℕ × ℕ => S.filter fun a =>
    z.1 ∣ cofactor a ∧ z.2 ≤ a.maxPrimeFac ∧ (cofactor a).Coprime z.2 ∧ a ≡ k z.2 [MOD z.2]
  let C := 2 * (N : ℝ) * (1 + log N)
  have hC : 0 ≤ C := by
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [C]
    positivity
  have h := card_of_cover S (Q ×ˢ Q) F (fun z => C / ((z.1 : ℝ) * z.2)) (by
    intro a ha
    obtain ⟨q, hq, q', hq', h⟩ := (hS a ha).2.2
    exact ⟨(q,q'), mem_product.mpr ⟨hq,hq'⟩, mem_filter.mpr ⟨ha,h⟩⟩) (by
    intro z hz
    obtain ⟨hz₁,hz₂⟩ := mem_product.mp hz
    have hz₁' : 0 < z.1 := by
      have := (mem_Icc.mp (mem_filter.mp hz₁).1).1
      omega
    have hz₂' : 0 < z.2 := by
      have := (mem_Icc.mp (mem_filter.mp hz₂).1).1
      omega
    exact fixed_residue_count hz₁' hz₂' (F z) (by
      intro a ha
      obtain ⟨haS, hz₁, hz₂, hc, hm⟩ := mem_filter.mp ha
      exact ⟨(hS a haS).1, (hS a haS).2.1, hz₁, hz₂, hc, hm⟩))
  have hsum : ∑ z ∈ Q ×ˢ Q, C / ((z.1 : ℝ) * z.2) =
      C * (∑ q ∈ Q, (q : ℝ)⁻¹)^2 := by
    rw [Finset.sum_product]
    simp only [div_eq_mul_inv, mul_inv, ← mul_assoc, ← mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum, pow_two]; ring
  rw [hsum] at h
  have hR := progression_recip (N := N) hr
  have hle : (∑ q ∈ Q, (q : ℝ)⁻¹)^2 ≤ ((1 + log (N : ℝ)) / r)^2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (by intros; positivity)) hR _
  refine h.trans ((mul_le_mul_of_nonneg_left hle hC).trans_eq ?_)
  dsimp [C]
  ring

private theorem all_residue_count {N K : ℕ} (hN : 1 ≤ N) (hK : 2 ≤ K) (k : ℕ → ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a ≤ N ∧ ∃ r, K ≤ r ∧ ResidueCase N r k a) :
    (S.card : ℝ) ≤ 8 * (N : ℝ) * (1 + log N)^3 / K := by
  classical
  let R := Icc K N
  let C := 2 * (N : ℝ) * (1 + log N)^3
  have hC : 0 ≤ C := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    dsimp [C]
    positivity
  have h := card_of_cover S R (fun r => S.filter (ResidueCase N r k))
    (fun r => C * ((r : ℝ)^2)⁻¹) (by
      intro a ha
      obtain ⟨r, hr, hR⟩ := (hS a ha).2.2
      have hRcopy := hR
      obtain ⟨q,hq,-⟩ := hRcopy
      obtain ⟨hrq,hqN⟩ := mem_Icc.mp (mem_filter.mp hq).1
      exact ⟨r,mem_Icc.mpr ⟨hr,by omega⟩,mem_filter.mpr ⟨ha,hR⟩⟩) (by
      intro r hr
      apply residue_count hN (by have := (mem_Icc.mp hr).1; omega)
      intro a ha
      obtain ⟨haS, hR⟩ := mem_filter.mp ha
      exact ⟨(hS a haS).1,(hS a haS).2.1,hR⟩)
  rw [← mul_sum] at h
  have hk : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hsum := recip_square_tail (Y := (K : ℝ) - 1) (N := N) (D := R) (by linarith)
    (by intro r hr; obtain ⟨hrK, hrN⟩ := mem_Icc.mp hr
        exact ⟨by linarith [show (K : ℝ) ≤ r by exact_mod_cast hrK], hrN⟩)
  have hle : 2 / ((K : ℝ) - 1) ≤ 4 / K := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    linarith [show (2 : ℝ) ≤ K by exact_mod_cast hK]
  exact h.trans ((mul_le_mul_of_nonneg_left (hsum.trans hle) hC).trans_eq (by dsimp [C]; ring))

private theorem get_residue {N K a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ N) (hbN : b ≤ N) (hp : b.maxPrimeFac ≤ a.maxPrimeFac)
    (hc : a.Coprime b) (he : φ a = φ b) (hs : ¬ HasLargeSquare K b)
    (hsa : ¬ HasLargeSquare K a) (hm : φ (cofactor a) ∉ K.smoothNumbers)
    (k : ℕ → ℕ) (hmod : ∀ q, q.Prime → q ∣ b → a ≡ k q [MOD q]) :
    ∃ r, K ≤ r ∧ ResidueCase N r k a := by
  rw [Nat.mem_smoothNumbers'] at hm
  push Not at hm
  obtain ⟨r, hr, hrd, hrK⟩ := hm
  have hma := cofactor_dvd a
  have hbig : ¬ HasLargeSquare K (cofactor a) := by
    intro h
    obtain ⟨p, hp, hpK, hpm⟩ := h
    exact hsa ⟨p,hp,hpK,hpm.trans hma⟩
  have hrd' : r ∣ φ b := he ▸ hrd.trans (Nat.totient_dvd_of_dvd hma)
  obtain ⟨q,hq,hqd,hqr⟩ := prime_dvd_sub_one_of_dvd_totient (cofactor_pos ha) hr hrK hbig hrd
  obtain ⟨q',hq',hq'd,hq'r⟩ := prime_dvd_sub_one_of_dvd_totient hb hr hrK hs hrd'
  have inProg {p w : ℕ} (hw : 0 < w) (hwN : w ≤ N) (pp : p.Prime)
      (pd : p ∣ w) (pr : r ∣ p - 1) : p ∈ progression N r := by
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, (Nat.le_of_dvd hw pd).trans hwN⟩, pr⟩
    have hp₂ := pp.two_le
    have := Nat.le_of_dvd (show 0 < p - 1 by omega) pr
    omega
  refine ⟨r, hrK, q, inProg ha haN hq (hqd.trans hma) hqr, q', inProg hb hbN hq' hq'd hq'r,
    hqd, (Nat.le_maxPrimeFac hb.ne' hq' hq'd).trans hp, hc.of_dvd hma hq'd, hmod q' hq' hq'd⟩


private theorem card_shift (S : Finset ℕ) :
    (S.image (· + 1)).card = S.card :=
  card_image_of_injOn (fun _ _ _ _ h => Nat.add_right_cancel h)

private theorem mul_bound {N : ℕ} {a b : ℝ} (h : a ≤ b) :
    (N : ℝ) * a ≤ N * b := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)

private theorem count_all {N K L T : ℕ} (hN : 1 ≤ N) (hK : 2 ≤ K) (hL : 0 < L)
    (hKL : K ≤ L^2) (hT : 2 ≤ T) {d₀ d s' E : ℝ}
    (hd₀ : d₀ < 1) (hd : 0 ≤ d) (hd₁ : d ≤ 1/2) (hs' : 0 < s') (hss : s' ≤ 1-d)
    (htiny : 3 ≤ (N : ℝ)*E)
    (hsm : (N : ℝ)^(-d₀) * smoothEuler (L^2) (1-d₀) ≤ E)
    (hsq : 4 / (K : ℝ) ≤ E) (hcl : 2 / (L : ℝ) ≤ E)
    (hphi : (L : ℝ)^(-d) * exp (4 * ((T : ℝ)^d * (exp 1 * log (1 + log T)) +
      2 * (T : ℝ)^(-(1-d-s')) * smoothEuler K s')) ≤ E)
    (hres : 8 * (1 + log N)^3 / (K : ℝ) ≤ E)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n + 1 ≤ N ∧ φ n = φ (n + 1)) :
    (S.card : ℝ) ≤ 10 * ((N : ℝ)*E) := by
  classical
  let B : Fin 10 → Finset ℕ
    | 0 => S.filter (· ≤ 2)
    | 1 => S.filter (· ∈ (L^2).smoothNumbers)
    | 2 => S.filter fun n => n + 1 ∈ (L^2).smoothNumbers
    | 3 => S.filter (HasLargeSquare K)
    | 4 => S.filter fun n => HasLargeSquare K (n + 1)
    | 5 => S.filter fun n => Regular K (L^2) n ∧ (cofactor n ≤ L ∨ cofactor (n+1) ≤ L)
    | 6 => S.filter fun n => 0 < n ∧ ∃ m, m ∣ n ∧ L < m ∧ φ m ∈ K.smoothNumbers
    | 7 => S.filter fun n => ∃ m, m ∣ n + 1 ∧ L < m ∧ φ m ∈ K.smoothNumbers
    | 8 => S.filter fun n => 0 < n ∧ ∃ r, K ≤ r ∧ ResidueCase N r (· - 1) n
    | 9 => S.filter fun n => ∃ r, K ≤ r ∧ ResidueCase N r (fun _ => 1) (n + 1)
  have hcover (n : ℕ) (hn : n ∈ S) : ∃ i ∈ (univ : Finset (Fin 10)), n ∈ B i := by
    have hnN := (hS n hn).1
    have he := (hS n hn).2
    have hnle : n ≤ N := by omega
    by_cases h₀ : n ≤ 2
    · exact ⟨0,mem_univ _,mem_filter.mpr ⟨hn,h₀⟩⟩
    have hn₀ : 0 < n := by omega
    have hn₁ : 0 < n + 1 := by omega
    by_cases h₁ : n ∈ (L^2).smoothNumbers
    · exact ⟨1,mem_univ _,mem_filter.mpr ⟨hn,h₁⟩⟩
    by_cases h₂ : n + 1 ∈ (L^2).smoothNumbers
    · exact ⟨2,mem_univ _,mem_filter.mpr ⟨hn,h₂⟩⟩
    by_cases h₃ : HasLargeSquare K n
    · exact ⟨3,mem_univ _,mem_filter.mpr ⟨hn,h₃⟩⟩
    by_cases h₄ : HasLargeSquare K (n+1)
    · exact ⟨4,mem_univ _,mem_filter.mpr ⟨hn,h₄⟩⟩
    by_cases h₅ : cofactor n ≤ L ∨ cofactor (n+1) ≤ L
    · exact ⟨5,mem_univ _,mem_filter.mpr ⟨hn,
        ⟨by omega,he,large_maxPrimeFac hn₀.ne' h₁,large_maxPrimeFac hn₁.ne' h₂,h₃,h₄⟩,h₅⟩⟩
    push Not at h₅
    by_cases h₆ : φ (cofactor n) ∈ K.smoothNumbers
    · exact ⟨6,mem_univ _,mem_filter.mpr ⟨hn,hn₀,cofactor n,cofactor_dvd n,h₅.1,h₆⟩⟩
    by_cases h₇ : φ (cofactor (n+1)) ∈ K.smoothNumbers
    · exact ⟨7,mem_univ _,mem_filter.mpr ⟨hn,cofactor (n+1),cofactor_dvd _,h₅.2,h₇⟩⟩
    have hc : n.Coprime (n+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rcases le_total (n+1).maxPrimeFac n.maxPrimeFac with hp | hp
    · refine ⟨8,mem_univ _,mem_filter.mpr ⟨hn,hn₀,
          get_residue hn₀ hn₁ hnle hnN hp hc he h₄ h₃ h₆ (· - 1) ?_⟩⟩
      intro q hq hdq
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel hq.one_lt.le]
      exact (Nat.modEq_zero_iff_dvd.mpr hdq).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_refl q)).symm
    · refine ⟨9,mem_univ _,mem_filter.mpr ⟨hn,
          get_residue hn₁ hn₀ hnN hnle hp hc.symm he.symm h₃ h₄ h₇ (fun _ => 1) ?_⟩⟩
      intro q _ hdq
      simpa using (Nat.modEq_zero_iff_dvd.mpr hdq).add (Nat.ModEq.refl (n := q) 1)
  have smoothBound (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N ∧ a ∈ (L^2).smoothNumbers) :
      (A.card : ℝ) ≤ N * E := by
    refine (count_smooth (by omega) hd₀ A hA).trans ?_
    rw [show 1-d₀ = 1+(-d₀) by ring, Real.rpow_add (by exact_mod_cast zero_lt_one.trans_le hN),
      Real.rpow_one, mul_assoc]
    exact mul_bound hsm
  have squareBound (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N ∧ HasLargeSquare K a) :
      (A.card : ℝ) ≤ N * E := by
    refine (count_large_square hK A hA).trans ?_
    calc
      _ = (N : ℝ) * (4 / (K : ℝ)) := by ring
      _ ≤ _ := mul_bound hsq
  have phiBound (A : Finset ℕ)
      (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N ∧ ∃ m, m ∣ a ∧ L < m ∧ φ m ∈ K.smoothNumbers) :
      (A.card : ℝ) ≤ N * E :=
    (count_smooth_totient_divisor hL hT hd hd₁ hs' hss A hA).trans (mul_bound hphi)
  have resBound (A : Finset ℕ) (k : ℕ → ℕ)
      (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N ∧ ∃ r, K ≤ r ∧ ResidueCase N r k a) :
      (A.card : ℝ) ≤ N * E := by
    refine (all_residue_count hN hK k A hA).trans ?_
    calc
      _ = (N : ℝ) * (8 * (1 + log N)^3 / (K : ℝ)) := by ring
      _ ≤ _ := mul_bound hres
  have hb (i : Fin 10) (_ : i ∈ (univ : Finset (Fin 10))) : ((B i).card : ℝ) ≤ N * E := by
    fin_cases i
    · refine le_trans ?_ htiny
      exact_mod_cast (show (B 0).card ≤ 3 by
        simpa using card_le_card (show B 0 ⊆ range 3 by
          intro n hn; exact mem_range.mpr (by have := (mem_filter.mp hn).2; omega)))
    · apply smoothBound
      intro a ha
      obtain ⟨h,hs⟩ := mem_filter.mp ha
      exact ⟨by have := (hS a h).1; omega,hs⟩
    · rw [← card_shift (B 2)]
      apply smoothBound
      intro a ha
      obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
      obtain ⟨h,hs⟩ := mem_filter.mp hn
      exact ⟨(hS n h).1,hs⟩
    · apply squareBound
      intro a ha
      obtain ⟨h,p,hp,hKp,hd⟩ := mem_filter.mp ha
      -- The target set has no zero since the two totients at 0 and 1 differ.
      have he := (hS a h).2
      have ha₀ : 0 < a := by
        by_contra! hh
        have ha' : a = 0 := by omega
        norm_num [ha'] at he
      exact ⟨ha₀,by have := (hS a h).1; omega,p,hp,hKp,hd⟩
    · rw [← card_shift (B 4)]
      apply squareBound
      intro a ha
      obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
      obtain ⟨h,hs⟩ := mem_filter.mp hn
      exact ⟨by omega,(hS n h).1,hs⟩
    · refine (count_regular_small (N := N) hKL hL (B 5) ?_).trans ?_
      · intro n hn
        obtain ⟨h,hR⟩ := mem_filter.mp hn
        exact ⟨(hS n h).1,hR⟩
      · calc
          _ = (N : ℝ) * (2 / (L : ℝ)) := by ring
          _ ≤ _ := mul_bound hcl
    · apply phiBound
      intro a ha
      obtain ⟨h,hp,hm⟩ := mem_filter.mp ha
      exact ⟨hp,by have := (hS a h).1; omega,hm⟩
    · rw [← card_shift (B 7)]
      apply phiBound
      intro a ha
      obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
      obtain ⟨h,hm⟩ := mem_filter.mp hn
      exact ⟨by omega,(hS n h).1,hm⟩
    · apply resBound _ (· - 1)
      intro a ha
      obtain ⟨h,hp,hm⟩ := mem_filter.mp ha
      exact ⟨hp,by have := (hS a h).1; omega,hm⟩
    · rw [← card_shift (B 9)]
      apply resBound _ (fun _ => 1)
      intro a ha
      obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
      obtain ⟨h,hm⟩ := mem_filter.mp hn
      exact ⟨by omega,(hS n h).1,hm⟩
  simpa using card_of_cover S (univ : Finset (Fin 10)) B (fun _ => (N : ℝ)*E) hcover hb


private theorem log_ceil_exp {a : ℝ} (ha : 0 ≤ a) :
    a ≤ log (⌈exp a⌉₊ : ℕ) ∧ log (⌈exp a⌉₊ : ℕ) ≤ a + 1 := by
  have he : (1 : ℝ) ≤ exp a := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ha
  have hle : exp a ≤ (⌈exp a⌉₊ : ℕ) := Nat.le_ceil _
  have hu : (⌈exp a⌉₊ : ℕ) < exp a + 1 := Nat.ceil_lt_add_one (by positivity)
  have h₂ : (⌈exp a⌉₊ : ℕ) ≤ (2 : ℝ) * exp a := by linarith
  constructor
  · simpa using Real.log_le_log (Real.exp_pos a) hle
  · calc
      log (⌈exp a⌉₊ : ℕ) ≤ log (2 * exp a) :=
        Real.log_le_log ((Real.exp_pos a).trans_le hle) h₂
      _ = log 2 + a := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem eventually_const_mul_log_le_pow {C u : ℝ} (hC : 0 < C) (hu : 0 < u) :
    ∀ᶠ t : ℝ in atTop, C * log t ≤ t ^ u := by
  have h := (isLittleO_log_rpow_atTop hu).bound (inv_pos.mpr hC)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t htup ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at htup
  have hh := mul_le_mul_of_nonneg_left htup hC.le
  rwa [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hh

private theorem ceil_exp_ge_two {a : ℝ} (ha : 1 ≤ a) : 2 ≤ ⌈exp a⌉₊ := by
  have ha' := Real.add_one_le_exp a
  have hb : (2 : ℝ) ≤ (⌈exp a⌉₊ : ℕ) := by linarith [Nat.le_ceil (exp a)]
  exact_mod_cast hb

private theorem smoothEuler_at_small_d {P : ℕ} (hP : 2 ≤ P) {t d : ℝ}
    (ht : 1 ≤ t) (hlt : 1 ≤ log t) (hd : 0 ≤ d) (hd₂ : d ≤ 1/2)
    (hp : d * log P ≤ log t / 4) (hp' : log (1 + log (P : ℝ)) ≤ 4 * log t)
    (hlog : 30 * log t ≤ t ^ (3/4 : ℝ)) :
    log (smoothEuler P (1-d)) ≤ t := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have ht0 : 0 < t := by linarith
  have hpwr : (P : ℝ)^d ≤ t^(1/4 : ℝ) := by
    rw [Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    linarith
  have hpwr' : 1 ≤ t^(1/4 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hPL : 0 ≤ log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have h := smoothEuler_log_le hP (s := 1-d) (by linarith) (by linarith)
  rw [show 1 - (1-d) = d by ring] at h
  have hmain : 12 * (1 + d * log P) * (P : ℝ)^d ≤ 15 * log t * t^(1/4 : ℝ) := by
    have hc : 12 * (1 + d * log P) ≤ 15 * log t := by linarith
    calc
      _ ≤ 12 * (1 + d * log P) * t^(1/4 : ℝ) :=
        mul_le_mul_of_nonneg_left hpwr (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hsmall : 4 * log t ≤ 4 * log t * t^(1/4 : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hpwr' (by positivity : 0 ≤ 4 * log t)
  have hlarge : 30 * log t * t^(1/4 : ℝ) ≤ t := by
    have hm := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ t^(1/4 : ℝ))
    rw [← Real.rpow_add ht0, show (3/4 : ℝ) + 1/4 = 1 by norm_num, Real.rpow_one] at hm
    exact hm
  have hpos : 0 ≤ log t * t^(1/4 : ℝ) := by positivity
  linarith [h, hmain, hsmall, hlarge, hpos]

private theorem smoothEuler_near_one {K : ℕ} (hK : 2 ≤ K) {t : ℝ} (ht : 1 ≤ t)
    (hk : 4*t ≤ log K) (hk' : log (K : ℝ) ≤ 5*t) :
    smoothEuler K (1 - (log (K : ℝ))⁻¹) ≤ (6 * exp (24 * exp 1)) * t := by
  have hkpos : 0 < log (K : ℝ) := by linarith
  let a := (log (K : ℝ))⁻¹
  have ha : 0 < a := by positivity
  have hal : a * log (K : ℝ) = 1 := inv_mul_cancel₀ hkpos.ne'
  have ha' : a ≤ 1/2 := by
    dsimp [a]
    rw [inv_eq_one_div, div_le_iff₀ hkpos]
    linarith
  have hw := smoothEuler_log_le hK (s := 1-a) (by linarith) (by linarith)
  rw [show 1 - (1-a) = a by ring, hal] at hw
  have hp : (K : ℝ)^a = exp 1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < K by omega)), mul_comm, hal]
  rw [hp] at hw
  have hb := Real.exp_le_exp.mpr hw
  rw [Real.exp_log (smoothEuler_pos (N := K) (s := 1-a) (by linarith)),
    Real.exp_add, Real.exp_log (by linarith : 0 < 1 + log (K : ℝ))] at hb
  norm_num at hb
  dsimp [a] at hb ⊢
  calc
    _ ≤ (1 + log (K : ℝ)) * exp (24 * exp 1) := hb
    _ ≤ (6 * t) * exp (24 * exp 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

-- Choose the cutoffs on the scale t = (log x)^(1/3).
set_option maxHeartbeats 1800000 in
private theorem large_scale_count :
    ∀ᶠ t : ℝ in atTop, ∀ (N : ℕ), 1 ≤ N → t^3 ≤ log (N : ℝ) →
      log (N : ℝ) ≤ t^3 + 1 → ∀ S : Finset ℕ,
      (∀ n ∈ S, n + 1 ≤ N ∧ φ n = φ (n + 1)) →
      (S.card : ℝ) ≤ 10 * ((N : ℝ) * exp (-2*t)) := by
  let C : ℝ := 6 * exp (24 * exp 1)
  let W : ℝ := 64 * exp 101000 * exp 1
  have Cpos : 0 < C := by dsimp [C]; positivity
  have Wpos : 0 < W := by dsimp [W]; positivity
  have hpower := (tendsto_exp_mul_div_rpow_atTop 9 2 (by norm_num)).eventually_ge_atTop 64
  filter_upwards [eventually_ge_atTop (1000 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 10000,
    eventually_const_mul_log_le_pow (C := 30) (u := 3/4) (by norm_num) (by norm_num),
    eventually_const_mul_log_le_pow (C := W) (u := 1) Wpos zero_lt_one,
    eventually_ge_atTop (32*C), hpower] with t ht hlt h30 hW hC hp9
  intro N hN hNlo hNhi S hS
  let A : ℝ := t^2 * log t / 100
  let B : ℝ := 100 * t * log t
  let L : ℕ := ⌈exp A⌉₊
  let K : ℕ := ⌈exp (4*t)⌉₊
  let T : ℕ := ⌈exp B⌉₊
  let d₀ : ℝ := 4 / t^2
  let d : ℝ := 1000 / (t * log t)
  let e : ℝ := (log (K : ℝ))⁻¹
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hlog1 : 1 ≤ log t := by linarith
  have hlog0 : 0 < log t := by linarith
  have hlogt := Real.log_le_sub_one_of_pos ht0
  have ht2 : t ≤ t^2 := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
  have ht3 : t^2 ≤ t^3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  have ht4 : t^3 + 2 ≤ t^4 := by
    have ht32 : 2 ≤ t^3 := by linarith
    have hh := mul_nonneg (show 0 ≤ t^3 by positivity) (show 0 ≤ t - 2 by linarith)
    linarith only [hh,ht32]
  have hA : 5*t ≤ A := by
    dsimp [A]
    have hh : t^2 ≤ t^2 * log t := by simpa using mul_le_mul_of_nonneg_left hlog1 (sq_nonneg t)
    have hhh : 1000*t ≤ t^2 := by nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht)]
    linarith
  have hB : 1 ≤ B := by
    dsimp [B]
    have hh : t ≤ t * log t := by simpa using mul_le_mul_of_nonneg_left hlog1 ht0.le
    linarith
  obtain ⟨hLlo,hLhi⟩ := log_ceil_exp (show 0 ≤ A by linarith)
  obtain ⟨hKlo,hKhi⟩ := log_ceil_exp (show 0 ≤ 4*t by positivity)
  obtain ⟨hTlo,hThi⟩ := log_ceil_exp (show 0 ≤ B by linarith)
  change A ≤ log (L : ℝ) at hLlo
  change log (L : ℝ) ≤ A+1 at hLhi
  change 4*t ≤ log (K : ℝ) at hKlo
  change log (K : ℝ) ≤ 4*t+1 at hKhi
  change B ≤ log (T : ℝ) at hTlo
  change log (T : ℝ) ≤ B+1 at hThi
  have hL2 : 2 ≤ L := ceil_exp_ge_two (by linarith)
  have hK2 : 2 ≤ K := ceil_exp_ge_two (by linarith)
  have hT2 : 2 ≤ T := ceil_exp_ge_two hB
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKlog : 0 < log (K : ℝ) := by linarith
  have hKhi' : log (K : ℝ) ≤ 5*t := by linarith
  have hPlog : log ((L^2 : ℕ) : ℝ) = 2 * log (L : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hP0 : (0 : ℝ) < (L^2 : ℕ) := by exact_mod_cast pow_pos (show 0 < L by omega) 2
  have hKL : K ≤ L^2 := by
    have hh : log (K : ℝ) ≤ log ((L^2 : ℕ) : ℝ) := by rw [hPlog]; linarith
    have hz := Real.exp_le_exp.mpr hh
    rw [Real.exp_log hK0, Real.exp_log hP0] at hz
    exact_mod_cast hz
  have hd0 : 0 ≤ d₀ := by positivity
  have hd02 : d₀ ≤ 1/2 := by
    dsimp [d₀]
    rw [div_le_iff₀ (sq_pos_of_pos ht0)]
    linarith
  have hd : 0 ≤ d := by positivity
  have hdlo : d ≤ (10*t)⁻¹ := by
    dsimp [d]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hlt ht0.le
    nlinarith
  have hd2 : d ≤ 1/2 := hdlo.trans (by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    linarith)
  have helo : (5*t)⁻¹ ≤ e := inv_anti₀ hKlog hKhi'
  have he0 : 0 < e := by positivity
  have he2 : e ≤ 1/2 := by
    dsimp [e]
    rw [inv_eq_one_div, div_le_iff₀ hKlog]
    linarith
  have hgap : (10*t)⁻¹ ≤ e-d := by
    have hh : (5*t)⁻¹ = 2 * (10*t)⁻¹ := by field_simp; norm_num
    rw [hh] at helo
    linarith
  have hle : d ≤ e := by linarith [inv_pos.mpr (show 0 < 10*t by positivity)]
  have ht4eq : log (t^4) = 4 * log t := by rw [Real.log_pow]; norm_num
  have hT1 : log (T : ℝ) ≤ 101*t*log t := by
    have hh : t ≤ t*log t := by simpa using mul_le_mul_of_nonneg_left hlog1 ht0.le
    dsimp [B] at hThi
    nlinarith
  have hT2log : log (1 + log (T : ℝ)) ≤ 4 * log t := by
    have htl : 0 < log (T : ℝ) := by linarith
    rw [← ht4eq]
    apply Real.log_le_log (by linarith)
    have hmul : 101*t*log t ≤ 101*t^2 := by
      have hh := mul_le_mul_of_nonneg_left (show log t ≤ t by linarith) (by positivity : 0 ≤ 101*t)
      nlinarith
    have hbig : 102*t^2 ≤ t^4 := by
      have hh := mul_le_mul_of_nonneg_right (show 102 ≤ t^2 by linarith [ht2]) (sq_nonneg t)
      nlinarith
    linarith
  have hPv : log ((L^2 : ℕ) : ℝ) ≤ t^2 * log t / 20 := by
    rw [hPlog]
    have hh : t^2 ≤ t^2 * log t := by simpa using mul_le_mul_of_nonneg_left hlog1 (sq_nonneg t)
    dsimp [A] at hLhi
    linarith
  have hPvp : d₀ * log ((L^2 : ℕ) : ℝ) ≤ log t/4 := by
    have hh : d₀ * (t^2*log t/20) = log t/5 := by
      dsimp [d₀]
      field_simp
      <;> ring
    have hh' := mul_le_mul_of_nonneg_left hPv hd0
    rw [hh] at hh'
    linarith
  have hPloglog : log (1 + log ((L^2 : ℕ) : ℝ)) ≤ 4*log t := by
    rw [← ht4eq]
    have hpL : 0 ≤ log ((L^2 : ℕ) : ℝ) := by rw [hPlog]; linarith
    apply Real.log_le_log (by linarith)
    have hh := mul_le_mul_of_nonneg_left (show log t ≤ t by linarith) (sq_nonneg t)
    nlinarith
  have hP2 : 2 ≤ L^2 := hL2.trans (Nat.le_self_pow (by decide) L)
  have hES := smoothEuler_at_small_d hP2 ht1 hlog1 hd0 hd02 hPvp hPloglog h30
  have hSM : (N : ℝ)^(-d₀) * smoothEuler (L^2) (1-d₀) ≤ exp (-2*t) := by
    have hn : 4*t ≤ d₀ * log (N : ℝ) := by
      have hh : d₀*t^3=4*t := by dsimp [d₀]; field_simp
      rw [← hh]
      exact mul_le_mul_of_nonneg_left hNlo hd0
    rw [Real.rpow_def_of_pos hN0,
      ← Real.exp_log (smoothEuler_pos (N := L^2) (s := 1-d₀) (by linarith)), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hn,hES,ht0]
  have hLA : 10*t ≤ d * log (L : ℝ) := by
    have hh : d*A = 10*t := by dsimp [d,A]; field_simp; ring
    rw [← hh]
    exact mul_le_mul_of_nonneg_left hLlo hd
  have hTB : (T : ℝ)^d ≤ exp 101000 := by
    rw [Real.rpow_def_of_pos hT0]
    apply Real.exp_le_exp.mpr
    have hx : d * (101*t*log t) = 101000 := by dsimp [d]; field_simp; ring
    have hh := mul_le_mul_of_nonneg_left hT1 hd
    nlinarith only [hx,hh]
  have hTT : (T : ℝ)^(-(1-d-(1-e))) ≤ t^(-10 : ℝ) := by
    rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    have hh : (10*t)⁻¹ * B = 10 * log t := by dsimp [B]; field_simp; ring
    have h₁ := mul_le_mul_of_nonneg_right hgap (show 0 ≤ B by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hTlo (sub_nonneg.mpr hle)
    nlinarith only [hh,h₁,h₂]
  have hEK : smoothEuler K (1-e) ≤ C*t := smoothEuler_near_one hK2 ht1 hKlo hKhi'
  have hPhiSmall : (T : ℝ)^d * (exp 1 * log (1 + log (T : ℝ))) ≤ t/16 := by
    rw [Real.rpow_one] at hW
    have hh : 0 ≤ log (1 + log (T : ℝ)) := Real.log_nonneg (by linarith)
    have hprod : (T : ℝ)^d * (exp 1 * log (1 + log (T : ℝ))) ≤
        exp 101000 * (exp 1 * (4 * log t)) := by
      gcongr
    dsimp [W] at hW
    linarith [hprod]
  have hPhiLarge : 2 * (T : ℝ)^(-(1-d-(1-e))) * smoothEuler K (1-e) ≤ t/16 := by
    have hprod : 2 * (T : ℝ)^(-(1-d-(1-e))) * smoothEuler K (1-e) ≤
        2 * t^(-10 : ℝ) * (C*t) := by
      have hh := (smoothEuler_pos (N := K) (s := 1-e) (by linarith)).le
      gcongr
    have hps : t^(-10 : ℝ) * t ≤ 1 := by
      calc
        t^(-10 : ℝ) * t = t^(-10 : ℝ) * t^(1 : ℝ) := by rw [Real.rpow_one]
        _ = t^(-9 : ℝ) := by rw [← Real.rpow_add ht0]; congr 1; norm_num
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have hc := mul_le_mul_of_nonneg_left hps (show 0 ≤ 2*C by positivity)
    linarith [hprod,hc]
  have hPhi : (L : ℝ)^(-d) * exp (4 * ((T : ℝ)^d * (exp 1 * log (1 + log T)) +
      2 * (T : ℝ)^(-(1-d-(1-e))) * smoothEuler K (1-e))) ≤ exp (-2*t) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hLA,hPhiSmall,hPhiLarge,ht0]
  have hKexp : exp (4*t) ≤ (K : ℝ) := Nat.le_ceil _
  have hlexp : exp (4*t) ≤ (L : ℝ) :=
    (Real.exp_le_exp.mpr (show 4*t ≤ A by linarith)).trans (Nat.le_ceil _)
  have hKrule {F : ℝ} (hF : F ≤ exp (2*t)) : F / (K : ℝ) ≤ exp (-2*t) := by
    apply (div_le_iff₀ hK0).mpr
    calc
      _ ≤ exp (2*t) := hF
      _ = exp (-2*t) * exp (4*t) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKexp (by positivity)
  have h4Exp : 4 ≤ exp (2*t) := by linarith [Real.add_one_le_exp (2*t)]
  have hLrate : 2 / (L : ℝ) ≤ exp (-2*t) := by
    apply (div_le_iff₀ hL0).mpr
    calc
      (2 : ℝ) ≤ exp (2*t) := by linarith
      _ = exp (-2*t) * exp (4*t) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlexp (by positivity)
  have hNlog : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hR : 8*(1 + log (N : ℝ))^3 ≤ exp (2*t) := by
    change (64 : ℝ) ≤ exp (2*t) / t^(9 : ℝ) at hp9
    rw [le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)] at hp9
    have heq : t^(9 : ℝ) = t^9 := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast t 9
    rw [heq] at hp9
    have hN3 : 1 + log (N : ℝ) ≤ 2*t^3 := by linarith
    calc
      _ ≤ 8*(2*t^3)^3 := by gcongr
      _ = 64*t^9 := by ring
      _ ≤ _ := hp9
  have hTiny : 3 ≤ (N : ℝ)*exp (-2*t) := by
    have hh : 3*t ≤ t^3 := by
      have hy := mul_le_mul_of_nonneg_right (show 3 ≤ t^2 by linarith only [ht, ht2]) ht0.le
      nlinarith only [hy]
    rw [← Real.exp_log hN0, ← Real.exp_add]
    calc
      (3 : ℝ) ≤ exp t := by linarith [Real.add_one_le_exp t]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hh,hNlo])
  exact count_all hN hK2 (by omega) hKL hT2 (by linarith) hd hd2 (by linarith) (by linarith)
    hTiny hSM (hKrule h4Exp) hLrate hPhi (hKrule hR) S hS

private theorem target_bound :
    ∀ᶠ x : ℝ in atTop, ((({n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n+1)}).ncard : ℕ) : ℝ) ≤
      x / exp ((log x) ^ ((1 : ℝ)/3)) := by
  let t := fun x : ℝ => (log x)^((1 : ℝ)/3)
  have hT : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ)/3)).comp Real.tendsto_log_atTop
  filter_upwards [hT.eventually large_scale_count, eventually_ge_atTop (1 : ℝ),
    hT.eventually (eventually_ge_atTop (20 : ℝ))] with x hCount hx ht
  let N := ⌊x⌋₊ + 1
  let S := (range N).filter fun n => φ n = φ (n+1)
  have hN : x ≤ (N : ℝ) := by simpa [N] using (Nat.lt_floor_add_one x).le
  have hN' : (N : ℝ) ≤ 2*x := by
    have hNf := Nat.floor_le (by linarith : 0 ≤ x)
    dsimp [N]
    push_cast
    linarith
  have ht' : t x ^ 3 = log x := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (Real.log_nonneg hx)]
    norm_num
  have hNlo : t x ^ 3 ≤ log (N : ℝ) := by
    rw [ht']
    exact Real.log_le_log (by linarith) hN
  have hNhi : log (N : ℝ) ≤ t x ^ 3 + 1 := by
    rw [ht']
    calc
      _ ≤ log (2*x) := Real.log_le_log (by positivity) hN'
      _ = log 2 + log x := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : ∀ n : ℕ, n ∈ S ↔ (n : ℝ) ≤ x ∧ φ n = φ (n+1) := by
    intro n
    simp only [S, mem_filter, mem_range, N, Nat.lt_succ_iff]
    rw [Nat.le_floor_iff (by linarith : 0 ≤ x)]
  have hcard : ({n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n+1)}).ncard = S.card := by
    have hset : {n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n+1)} = ↑S := by
      ext n
      exact (he n).symm
    rw [hset, Set.ncard_coe_finset]
  rw [hcard]
  have hh := hCount N (by dsimp [N]; omega) hNlo hNhi S
    (fun n hn => ⟨Nat.succ_le_of_lt (mem_range.mp (mem_filter.mp hn).1), (he n).mp hn |>.2⟩)
  refine hh.trans ?_
  calc
    _ ≤ 20 * (x * exp (-2*t x)) := by
      calc
        _ ≤ 10 * ((2*x) * exp (-2*t x)) := by gcongr
        _ = _ := by ring
    _ = x * exp (-t x) * (20 / exp (t x)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      rw [show -2*t x = -t x + -t x by ring, Real.exp_add]
      ring
    _ ≤ x * exp (-t x) := by
      have hh : 20 / exp (t x) ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (by
        linarith [Real.add_one_le_exp (t x)])
      exact mul_le_of_le_one_right (by positivity) hh
    _ = _ := by rw [Real.exp_neg, div_eq_mul_inv]

end EqualTotientCount

theorem OMA.solution : type_of% @Erdos1003.erdos_1003.variants.eps87 := by
  exact EqualTotientCount.target_bound
