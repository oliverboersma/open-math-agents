import FormalConjectures.ErdosProblems.«18»
import Mathlib

/-!
# Infinitely many practical numbers with short divisor sums

This independent formalization follows the mathematical argument of Wouter van Doorn and
GPT-6 Astra Pro in Practical numbers and Egyptian fractions, building on work by Liam Price
and GPT-5.6 Sol Pro. We sample the primes independently and penalize repeated choices.
https://github.com/Woett/ChatGPT-s-note-on-Erdos18
-/


/- Divisor-sum lifting and iteration for Erdős 18. -/

open Finset Filter Real
open scoped BigOperators

namespace Erdos18Iteration

def SmallRepresentation (n L : ℕ) : Prop :=
  ∀ m ≤ n, ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card ≤ L ∧ D.sum id = m

theorem SmallRepresentation.practical {n L : ℕ} (h : SmallRepresentation n L) :
    n.IsPractical := by
  intro m hm
  obtain ⟨D, hD, _, hsum⟩ := h m hm
  exact ⟨D, hD, hsum.symm⟩

theorem SmallRepresentation.practicalH_le {n L : ℕ} (h : SmallRepresentation n L) :
    Erdos18.practicalH n ≤ L := by
  apply Finset.sup_le
  intro m hm
  obtain ⟨D, hD, hsize, hsum⟩ := h m (Finset.mem_Icc.mp hm).2
  exact (Nat.sInf_le (show D.card ∈ {k | ∃ F : Finset ℕ,
    F ⊆ n.divisors ∧ F.card = k ∧ m ∈ subsetSums F} from
    ⟨D, hD, rfl, D, subset_rfl, hsum.symm⟩)).trans hsize

theorem lift {n A L B : ℕ} (hn : 0 < n) (hA : 2 ≤ A) (h : SmallRepresentation n L)
    (hres : ∀ m : ℕ, ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card ≤ B ∧ D.sum id ≤ n ∧
      (∀ d ∈ D, ¬ A ∣ d) ∧ m ≡ D.sum id [MOD A]) :
    SmallRepresentation (A * n) (L + B) := by
  have hn' : A * n ≠ 0 := by positivity
  intro m hm
  by_cases hmn : m ≤ n
  · obtain ⟨D, hD, hsize, hsum⟩ := h m hmn
    refine ⟨D, ?_, hsize.trans (Nat.le_add_right _ _), hsum⟩
    intro d hd
    exact Nat.mem_divisors.mpr
      ⟨(Nat.dvd_of_mem_divisors (hD hd)).trans (Nat.dvd_mul_left n A), hn'⟩
  obtain ⟨D, hD, hsize, hsum, hnot, hmod⟩ := hres m
  have hsm : D.sum id ≤ m := hsum.trans (Nat.le_of_lt (lt_of_not_ge hmn))
  have hdvd : A ∣ m - D.sum id := (Nat.modEq_iff_dvd' hsm).mp hmod.symm
  obtain ⟨q, hq⟩ := hdvd
  have hmEq : m = D.sum id + A * q := by omega
  have hqle : q ≤ n := Nat.le_of_mul_le_mul_left (by omega : A * q ≤ A * n) (by omega)
  obtain ⟨F, hF, hFsize, hFsum⟩ := h q hqle
  let e : ℕ ↪ ℕ := ⟨fun x ↦ A * x, fun x y he ↦ Nat.eq_of_mul_eq_mul_left (by omega) he⟩
  have hdj : Disjoint D (F.map e) := by
    refine Finset.disjoint_left.mpr ?_
    intro d hd hmem
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hmem
    exact hnot _ hd (dvd_mul_right _ _)
  refine ⟨D ∪ F.map e, ?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Nat.mem_divisors.mpr
        ⟨(Nat.dvd_of_mem_divisors (hD hd)).trans (Nat.dvd_mul_left n A), hn'⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hd
      exact Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left A (Nat.dvd_of_mem_divisors (hF hf)), hn'⟩
  · rw [Finset.card_union_of_disjoint hdj, Finset.card_map]
    omega
  · rw [Finset.sum_union hdj, Finset.sum_map]
    change D.sum id + (∑ x ∈ F, A * x) = m
    rw [← Finset.mul_sum]
    change D.sum id + A * F.sum id = m
    rw [hFsum, ← hmEq]

def ResidueCover (V A : ℕ) : Prop :=
  ∀ m : ℕ, ∃ z : Fin 4 → ℕ, (∀ i, z i ∣ V) ∧
    m ≡ (∑ i, 2 ^ i.val * z i) [MOD A]


theorem prod_pos_of_prime {S : Finset ℕ} (h : ∀ p ∈ S, p.Prime) :
    0 < S.prod id :=
  Finset.prod_pos (fun p hp ↦ (h p hp).pos)

theorem not_two_dvd_prod {S : Finset ℕ} (h : ∀ p ∈ S, Odd p) :
    ¬ 2 ∣ S.prod id := by
  intro he
  obtain ⟨p, hp, hd⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff id).mp he
  exact (h p hp).not_two_dvd_nat hd

theorem lift_four {A V E L : ℕ} (hA : 2 ≤ A) (hVpos : 0 < V)
    (hVodd : ¬ 2 ∣ V) (h2A : ¬ 2 ∣ A) (hAV : A.Coprime V) (hE : 4 ≤ E)
    (h : SmallRepresentation (2 ^ E * V) L) (hcover : ResidueCover V A) :
    SmallRepresentation (2 ^ E * (V * A)) (L + 4) := by
  rw [show 2 ^ E * (V * A) = A * (2 ^ E * V) by ring]
  apply lift (by positivity) hA h
  intro m
  obtain ⟨z, hz, hmod⟩ := hcover m
  let F (i : Fin 4) : ℕ := 2 ^ i.val * z i
  have hpos (i : Fin 4) : 0 < z i := Nat.pos_of_dvd_of_pos (hz i) hVpos
  have hcardinj : Function.Injective F := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hval (i : Fin 4) : padicValNat 2 (F i) = i.val := by
      rw [show F i = 2 ^ i.val * z i by rfl]
      rw [padicValNat.mul (by positivity) (hpos i).ne', padicValNat.pow, padicValNat_self]
      have hz0 : padicValNat 2 (z i) = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hd ↦ hVodd (hd.trans (hz i)))
      simp [hz0]
    intro i j he
    exact Fin.ext (by rw [← hval i, ← hval j, he])
  let D : Finset ℕ := Finset.univ.image F
  have hsum : D.sum id = ∑ i, F i := by
    simp [D, Finset.sum_image hcardinj.injOn]
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (pow_dvd_pow _ (by omega)) (hz i), by positivity⟩
  · rw [show D.card = 4 by simp [D, Finset.card_image_of_injective, hcardinj]]
  · rw [hsum]
    calc
      ∑ i : Fin 4, F i ≤ ∑ i : Fin 4, 2 ^ i.val * V := by
        exact Finset.sum_le_sum (fun i _ ↦ Nat.mul_le_mul_left _ (Nat.le_of_dvd hVpos (hz i)))
      _ = 15 * V := by
        rw [← Finset.sum_mul]
        congr 1
      _ ≤ 2 ^ E * V := by
        apply Nat.mul_le_mul_right
        exact (by decide : 15 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_right (by decide) hE)
  · intro d hd hAd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    have hA2 : A.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2A).symm
    have hAz : A.Coprime (z i) := hAV.of_dvd_right (hz i)
    have hcop : A.Coprime (F i) := (hA2.pow_right _).mul_right hAz
    exact (by omega : A ≠ 1) (by simpa using hcop.of_dvd_right hAd)
  · rw [hsum]
    exact hmod

theorem power_two_representation (E : ℕ) : SmallRepresentation (2 ^ E) (E + 1) := by
  induction E with
  | zero =>
    norm_num
    intro m hm
    interval_cases m
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp, by simp⟩
  | succ E ih =>
    rw [pow_succ, mul_comm (2 ^ E) 2]
    apply lift (by positivity) (by decide) ih
    intro m
    by_cases he : m % 2 = 0
    · exact ⟨∅, by simp, by simp, by simp, by simp, by simpa [Nat.ModEq] using he⟩
    · refine ⟨{1}, ?_, by simp, ?_, by simp, ?_⟩
      · simp [Nat.mem_divisors]
      · simpa using Nat.one_le_pow E 2 (by decide)
      · simp [Nat.ModEq]
        omega

theorem seed_representation {S : Finset ℕ} {E : ℕ}
    (hp : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ p ≤ 2 ^ E) :
    ∃ L, SmallRepresentation (2 ^ E * S.prod id) L := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E + 1, by simpa using power_two_representation E⟩
  | @insert p S hpS ih =>
    obtain ⟨L, h⟩ := ih (fun q hq ↦ hp q (Finset.mem_insert_of_mem hq))
    have hpp := hp p (Finset.mem_insert_self p S)
    have hn : 0 < 2 ^ E * S.prod id :=
      mul_pos (by positivity) (prod_pos_of_prime (fun q hq ↦ (hp q (Finset.mem_insert_of_mem hq)).1))
    refine ⟨L + (E + 1), ?_⟩
    rw [Finset.prod_insert hpS, id_eq, ← mul_assoc, mul_comm (2 ^ E) p, mul_assoc]
    apply lift hn hpp.1.two_le h
    intro m
    obtain ⟨D, hD, hcard, hsum⟩ :=
      power_two_representation E (m % p) ((Nat.mod_lt m hpp.1.pos).le.trans hpp.2.2)
    refine ⟨D, ?_, hcard, ?_, ?_, ?_⟩
    · exact fun d hd ↦ Nat.mem_divisors.mpr
        ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors (hD hd)) _, hn.ne'⟩
    · rw [hsum]
      apply (Nat.mod_lt _ hpp.1.pos).le.trans
      apply hpp.2.2.trans
      have hprod := prod_pos_of_prime (fun q hq ↦ (hp q (Finset.mem_insert_of_mem hq)).1)
      exact Nat.le_mul_of_pos_right _ hprod
    · intro d hd hpd
      have h2 := hpp.1.dvd_of_dvd_pow (hpd.trans (Nat.dvd_of_mem_divisors (hD hd)))
      exact hpp.2.1 ((Nat.prime_dvd_prime_iff_eq hpp.1 Nat.prime_two).mp h2)
    · rw [hsum]
      exact (Nat.mod_modEq m p).symm


noncomputable def increment (k : ℕ) : ℕ := ⌊(k : ℝ) / (1000 * log (k : ℝ))⌋₊

def GoodPrimes (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≤ 4 * S.card ^ 12

def Selection : Prop :=
  ∃ K : ℕ, ∀ S : Finset ℕ, K ≤ S.card → GoodPrimes S → ∃ T : Finset ℕ,
    Disjoint S T ∧ T.card = increment S.card ∧
      (∀ p ∈ T, p.Prime ∧ Odd p ∧ S.card ^ 12 < p ∧ p ≤ 4 * S.card ^ 12) ∧
      ResidueCover (S.prod id) (T.prod id)

theorem step_of_selection {S T : Finset ℕ} {E L : ℕ} (hE : 4 ≤ E) (hS : GoodPrimes S)
    (hSR : SmallRepresentation (2 ^ E * S.prod id) L)
    (hd : Disjoint S T) (hTne : T.Nonempty)
    (hT : ∀ p ∈ T, p.Prime ∧ Odd p ∧ p ≤ 4 * S.card ^ 12)
    (hc : ResidueCover (S.prod id) (T.prod id)) :
    GoodPrimes (S ∪ T) ∧ SmallRepresentation (2 ^ E * (S ∪ T).prod id) (L + 4) := by
  have hApos : 0 < T.prod id := prod_pos_of_prime fun p hp ↦ (hT p hp).1
  obtain ⟨p, hp⟩ := hTne
  have hA : 2 ≤ T.prod id :=
    (hT p hp).1.two_le.trans (Nat.le_of_dvd hApos (Finset.dvd_prod_of_mem id hp))
  have hAV : (T.prod id).Coprime (S.prod id) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hqp := (hS q hq).1
    apply Nat.Coprime.symm
    apply hqp.coprime_iff_not_dvd.mpr
    intro hqD
    obtain ⟨r, hr, hqr⟩ := (hqp.prime.dvd_finsetProd_iff id).mp hqD
    have he := (Nat.prime_dvd_prime_iff_eq hqp (hT r hr).1).mp hqr
    exact (Finset.disjoint_left.mp hd hq) (he ▸ hr)
  constructor
  · intro q hq
    have hsle : S.card ≤ (S ∪ T).card := Finset.card_le_card Finset.subset_union_left
    have hpow : 4 * S.card ^ 12 ≤ 4 * (S ∪ T).card ^ 12 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsle _)
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨hp, ho, hb⟩ := hS _ hq
      exact ⟨hp, ho, hb.trans hpow⟩
    · obtain ⟨hp, ho, hb⟩ := hT _ hq
      exact ⟨hp, ho, hb.trans hpow⟩
  · rw [Finset.prod_union hd]
    apply lift_four hA (prod_pos_of_prime (fun q hq ↦ (hS q hq).1))
      (not_two_dvd_prod (fun q hq ↦ (hS q hq).2.1))
      (not_two_dvd_prod (fun q hq ↦ (hT q hq).2.1)) hAV hE hSR hc

theorem prime_seed (k : ℕ) (hk : 10 ≤ k) :
    ∃ S : Finset ℕ, S.card = k ∧ GoodPrimes S := by
  let x := k ^ 3
  have hkR : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hx2 : 2 ≤ x := (by decide : 2 ≤ (10 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hk 3)
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hl : log (x : ℝ) > 0 := log_pos (by linarith)
  have hxSquare : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (x : ℝ) by positivity) (show 0 ≤ (x : ℝ) - 2 by linarith)]
  have hlogAdd : log ((x : ℝ) + 1) ≤ 2 * log (x : ℝ) := by
    have hcast := log_le_log (by positivity) hxSquare
    simpa [Real.log_pow] using hcast
  have hxLog : log (x : ℝ) ≤ 3 * (k : ℝ) := by
    simp only [x, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    have hu := log_le_sub_one_of_pos (show 0 < (k : ℝ) by linarith)
    linarith
  have logTwoHalf : (1 / 2 : ℝ) ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hxSize : ((k : ℝ) + 3) * log (x : ℝ) ≤ (x : ℝ) * log 2 := calc
    _ ≤ ((k : ℝ) + 3) * (3 * (k : ℝ)) := mul_le_mul_of_nonneg_left hxLog (by positivity)
    _ ≤ (x : ℝ) * (1 / 2) := by
      have hkSq : (10 : ℝ) * k ≤ (k : ℝ)^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hkR (show 0 ≤ (k : ℝ) by positivity)]
      have ha : 0 ≤ (k : ℝ)^2 - 6 * k - 18 := by linarith
      have hb := mul_nonneg (show 0 ≤ (k : ℝ) by positivity) ha
      simp only [x, Nat.cast_pow]
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left logTwoHalf (by positivity)
  have hcheb := Chebyshev.pi_ge x
  rw [div_le_iff₀ hl] at hcheb
  have hcntR : (k : ℝ) + 1 ≤ x.primeCounting := by
    apply le_of_mul_le_mul_right ?_ hl
    linarith
  have hcnt : k + 1 ≤ (Nat.primesLE x).card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast hcntR
  have htwo : 2 ∈ Nat.primesLE x := by
    simp [Nat.mem_primesLE, hx2, Nat.prime_two]
  have hge : k ≤ ((Nat.primesLE x).erase 2).card := by
    rw [Finset.card_erase_of_mem htwo]
    omega
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hge
  refine ⟨S, hcard, ?_⟩
  intro p hp
  obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp (hS hp)
  obtain ⟨hbound, hprime⟩ := Nat.mem_primesLE.mp hp'
  refine ⟨hprime, hprime.odd_of_ne_two hne, ?_⟩
  rw [hcard]
  exact hbound.trans ((Nat.pow_le_pow_right (by omega : 0 < k) (by decide : 3 ≤ 12)).trans
    (Nat.le_mul_of_pos_left _ (by decide)))


theorem eventually_increment :
    ∀ᶠ k : ℕ in atTop, 0 < increment k ∧ increment k ≤ k ∧
      (1 : ℝ) ≤ 2000 * (log ((k + increment k : ℕ) : ℝ) ^ 2 - log (k : ℝ) ^ 2) := by
  have hlog : Tendsto (fun k : ℕ ↦ log (k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallR : ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 2000 : ℝ) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 2000)
  have hsmall : ∀ᶠ k : ℕ in atTop, ‖log (k : ℝ)‖ ≤ (1 / 2000 : ℝ) * ‖(k : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hsmallR
  filter_upwards [hsmall, hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with k hkSmall hkLog hkNat
  have hkp : (0 : ℝ) < k := by exact_mod_cast (zero_lt_one.trans_le hkNat)
  change 1 ≤ log (k : ℝ) at hkLog
  have hL : 0 < log (k : ℝ) := by linarith
  have h1000 : 0 < 1000 * log (k : ℝ) := by positivity
  rw [Real.norm_of_nonneg hL.le, Real.norm_of_nonneg hkp.le] at hkSmall
  let x : ℝ := (k : ℝ) / (1000 * log (k : ℝ))
  let t : ℕ := increment k
  have hx2 : (2 : ℝ) ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ h1000).2 (by linarith)
  have hxt : (t : ℝ) ≤ x :=
    Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
  have htx : x < (t : ℝ) + 1 := Nat.lt_floor_add_one x
  have ht2 : x / 2 ≤ (t : ℝ) := by linarith
  have htpR : (0 : ℝ) < t := by linarith
  have htp : 0 < t := by exact_mod_cast htpR
  have hXle : x ≤ k := by
    dsimp [x]
    apply (div_le_iff₀ h1000).2
    nlinarith [mul_nonneg hkp.le (show 0 ≤ log (k : ℝ) - 1 by linarith)]
  have htkR : (t : ℝ) ≤ k := hxt.trans hXle
  have htk : t ≤ k := by exact_mod_cast htkR
  refine ⟨htp, htk, ?_⟩
  let y := (t : ℝ) / (k : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := (div_le_one hkp).2 htkR
  have hlogDiff : y / 2 ≤ log (((k + t : ℕ) : ℝ)) - log (k : ℝ) := by
    have hy2 : y / 2 ≤ 2 * y / (y + 2) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hy1)]
    have hcalc : log (((k + t : ℕ) : ℝ)) - log (k : ℝ) = log (1 + y) := by
      rw [← log_div (by positivity) hkp.ne']
      congr 1
      push_cast
      dsimp [y]
      field_simp
    rw [hcalc]
    exact hy2.trans (Real.le_log_one_add_of_nonneg hy)
  have hprod : (1 / 4000 : ℝ) ≤ log (k : ℝ) *
      (log (((k + t : ℕ) : ℝ)) - log (k : ℝ)) := calc
    _ = log (k : ℝ) * (x / 2 / (k : ℝ) / 2) := by
      dsimp [x]
      field_simp
      ring
    _ ≤ log (k : ℝ) * (y / 2) := by
      dsimp [y]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ht2 hkp.le) (by norm_num)) hL.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogDiff hL.le
  change (1 : ℝ) ≤ 2000 * (log (((k + t : ℕ) : ℝ)) ^ 2 - log (k : ℝ) ^ 2)
  nlinarith [sq_nonneg (log (((k + t : ℕ) : ℝ)) - log (k : ℝ))]

theorem prod_prime_lower {S : Finset ℕ} (hS : GoodPrimes S) :
    2 ^ S.card ≤ S.prod id := by
  rw [← Finset.prod_const 2]
  exact Finset.prod_le_prod' (fun p hp ↦ (hS p hp).1.two_le)

theorem iterate (hsel : Selection) :
    ∃ (E L₀ K : ℕ), ∀ j : ℕ, ∃ S : Finset ℕ,
      GoodPrimes S ∧ K + j ≤ S.card ∧
        SmallRepresentation (2 ^ E * S.prod id) (L₀ + 4 * j) ∧
          (j : ℝ) ≤ 2000 * log (S.card : ℝ) ^ 2 := by
  obtain ⟨Ksel, hsel⟩ := hsel
  obtain ⟨Kinc, hinc⟩ := eventually_atTop.mp eventually_increment
  let K := max 10 (max Ksel Kinc)
  let E := 4 + 4 * K ^ 12
  have hE : 4 ≤ E := by dsimp [E]; omega
  obtain ⟨S₀, hS₀c, hS₀⟩ := prime_seed K (le_max_left 10 _)
  have hS0' (p : ℕ) (hp : p ∈ S₀) : p.Prime ∧ p ≠ 2 ∧ p ≤ 2 ^ E := by
    obtain ⟨hpp, hodd, hb⟩ := hS₀ p hp
    refine ⟨hpp, fun he ↦ hodd.not_two_dvd_nat (he ▸ dvd_rfl), ?_⟩
    rw [hS₀c] at hb
    exact hb.trans ((Nat.le_add_left _ _).trans (E.lt_two_pow_self.le))
  obtain ⟨L₀, hSR⟩ := seed_representation (E := E) hS0'
  refine ⟨E, L₀, K, fun j ↦ ?_⟩
  induction j with
  | zero =>
    refine ⟨S₀, hS₀, by simp [hS₀c], by simpa using hSR, ?_⟩
    simp only [Nat.cast_zero]
    positivity
  | succ j ih =>
    obtain ⟨S, hS, hcard, hSrep, hj⟩ := ih
    have hK : K ≤ S.card := (Nat.le_add_right _ _).trans hcard
    obtain ⟨T, hd, ht, hT, hcov⟩ := hsel S
      (((le_max_left Ksel Kinc).trans (le_max_right 10 _)).trans hK) hS
    obtain ⟨htpos, _, hic⟩ := hinc S.card
      (((le_max_right Ksel Kinc).trans (le_max_right 10 _)).trans hK)
    have hTne : T.Nonempty := Finset.card_pos.mp (ht ▸ htpos)
    obtain ⟨hUnion, hRep⟩ := step_of_selection hE hS hSrep hd hTne
      (fun p hp ↦ ⟨(hT p hp).1, (hT p hp).2.1, (hT p hp).2.2.2⟩) hcov
    have hcard' : (S ∪ T).card = S.card + increment S.card := by
      rw [Finset.card_union_of_disjoint hd, ht]
    refine ⟨S ∪ T, hUnion, ?_, ?_, ?_⟩
    · rw [hcard']; omega
    · simpa [Nat.mul_succ, Nat.add_assoc] using hRep
    · rw [hcard']
      push_cast at hic ⊢
      linarith

theorem lower_loglog {n k : ℕ} (hk : 4 ≤ k) (hn : 2 ^ k ≤ n) :
    log (k : ℝ) / 2 ≤ log (log (n : ℝ)) := by
  have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hnR : (2 : ℝ)^k ≤ (n : ℝ) := by exact_mod_cast hn
  have hln : (k : ℝ) * log 2 ≤ log (n : ℝ) := by
    rw [← log_pow]
    exact log_le_log (by positivity) hnR
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkHalf : (k : ℝ)/2 ≤ log (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ (k : ℝ) by positivity)]
  have hsum : log (k : ℝ) / 2 ≤ log ((k : ℝ) / 2) := by
    rw [log_div (by positivity) (by norm_num)]
    have aux : 2 * log 2 ≤ log (k : ℝ) := by
      have := log_le_log (show 0 < (2 : ℝ)^2 by positivity)
        (show (2 : ℝ)^2 ≤ k by norm_num; exact hk)
      simpa [Real.log_pow] using this
    linarith
  exact hsum.trans (log_le_log (by positivity) hkHalf)

theorem conclusion (hsel : Selection) : type_of% @Erdos18.erdos_18a := by
  obtain ⟨E, L₀, K, hh⟩ := iterate hsel
  refine ⟨4, by norm_num, frequently_atTop.mpr (fun a ↦ ?_)⟩
  have hab :
      ∀ᶠ k : ℕ in atTop, 1 ≤ log (k : ℝ) ∧
        (L₀ : ℝ) + 8000 * log (k : ℝ) ^ 2 < (log (k : ℝ) / 2) ^ 4 := by
    have hlog : Tendsto (fun k : ℕ ↦ log (k : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually
      (eventually_gt_atTop (16 * ((L₀ : ℝ) + 8001)))] with k hk
    let u := log (k : ℝ)
    have hu : 16 * ((L₀ : ℝ) + 8001) < u := hk
    have hu1 : 1 ≤ u := by linarith
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    have h1 : ((L₀ : ℝ) + 8000) < u ^ 2 / 16 := by nlinarith [sq_nonneg (u - 1)]
    have h2 : (L₀ : ℝ) + 8000 * u ^ 2 ≤ ((L₀ : ℝ) + 8000) * u ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (L₀ : ℝ) by positivity) (sub_nonneg.mpr hu2)]
    exact ⟨hu1, h2.trans_lt (by
      calc
        _ < (u ^ 2 / 16) * u ^ 2 := mul_lt_mul_of_pos_right h1 (by linarith)
        _ = (u / 2) ^ 4 := by ring)⟩
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hab
  let j := max a (max 4 k₁)
  obtain ⟨S, hS, hcard, hrep, hcost⟩ := hh j
  let n := 2 ^ E * S.prod id
  have hpow : 2 ^ S.card ≤ n := (prod_prime_lower hS).trans
    (Nat.le_mul_of_pos_left _ (by positivity))
  have hcj : j ≤ S.card := (Nat.le_add_left _ _).trans hcard
  have hka : a ≤ n := (le_max_left _ _).trans <| hcj.trans <|
    (S.card.lt_two_pow_self.le).trans hpow
  have hk4 : 4 ≤ S.card := (le_max_left _ _).trans ((le_max_right _ _).trans hcj)
  have hk1 : k₁ ≤ S.card := (le_max_right _ _).trans ((le_max_right _ _).trans hcj)
  have hlog := lower_loglog hk4 hpow
  have habs := hk₁ _ hk1
  refine ⟨n, hka, hrep.practical, ?_⟩
  rw [Real.rpow_ofNat]
  change (Erdos18.practicalH n : ℝ) < log (log (n : ℝ)) ^ (4 : ℕ)
  have hr : (Erdos18.practicalH n : ℝ) ≤ (L₀ : ℝ) + 4 * (j : ℝ) := by
    exact_mod_cast hrep.practicalH_le
  calc
    _ ≤ (L₀ : ℝ) + 4 * (j : ℝ) := hr
    _ ≤ (L₀ : ℝ) + 8000 * log (S.card : ℝ)^2 := by linarith
    _ < (log (S.card : ℝ) / 2)^4 := habs.2
    _ ≤ _ := by
      exact pow_le_pow_left₀ (by linarith [habs.1]) hlog _

end Erdos18Iteration


namespace Erdos18Numeric

open Filter Real

noncomputable def weight (k : ℕ) : ℝ := (k : ℝ)^9

noncomputable def rate (k : ℕ) : ℝ := 1 / (k : ℝ)^10

theorem eventually_numeric :
    ∀ᶠ k : ℕ in atTop,
      2 ≤ k ∧ 0 < Erdos18Iteration.increment k ∧
      (Erdos18Iteration.increment k : ℝ) * (weight k * rate k) ≤ 1/100 ∧
      (Erdos18Iteration.increment k : ℝ)^2 / ((2*k^11 : ℕ) : ℝ) ≤ 1/10 ∧
      (∀ s : ℕ, s ≤ Erdos18Iteration.increment k → ((2 : ℝ)^(k/2 : ℕ))⁻¹ ≤ rate k ^ s) ∧
      (4 * (k : ℝ)^12)^2 ≤ weight k ^ 3 := by
  have hlog : Tendsto (fun k : ℕ ↦ log (k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Erdos18Iteration.eventually_increment,
    eventually_ge_atTop (10 : ℕ), hlog.eventually (eventually_ge_atTop (1 : ℝ))] with k hstep hk hlogk
  have hkR : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkP : (0 : ℝ) < k := by linarith
  change 1 ≤ log (k : ℝ) at hlogk
  have hlogP : 0 < log (k : ℝ) := by linarith
  let t := Erdos18Iteration.increment k
  have htReal : (t : ℝ) ≤ (k : ℝ) / (1000 * log (k : ℝ)) :=
    Nat.floor_le (by positivity)
  have htk : (t : ℝ) ≤ (k : ℝ) := by exact_mod_cast hstep.2.1
  have hmul : (t : ℝ) * (1000 * log (k : ℝ)) ≤ (k : ℝ) :=
    (le_div_iff₀ (by positivity)).mp htReal
  refine ⟨by omega, hstep.1, ?_, ?_, ?_, ?_⟩
  · change (t : ℝ) * (weight k * rate k) ≤ 1/100
    unfold weight rate
    have hpow : (k : ℝ)^9 * (1 / (k : ℝ)^10) = 1 / (k : ℝ) := by
      field_simp
    rw [hpow, mul_one_div]
    apply (div_le_iff₀ hkP).mpr
    nlinarith [mul_nonneg (show 0 ≤ (t : ℝ) by positivity) (sub_nonneg.mpr hlogk)]
  · push_cast
    change (t : ℝ)^2 / (2 * (k : ℝ)^11) ≤ 1/10
    apply (div_le_iff₀ (by positivity)).mpr
    have htsq := pow_le_pow_left₀ (show 0 ≤ (t : ℝ) by positivity) htk 2
    have hk5 : (5 : ℝ) ≤ (k : ℝ)^9 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hkR 9
      norm_num at h
      linarith
    have hpow : (k : ℝ)^2 * (k : ℝ)^9 = (k : ℝ)^11 := by ring
    have h := mul_le_mul_of_nonneg_left hk5 (sq_nonneg (k : ℝ))
    nlinarith only [htsq, hpow, h]
  · intro s hs
    have hsCast : (s : ℝ) ≤ t := by exact_mod_cast hs
    have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by
      have h := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hhalf : (k : ℝ) / 4 ≤ ((k / 2 : ℕ) : ℝ) := by
      have ha : k ≤ 4 * (k/2) := by omega
      have ha' : (k : ℝ) ≤ 4 * ((k/2 : ℕ) : ℝ) := by exact_mod_cast ha
      linarith
    have hsbound : (s : ℝ) * (1000 * log (k : ℝ)) ≤ (k : ℝ) :=
      (mul_le_mul_of_nonneg_right hsCast (by positivity)).trans hmul
    have hlb : (k : ℝ)/8 ≤ ((k/2 : ℕ) : ℝ) * log 2 :=
      (by ring : (k : ℝ)/8 = (k : ℝ)/4*(1/2)).le.trans
        (mul_le_mul hhalf hlog2 (by norm_num) (by positivity))
    have hle : ((s * 10 : ℕ) : ℝ) * log (k : ℝ) ≤ ((k/2 : ℕ) : ℝ) * log 2 := by
      push_cast
      nlinarith only [hsbound, hlb, hkP]
    have hpow : (k : ℝ) ^ (s*10) ≤ (2 : ℝ) ^ (k/2 : ℕ) := by
      apply (log_le_log_iff (by positivity) (by positivity)).mp
      simpa only [log_pow] using hle
    unfold rate
    rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm 10, one_div]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
  · unfold weight
    have hk16 : (16 : ℝ) ≤ (k : ℝ)^3 := by
      have hi := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hkR 3
      norm_num at hi
      linarith
    calc
      _ = (16 : ℝ)*(k : ℝ)^24 := by ring
      _ ≤ (k : ℝ)^3*(k : ℝ)^24 := mul_le_mul_of_nonneg_right hk16 (by positivity)
      _ = _ := by ring

end Erdos18Numeric

/- Prime supply and bounds for prime divisors of differences. -/

open Filter Finset Real
open scoped BigOperators

namespace Erdos18PrimeBounds

def eligiblePrimes (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((Nat.primesLE (4 * k ^ 12)) \ Nat.primesLE (k ^ 12)) \ S

theorem mem_eligiblePrimes {k p : ℕ} {S : Finset ℕ} :
    p ∈ eligiblePrimes k S ↔ p.Prime ∧ k ^ 12 < p ∧ p ≤ 4 * k ^ 12 ∧ p ∉ S := by
  simp only [eligiblePrimes, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨⟨hu, hp⟩, hlow⟩, hs⟩
    exact ⟨hp, lt_of_not_ge (fun h ↦ hlow ⟨h, hp⟩), hu, hs⟩
  · rintro ⟨hp, hlo, hu, hs⟩
    exact ⟨⟨⟨hu, hp⟩, fun h ↦ (not_le_of_gt hlo) h.1⟩, hs⟩

theorem eventually_eligible_card :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset ℕ, S.card ≤ k →
      2 * k ^ 11 ≤ (eligiblePrimes k S).card := by
  have hsmallR : ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 1000 : ℝ) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 1000)
  have hsmallN : ∀ᶠ k : ℕ in atTop, ‖log (k : ℝ)‖ ≤ (1 / 1000 : ℝ) * ‖(k : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hsmallR
  filter_upwards [hsmallN, eventually_ge_atTop (2 : ℕ)] with k hsmall hk S hS
  let x : ℕ := k ^ 12
  let y : ℕ := 4 * x
  let B := Nat.primesLE y \ Nat.primesLE x
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : (1 : ℝ) ≤ k := by linarith
  have hln : 0 ≤ log (k : ℝ) := log_nonneg hkn
  rw [Real.norm_of_nonneg hln, Real.norm_of_nonneg (by positivity)] at hsmall
  have hy2 : (2 : ℝ) ≤ y := by
    have hx : 1 ≤ x := by
      dsimp [x]
      exact (show 1 ≤ (2 : ℕ)^12 by decide).trans (Nat.pow_le_pow_left hk 12)
    have hyy : 2 ≤ y := by dsimp [y]; omega
    exact_mod_cast hyy
  have hyR : (y : ℝ) = 4 * (k : ℝ) ^ 12 := by simp [y, x]
  have hxR : (x : ℝ) = (k : ℝ) ^ 12 := by simp [x]
  have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogY : log (y : ℝ) ≤ 14 * log (k : ℝ) := by
    rw [hyR, Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlog4]
    have h := log_le_log zero_lt_two hkR
    norm_num
    linarith
  have hlogAdd : log ((y : ℝ) + 1) ≤ 2 * log (y : ℝ) := by
    have hs : (y : ℝ) + 1 ≤ (y : ℝ)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ (y : ℝ) by positivity) (show 0 ≤ (y : ℝ) - 2 by linarith)]
    simpa [Real.log_pow] using log_le_log (by positivity : (0 : ℝ) < (y : ℝ) + 1) hs
  have hroot : √(y : ℝ) = 2 * (k : ℝ)^6 := by
    rw [hyR, show 4 * (k : ℝ)^12 = (2 * (k : ℝ)^6)^2 by ring]
    rw [Real.sqrt_sq (by positivity)]
  have hpow6 : 1 ≤ (k : ℝ)^6 := one_le_pow₀ hkn
  have hpow7 : (k : ℝ)^7 ≤ (k : ℝ)^12 := pow_le_pow_right₀ hkn (by decide)
  have herr : log ((y : ℝ) + 1) + 2 * √(y : ℝ) * log y ≤ (x : ℝ) / 2 := calc
    _ ≤ (2 + 4 * (k : ℝ)^6) * log y := by rw [hroot]; linarith
    _ ≤ (6 * (k : ℝ)^6) * (14 * log (k : ℝ)) := by
      exact mul_le_mul (by linarith) hlogY (log_nonneg (by linarith)) (by positivity)
    _ ≤ (6 * (k : ℝ)^6) * (14 * ((k : ℝ) / 1000)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (84 / 1000 : ℝ) * (k : ℝ)^7 := by ring
    _ ≤ (84 / 1000 : ℝ) * (k : ℝ)^12 :=
      mul_le_mul_of_nonneg_left hpow7 (by norm_num)
    _ ≤ (x : ℝ) / 2 := by
      rw [hxR]
      nlinarith [show 0 ≤ (k : ℝ)^12 by positivity]
  have hmain : (x : ℝ) ≤ (y : ℝ) * log 2 - log 4 * x := by
    rw [hlog4, hyR, hxR]
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ)^12 by positivity) (sub_nonneg.mpr hlog2)]
  have htheta : (x : ℝ) / 2 ≤ Chebyshev.theta y - Chebyshev.theta x := by
    linarith [Chebyshev.theta_ge y, Chebyshev.theta_le_log4_mul_x
      (x := (x : ℝ)) (by positivity)]
  have hsum : Chebyshev.theta y - Chebyshev.theta x = ∑ p ∈ B, log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact (Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (by dsimp [y]; omega))).symm
  have hsumBound : (∑ p ∈ B, log (p : ℝ)) ≤ (B.card : ℝ) * log y := by
    calc
      _ ≤ ∑ _p ∈ B, log (y : ℝ) := Finset.sum_le_sum fun p hp ↦
        log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos)
          (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).1)
      _ = _ := by simp
  have hB : 3 * k ^ 11 ≤ B.card := by
    have hlogPos : 0 < log (y : ℝ) := log_pos (by linarith)
    have hlhs : (3 * (k : ℝ)^11) * log y ≤ (x : ℝ)/2 := calc
      _ ≤ (3 * (k : ℝ)^11) * (14 * ((k : ℝ) / 1000)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (42 / 1000 : ℝ) * (k : ℝ)^12 := by ring
      _ ≤ _ := by rw [hxR]; nlinarith [show 0 ≤ (k : ℝ)^12 by positivity]
    have hz := hlhs.trans ((htheta.trans_eq hsum).trans hsumBound)
    exact_mod_cast (le_of_mul_le_mul_right hz hlogPos)
  have hK : k ≤ k ^ 11 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < k) (show 1 ≤ 11 by decide))
  have hBcard : (B \ S).card + S.card ≥ B.card := Finset.card_le_card_sdiff_add_card
  change 2 * k ^ 11 ≤ (B \ S).card
  omega

theorem large_prime_diff_bound {k : ℕ} {P : Finset ℕ} (hk : 2 ≤ k)
    (hP : ∀ p ∈ P, p.Prime ∧ k ^ 12 < p) {a b : ℕ} (hab : a ≠ b)
    (ha : a ≤ (4 * k ^ 12)^k) (hb : b ≤ (4 * k ^ 12)^k) :
    (P.filter fun p ↦ p ∣ Nat.dist a b).card ≤ 2 * k := by
  let T := P.filter fun p ↦ p ∣ Nat.dist a b
  have hPrimes (p : ℕ) (hp : p ∈ T) : p.Prime ∧ k ^ 12 < p :=
    hP p (Finset.mem_filter.mp hp).1
  have hprod : T.prod id ∣ Nat.dist a b := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hPrimes p hp).1 (hPrimes q hq).1).2 hpq)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hdist : Nat.dist a b ≤ (4 * k ^ 12)^k := by unfold Nat.dist; omega
  have hpow : (k ^ 12)^T.card ≤ T.prod id := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod'
    exact fun p hp ↦ (hPrimes p hp).2.le
  have h4 : 4 < k ^ 12 := (by decide : 4 < (2 : ℕ)^12).trans_le (Nat.pow_le_pow_left hk 12)
  have hstrict : (4 * k ^ 12)^k < (k ^ 12)^(2 * k) := by
    rw [pow_mul, pow_two]
    exact Nat.pow_lt_pow_left (Nat.mul_lt_mul_of_pos_right h4 (by positivity))
      (by omega : k ≠ 0)
  have hh := hpow.trans_lt ((Nat.le_of_dvd (Nat.dist_pos_of_ne hab) hprod).trans_lt
    (hdist.trans_lt hstrict))
  change T.card ≤ 2 * k
  by_contra! hlarge
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by omega : 0 < k ^ 12) hlarge.le)) hh

theorem collision_bound {k : ℕ} {P : Finset ℕ} (hk : 2 ≤ k)
    (hP : ∀ p ∈ P, p.Prime ∧ k ^ 12 < p) (hsize : 2 * k ^ 11 ≤ P.card)
    {a b : ℕ} (hab : a ≠ b) (ha : a ≤ (4 * k ^ 12)^k) (hb : b ≤ (4 * k ^ 12)^k) :
    (((Finset.univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).card : ℝ) /
      Fintype.card P ≤ 1 / (k : ℝ)^10 := by
  let T := P.filter fun p ↦ p ∣ Nat.dist a b
  have hcard : ((Finset.univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).card =
      T.card := by
    have hm : ((Finset.univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).map
        (Function.Embedding.subtype _) = T := by ext p; simp [T, and_comm]
    rw [← hm, Finset.card_map]
  rw [hcard, Fintype.card_coe]
  have hlarge : T.card ≤ 2 * k := large_prime_diff_bound hk hP hab ha hb
  have hlargeR : (T.card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hlarge
  have hszR : 2 * (k : ℝ)^11 ≤ P.card := by exact_mod_cast hsize
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hPpos : (0 : ℝ) < P.card := lt_of_lt_of_le (by positivity) hszR
  refine (div_le_div_iff₀ hPpos (by positivity)).mpr ?_
  calc
    (T.card : ℝ) * (k : ℝ)^10 ≤ (2 * (k : ℝ)) * (k : ℝ)^10 :=
      mul_le_mul_of_nonneg_right hlargeR (by positivity)
    _ = 2 * (k : ℝ)^11 := by ring
    _ ≤ 1 * P.card := by simpa using hszR

end Erdos18PrimeBounds

/- # Fourier bounds for four-term sums of divisors -/

namespace Erdos18Independent

open Finset Complex
open scoped ComplexConjugate

noncomputable def collision (d : ℕ) (X : Finset ℕ) : ℝ :=
  (∑ a ∈ X, ∑ b ∈ X, if d ∣ Nat.dist a b then (1 : ℝ) else 0) / (X.card : ℝ)^2

lemma mod_eq_iff_dist {d a b : ℕ} : a % d = b % d ↔ d ∣ Nat.dist a b := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact Nat.modEq_iff_dvd' h
  · rw [Nat.dist_eq_sub_of_le_right h, eq_comm]
    exact Nat.modEq_iff_dvd' h

noncomputable def coeff (d : ℕ) [NeZero d] (X : Finset ℕ) (t : ZMod d) : ℂ :=
  (∑ x ∈ X, ZMod.stdAddChar (t * (x : ZMod d))) / X.card

lemma wave_sum {d : ℕ} [NeZero d] (x : ZMod d) :
    ∑ t : ZMod d, ZMod.stdAddChar (t*x) = if x = 0 then (d : ℂ) else 0 := by
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · rw [if_neg hx]
    simp only [mul_comm _ x, ← AddChar.mulShift_apply]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hx)

lemma wave_neg {d : ℕ} [NeZero d] (x : ZMod d) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
    AddChar.map_neg_eq_inv]

lemma coeff_energy {d : ℕ} [NeZero d] (X : Finset ℕ) :
    ∑ t : ZMod d, ‖coeff d X t‖ ^ 2 = d * collision d X := by
  classical
  have hterm (t : ZMod d) :
      ((‖coeff d X t‖ ^ 2 : ℝ) : ℂ) =
        (∑ p ∈ X ×ˢ X, ZMod.stdAddChar (t * ((p.1 : ZMod d) - (p.2 : ZMod d)))) /
          (X.card : ℂ)^2 := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [coeff, map_div₀, map_natCast, map_sum, wave_neg, div_mul_div_comm, ← pow_two]
    congr 1
    rw [Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← AddChar.map_add_eq_mul, mul_sub, sub_eq_add_neg]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [hterm, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [wave_sum, sub_eq_zero, ZMod.natCast_eq_natCast_iff', mod_eq_iff_dist]
  rw [Finset.sum_product]
  unfold collision
  push_cast
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

private def residueCount (d : ℕ) (X : Finset ℕ) (r : ZMod d) : ℕ :=
  (X.filter (fun x : ℕ ↦ (x : ZMod d) = r)).card

lemma sum_by_residue {M : Type*} [AddCommMonoid M] {d : ℕ} [NeZero d]
    (X : Finset ℕ) (f : ZMod d → M) :
    ∑ x ∈ X, f (x : ZMod d) = ∑ r, residueCount d X r • f r := by
  rw [← Finset.sum_fiberwise X (fun x ↦ (x : ZMod d))]
  apply Finset.sum_congr rfl
  intro r _
  rw [residueCount, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

lemma collision_count {d : ℕ} [NeZero d] (X : Finset ℕ) :
    collision d X = (∑ r : ZMod d, (residueCount d X r : ℝ)^2) / (X.card : ℝ)^2 := by
  classical
  unfold collision
  congr 1
  have hterm (a : ℕ) :
      (∑ b ∈ X, if d ∣ Nat.dist a b then (1 : ℝ) else 0) =
        (residueCount d X (a : ZMod d) : ℝ) := by
    calc
      _ = ∑ b ∈ X, if (b : ZMod d) = (a : ZMod d) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [← mod_eq_iff_dist, ← ZMod.natCast_eq_natCast_iff', eq_comm]
      _ = _ := by rw [Finset.sum_boole]; rfl
  simp_rw [hterm]
  rw [sum_by_residue X (fun r ↦ (residueCount d X r : ℝ))]
  apply Finset.sum_congr rfl
  intro r _
  simp [nsmul_eq_mul, pow_two]

lemma coeff_zero {d : ℕ} [NeZero d] {X : Finset ℕ} (hX : X.Nonempty) : coeff d X 0 = 1 := by
  simp [coeff, hX.card_ne_zero]

lemma coeff_product {d V₁ V₂ : ℕ} [NeZero d] (h : V₁.Coprime V₂) (t : ZMod d) :
    coeff d (V₁ * V₂).divisors t =
      (∑ x ∈ V₁.divisors, coeff d V₂.divisors (t * (x : ZMod d))) / V₁.divisors.card := by
  classical
  unfold coeff
  rw [Nat.divisors_mul]
  change
    (∑ z ∈ (V₁.divisors ×ˢ V₂.divisors).image (fun p ↦ p.1 * p.2),
      ZMod.stdAddChar (t * (z : ZMod d))) /
      (((V₁.divisors ×ˢ V₂.divisors).image (fun p ↦ p.1 * p.2)).card : ℂ) = _
  rw [Finset.sum_image h.mul_injOn_divisors, Finset.card_image_of_injOn h.mul_injOn_divisors,
    Finset.sum_product, Finset.card_product, Nat.cast_mul]
  simp_rw [Nat.cast_mul, mul_assoc t, ← Finset.sum_div]
  ring

lemma bilinear_bound {d V₁ V₂ : ℕ} [NeZero d] (h : V₁.Coprime V₂)
    (t : (ZMod d)ˣ) :
    ‖coeff d (V₁ * V₂).divisors t‖ ^ 2 ≤
      d * collision d V₁.divisors * collision d V₂.divisors := by
  classical
  let f (r : ZMod d) := ‖coeff d V₂.divisors ((t : ZMod d) * r)‖
  rw [coeff_product h, norm_div, Complex.norm_natCast, div_pow]
  have htri := norm_sum_le V₁.divisors
    (fun x ↦ coeff d V₂.divisors ((t : ZMod d) * (x : ZMod d)))
  have hnormle : ‖∑ x ∈ V₁.divisors, coeff d V₂.divisors ((t : ZMod d) * (x : ZMod d))‖ ^ 2 ≤
      (∑ x ∈ V₁.divisors, f (x : ZMod d)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [sum_by_residue] at hnormle
  simp only [nsmul_eq_mul] at hnormle
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun r : ZMod d ↦ (residueCount d V₁.divisors r : ℝ)) f
  refine (div_le_div_of_nonneg_right (hnormle.trans hc) (sq_nonneg _)).trans_eq ?_
  have henergy : ∑ r : ZMod d, f r ^ 2 = d * collision d V₂.divisors := by
    rw [← coeff_energy]
    exact Fintype.sum_bijective _ t.mulLeft_bijective _ _ (fun _ ↦ rfl)
  rw [henergy, collision_count V₁.divisors]
  ring

noncomputable def errorWeight (d : ℕ) [NeZero d] (X : Finset ℕ) (t : ZMod d) : ℝ :=
  ‖coeff d X t‖ * ‖coeff d X (2 * t)‖ * (‖coeff d X (4 * t)‖ * ‖coeff d X (8 * t)‖)

lemma errorWeight_nonneg {d : ℕ} [NeZero d] (X : Finset ℕ) (t : ZMod d) :
    0 ≤ errorWeight d X t := by
  unfold errorWeight
  positivity

lemma collision_nonneg (d : ℕ) (X : Finset ℕ) : 0 ≤ collision d X := by
  unfold collision
  exact div_nonneg (Finset.sum_nonneg fun a ha ↦
    Finset.sum_nonneg fun b hb ↦ by split_ifs <;> norm_num) (sq_nonneg _)

lemma errorWeight_sum {d V₁ V₂ : ℕ} [NeZero d] (h : V₁.Coprime V₂) (hd : Odd d) :
    (∑ t ∈ (Finset.univ : Finset (ZMod d)).filter IsUnit, errorWeight d (V₁ * V₂).divisors t)
      ≤ (d : ℝ)^2 * collision d V₁.divisors * collision d V₂.divisors *
        collision d (V₁ * V₂).divisors := by
  classical
  let X := (V₁ * V₂).divisors
  let K : ℝ := d * collision d V₁.divisors * collision d V₂.divisors
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (collision_nonneg ..)) (collision_nonneg ..)
  have h2 : IsUnit (2 : ZMod d) := by
    exact (ZMod.isUnit_iff_coprime 2 d).mpr (Nat.coprime_two_left.mpr hd)
  have hle (t : ZMod d) (ht : IsUnit t) : errorWeight d X t ≤
      K * ((‖coeff d X (4 * t)‖ ^ 2 + ‖coeff d X (8 * t)‖ ^ 2) / 2) := by
    obtain ⟨u, rfl⟩ := ht
    obtain ⟨v, hv⟩ := h2.mul u.isUnit
    have H₁ : ‖coeff d X (u : ZMod d)‖ ^ 2 ≤ K := bilinear_bound h u
    have H₂ : ‖coeff d X (2 * u)‖ ^ 2 ≤ K := by
      rw [← hv]
      exact bilinear_bound h v
    have H₃ : ‖coeff d X (u : ZMod d)‖ * ‖coeff d X (2 * u)‖ ≤ K := by
      nlinarith only [H₁, H₂, sq_nonneg (‖coeff d X (u : ZMod d)‖ - ‖coeff d X (2 * u)‖)]
    have H₄ : ‖coeff d X (4 * u)‖ * ‖coeff d X (8 * u)‖ ≤
        (‖coeff d X (4 * u)‖ ^ 2 + ‖coeff d X (8 * u)‖ ^ 2) / 2 := by
      nlinarith only [sq_nonneg (‖coeff d X (4 * u)‖ - ‖coeff d X (8 * u)‖)]
    unfold errorWeight
    exact mul_le_mul H₃ H₄ (by positivity) hK
  have hscale (r : ZMod d) (hr : IsUnit r) : ∑ t : ZMod d, ‖coeff d X (r * t)‖ ^ 2 =
      d * collision d X := by
    obtain ⟨u, rfl⟩ := hr
    rw [← coeff_energy]
    exact Fintype.sum_bijective _ u.mulLeft_bijective _ _ (fun _ ↦ rfl)
  have h4 : IsUnit (4 : ZMod d) := by
    convert h2.pow 2 using 1
    norm_num
  have h8 : IsUnit (8 : ZMod d) := by
    convert h2.pow 3 using 1
    norm_num
  calc
    _ ≤ ∑ t ∈ (Finset.univ : Finset (ZMod d)).filter IsUnit,
          K * ((‖coeff d X (4 * t)‖ ^ 2 + ‖coeff d X (8 * t)‖ ^ 2) / 2) :=
      Finset.sum_le_sum fun t ht ↦ hle t (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t : ZMod d, K * ((‖coeff d X (4 * t)‖ ^ 2 + ‖coeff d X (8 * t)‖ ^ 2) / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦
        mul_nonneg hK (by positivity)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hscale _ h4,
        hscale _ h8]
      dsimp [K, X]
      ring

lemma sum_zmod_range {M : Type*} [AddCommMonoid M] {d : ℕ} [NeZero d] (f : ZMod d → M) :
    (∑ t : ZMod d, f t) = ∑ t ∈ Finset.range d, f (t : ZMod d) := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine (Fintype.sum_equiv (ZMod.finEquiv d).toEquiv _ _ (fun t ↦ ?_)).symm
  congr 1
  cases d with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ d =>
    change (t.val : ZMod (d + 1)) = t
    exact ZMod.natCast_zmod_val (n := d + 1) t

lemma wave_natCast {d : ℕ} [NeZero d] (t : ℕ) :
    ZMod.stdAddChar (t : ZMod d) = cexp (2 * Real.pi * I * t / d) := by
  exact_mod_cast (ZMod.stdAddChar_coe (N := d) (t : ℤ))

lemma scaled_coeff {A d g u t : ℕ} [NeZero A] [NeZero d]
    (hA : A = d * g) (ht : t = u * g) (hg : 0 < g)
    (X : Finset ℕ) (r : ℕ) :
    coeff A X ((r : ZMod A) * t) = coeff d X ((r : ZMod d) * u) := by
  unfold coeff
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
  rw [wave_natCast, wave_natCast]
  congr 1
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [hA, ht]
  push_cast
  field_simp

lemma reduced_errorWeight {A d g u t : ℕ} [NeZero A] [NeZero d]
    (hA : A = d * g) (ht : t = u * g) (hg : 0 < g)
    (X : Finset ℕ) :
    errorWeight A X (t : ZMod A) = errorWeight d X (u : ZMod d) := by
  unfold errorWeight
  have he1 := scaled_coeff hA ht hg X 1
  have he2 := scaled_coeff hA ht hg X 2
  have he4 := scaled_coeff hA ht hg X 4
  have he8 := scaled_coeff hA ht hg X 8
  simp only [Nat.cast_ofNat] at he2 he4 he8
  simp only [Nat.cast_one, one_mul] at he1
  rw [he1, he2, he4, he8]

lemma errorWeight_bound {A V₁ V₂ : ℕ} [NeZero A] (h : V₁.Coprime V₂) (hA : Odd A) :
    (∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, errorWeight A (V₁ * V₂).divisors t) ≤
      ∑ d ∈ A.divisors.filter (fun d ↦ 1 < d),
        (d : ℝ)^2 * collision d V₁.divisors * collision d V₂.divisors *
          collision d (V₁ * V₂).divisors := by
  classical
  let X := (V₁ * V₂).divisors
  let N := (Finset.range A).erase 0
  let D := A.divisors.filter (fun d ↦ 1 < d)
  let g (t : ℕ) := A.gcd t
  let den (t : ℕ) := A / g t
  let num (t : ℕ) := t / g t
  have hAnz : A ≠ 0 := NeZero.ne A
  have hApos : 0 < A := Nat.pos_of_ne_zero hAnz
  have hg (t : ℕ) : 0 < g t := Nat.gcd_pos_of_pos_left _ hApos
  have hDmul (t : ℕ) : den t * g t = A := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have hNmul (t : ℕ) : num t * g t = t := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have hden_dvd (t : ℕ) : den t ∣ A := ⟨g t, (hDmul t).symm⟩
  have hlt (t : ℕ) (ht : t ∈ N) : num t < den t := by
    apply (Nat.div_lt_iff_lt_mul (hg t)).mpr
    rw [hDmul]
    exact Finset.mem_range.mp (Finset.mem_erase.mp ht).2
  have hden (t : ℕ) (ht : t ∈ N) : 1 < den t := by
    by_contra! hle
    have hNp : num t ≠ 0 := by
      intro he
      have hh := (Finset.mem_erase.mp ht).1
      apply hh
      simpa [he] using (hNmul t).symm
    have hsmall := hlt t ht
    omega
  have hDenMaps (t : ℕ) (ht : t ∈ N) : den t ∈ D :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hden_dvd t, hAnz⟩, hden t ht⟩
  have hcoprime (t : ℕ) : (num t).Coprime (den t) := by
    simpa only [Nat.coprime_comm] using (Nat.gcd_div_gcd_div_gcd_of_pos_left
      (n := A) (m := t) hApos : (A / A.gcd t).Coprime (t / A.gcd t))
  have hsumRange :
      (∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, errorWeight A X t) =
        ∑ t ∈ N, errorWeight A X (t : ZMod A) := by
    apply add_right_cancel (b := errorWeight A X 0)
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ _)]
    have hzero : 0 ∈ Finset.range A := Finset.mem_range.mpr hApos
    have hr := Finset.sum_erase_add (Finset.range A)
      (fun t : ℕ ↦ errorWeight A X (t : ZMod A)) hzero
    simp only [Nat.cast_zero] at hr
    rw [show (∑ t ∈ N, errorWeight A X (t : ZMod A)) + errorWeight A X 0 =
      ∑ t ∈ Finset.range A, errorWeight A X (t : ZMod A) from hr]
    exact sum_zmod_range _
  change (∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, errorWeight A X t) ≤ ∑ d ∈ D, _
  rw [hsumRange, ← Finset.sum_fiberwise_of_maps_to hDenMaps]
  apply Finset.sum_le_sum
  intro d hd
  have hdgt := (Finset.mem_filter.mp hd).2
  have hddvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  haveI : NeZero d := ⟨by omega⟩
  have hdodd := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr hA).coprime_dvd_right hddvd)
  let R := N.filter (fun t ↦ den t = d)
  let U := (Finset.range d).filter (fun u ↦ u.Coprime d)
  have hmaps : R.image num ⊆ U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨htN, htd⟩ := Finset.mem_filter.mp ht
    unfold U
    rw [← htd]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt t htN), hcoprime t⟩
  have hinj : Set.InjOn num (R : Set ℕ) := by
    intro x hx y hy heq
    have hx' := (Finset.mem_filter.mp (show x ∈ R from hx)).2
    have hy' := (Finset.mem_filter.mp (show y ∈ R from hy)).2
    have hgxy : g x = g y := by
      apply (Nat.mul_right_inj (show d ≠ 0 by omega)).mp
      simpa only [hx', hy'] using (hDmul x).trans (hDmul y).symm
    rw [← hNmul x, ← hNmul y, heq, hgxy]
  calc
    ∑ t ∈ R, errorWeight A X (t : ZMod A) =
        ∑ t ∈ R, errorWeight d X (num t : ZMod d) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htd := (Finset.mem_filter.mp ht).2
      apply reduced_errorWeight (g := g t)
      · simpa only [htd] using (hDmul t).symm
      · exact (hNmul t).symm
      · exact hg t
    _ = ∑ u ∈ R.image num, errorWeight d X (u : ZMod d) :=
      (Finset.sum_image (f := fun t : ℕ ↦ errorWeight d X (t : ZMod d)) hinj).symm
    _ ≤ ∑ u ∈ U, errorWeight d X (u : ZMod d) :=
      Finset.sum_le_sum_of_subset_of_nonneg hmaps fun u _ _ ↦ errorWeight_nonneg X _
    _ = ∑ u ∈ (Finset.univ : Finset (ZMod d)).filter IsUnit, errorWeight d X u := by
      unfold U
      rw [Finset.sum_filter, Finset.sum_filter, sum_zmod_range]
      simp only [ZMod.isUnit_iff_coprime]
    _ ≤ _ := errorWeight_sum h hdodd

lemma coverage {A V₁ V₂ : ℕ} (hA : 1 < A) (hOdd : Odd A) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hcop : V₁.Coprime V₂)
    (hbound : (∑ d ∈ A.divisors.filter (fun d ↦ 1 < d),
        (d : ℝ)^2 * collision d V₁.divisors * collision d V₂.divisors *
          collision d (V₁ * V₂).divisors) < 1) (c : ℕ) :
    ∃ z₀ ∈ (V₁ * V₂).divisors, ∃ z₁ ∈ (V₁ * V₂).divisors,
      ∃ z₂ ∈ (V₁ * V₂).divisors, ∃ z₃ ∈ (V₁ * V₂).divisors,
        c ≡ z₀ + 2*z₁ + 4*z₂ + 8*z₃ [MOD A] := by
  classical
  haveI : NeZero A := ⟨by omega⟩
  let X := (V₁ * V₂).divisors
  have hX : X.Nonempty := ⟨1, Nat.one_mem_divisors.mpr (by positivity)⟩
  by_contra! hnone
  let term (t : ZMod A) :=
    ZMod.stdAddChar (-(t * (c : ZMod A))) *
      (coeff A X t * coeff A X (2*t) * (coeff A X (4*t) * coeff A X (8*t)))
  let value (a b u v : ℕ) : ZMod A := (v : ZMod A) + 2*(u : ZMod A) +
    4*(b : ZMod A) + 8*(a : ZMod A) - (c : ZMod A)
  have hvalue (a : ℕ) (ha : a ∈ X) (b : ℕ) (hb : b ∈ X)
      (u : ℕ) (hu : u ∈ X) (v : ℕ) (hv : v ∈ X) :
      value a b u v ≠ 0 := by
    intro he
    apply hnone v hv u hu b hb a ha
    have hs := sub_eq_zero.mp he
    exact (ZMod.natCast_eq_natCast_iff ..).mp (by exact_mod_cast hs.symm)
  have hexpand (t : ZMod A) :
      term t = (∑ a ∈ X, ∑ b ∈ X, ∑ u ∈ X, ∑ v ∈ X,
        ZMod.stdAddChar (t * value a b u v)) / (X.card : ℂ)^4 := by
    unfold term coeff
    calc
      _ = (ZMod.stdAddChar (-(t * (c : ZMod A))) *
          ((∑ a ∈ X, ZMod.stdAddChar (t * (a : ZMod A))) *
            (∑ b ∈ X, ZMod.stdAddChar (2*t*(b : ZMod A))) *
            ((∑ u ∈ X, ZMod.stdAddChar (4*t*(u : ZMod A))) *
              (∑ v ∈ X, ZMod.stdAddChar (8*t*(v : ZMod A)))))) /
              (X.card : ℂ)^4 := by ring
      _ = _ := by
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        simp only [← AddChar.map_add_eq_mul, value]
        congr 1
        ring
  have htotal : ∑ t : ZMod A, term t = 0 := by
    simp_rw [hexpand, ← Finset.sum_div]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod A))), wave_sum]
    have hsum : ∑ a ∈ X, ∑ b ∈ X, ∑ u ∈ X, ∑ v ∈ X,
        (if value a b u v = 0 then (A : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b hb
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      exact if_neg (hvalue a ha b hb u hu v hv)
    simp [hsum]
  have hAtZero : term 0 = 1 := by simp [term, coeff_zero hX]
  have hrest : ∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, term t = -1 := by
    have hs := Finset.sum_erase_add (Finset.univ : Finset (ZMod A)) term (Finset.mem_univ 0)
    rw [hAtZero, htotal] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hcover : (1 : ℝ) ≤
      ∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, errorWeight A X t := by
    calc
      (1 : ℝ) = ‖∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, term t‖ := by simp [hrest]
      _ ≤ ∑ t ∈ (Finset.univ : Finset (ZMod A)).erase 0, ‖term t‖ := norm_sum_le ..
      _ = _ := by simp only [term, norm_mul, AddChar.norm_apply, one_mul, errorWeight]
  exact (not_lt_of_ge (hcover.trans (errorWeight_bound hcop hOdd))) hbound

lemma coverage_tuple {A V₁ V₂ : ℕ} (hA : 1 < A) (hOdd : Odd A)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) (hcop : V₁.Coprime V₂)
    (hbound : (∑ d ∈ A.divisors.filter (fun d ↦ 1 < d),
        (d : ℝ)^2 * collision d V₁.divisors * collision d V₂.divisors *
          collision d (V₁ * V₂).divisors) < 1) :
    ∀ m : ℕ, ∃ z : Fin 4 → ℕ, (∀ i, z i ∣ V₁ * V₂) ∧
      m ≡ (∑ i, 2 ^ i.val * z i) [MOD A] := by
  intro m
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hmod⟩ := coverage hA hOdd hV₁ hV₂ hcop hbound m
  refine ⟨![a, b, c, d], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Nat.dvd_of_mem_divisors ha
    · exact Nat.dvd_of_mem_divisors hb
    · exact Nat.dvd_of_mem_divisors hc
    · exact Nat.dvd_of_mem_divisors hd
  · simpa [Fin.sum_univ_four] using hmod

end Erdos18Independent


namespace OMA18Selection

open Finset

noncomputable def mean {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x : X, f x) / Fintype.card X

lemma mean_mono {X : Type*} [Fintype X] {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (sum_le_sum fun x _ ↦ h x) (by positivity)

lemma mean_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    mean (fun x ↦ f x + g x) = mean f + mean g := by
  simp only [mean, sum_add_distrib, add_div]

lemma mean_mul_left {X : Type*} [Fintype X] (a : ℝ) (f : X → ℝ) :
    mean (fun x ↦ a * f x) = a * mean f := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_sum {X I : Type*} [Fintype X] (S : Finset I) (f : I → X → ℝ) :
    mean (fun x ↦ ∑ i ∈ S, f i x) = ∑ i ∈ S, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

lemma mean_const {X : Type*} [Fintype X] [Nonempty X] (a : ℝ) :
    mean (fun _ : X ↦ a) = a := by
  have h : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, nsmul_eq_mul, h]

lemma exists_lt_of_mean_lt {X : Type*} [Fintype X] [Nonempty X] {f : X → ℝ} {c : ℝ}
    (h : mean f < c) : ∃ x, f x < c := by
  by_contra! hn
  have h' := mean_mono hn
  rw [mean_const] at h'
  exact h.not_ge h'

lemma coordinate_filter {X : Type*} [Fintype X] [DecidableEq X] {t : ℕ}
    (J : Finset (Fin t)) (D : Finset X) :
    ((univ : Finset (Fin t → X)).filter fun f ↦ ∀ i ∈ J, f i ∈ D) =
      Fintype.piFinset (fun i : Fin t ↦ if i ∈ J then D else univ) := by
  ext f
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h i
    by_cases hi : i ∈ J
    · simpa [hi] using h i hi
    · simp [hi]
  · intro h i hi
    simpa [hi] using h i

lemma mean_coordinates {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {t : ℕ}
    (J : Finset (Fin t)) (D : Finset X) :
    mean (fun f : Fin t → X ↦ if ∀ i ∈ J, f i ∈ D then (1 : ℝ) else 0) =
      ((D.card : ℝ) / Fintype.card X) ^ J.card := by
  classical
  unfold mean
  rw [Finset.sum_boole, coordinate_filter, Fintype.card_piFinset, Fintype.card_pi_const]
  push_cast
  rw [← show (∏ _i : Fin t, (Fintype.card X : ℝ)) = (Fintype.card X : ℝ)^t by simp,
    ← Finset.prod_div_distrib]
  have h : ∀ i : Fin t,
      (↑((if i ∈ J then D else univ).card) : ℝ) / Fintype.card X =
        if i ∈ J then (D.card : ℝ) / Fintype.card X else 1 := by
    intro i
    by_cases hi : i ∈ J
    · simp [hi]
    · have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [hi, hX]
  simp_rw [h]
  rw [← Finset.prod_filter]
  simp [div_pow]

lemma same_coordinate_mean {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {t : ℕ} {i j : Fin t} (hne : i ≠ j) :
    mean (fun f : Fin t → X ↦ if f i = f j then (1 : ℝ) else 0) =
      (Fintype.card X : ℝ)⁻¹ := by
  classical
  have hFun (f : Fin t → X) :
      (if f i = f j then (1 : ℝ) else 0) =
        ∑ x : X, if ∀ k ∈ ({i, j} : Finset (Fin t)), f k ∈ ({x} : Finset X) then 1 else 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp]
    rw [Finset.sum_eq_single (f i)]
    · by_cases heq : f i = f j <;> simp [heq, eq_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  simp_rw [hFun]
  rw [mean_sum]
  simp only [mean_coordinates, card_singleton, Nat.cast_one]
  have hcard : ({i, j} : Finset (Fin t)).card = 2 := by simp [hne]
  rw [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma duplicate_mean_bound {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (t : ℕ) :
    mean (fun f : Fin t → X ↦ if Function.Injective f then (0 : ℝ) else 1) ≤
      (t : ℝ)^2 / Fintype.card X := by
  classical
  let pairs : Finset (Fin t × Fin t) := univ.filter (fun p ↦ p.1 ≠ p.2)
  calc
    _ ≤ mean (fun f : Fin t → X ↦ ∑ p ∈ pairs, if f p.1 = f p.2 then (1 : ℝ) else 0) := by
      apply mean_mono
      intro f
      by_cases hf : Function.Injective f
      · rw [if_pos hf]
        positivity
      · rw [if_neg hf]
        unfold Function.Injective at hf
        push Not at hf
        obtain ⟨i, j, heq, hne⟩ := hf
        have hp : (i,j) ∈ pairs := by simp [pairs, hne]
        have h := Finset.single_le_sum (s := pairs)
          (f := fun p ↦ if f p.1 = f p.2 then (1 : ℝ) else 0) (fun p _ ↦ by positivity) hp
        simpa only [if_pos heq] using h
    _ = (pairs.card : ℝ) / Fintype.card X := by
      rw [mean_sum]
      have h (p : Fin t × Fin t) (hp : p ∈ pairs) :
          mean (fun f : Fin t → X ↦ if f p.1 = f p.2 then (1 : ℝ) else 0) =
            (Fintype.card X : ℝ)⁻¹ :=
        same_coordinate_mean (by simpa [pairs] using hp)
      rw [sum_congr rfl h, sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := Finset.card_filter_le (s := (univ : Finset (Fin t × Fin t))) (fun p ↦ p.1 ≠ p.2)
      have h' : pairs.card ≤ t ^ 2 := by simpa [pairs, pow_two] using h
      exact_mod_cast h'

noncomputable def collision (d : ℕ) (S : Finset ℕ) : ℝ :=
  (∑ a ∈ S, ∑ b ∈ S, if d ∣ Nat.dist a b then (1 : ℝ) else 0) / (S.card : ℝ)^2

lemma collision_nonneg (d : ℕ) (S : Finset ℕ) : 0 ≤ collision d S := by
  unfold collision
  positivity

lemma diagonal_sum (S : Finset ℕ) :
    (∑ a ∈ S, ∑ b ∈ S, if a = b then (1 : ℝ) else 0) = S.card := by
  calc
    (∑ a ∈ S, ∑ b ∈ S, if a = b then (1 : ℝ) else 0) = ∑ _a ∈ S, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [ha]
    _ = S.card := by simp

lemma collision_mean_bound (P S : Finset ℕ) (hP : P.Nonempty) (hS : S.Nonempty)
    {t : ℕ} (J : Finset (Fin t)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbound : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (((univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).card : ℝ) /
        Fintype.card P ≤ ρ) :
    mean (fun f : Fin t → P ↦ collision (∏ i ∈ J, (f i : ℕ)) S) ≤
      (S.card : ℝ)⁻¹ + ρ ^ J.card := by
  classical
  let : Nonempty P := hP.to_subtype
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hterm (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) :
      mean (fun f : Fin t → P ↦ if (∏ i ∈ J, (f i : ℕ)) ∣ Nat.dist a b
        then (1 : ℝ) else 0) ≤ (if a = b then 1 else 0) + ρ ^ J.card := by
    by_cases heq : a = b
    · subst b
      simp only [Nat.dist_self, dvd_zero, if_true, mean_const]
      exact le_add_of_nonneg_right (pow_nonneg hρ _)
    · rw [if_neg heq, zero_add]
      let D : Finset P := univ.filter fun p ↦ (p : ℕ) ∣ Nat.dist a b
      calc
        _ ≤ mean (fun f : Fin t → P ↦ if ∀ i ∈ J, f i ∈ D then (1 : ℝ) else 0) := by
          apply mean_mono
          intro f
          split
          · rename_i hd
            have hi (i : Fin t) (hiJ : i ∈ J) : f i ∈ D := by
              simp only [D, mem_filter, mem_univ, true_and]
              exact dvd_trans (dvd_prod_of_mem (fun j : Fin t ↦ (f j : ℕ)) hiJ) hd
            rw [if_pos hi]
          · positivity
        _ = ((D.card : ℝ) / Fintype.card P)^J.card := mean_coordinates _ _
        _ ≤ ρ ^ J.card := pow_le_pow_left₀ (by positivity) (hbound a ha b hb heq) _
  simp_rw [collision, div_eq_mul_inv, mul_comm _ (((S.card : ℝ)^2)⁻¹), mean_mul_left, mean_sum]
  calc
    _ ≤ (((S.card : ℝ)^2)⁻¹) *
        ∑ a ∈ S, ∑ b ∈ S, ((if a = b then 1 else 0) + ρ ^ J.card) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun a ha ↦ sum_le_sum fun b hb ↦
        hterm a b ha hb) (by positivity)
    _ = _ := by
      simp_rw [sum_add_distrib]
      rw [diagonal_sum]
      simp only [sum_const, nsmul_eq_mul]
      field_simp

end OMA18Selection

namespace OMA18Selection

open Finset

lemma geometric_small (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (t : ℕ) :
    ∑ i ∈ range t, r ^ (i+1) ≤ r / (1-r) := by
  induction t with
  | zero => simp; positivity
  | succ t ih =>
    have hp : 0 ≤ r ^ (t+1) := pow_nonneg hr _
    have hgeom := geom_sum_mul r (t+1)
    have hs : (∑ i ∈ range (t+1), r^i) = (∑ i ∈ range t, r^(i+1)) + 1 := by
      rw [sum_range_succ']
      simp
    rw [hs] at hgeom
    rw [sum_range_succ]
    apply (le_div_iff₀ (by linarith : 0 < 1 - r)).mpr
    nlinarith

lemma sum_nonempty_powerset_pow_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (r : ℝ) (hr : 0 ≤ r) (hr' : (I.card : ℝ)*r < 1) :
    ∑ J ∈ I.powerset.erase ∅, r^J.card ≤ (I.card : ℝ)*r / (1-(I.card : ℝ)*r) := by
  have hEmpty : (∅ : Finset ι) ∈ I.powerset := empty_mem_powerset _
  have hErase := sum_erase_add I.powerset (fun J : Finset ι ↦ r^J.card) hEmpty
  rw [sum_powerset_apply_card] at hErase
  rw [sum_range_succ'] at hErase
  simp only [card_empty, pow_zero, Nat.choose_zero_right, one_smul] at hErase
  have hEq : ∑ J ∈ I.powerset.erase ∅, r^J.card =
      ∑ i ∈ range I.card, I.card.choose (i+1) • r^(i+1) := by linarith
  rw [hEq]
  calc
    _ ≤ ∑ i ∈ range I.card, ((I.card : ℝ)*r)^(i+1) := by
      apply sum_le_sum
      intro i _
      rw [nsmul_eq_mul, mul_pow]
      have hc : (I.card.choose (i+1) : ℝ) ≤ (I.card : ℝ)^(i+1) := by
        exact_mod_cast Nat.choose_le_pow _ _
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg hr _)
    _ ≤ _ := geometric_small _ (by positivity) hr' _

lemma pick_small_error (P S₁ S₂ S₃ : Finset ℕ) (hP : P.Nonempty)
    (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty) (hS₃ : S₃.Nonempty)
    (t : ℕ) (w ρ : ℝ) (hw : 0 ≤ w) (hρ : 0 ≤ ρ)
    (hOff : ∀ S ∈ ({S₁,S₂,S₃} : Finset (Finset ℕ)), ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (((univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).card : ℝ) /
        Fintype.card P ≤ ρ)
    (hDiag : ∀ s : ℕ, 1 ≤ s → s ≤ t →
      (S₁.card : ℝ)⁻¹ ≤ ρ^s ∧ (S₂.card : ℝ)⁻¹ ≤ ρ^s ∧ (S₃.card : ℝ)⁻¹ ≤ ρ^s)
    (hScale : (t : ℝ)*(w*ρ) ≤ 1/100)
    (hDup : (t : ℝ)^2 / Fintype.card P ≤ 1/10) :
    ∃ f : Fin t → P, Function.Injective f ∧
      ∑ J ∈ (univ : Finset (Fin t)).powerset.erase ∅,
        w^J.card * (collision (∏ i ∈ J, (f i : ℕ)) S₁ +
          collision (∏ i ∈ J, (f i : ℕ)) S₂ +
          collision (∏ i ∈ J, (f i : ℕ)) S₃) < 1 := by
  classical
  let : Nonempty P := hP.to_subtype
  let U : Finset (Fin t) := univ
  let pen (f : Fin t → P) : ℝ :=
    ∑ J ∈ U.powerset.erase ∅,
      w^J.card * (collision (∏ i ∈ J, (f i : ℕ)) S₁ +
        collision (∏ i ∈ J, (f i : ℕ)) S₂ +
        collision (∏ i ∈ J, (f i : ℕ)) S₃)
  have hp_nonneg (f : Fin t → P) : 0 ≤ pen f := by
    unfold pen
    apply sum_nonneg
    intro J _
    positivity [collision_nonneg (∏ i ∈ J, (f i : ℕ)) S₁,
      collision_nonneg (∏ i ∈ J, (f i : ℕ)) S₂,
      collision_nonneg (∏ i ∈ J, (f i : ℕ)) S₃]
  have hpMean : mean pen ≤ 6 * (t*(w*ρ) / (1-t*(w*ρ))) := by
    unfold pen
    rw [mean_sum]
    calc
      _ ≤ ∑ J ∈ U.powerset.erase ∅, 6 * (w*ρ)^J.card := by
        apply sum_le_sum
        intro J hJ
        have hJne : J.Nonempty := nonempty_iff_ne_empty.mpr (mem_erase.mp hJ).1
        have hJle : J.card ≤ t := by
          simpa [U] using card_le_card (mem_powerset.mp (mem_erase.mp hJ).2)
        have hd := hDiag J.card hJne.card_pos hJle
        simp only [mean_mul_left, mean_add]
        have h₁ := collision_mean_bound P S₁ hP hS₁ J hρ (hOff S₁ (by simp))
        have h₂ := collision_mean_bound P S₂ hP hS₂ J hρ (hOff S₂ (by simp))
        have h₃ := collision_mean_bound P S₃ hP hS₃ J hρ (hOff S₃ (by simp))
        rw [mul_pow, mul_comm 6, mul_assoc]
        rw [mul_comm (ρ ^ J.card) 6]
        exact mul_le_mul_of_nonneg_left (by linarith [hd.1, hd.2.1, hd.2.2]) (by positivity)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hb := sum_nonempty_powerset_pow_le U (w*ρ) (mul_nonneg hw hρ)
          (by simpa [U] using (show (t : ℝ)*(w*ρ) < 1 by linarith))
        simpa [U] using hb
  let loss (f : Fin t → P) : ℝ := (if Function.Injective f then 0 else 1) + pen f
  have hLoss : mean loss < 1 := by
    unfold loss
    rw [mean_add]
    have hb := duplicate_mean_bound (X := P) t
    have hfrac : ((t : ℝ)*(w*ρ)) / (1-t*(w*ρ)) ≤ 1/99 := by
      apply (div_le_iff₀ (by linarith : 0 < 1-t*(w*ρ))).mpr
      linarith
    linarith
  obtain ⟨f, hf⟩ := exists_lt_of_mean_lt hLoss
  refine ⟨f, ?_⟩
  by_cases hinj : Function.Injective f
  · refine ⟨hinj, ?_⟩
    simpa [loss, hinj, pen, U] using hf
  · have h := hp_nonneg f
    simp [loss, hinj] at hf
    linarith

end OMA18Selection

namespace OMA18Selection

open Finset

lemma prime_product_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).2 hne)
  · intro p hp
    exact (hS p hp).squarefree

lemma prime_product_divisors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).divisors = S.powerset.image (fun T : Finset ℕ ↦ ∏ p ∈ T, p) := by
  have hprod : (∏ p ∈ S, p) ≠ 0 := (prime_product_squarefree S hS).ne_zero
  ext d
  constructor
  · intro hd
    have hd' := (Nat.mem_divisors.mp hd).1
    have hsub := Nat.primeFactors_mono hd' hprod
    rw [Nat.primeFactors_prod hS] at hsub
    exact mem_image.mpr ⟨d.primeFactors, mem_powerset.mpr hsub,
      Nat.prod_primeFactors_of_squarefree ((prime_product_squarefree S hS).squarefree_of_dvd hd')⟩
  · rintro hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset T S id (mem_powerset.mp hT), hprod⟩

lemma prime_product_divisors_card (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).divisors.card = 2 ^ S.card := by
  rw [prime_product_divisors S hS, Finset.card_image_of_injOn, Finset.card_powerset]
  intro T hT U hU he
  have hTsub := mem_powerset.mp hT
  have hUsub := mem_powerset.mp hU
  have he' := congrArg Nat.primeFactors he
  rw [Nat.primeFactors_prod (fun p hp ↦ hS p (hTsub hp)),
    Nat.primeFactors_prod (fun p hp ↦ hS p (hUsub hp))] at he'
  exact he'

lemma prime_product_coprime {S T : Finset ℕ} (hST : Disjoint S T)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ S, p).Coprime (∏ p ∈ T, p) := by
  exact Nat.coprime_of_squarefree_mul (by
    rw [← Finset.prod_union hST]
    exact prime_product_squarefree (S ∪ T) fun p hp ↦
      (mem_union.mp hp).elim (hS p) (hT p))

lemma sum_cube_bound {X : Type*} [DecidableEq X] (S : Finset X) (f : X → ℝ)
    (hn : ∀ x ∈ S, 0 ≤ f x) : ∑ x ∈ S, (f x)^3 ≤ (∑ x ∈ S, f x)^3 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ha' : 0 ≤ f a := hn a (mem_insert_self _ _)
    have hS : ∀ x ∈ S, 0 ≤ f x := fun x hx ↦ hn x (mem_insert_of_mem hx)
    have hs' : 0 ≤ ∑ x ∈ S, f x := sum_nonneg hS
    rw [sum_insert ha, sum_insert ha]
    have hc : (f a)^3 + (∑ x ∈ S, f x)^3 ≤ (f a + ∑ x ∈ S, f x)^3 := by
      calc
        _ ≤ (f a)^3 + (∑ x ∈ S, f x)^3 + 3 * (f a)^2 * (∑ x ∈ S, f x) +
              3 * (f a) * (∑ x ∈ S, f x)^2 := by
          exact le_add_of_nonneg_right (by positivity) |>.trans (le_add_of_nonneg_right (by positivity))
        _ = _ := by ring
    exact (add_le_add le_rfl (ih hS)).trans hc

lemma three_collision_error {X : Type*} [DecidableEq X] (J : Finset X)
    (d : X → ℕ) (w : X → ℝ) (S₁ S₂ S₃ : Finset ℕ)
    (hn : ∀ j ∈ J, 0 ≤ w j)
    (hd : ∀ j ∈ J, (d j : ℝ)^2 ≤ (w j)^3)
    (hs : ∑ j ∈ J, w j * (collision (d j) S₁ + collision (d j) S₂ + collision (d j) S₃) < 1) :
    ∑ j ∈ J, (d j : ℝ)^2 * collision (d j) S₁ * collision (d j) S₂ *
      collision (d j) S₃ < 1 := by
  let f (j : X) := w j * (collision (d j) S₁ + collision (d j) S₂ + collision (d j) S₃)
  have hf (j : X) (hj : j ∈ J) : 0 ≤ f j := by
    unfold f
    exact mul_nonneg (hn j hj) (add_nonneg
      (add_nonneg (collision_nonneg _ _) (collision_nonneg _ _)) (collision_nonneg _ _))
  calc
    _ ≤ ∑ j ∈ J, (f j)^3 := by
      apply sum_le_sum
      intro j hj
      have hc₁ := collision_nonneg (d j) S₁
      have hc₂ := collision_nonneg (d j) S₂
      have hc₃ := collision_nonneg (d j) S₃
      unfold f
      rw [mul_pow]
      have hp : 0 ≤ (w j)^3 := pow_nonneg (hn j hj) _
      have hs₁ : collision (d j) S₁ ≤ collision (d j) S₁ + collision (d j) S₂ +
        collision (d j) S₃ := by linarith
      have hs₂ : collision (d j) S₂ ≤ collision (d j) S₁ + collision (d j) S₂ +
        collision (d j) S₃ := by linarith
      have hs₃ : collision (d j) S₃ ≤ collision (d j) S₁ + collision (d j) S₂ +
        collision (d j) S₃ := by linarith
      have hb : 0 ≤ collision (d j) S₁ + collision (d j) S₂ + collision (d j) S₃ := by
        linarith
      calc
        _ ≤ (w j)^3 * collision (d j) S₁ * collision (d j) S₂ * collision (d j) S₃ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hd j hj) hc₁) hc₂) hc₃
        _ ≤ _ := by
          have hl :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul hs₁ hs₂ hc₂ hb) hs₃ hc₃ (mul_nonneg hb hb)) hp
          convert hl using 1 <;> (first | rfl | ring)
    _ ≤ (∑ j ∈ J, f j)^3 := sum_cube_bound J f hf
    _ < 1 := by
      simpa only [one_pow] using
        (pow_lt_pow_left₀ (show (∑ j ∈ J, f j) < 1 from hs) (sum_nonneg hf) (by decide : 3 ≠ 0))

end OMA18Selection

namespace OMA18Selection

open Finset

lemma list_subproducts {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι ↪ ℕ)
    (hf : ∀ i, (f i).Prime) :
    ((univ.map f).prod id).divisors.erase 1 =
      ((univ : Finset ι).powerset.erase ∅).image (fun J : Finset ι ↦ ∏ i ∈ J, f i) := by
  classical
  let T : Finset ℕ := univ.map f
  have hT : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_map.mp hp
    exact hf i
  change (∏ p ∈ T, p).divisors.erase 1 = _
  rw [prime_product_divisors T hT]
  have hInj : Set.InjOn (fun U : Finset ℕ ↦ ∏ p ∈ U, p) T.powerset := by
    intro U hU W hW h
    have h' := congrArg Nat.primeFactors h
    rw [Nat.primeFactors_prod (fun p hp ↦ hT p (mem_powerset.mp hU hp)),
      Nat.primeFactors_prod (fun p hp ↦ hT p (mem_powerset.mp hW hp))] at h'
    exact h'
  have image_eq :
      T.powerset.image (fun U : Finset ℕ ↦ ∏ p ∈ U, p) =
        (univ : Finset ι).powerset.image (fun J : Finset ι ↦ ∏ i ∈ J, f i) := by
    ext n
    constructor
    · rintro hn
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hn
      let J : Finset ι := univ.filter fun i ↦ f i ∈ U
      have hJ : J.map f = U := by
        ext p
        constructor
        · rintro hp
          obtain ⟨i, hi, rfl⟩ := mem_map.mp hp
          exact (mem_filter.mp hi).2
        · intro hp
          have hpT := mem_powerset.mp hU hp
          obtain ⟨i, hi, rfl⟩ := mem_map.mp hpT
          exact mem_map.mpr ⟨i, mem_filter.mpr ⟨hi, hp⟩, rfl⟩
      exact mem_image.mpr ⟨J, mem_powerset.mpr (subset_univ _), by rw [← hJ, prod_map]⟩
    · rintro hn
      obtain ⟨J, hJ, rfl⟩ := mem_image.mp hn
      exact mem_image.mpr ⟨J.map f, mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp hJ)),
        by rw [prod_map]⟩
  rw [image_eq]
  ext n
  constructor
  · intro hn
    obtain ⟨hne, hmem⟩ := mem_erase.mp hn
    obtain ⟨J, hJ, rfl⟩ := mem_image.mp hmem
    refine mem_image.mpr ⟨J, mem_erase.mpr ⟨?_, hJ⟩, rfl⟩
    intro h
    subst J
    exact hne (by simp)
  · intro hn
    obtain ⟨J, hJ, rfl⟩ := mem_image.mp hn
    obtain ⟨hne, hJ⟩ := mem_erase.mp hJ
    refine mem_erase.mpr ⟨?_, mem_image.mpr ⟨J, hJ, rfl⟩⟩
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hne
    intro he
    exact (hf i).not_dvd_one (he ▸ dvd_prod_of_mem f hi)

lemma sum_subproducts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι ↪ ℕ) (hf : ∀ i, (f i).Prime) (g : ℕ → ℝ) :
    ∑ d ∈ ((univ.map f).prod id).divisors.erase 1, g d =
      ∑ J ∈ (univ : Finset ι).powerset.erase ∅, g (∏ i ∈ J, f i) := by
  rw [list_subproducts f hf]
  apply sum_image
  intro J _ K _ he
  have hp := congrArg Nat.primeFactors he
  have hJ : Nat.primeFactors (∏ i ∈ J, f i) = J.map f := by
    rw [← show (∏ i ∈ J.map f, i) = ∏ i ∈ J, f i by rw [prod_map]]
    exact Nat.primeFactors_prod fun p hp ↦ by
      obtain ⟨i, _, rfl⟩ := mem_map.mp hp
      exact hf i
  have hK : Nat.primeFactors (∏ i ∈ K, f i) = K.map f := by
    rw [← show (∏ i ∈ K.map f, i) = ∏ i ∈ K, f i by rw [prod_map]]
    exact Nat.primeFactors_prod fun p hp ↦ by
      obtain ⟨i, _, rfl⟩ := mem_map.mp hp
      exact hf i
  rw [hJ, hK] at hp
  exact map_injective f hp

end OMA18Selection

namespace OMA18Finish

open Finset Filter
open OMA18Selection Erdos18PrimeBounds

lemma select_at (S : Finset ℕ) (hS : Erdos18Iteration.GoodPrimes S)
    (hk : 2 ≤ S.card)
    (hPrimes : 2 * S.card^11 ≤ (eligiblePrimes S.card S).card)
    (ht : 0 < Erdos18Iteration.increment S.card)
    (hScale : (Erdos18Iteration.increment S.card : ℝ) *
      ((S.card : ℝ)^9 * (1/(S.card : ℝ)^10)) ≤ 1/100)
    (hDup : (Erdos18Iteration.increment S.card : ℝ)^2 / ((2*S.card^11 : ℕ) : ℝ) ≤ 1/10)
    (hDiag : ∀ s : ℕ, 1 ≤ s → s ≤ Erdos18Iteration.increment S.card →
      ((2 : ℝ)^(S.card/2))⁻¹ ≤ (1/(S.card : ℝ)^10)^s)
    (hSize : (4*(S.card : ℝ)^12)^2 ≤ ((S.card : ℝ)^9)^3) :
    ∃ T : Finset ℕ, Disjoint S T ∧ T.card = Erdos18Iteration.increment S.card ∧
      (∀ p ∈ T, p.Prime ∧ Odd p ∧ S.card ^ 12 < p ∧ p ≤ 4 * S.card ^ 12) ∧
      Erdos18Iteration.ResidueCover (S.prod id) (T.prod id) := by
  classical
  let k := S.card
  let t := Erdos18Iteration.increment k
  let P := eligiblePrimes k S
  let w : ℝ := (k : ℝ)^9
  let ρ : ℝ := 1/(k : ℝ)^10
  have hPcard : 2*k^11 ≤ P.card := hPrimes
  have hPk : 0 < P.card := by
    have : 0 < k := by omega
    exact lt_of_lt_of_le (by positivity : 0 < 2*k^11) hPcard
  have hP : P.Nonempty := card_pos.mp hPk
  have hPmem (p : ℕ) (hp : p ∈ P) :
      p.Prime ∧ k^12 < p ∧ p ≤ 4*k^12 ∧ p ∉ S := mem_eligiblePrimes.mp hp
  obtain ⟨S₁, hSub, hS₁⟩ := exists_subset_card_eq (s := S) (n := k/2) (by dsimp [k]; omega)
  let S₂ := S \ S₁
  have hSub₂ : S₂ ⊆ S := sdiff_subset
  have hDis : Disjoint S₁ S₂ := disjoint_sdiff
  have hUnion : S₁ ∪ S₂ = S := union_sdiff_of_subset hSub
  have hS₂ : k/2 ≤ S₂.card := by
    change k / 2 ≤ (S \ S₁).card
    rw [card_sdiff_of_subset hSub, hS₁]
    dsimp [k]
    omega
  let V₁ := S₁.prod id
  let V₂ := S₂.prod id
  let V := S.prod id
  have hVmul : V₁ * V₂ = V := by
    change S₁.prod id * S₂.prod id = S.prod id
    rw [← prod_union hDis, hUnion]
  have hPrime : ∀ p ∈ S, p.Prime := fun p hp ↦ (hS p hp).1
  have hPrime₁ : ∀ p ∈ S₁, p.Prime := fun p hp ↦ hPrime p (hSub hp)
  have hPrime₂ : ∀ p ∈ S₂, p.Prime := fun p hp ↦ hPrime p (hSub₂ hp)
  have hVpos : 0 < V := Erdos18Iteration.prod_pos_of_prime hPrime
  have hV₁pos : 0 < V₁ := Erdos18Iteration.prod_pos_of_prime hPrime₁
  have hV₂pos : 0 < V₂ := Erdos18Iteration.prod_pos_of_prime hPrime₂
  have hVcop : V₁.Coprime V₂ := prime_product_coprime hDis hPrime₁ hPrime₂
  have hV₁dvd : V₁ ∣ V := hVmul ▸ dvd_mul_right V₁ V₂
  have hV₂dvd : V₂ ∣ V := hVmul ▸ dvd_mul_left V₂ V₁
  have hVupper : V ≤ (4*k^12)^k := by
    calc
      V ≤ ∏ _p ∈ S, 4*k^12 :=
        Finset.prod_le_prod' fun p hp ↦ (hS p hp).2.2
      _ = _ := by simp [k]
  have hDiv (D : Finset ℕ) (hD : D ∈ ({V₁.divisors,V₂.divisors,V.divisors} : Finset (Finset ℕ)))
      (a : ℕ) (ha : a ∈ D) : a ∣ V := by
    simp only [mem_insert, mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact (Nat.dvd_of_mem_divisors ha).trans hV₁dvd
    · exact (Nat.dvd_of_mem_divisors ha).trans hV₂dvd
    · exact Nat.dvd_of_mem_divisors ha
  have hCard₁ : V₁.divisors.card = 2^(k/2) := by
    change (∏ p ∈ S₁, p).divisors.card = _
    rw [prime_product_divisors_card S₁ hPrime₁, hS₁]
  have hCard₂ : 2^(k/2) ≤ V₂.divisors.card := by
    change _ ≤ (∏ p ∈ S₂, p).divisors.card
    rw [prime_product_divisors_card S₂ hPrime₂]
    exact Nat.pow_le_pow_right (by decide) hS₂
  have hCard₃ : 2^(k/2) ≤ V.divisors.card := by
    change _ ≤ (∏ p ∈ S, p).divisors.card
    rw [prime_product_divisors_card S hPrime]
    exact Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hInverses (s : ℕ) (hs : 1 ≤ s) (hst : s ≤ t) :
      (V₁.divisors.card : ℝ)⁻¹ ≤ ρ^s ∧
      (V₂.divisors.card : ℝ)⁻¹ ≤ ρ^s ∧ (V.divisors.card : ℝ)⁻¹ ≤ ρ^s := by
    have hinv (D : Finset ℕ) (hD : 2^(k/2) ≤ D.card) :
        (D.card : ℝ)⁻¹ ≤ ((2 : ℝ)^(k/2))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact_mod_cast hD
    exact ⟨(hinv _ hCard₁.ge).trans (hDiag s hs hst),
      (hinv _ hCard₂).trans (hDiag s hs hst), (hinv _ hCard₃).trans (hDiag s hs hst)⟩
  have hOff (D : Finset ℕ) (hD : D ∈ ({V₁.divisors,V₂.divisors,V.divisors} : Finset (Finset ℕ)))
      (a : ℕ) (ha : a ∈ D) (b : ℕ) (hb : b ∈ D) (hne : a ≠ b) :
      (((univ : Finset P).filter fun p : P ↦ (p : ℕ) ∣ Nat.dist a b).card : ℝ) /
        Fintype.card P ≤ ρ :=
    collision_bound hk (fun p hp ↦ ⟨(hPmem p hp).1, (hPmem p hp).2.1⟩) hPcard hne
      ((Nat.le_of_dvd hVpos (hDiv D hD a ha)).trans hVupper)
      ((Nat.le_of_dvd hVpos (hDiv D hD b hb)).trans hVupper)
  have hDups : (t : ℝ)^2 / Fintype.card P ≤ 1/10 := by
    have hPos : 0 < ((2*k^11 : ℕ) : ℝ) := by
      have : 0 < k := by omega
      positivity
    have hle : ((2*k^11 : ℕ) : ℝ) ≤ Fintype.card P := by
      exact_mod_cast (show 2*k^11 ≤ Fintype.card P by simpa using hPcard)
    exact (div_le_div_of_nonneg_left (by positivity) hPos hle).trans hDup
  obtain ⟨f, hf, hError⟩ := pick_small_error P V₁.divisors V₂.divisors V.divisors hP
    ⟨1, Nat.one_mem_divisors.mpr hV₁pos.ne'⟩
    ⟨1, Nat.one_mem_divisors.mpr hV₂pos.ne'⟩
    ⟨1, Nat.one_mem_divisors.mpr hVpos.ne'⟩ t w ρ
    (by dsimp [w]; positivity) (by dsimp [ρ]; positivity) hOff hInverses hScale hDups
  let e : Fin t ↪ ℕ := ⟨fun i ↦ (f i : ℕ), Subtype.val_injective.comp hf⟩
  let T : Finset ℕ := univ.map e
  let A := T.prod id
  have hTsubset : T ⊆ P := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_map.mp hp
    exact (f i).property
  have hTprime (p : ℕ) (hp : p ∈ T) : p.Prime := (hPmem p (hTsubset hp)).1
  have hTcard : T.card = t := by simp [T]
  have hTodd (p : ℕ) (hp : p ∈ T) : Odd p := by
    have hkpow : 2 ≤ k^12 :=
      hk.trans (Nat.le_self_pow (by decide) k)
    exact (hTprime p hp).odd_of_ne_two (by have := (hPmem p (hTsubset hp)).2.1; omega)
  have hApos : 0 < A := Erdos18Iteration.prod_pos_of_prime hTprime
  have hA : 1 < A := by
    have hTpos : 0 < T.card := by rw [hTcard]; exact ht
    obtain ⟨p, hp⟩ := card_pos.mp hTpos
    exact (hTprime p hp).one_lt.trans_le
      (Nat.le_of_dvd hApos (dvd_prod_of_mem id hp))
  have hAodd : Odd A := by
    rcases Nat.even_or_odd A with he | ho
    · exact (Erdos18Iteration.not_two_dvd_prod hTodd (even_iff_two_dvd.mp he)).elim
    · exact ho
  have hTdis : Disjoint S T := by
    rw [Finset.disjoint_left]
    exact fun p hp hpT ↦ (hPmem p (hTsubset hpT)).2.2.2 hp
  refine ⟨T, hTdis, hTcard, fun p hp ↦
    ⟨hTprime p hp, hTodd p hp, (hPmem p (hTsubset hp)).2.1,
      (hPmem p (hTsubset hp)).2.2.1⟩, ?_⟩
  have hDivFilter : A.divisors.filter (fun d ↦ 1 < d) = A.divisors.erase 1 := by
    ext d
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun ⟨hd, hd'⟩ ↦ ⟨by omega, hd⟩
    · intro ⟨hd1, hd⟩
      have hp := Nat.pos_of_mem_divisors hd
      exact ⟨hd, by omega⟩
  let divOf (J : Finset (Fin t)) : ℕ := ∏ i ∈ J, e i
  let wt (J : Finset (Fin t)) : ℝ := w^J.card
  have hProd (J : Finset (Fin t)) : (divOf J : ℝ) ≤ (4*(k : ℝ)^12)^J.card := by
    unfold divOf
    push_cast
    calc
      _ ≤ ∏ _i ∈ J, 4*(k : ℝ)^12 := by
        apply Finset.prod_le_prod
        · intros
          positivity
        · intro i _
          exact_mod_cast (hPmem (f i) (f i).property).2.2.1
      _ = _ := by simp
  have hCube (J : Finset (Fin t)) : (divOf J : ℝ)^2 ≤ (wt J)^3 := by
    calc
      _ ≤ ((4*(k : ℝ)^12)^J.card)^2 := pow_le_pow_left₀ (by positivity) (hProd J) _
      _ = ((4*(k : ℝ)^12)^2)^J.card := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (w^3)^J.card := pow_le_pow_left₀ (by positivity) hSize _
      _ = _ := pow_right_comm w 3 J.card
  have hError' :=
    three_collision_error ((univ : Finset (Fin t)).powerset.erase ∅)
      divOf wt V₁.divisors V₂.divisors V.divisors
      (fun J _ ↦ pow_nonneg (by dsimp [w]; positivity) _) (fun J _ ↦ hCube J) hError
  have hFourier : (∑ d ∈ A.divisors.filter (fun d ↦ 1 < d),
      (d : ℝ)^2 * Erdos18Independent.collision d V₁.divisors *
        Erdos18Independent.collision d V₂.divisors *
        Erdos18Independent.collision d (V₁*V₂).divisors) < 1 := by
    rw [hDivFilter, hVmul]
    change (∑ d ∈ ((univ.map e).prod id).divisors.erase 1,
      (d : ℝ)^2 * collision d V₁.divisors * collision d V₂.divisors * collision d V.divisors) < 1
    rw [sum_subproducts e (fun i ↦ (hPmem (f i) (f i).property).1)]
    exact hError'
  have hCover : Erdos18Iteration.ResidueCover (V₁*V₂) A :=
    Erdos18Independent.coverage_tuple hA hAodd hV₁pos hV₂pos hVcop hFourier
  rwa [hVmul] at hCover

theorem selection : Erdos18Iteration.Selection := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (Erdos18Numeric.eventually_numeric.and eventually_eligible_card)
  refine ⟨K, fun S hKS hGood ↦ ?_⟩
  obtain ⟨⟨hk, hInc, hSmall, hDup, hDiag, hSize⟩, hP⟩ := hK S.card hKS
  exact select_at S hGood hk (hP S le_rfl) hInc hSmall hDup (fun s _ hs ↦ hDiag s hs) hSize

end OMA18Finish

theorem OMA.solution : type_of% @Erdos18.erdos_18a :=
  Erdos18Iteration.conclusion OMA18Finish.selection
