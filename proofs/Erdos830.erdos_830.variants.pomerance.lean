import FormalConjectures.ErdosProblems.«830»
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Pomerance's upper bound for amicable numbers, from On Amicable Numbers (2015), Theorem 1.1.

The proof uses Pomerance's decomposition into exceptional sets and arithmetic progressions.
The smooth shifted-prime estimate here uses a split of the finite Euler product and a
factorial/Chebyshev bound on the sum of log p / p.
-/

open scoped ArithmeticFunction.sigma BigOperators Topology
open Finset Filter Real
open ArithmeticFunction hiding log

namespace AmicableCount

private theorem sigma_ge_self {m : ℕ} (hm : 0 < m) : m ≤ σ 1 m := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self m hm.ne')

private theorem sigma_prime_mul {p m : ℕ} (hp : p.Prime) (hc : ¬ p ∣ m) :
    σ 1 (p * m) = (p + 1) * σ 1 m := by
  rw [isMultiplicative_sigma.map_mul_of_coprime ((hp.coprime_iff_not_dvd).mpr hc)]
  have h : σ 1 (p ^ 1) = p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [sum_range_succ, add_comm]
  simpa using congrArg (fun s => s * σ 1 m) (by simpa using h : σ 1 p = p + 1)

private theorem amicable_symm {n n' : ℕ} (h : IsAmicable n n') : IsAmicable n' n :=
  ⟨by simpa [Nat.add_comm] using h.right, by simpa [Nat.add_comm] using h.left, h.ne.symm⟩

private theorem mate_unique {n n' m' : ℕ} (h : IsAmicable n n') (g : IsAmicable n m') :
    n' = m' := by
  have he := h.left.symm.trans g.left
  omega

private theorem amicable_factor_left {p m n' : ℕ} (hp : p.Prime) (hc : ¬ p ∣ m)
    (h : IsAmicable (p * m) n') :
    (n' : ℤ) = p * ((σ 1 m : ℤ) - m) + (σ 1 m : ℤ) := by
  have hl := h.left
  rw [sigma_prime_mul hp hc] at hl
  exact_mod_cast (show (n' : ℤ) = (p : ℤ) * ((σ 1 m : ℤ) - (m : ℤ)) + (σ 1 m : ℤ) by
    zify at hl
    linear_combination -hl)

private theorem amicable_eliminate_left {p p' m m' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hc : ¬ p ∣ m) (hc' : ¬ p' ∣ m')
    (h : IsAmicable (p * m) (p' * m')) :
    (p' : ℤ) * ((m' : ℤ) * (σ 1 m : ℤ) - (σ 1 m' : ℤ) * ((σ 1 m : ℤ) - m)) =
      (σ 1 m' : ℤ) * ((σ 1 m : ℤ) - m) + (m : ℤ) * (σ 1 m : ℤ) := by
  have h₁ := amicable_factor_left hp hc h
  push_cast at h₁
  have h₂ := h.left.trans h.right.symm
  rw [sigma_prime_mul hp hc, sigma_prime_mul hp' hc'] at h₂
  zify at h₂
  linear_combination (σ 1 m : ℤ) * h₁ + ((σ 1 m : ℤ) - (m : ℤ)) * h₂

private theorem amicable_factor_right_unique {p p' q q' m m' : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hq : q.Prime) (hq' : q'.Prime)
    (hcp : ¬ p ∣ m) (hcp' : ¬ p' ∣ m') (hcq : ¬ q ∣ m) (hcq' : ¬ q' ∣ m')
    (h : IsAmicable (p * m) (p' * m')) (g : IsAmicable (q * m) (q' * m')) : p' = q' := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun he => hcp (he ▸ dvd_zero p)
  have hpσ : (0 : ℤ) < (σ 1 m : ℤ) := by exact_mod_cast (sigma_pos 1 m hm.ne')
  have hσ : (m : ℤ) ≤ (σ 1 m : ℤ) := by exact_mod_cast (sigma_ge_self hm)
  have hpos : 0 < (σ 1 m' : ℤ) * ((σ 1 m : ℤ) - m) + (m : ℤ) * (σ 1 m : ℤ) := by
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (sub_nonneg.mpr hσ))
      (mul_pos (by exact_mod_cast hm) hpσ)
  have h₁ := amicable_eliminate_left hp hp' hcp hcp' h
  have h₂ := amicable_eliminate_left hq hq' hcq hcq' g
  have key : (m' : ℤ) * (σ 1 m : ℤ) - (σ 1 m' : ℤ) * ((σ 1 m : ℤ) - m) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h₁
    exact hpos.ne' h₁.symm
  exact_mod_cast (mul_right_cancel₀ key (h₁.trans h₂.symm))

private theorem amicable_divisor_congruence {p m n' d M : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) (hn : IsAmicable (p * m) n')
    (hd : d.Coprime M) (he : n' = d * M) :
    σ 1 m * d * M ≡ m * σ 1 m [MOD σ 1 d] := by
  have hfact := amicable_factor_left hp hpm hn
  have hsig := hn.left.trans hn.right.symm
  rw [sigma_prime_mul hp hpm, he, isMultiplicative_sigma.map_mul_of_coprime hd] at hsig
  have hmod := show ((σ 1 d : ℤ) ∣ (σ 1 m : ℤ) * (m : ℤ) - (σ 1 m : ℤ) * (d : ℤ) * (M : ℤ)) by
    refine ⟨-((σ 1 m : ℤ) - m) * (σ 1 M : ℤ), ?_⟩
    rw [he] at hfact
    push_cast at hfact
    zify at hsig
    linear_combination -(σ 1 m : ℤ) * hfact - ((σ 1 m : ℤ) - m) * hsig
  rw [Nat.modEq_iff_dvd]
  push_cast
  simpa [mul_comm (σ 1 m : ℤ) (m : ℤ)] using hmod

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

private theorem sigma_ratio_bound {n : ℕ} (hn : 0 < n) :
    (σ 1 n : ℝ) ≤ (n : ℝ) * (1 + log n) := by
  rw [sigma_eq_sum_div]
  simp only [pow_one, Nat.cast_sum]
  calc
    ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ≤ ∑ d ∈ n.divisors, (n : ℝ) * (d : ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      rw [← div_eq_mul_inv, le_div_iff₀ (by exact_mod_cast hd0)]
      exact_mod_cast Nat.div_mul_le_self n d
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply harmonic_bound_finset
      intro d hd
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩

private theorem squarefull_representation {n : ℕ} (hn : n ≠ 0)
    (hs : ∀ p ∈ n.primeFactors, n.factorization p ≠ 1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 * b ^ 3 := by
  let a := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2 - n.factorization p % 2)
  let b := ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)
  have hpp : ∀ p ∈ n.primeFactors, 0 < p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  refine ⟨a, b, Finset.prod_pos (fun p hp => pow_pos (hpp p hp) _),
    Finset.prod_pos (fun p hp => pow_pos (hpp p hp) _), ?_⟩
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = a ^ 2 * b ^ 3 := by
      simp only [a, b, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
      apply Finset.prod_congr rfl
      intro p hp
      congr 1
      have hp1 := hs p hp
      omega

private theorem exists_divisor_in_window {n : ℕ} {Y B : ℝ} (hY : 1 ≤ Y) (hn : Y < n)
    (hP : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ B) :
    ∃ d : ℕ, d ∣ n ∧ Y < (d : ℝ) ∧ (d : ℝ) ≤ Y * B := by
  classical
  have hex : ∃ d : ℕ, d ∣ n ∧ Y < (d : ℝ) := ⟨n, dvd_rfl, hn⟩
  let d := Nat.find hex
  have hd : d ∣ n ∧ Y < (d : ℝ) := Nat.find_spec hex
  have hd1 : 1 < d := by exact_mod_cast (hY.trans_lt hd.2)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hsmall : d / p < d := Nat.div_lt_self (by omega) hp.one_lt
  have hdvd : d / p ∣ d := Nat.div_dvd_of_dvd hpd
  have hle : (d / p : ℕ) ≤ Y := by
    by_contra! hc
    exact (Nat.find_min hex hsmall) ⟨dvd_trans hdvd hd.1, hc⟩
  refine ⟨d, hd.1, hd.2, ?_⟩
  calc
    (d : ℝ) = ((d / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast (Nat.div_mul_cancel hpd).symm
    _ ≤ Y * B := mul_le_mul hle (hP p hp (hpd.trans hd.1)) (by positivity) (by linarith)

private theorem prime_dvd_sigma_prime_power {r n : ℕ} (hr : r.Prime) (hn : n ≠ 0)
    (hd : r ∣ σ 1 n) :
    ∃ p ∈ n.primeFactors, r ∣ σ 1 (p ^ n.factorization p) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn] at hd
  exact (hr.prime.dvd_finsetProd_iff _).mp hd

private theorem sigma_prime_power_twice {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ j) ≤ 2 * p ^ j := by
  rw [sigma_one_apply_prime_pow hp]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, pow_succ]
    have hpow : 2 * p ^ j ≤ p ^ j * p := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left _ hp.two_le
    omega

private theorem dvd_sigma_of_unitary {d M : ℕ} (hc : d.Coprime M) : σ 1 d ∣ σ 1 (d * M) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime hc]
  exact dvd_mul_right _ _

private theorem amicable_unitary_coprime_sigma {n n' d M : ℕ}
    (hn : IsAmicable n n') (he : n' = d * M)
    (hc : d.Coprime M) (hlarge : ∀ r : ℕ, r.Prime → r ∣ d → ¬ r ∣ n) :
    (σ 1 d).Coprime d := by
  apply Nat.coprime_of_dvd
  intro r hr hrdσ hrd
  have hrn' : r ∣ n' := he ▸ hrd.trans (dvd_mul_right d M)
  have hrsum : r ∣ n + n' := by
    rw [← hn.right, he]
    exact hrdσ.trans (dvd_sigma_of_unitary hc)
  exact hlarge r hr hrd ((Nat.dvd_add_iff_left hrn').mpr hrsum)

private theorem gcd_sigma_sub_dvd {p m n' Q : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hn : IsAmicable (p * m) n') (hQ : Q ∣ n') :
    Q.gcd (σ 1 m - m) ∣ m := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun he => hpm (he ▸ dvd_zero p)
  have hms := sigma_ge_self hm
  have he : n' = p * (σ 1 m - m) + σ 1 m := by
    have hl := amicable_factor_left hp hpm hn
    exact_mod_cast (show (n' : ℤ) = (p : ℤ) * ((σ 1 m - m : ℕ) : ℤ) + (σ 1 m : ℤ) by
      rw [Int.natCast_sub hms]
      exact hl)
  let g := Q.gcd (σ 1 m - m)
  have hg₁ : g ∣ σ 1 m - m := Nat.gcd_dvd_right _ _
  have hg₂ : g ∣ n' := (Nat.gcd_dvd_left _ _).trans hQ
  rw [he] at hg₂
  have hg₃ : g ∣ σ 1 m := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hg₁ p)).mpr hg₂
  have hab : σ 1 m = (σ 1 m - m) + m := by omega
  rw [hab] at hg₃
  exact (Nat.dvd_add_iff_right hg₁).mpr hg₃

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

private theorem sum_of_weighted_fiber_bounds {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (u : α → ℝ) (w : β → ℝ)
    (hT : ∀ x ∈ S, f x ∈ T)
    (hw : ∀ y ∈ T, ∑ x ∈ S.filter (fun x => f x = y), u x ≤ w y) :
    ∑ x ∈ S, u x ≤ ∑ y ∈ T, w y := by
  rw [← sum_fiberwise_of_maps_to hT]
  exact sum_le_sum hw

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

private theorem prime_power_recip_fiber {N r j : ℕ} (hr : 0 < r) (hj : 0 < j) (a : ℕ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≡ a [MOD r] ∧ r ∣ σ 1 (p ^ j)) :
    ∑ p ∈ S, ((p ^ j : ℕ) : ℝ)⁻¹ ≤ (3 + log N) / r := by
  let small := S.filter (· < r)
  let large := S.filter (fun p => r ≤ p)
  have hdisj : Disjoint small large := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    exact (not_le_of_gt (mem_filter.mp hp).2) (mem_filter.mp hq).2
  have heq : small ∪ large = S := by
    ext p
    by_cases hp : p < r
    · simp [small, large, hp, not_le_of_gt hp]
    · simp [small, large, hp, le_of_not_gt hp]
  have hl : (∑ p ∈ large, ((p ^ j : ℕ) : ℝ)⁻¹) ≤ (1 + log N) / r := by
    apply le_trans _ (recip_sum_congruence hr large (a := a) (fun p hp =>
      ⟨(mem_filter.mp hp).2, (hS p (mem_filter.mp hp).1).2.1, (hS p (mem_filter.mp hp).1).2.2.1⟩))
    apply sum_le_sum
    intro p hp
    have hp' := (hS p (mem_filter.mp hp).1).1
    exact inv_anti₀ (by exact_mod_cast hp'.pos) (by exact_mod_cast Nat.le_self_pow hj.ne' p)
  have hs : (∑ p ∈ small, ((p ^ j : ℕ) : ℝ)⁻¹) ≤ 2 / r := by
    by_cases hne : small.Nonempty
    · obtain ⟨p, hp⟩ := hne
      have h₁ := hS p (mem_filter.mp hp).1
      have hsmall : small = {p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hp, fun q hq => ?_⟩
        have h₂ := hS q (mem_filter.mp hq).1
        exact (h₂.2.2.1.trans h₁.2.2.1.symm).eq_of_lt_of_lt (mem_filter.mp hq).2 (mem_filter.mp hp).2
      rw [hsmall, sum_singleton]
      have hk : (r : ℝ) ≤ 2 * ((p ^ j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ h₁.1.ne_zero)) h₁.2.2.2).trans
          (sigma_prime_power_twice h₁.1 j)
      have hp₀ : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.pow_pos h₁.1.pos
      have hr₀ : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      rw [inv_eq_one_div, div_le_div_iff₀ hp₀ hr₀, one_mul]
      exact hk
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]; positivity
  rw [← heq, sum_union hdisj]
  linarith only [hs, hl, show (3 + log N) / (r : ℝ) = 2 / r + (1 + log N) / r by ring]

private theorem prime_power_congruence {r p : ℕ} (hp : p.Prime) (j : ℕ)
    (hd : r ∣ σ 1 (p ^ j)) : (p : ZMod r) ^ (j + 1) - 1 = 0 := by
  have h : (∑ k ∈ range (j + 1), (p : ZMod r) ^ k) = 0 := by
    have hz := (ZMod.natCast_eq_zero_iff (σ 1 (p ^ j)) r).mpr hd
    rw [sigma_one_apply_prime_pow hp] at hz
    push_cast at hz
    exact hz
  rw [← geom_sum_mul, h, zero_mul]

private theorem prime_power_recip_bound {N r j : ℕ} (hr : r.Prime) (hN : 1 ≤ N) (hj : 0 < j) :
    ∑ p ∈ N.primesLE.filter (fun p => r ∣ σ 1 (p ^ j)), ((p ^ j : ℕ) : ℝ)⁻¹ ≤
      (j + 1 : ℕ) * ((3 + log N) / r) := by
  classical
  let _ : Fact r.Prime := ⟨hr⟩
  let P : Polynomial (ZMod r) := Polynomial.X ^ (j + 1) - Polynomial.C 1
  let S := N.primesLE.filter (fun p => r ∣ σ 1 (p ^ j))
  let T := (P.rootSet_finite (ZMod r)).toFinset
  have hPd : P.natDegree = j + 1 := Polynomial.natDegree_X_pow_sub_C
  have hP : P ≠ 0 := fun hz => by simp [hz] at hPd
  have hT (p : ℕ) (hp : p ∈ S) : (p : ZMod r) ∈ T := by
    have hp' := mem_filter.mp hp
    simp only [T, Set.Finite.mem_toFinset]
    apply (Polynomial.mem_rootSet_of_ne hP).mpr
    simpa [P] using prime_power_congruence (Nat.mem_primesLE.mp hp'.1).2 j hp'.2
  have hf (a : ZMod r) (ha : a ∈ T) :
      ∑ p ∈ S.filter (fun p : ℕ => (p : ZMod r) = a), ((p ^ j : ℕ) : ℝ)⁻¹ ≤ (3 + log N) / r := by
    apply prime_power_recip_fiber hr.pos hj a.val
    intro p hp
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hp, hd⟩ := mem_filter.mp hp
    obtain ⟨hpN, hpP⟩ := Nat.mem_primesLE.mp hp
    refine ⟨hpP, hpN, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_, hd⟩
    simpa using he
  calc
    _ ≤ ∑ a ∈ T, (3 + log N) / (r : ℝ) := sum_of_weighted_fiber_bounds S T _ _ _ hT hf
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : T.card ≤ j + 1 := by
        rw [show T.card = (P.rootSet (ZMod r)).ncard by
          exact (Set.ncard_eq_toFinset_card _ (P.rootSet_finite (ZMod r))).symm, ← hPd]
        exact Polynomial.ncard_rootSet_le P (ZMod r)
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
      exact div_nonneg (by linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)]) (by positivity)

private theorem card_of_prod_bound {N : ℕ} {Y : ℝ} (hY : 0 ≤ Y) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ z.1 ≤ N ∧ 0 < z.2 ∧ (z.1 : ℝ) * z.2 ≤ Y) :
    (S.card : ℝ) ≤ Y * (1 + log N) := by
  have h := card_of_fiber_bounds S (Icc 1 N) Prod.fst (fun m => Y * (m : ℝ)⁻¹)
    (fun z hz => mem_Icc.mpr ⟨(hS z hz).1, (hS z hz).2.1⟩) ?_
  · rw [← mul_sum] at h
    exact h.trans (mul_le_mul_of_nonneg_left (harmonic_bound_finset _ (Subset.rfl)) hY)
  · intro m hm
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
    let T := S.filter fun z => z.1 = m
    have hc : T.card ≤ (Icc 1 ⌊Y / (m : ℝ)⌋₊).card := by
      apply card_le_card_of_injOn Prod.snd
      · intro z hz
        have ⟨hzS, hzm⟩ := mem_filter.mp hz
        have hs := hS z hzS
        refine mem_Icc.mpr ⟨hs.2.2.1, Nat.le_floor ?_⟩
        rw [le_div_iff₀ hm0, mul_comm, ← hzm]
        exact hs.2.2.2
      · intro z hz z' hz' he
        exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hz').2.symm) he
    have hfloor := Nat.floor_le (div_nonneg hY hm0.le)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    rw [← div_eq_mul_inv]
    exact (show (T.card : ℝ) ≤ ⌊Y / (m : ℝ)⌋₊ by exact_mod_cast hc).trans hfloor

private theorem count_small_cofactors {N : ℕ} {Y : ℝ} (hY : 0 ≤ Y) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, ∃ p q m n : ℕ, p.Prime ∧ q.Prime ∧ ¬ p ∣ m ∧ ¬ q ∣ n ∧
      z = (p * m, q * n) ∧ z.1 ≤ N ∧ IsAmicable z.1 z.2 ∧ (m : ℝ) * n ≤ Y) :
    (S.card : ℝ) ≤ Y * (1 + log N) := by
  classical
  let f (z : ℕ × ℕ) : ℕ × ℕ :=
    if h : z ∈ S then ⟨(hS z h).choose_spec.choose_spec.choose,
      (hS z h).choose_spec.choose_spec.choose_spec.choose⟩ else (0, 0)
  have hdata (z) (hz : z ∈ S) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ¬ p ∣ (f z).1 ∧
      ¬ q ∣ (f z).2 ∧ z = (p * (f z).1, q * (f z).2) ∧ z.1 ≤ N ∧
      IsAmicable z.1 z.2 ∧ ((f z).1 : ℝ) * (f z).2 ≤ Y := by
    refine ⟨(hS z hz).choose, (hS z hz).choose_spec.choose, ?_⟩
    simpa only [f, dif_pos hz] using (hS z hz).choose_spec.choose_spec.choose_spec.choose_spec
  have hf : Set.InjOn f S := by
    intro z hz z' hz' he
    obtain ⟨p, q, hp, hq, hpm, hqn, hzE, _, hzA, _⟩ := hdata z hz
    obtain ⟨p', q', hp', hq', hp'm, hq'n, hz'E, _, hz'A, _⟩ := hdata z' hz'
    simp only [← he] at hp'm hq'n hz'E
    rw [hzE] at hzA
    rw [hz'E] at hz'A
    have hqE := amicable_factor_right_unique hp hq hp' hq' hpm hqn hp'm hq'n hzA hz'A
    have hpE := amicable_factor_right_unique hq hp hq' hp' hqn hpm hq'n hp'm
      (amicable_symm hzA) (amicable_symm hz'A)
    simpa [hpE, hqE, hz'E] using hzE
  rw [← card_image_of_injOn hf]
  apply card_of_prod_bound hY (N := N)
  intro v hv
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
  obtain ⟨p, q, hp, hq, hpm, hqn, hze, hzN, _, hprod⟩ := hdata z hz
  have hm : 0 < (f z).1 := Nat.pos_of_ne_zero fun he => hpm (he ▸ dvd_zero p)
  have hn : 0 < (f z).2 := Nat.pos_of_ne_zero fun he => hqn (he ▸ dvd_zero q)
  have hmN : (f z).1 ≤ N := by
    rw [hze] at hzN
    exact (Nat.le_mul_of_pos_left _ hp.pos).trans hzN
  exact ⟨hm, hmN, hn, hprod⟩

private theorem pair_card_projection (S : Finset (ℕ × ℕ)) (T : Finset ℕ)
    (hS : ∀ z ∈ S, IsAmicable z.1 z.2 ∧ z.1 ∈ T) : S.card ≤ T.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro z hz
    exact (hS z hz).2
  · intro z hz z' hz' he
    have hA := (hS z hz).1
    have hA' := (hS z' hz').1
    rw [← he] at hA'
    exact Prod.ext he (mate_unique hA hA')

private noncomputable def primePart (n : ℕ) (P : ℕ → Prop) : ℕ :=
  open scoped Classical in
  ∏ p ∈ n.primeFactors.filter P, p ^ n.factorization p

private theorem primePart_pos (n : ℕ) (P : ℕ → Prop) : 0 < primePart n P := by
  classical
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

open scoped Classical in
private theorem primePart_factorization (n r : ℕ) (P : ℕ → Prop) :
    (primePart n P).factorization r = if P r then n.factorization r else 0 := by
  classical
  unfold primePart
  rw [Nat.factorization_prod_apply (fun p hp => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).ne_zero)]
  have hprime (p) (hp : p ∈ n.primeFactors.filter P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  by_cases hr : r ∈ n.primeFactors.filter P
  · rw [Finset.sum_eq_single_of_mem r hr]
    · rw [Nat.factorization_pow_self (hprime r hr), if_pos (mem_filter.mp hr).2]
    · intro p hp hn
      simp [Nat.Prime.factorization_pow (hprime p hp), Finsupp.single_apply, hn]
  · have hzero : ∀ p ∈ n.primeFactors.filter P, (p ^ n.factorization p).factorization r = 0 := by
      intro p hp
      have hne : p ≠ r := fun he => hr (he ▸ hp)
      simp [Nat.Prime.factorization_pow (hprime p hp), Finsupp.single_apply, hne]
    rw [Finset.sum_eq_zero hzero]
    split_ifs with hPr
    · have hr' : r ∉ n.primeFactors := fun h => hr (mem_filter.mpr ⟨h, hPr⟩)
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hr'
      exact hr'.symm
    · rfl

private theorem primePart_mul_complement {n : ℕ} (hn : n ≠ 0) (P : ℕ → Prop) :
    primePart n P * primePart n (fun p => ¬ P p) = n := by
  classical
  apply Nat.eq_of_factorization_eq (mul_ne_zero (primePart_pos n P).ne'
    (primePart_pos n fun p => ¬P p).ne') hn
  intro r
  rw [Nat.factorization_mul (primePart_pos n P).ne' (primePart_pos n (fun p => ¬P p)).ne',
    Finsupp.add_apply, primePart_factorization, primePart_factorization]
  by_cases h : P r <;> simp [h]

private theorem prime_dvd_primePart_iff {n r : ℕ} (hn : n ≠ 0) (hr : r.Prime) (P : ℕ → Prop) :
    r ∣ primePart n P ↔ r ∣ n ∧ P r := by
  classical
  rw [hr.dvd_iff_one_le_factorization (primePart_pos n P).ne', hr.dvd_iff_one_le_factorization hn,
    primePart_factorization]
  by_cases h : P r <;> simp [h]

private theorem primePart_coprime {n : ℕ} (hn : n ≠ 0) (P : ℕ → Prop) :
    (primePart n P).Coprime (primePart n fun p => ¬ P p) := by
  apply Nat.coprime_of_dvd
  intro r hr h₁ h₂
  exact ((prime_dvd_primePart_iff hn hr _).mp h₂).2 ((prime_dvd_primePart_iff hn hr _).mp h₁).2

private theorem squarefree_part_properties {n : ℕ} (hn : n ≠ 0) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ n = d * m ∧ d.Coprime m ∧ Squarefree m ∧
      (∀ p ∈ d.primeFactors, d.factorization p ≠ 1) := by
  let P (p : ℕ) := 2 ≤ n.factorization p
  let d := primePart n P
  let m := primePart n (fun p => ¬P p)
  refine ⟨d, m, primePart_pos _ _, primePart_pos _ _, (primePart_mul_complement hn P).symm,
    primePart_coprime hn P, ?_, ?_⟩
  · rw [Nat.squarefree_iff_factorization_le_one (primePart_pos n (fun p => ¬P p)).ne']
    intro p
    rw [primePart_factorization]
    dsimp [P]
    split <;> omega
  · intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpP := ((prime_dvd_primePart_iff hn hpp P).mp hpd).2
    dsimp only [d]
    rw [primePart_factorization, if_pos hpP]
    exact fun he => by simpa [P, he] using hpP

private theorem prime_once_of_large {n p : ℕ} {L : ℝ} (hp : p.Prime) (hpd : p ∣ n)
    (hL : L < (p : ℝ))
    (hsmall : ∀ d : ℕ, d ∣ n → 0 < d →
      (∀ q ∈ d.primeFactors, d.factorization q ≠ 1) → (d : ℝ) ≤ L) :
    n = p * (n / p) ∧ ¬ p ∣ n / p := by
  refine ⟨(Nat.mul_div_cancel' hpd).symm, ?_⟩
  intro hbad
  have hsq : p ^ 2 ∣ n := by
    rw [← Nat.mul_div_cancel' hpd, pow_two]
    exact Nat.mul_dvd_mul_left p hbad
  have hs : (p ^ 2 : ℕ) ≤ L := by
    apply hsmall _ hsq (pow_pos hp.pos _)
    intro q hq
    have hql := (Nat.mem_primeFactors.mp hq).1
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have he : q = p := (Nat.prime_dvd_prime_iff_eq hql hp).mp (hql.dvd_of_dvd_pow hqd)
    subst q
    rw [Nat.factorization_pow_self hp]
    decide
  have hle : (p : ℝ) ≤ ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) p
  exact (not_lt_of_ge (hle.trans hs)) hL

private noncomputable def scale (x : ℝ) : ℝ := √(x.log * x.log.log.log)

private theorem eventually_scale_pos : ∀ᶠ x : ℝ in atTop, 0 < scale x := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0),
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      Real.tendsto_log_atTop)).eventually (eventually_gt_atTop 0)] with x hx hy
  exact Real.sqrt_pos_of_pos (mul_pos hx hy)

private theorem asymptotic_coefficient (A : ℝ → ℝ) (hA : ∀ x, 0 ≤ A x)
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      A x ≤ x * exp (-(1 / 2 - ε) * scale x)) :
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧
      ∀ᶠ x : ℝ in atTop, A x ≤ x * exp (-(1 / 2 + o x) * scale x) := by
  let o (x : ℝ) := if A x = 0 then 0 else min 0 (-log (A x / x) / scale x - 1 / 2)
  have ho₀ (x : ℝ) : o x ≤ 0 := by
    dsimp [o]
    split <;> simp
  have hop (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, -ε ≤ o x := by
    filter_upwards [h ε hε, eventually_scale_pos, eventually_gt_atTop (0 : ℝ)] with x ht hs hx
    dsimp [o]
    split_ifs with he
    · linarith
    · apply le_min (by linarith)
      have hr : 0 < A x / x := div_pos (lt_of_le_of_ne (hA x) (fun hz => he hz.symm)) hx
      have hdiv : A x / x ≤ exp (-(1 / 2 - ε) * scale x) :=
        (div_le_iff₀ hx).mpr (by linarith only [ht])
      have hh := Real.log_le_log hr hdiv
      rw [Real.log_exp] at hh
      rw [le_sub_iff_add_le, le_div_iff₀ hs]
      linarith only [hh]
  refine ⟨o, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hop (ε / 2) (by linarith)] with x hox
    rw [Real.dist_eq, sub_zero, abs_of_nonpos (ho₀ x)]
    linarith
  · filter_upwards [eventually_scale_pos, eventually_gt_atTop (0 : ℝ)] with x hs hx
    by_cases hzero : A x = 0
    · rw [hzero]
      positivity
    · have ho : o x ≤ -log (A x / x) / scale x - 1 / 2 := by simpa [o, hzero] using min_le_right 0 (-log (A x / x) / scale x - 1 / 2)
      have he : log (A x / x) ≤ -(1 / 2 + o x) * scale x := by
        rw [le_sub_iff_add_le, le_div_iff₀ hs] at ho
        linarith only [ho]
      have hl := Real.exp_le_exp.mpr he
      rw [Real.exp_log (div_pos (lt_of_le_of_ne (hA x) (fun hz => hzero hz.symm)) hx)] at hl
      rw [div_le_iff₀ hx] at hl
      linarith only [hl]

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

private theorem count_large_smooth_divisor {N K : ℕ} {Y t : ℝ} (hY : 0 < Y)
    (ht : 0 ≤ t) (ht₁ : t < 1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ d : ℕ, d ∣ n ∧ d ∈ K.smoothNumbers ∧ Y < (d : ℝ)) :
    (S.card : ℝ) ≤ (N : ℝ) * (Y ^ (-t) * smoothEuler K (1 - t)) := by
  let D := (Icc 1 N).filter fun d => d ∈ K.smoothNumbers ∧ Y < (d : ℝ)
  have h₁ := count_has_divisor D S (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1) (by
    intro n hn
    obtain ⟨hn0, hnN, d, hdn, hdS, hdY⟩ := hS n hn
    have hd0 := Nat.pos_of_ne_zero hdS.1
    exact ⟨hn0, hnN, d, mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,
      (Nat.le_of_dvd hn0 hdn).trans hnN⟩, hdS, hdY⟩, hdn⟩)
  apply h₁.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∑ d ∈ D, (d : ℝ)⁻¹ ≤ ∑ d ∈ D, Y ^ (-t) * (d : ℝ) ^ (-(1 - t)) := by
      exact sum_le_sum (fun d hd => shifted_rpow_tail hY (mem_filter.mp hd).2.2.le ht)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_smooth_rpow_le (by linarith) D
        (fun d hd => (mem_filter.mp hd).2.1)) (by positivity)

set_option maxHeartbeats 1800000 in
private theorem sum_squarefull_recip_tail {N : ℕ} {Y s : ℝ} (hY : 0 < Y)
    (hs : 1 / 2 < s) (hs₁ : s ≤ 1) :
    ∑ d ∈ (Icc 1 N).filter (fun d : ℕ => Y < (d : ℝ) ∧
      ∀ p ∈ d.primeFactors, d.factorization p ≠ 1), (d : ℝ)⁻¹ ≤
      Y ^ (s - 1) * ((1 + 1 / (2 * s - 1)) * (1 + 1 / (3 * s - 1))) := by
  classical
  let D := (Icc 1 N).filter (fun d : ℕ => Y < (d : ℝ) ∧ ∀ p ∈ d.primeFactors, d.factorization p ≠ 1)
  have hrep (d) (hd : d ∈ D) : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ d = a ^ 2 * b ^ 3 :=
    squarefull_representation (Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1) (mem_filter.mp hd).2.2
  let f (d : ℕ) : ℕ × ℕ := if h : d ∈ D then
    ((hrep d h).choose, (hrep d h).choose_spec.choose) else (0, 0)
  have hspec (d) (hd : d ∈ D) : 0 < (f d).1 ∧ 0 < (f d).2 ∧ d = (f d).1 ^ 2 * (f d).2 ^ 3 := by
    simpa only [f, dif_pos hd] using (hrep d hd).choose_spec.choose_spec
  have hinj : Set.InjOn f D := by
    intro d hd e he heq
    exact (hspec d hd).2.2.trans (heq ▸ (hspec e he).2.2.symm)
  have hsub : D.image f ⊆ Icc 1 N ×ˢ Icc 1 N := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hv
    obtain ⟨ha, hb, he⟩ := hspec d hd
    have hN := (mem_Icc.mp (mem_filter.mp hd).1).2
    have h₁ : (f d).1 ≤ d := by
      calc (f d).1 ≤ (f d).1 ^ 2 := Nat.le_self_pow (by decide) _
           _ ≤ (f d).1 ^ 2 * (f d).2 ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos hb _)
           _ = d := he.symm
    have h₂ : (f d).2 ≤ d := by
      calc (f d).2 ≤ (f d).2 ^ 3 := Nat.le_self_pow (by decide) _
           _ ≤ (f d).1 ^ 2 * (f d).2 ^ 3 := Nat.le_mul_of_pos_left _ (pow_pos ha _)
           _ = d := he.symm
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, h₁.trans hN⟩, mem_Icc.mpr ⟨hb, h₂.trans hN⟩⟩
  have heq (d) (hd : d ∈ D) : (d : ℝ) ^ (-s) =
      ((f d).1 : ℝ) ^ (-(2 * s)) * ((f d).2 : ℝ) ^ (-(3 * s)) := by
    obtain ⟨ha, hb, he⟩ := hspec d hd
    conv_lhs => rw [he]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
      ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hsum : ∑ d ∈ D, (d : ℝ) ^ (-s) ≤
      (1 + 1 / (2 * s - 1)) * (1 + 1 / (3 * s - 1)) := by
    calc
      _ = ∑ z ∈ D.image f, (z.1 : ℝ) ^ (-(2 * s)) * (z.2 : ℝ) ^ (-(3 * s)) := by
        rw [sum_image hinj]
        exact sum_congr rfl heq
      _ ≤ ∑ z ∈ Icc 1 N ×ˢ Icc 1 N, (z.1 : ℝ) ^ (-(2 * s)) * (z.2 : ℝ) ^ (-(3 * s)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ _ := by
        simp only [Finset.sum_product, Prod.fst, Prod.snd]
        rw [← Finset.sum_mul_sum]
        apply mul_le_mul
        · exact ((Real.summable_nat_rpow.mpr (by linarith : -(2 * s) < -1)).sum_le_tsum _
            (fun _ _ => by positivity)).trans (rpow_series_bound (by linarith))
        · exact ((Real.summable_nat_rpow.mpr (by linarith : -(3 * s) < -1)).sum_le_tsum _
            (fun _ _ => by positivity)).trans (rpow_series_bound (by linarith))
        · positivity
        · exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith))
  change ∑ d ∈ D, (d : ℝ)⁻¹ ≤ _
  calc
    _ ≤ ∑ d ∈ D, Y ^ (s - 1) * (d : ℝ) ^ (-s) := by
      apply sum_le_sum
      intro d hd
      have h := shifted_rpow_tail hY (mem_filter.mp hd).2.1.le (show 0 ≤ 1 - s by linarith)
      simpa only [neg_sub, sub_sub_cancel] using h
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem pow_eq_primePower_data {N n p : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hp : p ∈ n.primeFactors) :
    p ∈ N.primesLE ∧ n.factorization p ∈ Icc 1 (Nat.log 2 N) ∧
      p ^ n.factorization p ∣ n := by
  obtain ⟨hpp, hd, _⟩ := Nat.mem_primeFactors.mp hp
  have hj := hpp.factorization_pos_of_dvd hn.ne' hd
  have hppow : p ^ n.factorization p ∣ n :=
    (hpp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
  have hNpos := hn.trans_le hnN
  have hpow := (Nat.le_of_dvd hn hppow).trans hnN
  have h₂ : 2 ^ n.factorization p ≤ N := (Nat.pow_le_pow_left hpp.two_le _).trans hpow
  refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn hd).trans hnN, hpp⟩, ?_, hppow⟩
  exact mem_Icc.mpr ⟨hj, Nat.le_log_of_pow_le (by decide) h₂⟩

private theorem prime_not_dvd_sigma_prime_power {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ¬ p ∣ σ 1 (p ^ j) := by
  intro hd
  have h := (ZMod.natCast_eq_zero_iff (σ 1 (p ^ j)) p).mpr hd
  rw [sigma_one_apply_prime_pow hp] at h
  push_cast at h
  have h₀ : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [h₀, Finset.sum_eq_single 0] at h
  · simp only [pow_zero] at h
    have _ : Fact p.Prime := ⟨hp⟩
    exact (one_ne_zero : (1 : ZMod p) ≠ 0) h
  · intro b _ hb
    exact zero_pow hb
  · intro hc
    exact (hc (mem_range.mpr (by omega))).elim

private theorem prime_power_recip_total {N r : ℕ} (hN : 1 ≤ N) (hr : r.Prime) :
    ∑ j ∈ Icc 1 (Nat.log 2 N),
      ∑ p ∈ N.primesLE.filter (fun p => r ∣ σ 1 (p ^ j)), ((p ^ j : ℕ) : ℝ)⁻¹ ≤
      ((Nat.log 2 N : ℕ) + 1 : ℝ) ^ 2 * ((3 + log N) / r) := by
  have hpos : 0 ≤ (3 + log N) / (r : ℝ) := by
    exact div_nonneg (by linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)]) (by positivity)
  calc
    _ ≤ ∑ j ∈ Icc 1 (Nat.log 2 N), ((Nat.log 2 N : ℕ) + 1 : ℝ) * ((3 + log N) / r) := by
      apply sum_le_sum
      intro j hj
      exact (prime_power_recip_bound hr hN (mem_Icc.mp hj).1).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.succ_le_succ (mem_Icc.mp hj).2)) hpos)
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      nlinarith [mul_nonneg hpos (show (0 : ℝ) ≤ ((Nat.log 2 N : ℕ) + 1 : ℝ) by positivity)]

private theorem count_sigma_shared_prime {N r : ℕ} (hN : 1 ≤ N) (hr : r.Prime) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ r ∣ n ∧ r ∣ σ 1 n) :
    (S.card : ℝ) ≤ (N : ℝ) * (((Nat.log 2 N : ℕ) + 1 : ℝ) ^ 2 * (3 + log N)) / (r : ℝ)^2 := by
  let J := Icc 1 (Nat.log 2 N)
  let B (j : ℕ) := (N.primesLE.filter (fun p => r ∣ σ 1 (p ^ j)))
  let S' (j : ℕ) := S.filter fun n => ∃ p ∈ B j, p ≠ r ∧ p ^ j ∣ n
  have hcov (n : ℕ) (hn : n ∈ S) : ∃ j ∈ J, n ∈ S' j := by
    obtain ⟨hn0, hnN, _, hrs⟩ := hS n hn
    obtain ⟨p, hp, hpd⟩ := prime_dvd_sigma_prime_power hr hn0.ne' hrs
    obtain ⟨hpN, hj, hpn⟩ := pow_eq_primePower_data hn0 hnN hp
    have hne : p ≠ r := by
      intro he
      subst p
      exact prime_not_dvd_sigma_prime_power hr _ hpd
    exact ⟨n.factorization p, hj, mem_filter.mpr ⟨hn, p, mem_filter.mpr ⟨hpN, hpd⟩, hne, hpn⟩⟩
  have hsub (j : ℕ) (hj : j ∈ J) : ((S' j).card : ℝ) ≤
      ∑ p ∈ B j, ((N : ℝ) / r) * ((p ^ j : ℕ) : ℝ)⁻¹ := by
    have hcov' (n : ℕ) (hn : n ∈ S' j) : ∃ p ∈ B j, n ∈
        (S' j).filter (fun n => p ≠ r ∧ p ^ j ∣ n) := by
      obtain ⟨_, p, hp, hp'⟩ := mem_filter.mp hn
      exact ⟨p, hp, mem_filter.mpr ⟨hn, hp'⟩⟩
    refine card_of_cover (S' j) (B j) (fun p => (S' j).filter (fun n => p ≠ r ∧ p ^ j ∣ n)) _ hcov' ?_
    intro p hp
    have hpp := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr.pos
    have hpow : (0 : ℝ) < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast (pow_pos hpp.pos j)
    rw [show (N : ℝ) / r * ((p ^ j : ℕ) : ℝ)⁻¹ = (N : ℝ) / ((r * p ^ j : ℕ) : ℝ) by
      push_cast; ring]
    apply card_divisor_fiber (mul_pos hr.pos (pow_pos hpp.pos j))
    intro n hn
    obtain ⟨hnj, hpne, hpn⟩ := mem_filter.mp hn
    obtain ⟨hn₀, hnN, hrn, _⟩ := hS n (mem_filter.mp hnj).1
    refine ⟨hn₀, hnN, ?_⟩
    have hcop : r.Coprime p := hr.coprime_iff_not_dvd.mpr fun h =>
      hpne ((Nat.prime_dvd_prime_iff_eq hr hpp).mp h).symm
    exact (hcop.pow_right j).mul_dvd_of_dvd_of_dvd hrn hpn
  have h := card_of_cover S J S' _ hcov hsub
  simp only [← mul_sum] at h
  have h₂ := mul_le_mul_of_nonneg_left (prime_power_recip_total hN hr)
    (div_nonneg (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ r))
  refine h.trans (h₂.trans_eq ?_)
  ring

private theorem squarefree_sigma_dvd {m p : ℕ} (hm : Squarefree m) (hp : p ∈ m.primeFactors) :
    p + 1 ∣ σ 1 m := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hv : m.factorization p = 1 := by
    have h₁ := hprime.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
    have h₂ := (Nat.squarefree_iff_factorization_le_one hm0).mp hm p
    omega
  rw [isMultiplicative_sigma.multiplicative_factorization _ hm0]
  have h := dvd_prod_of_mem (fun q => σ 1 (q ^ m.factorization q)) hp
  rw [hv, pow_one] at h
  have hσ := sigma_prime_mul hprime (m := 1) (hprime.not_dvd_one)
  simpa using (show σ 1 p = p + 1 by simpa using hσ) ▸ h

private theorem rankin_squarefree_count {z s : ℝ} (hz : 0 < z) (hs : 0 ≤ s)
    (S T : Finset ℕ) (hS : ∀ n ∈ S, Squarefree n ∧ (n : ℝ) ≤ z ∧ n.primeFactors ⊆ T) :
    (S.card : ℝ) ≤ z ^ s * exp (∑ p ∈ T, (p : ℝ) ^ (-s)) := by
  have hP : S.image Nat.primeFactors ⊆ T.powerset := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
    exact mem_powerset.mpr (hS n hn).2.2
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro a ha b hb he
    rw [← Nat.prod_primeFactors_of_squarefree (hS a ha).1,
      ← Nat.prod_primeFactors_of_squarefree (hS b hb).1, he]
  have hweight (n) (hn : n ∈ S) : (n : ℝ) ^ (-s) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (-s) := by
    change naturalPower (-s) n = ∏ p ∈ n.primeFactors, naturalPower (-s) p
    rw [← map_prod, Nat.prod_primeFactors_of_squarefree (hS n hn).1]
  have hsingle (n) (hn : n ∈ S) : (1 : ℝ) ≤ z ^ s * (n : ℝ) ^ (-s) := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hS n hn).1.ne_zero
    calc
      1 = (n : ℝ) ^ s * (n : ℝ) ^ (-s) := by rw [← Real.rpow_add hn₀, add_neg_cancel, Real.rpow_zero]
      _ ≤ _ := by gcongr; exact (hS n hn).2.1
  calc
    (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, z ^ s * (n : ℝ) ^ (-s) := sum_le_sum hsingle
    _ = z ^ s * ∑ U ∈ S.image Nat.primeFactors, ∏ p ∈ U, (p : ℝ) ^ (-s) := by
      rw [← mul_sum, sum_image hinj]
      exact congrArg (fun a => z ^ s * a) (sum_congr rfl hweight)
    _ ≤ z ^ s * ∑ U ∈ T.powerset, ∏ p ∈ U, (p : ℝ) ^ (-s) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hP
        (fun _ _ _ => by positivity)) (by positivity)
    _ = z ^ s * ∏ p ∈ T, (1 + (p : ℝ) ^ (-s)) := by rw [Finset.prod_one_add]
    _ ≤ _ := by
      rw [Real.exp_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.prod_le_prod (fun _ _ => by positivity)
        (fun p _ => by simpa [add_comm] using Real.add_one_le_exp ((p : ℝ) ^ (-s)))

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
    ∑ p ∈ N.primesLE.filter (fun p => p + 1 ∈ K.smoothNumbers), (p : ℝ) ^ (-s) ≤
      (T : ℝ) ^ (1 - s) * (exp 1 * log (1 + log T)) +
        2 * (T : ℝ) ^ (-(s - s')) * smoothEuler K s' := by
  let P := N.primesLE.filter (fun p => p + 1 ∈ K.smoothNumbers)
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
          congr 1 <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hp₀.le (by exact_mod_cast hpT.le) (by linarith)) (by positivity)
    calc
      _ ≤ ∑ p ∈ S, (T : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ := sum_le_sum he
      _ ≤ _ := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (shifted_prime_recip_log hT)
  have hbig : ∑ p ∈ B, (p : ℝ) ^ (-s) ≤ 2 * (T : ℝ) ^ (-(s - s')) * smoothEuler K s' := by
    let D := B.image (· + 1)
    have hinj : Set.InjOn (fun p : ℕ => p + 1) B := by intro a ha b hb h; exact Nat.add_right_cancel h
    have hDs (p) (hp : p ∈ D) : p ∈ K.smoothNumbers := by
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp (mem_filter.mp ha).1).2
    have hterm (p) (hp : p ∈ B) : (p : ℝ) ^ (-s) ≤
        2 * (T : ℝ) ^ (-(s - s')) * ((p + 1 : ℕ) : ℝ) ^ (-s') := by
      have hT₀ : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
      have hpT := (mem_filter.mp hp).2
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hsum : ((p + 1 : ℕ) : ℝ) ≤ 2 * (p : ℝ) := by
        exact_mod_cast show p + 1 ≤ 2 * p by omega
      have hmono : (p : ℝ) ^ (-s) ≤ 2 * ((p + 1 : ℕ) : ℝ) ^ (-s) := by
        have he : (p : ℝ) ^ (-s) * (2 : ℝ) ^ (-s) ≤ ((p + 1 : ℕ) : ℝ) ^ (-s) := by
          rw [← Real.mul_rpow hp₀.le (by norm_num), mul_comm]
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hsum (by linarith)
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv] at he
        rw [div_le_iff₀ (by positivity)] at he
        have h2 : (2 : ℝ)^s ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs
        calc
          _ ≤ ((p + 1 : ℕ) : ℝ) ^ (-s) * (2 : ℝ) ^ s := he
          _ ≤ ((p + 1 : ℕ) : ℝ) ^ (-s) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := mul_comm _ _
      have hdec : ((p + 1 : ℕ) : ℝ) ^ (-(s - s')) ≤ (T : ℝ) ^ (-(s - s')) :=
        Real.rpow_le_rpow_of_nonpos hT₀ (by exact_mod_cast (show T ≤ p + 1 by omega)) (by linarith)
      have heq : ((p + 1 : ℕ) : ℝ) ^ (-s) =
          ((p + 1 : ℕ) : ℝ) ^ (-(s - s')) * ((p + 1 : ℕ) : ℝ) ^ (-s') := by
        rw [← Real.rpow_add (by positivity)]
        congr 1 <;> ring
      rw [heq] at hmono
      exact hmono.trans (by
        rw [mul_assoc 2]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdec (by positivity)) (by positivity))
    calc
      _ ≤ ∑ p ∈ B, 2 * (T : ℝ) ^ (-(s - s')) * ((p + 1 : ℕ) : ℝ) ^ (-s') := sum_le_sum hterm
      _ ≤ _ := by
        have he : (∑ d ∈ D, (d : ℝ) ^ (-s')) = ∑ p ∈ B, ((p + 1 : ℕ) : ℝ) ^ (-s') := by
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

private theorem count_amicable_large_prime {N : ℕ} (hN : 1 ≤ N) {B U Y : ℝ}
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hY : 0 < Y) (hBN : B ≤ N) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, IsAmicable z.1 z.2 ∧ z.2 ≤ N ∧
      ∃ p m d M : ℕ, p.Prime ∧ ¬ p ∣ m ∧ (m : ℝ) ≤ B ∧
        Y < (d : ℝ) ∧ (d : ℝ) ≤ U ∧ d.Coprime M ∧ (σ 1 d).Coprime d ∧
        z = (p * m, d * M)) :
    (S.card : ℝ) ≤ B * U + (N : ℝ) * B ^ 2 * (1 + log N) * (2 / Y) := by
  classical
  let C := Icc 1 ⌊B⌋₊
  let D := (Icc 1 ⌊U⌋₊).filter fun d : ℕ => Y < (d : ℝ)
  let F (md : ℕ × ℕ) := S.filter fun z =>
    ∃ M : ℕ, z.2 = md.2 * M ∧ (σ 1 md.2).Coprime md.2 ∧
      σ 1 md.1 * md.2 * M ≡ md.1 * σ 1 md.1 [MOD σ 1 md.2]
  let w (md : ℕ × ℕ) : ℝ := 1 + (N : ℝ) * (σ 1 md.1 : ℝ) * ((md.2 : ℝ) ^ 2)⁻¹
  have hcov : ∀ z ∈ S, ∃ md ∈ C ×ˢ D, z ∈ F md := by
    intro z hz
    obtain ⟨hA, _, p, m, d, M, hp, hpm, hmB, hdY, hdU, hdM, hσ, hz'⟩ := hS z hz
    have hm0 := Nat.pos_of_ne_zero (fun he : m = 0 => hpm (he ▸ dvd_zero p))
    have hd0 : 0 < d := by exact_mod_cast (hY.trans hdY)
    have hdmem : d ∈ D := mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0, Nat.le_floor hdU⟩, hdY⟩
    refine ⟨(m, d), mem_product.mpr ⟨mem_Icc.mpr ⟨hm0, Nat.le_floor hmB⟩, hdmem⟩, ?_⟩
    have he : IsAmicable (p * m) (d * M) := by simpa only [hz'] using hA
    exact mem_filter.mpr ⟨hz, M, by simp [hz'], hσ,
      amicable_divisor_congruence hp hpm he hdM rfl⟩
  have hf : ∀ md ∈ C ×ˢ D, ((F md).card : ℝ) ≤ w md := by
    intro md hmd
    have hd₀ : 0 < md.2 := (mem_Icc.mp (mem_filter.mp (mem_product.mp hmd).2).1).1
    let f (z : ℕ × ℕ) := z.2 / md.2
    have hf (z) (hz : z ∈ F md) : md.2 * f z = z.2 := by
      obtain ⟨_, M, hM, _, _⟩ := mem_filter.mp hz
      exact Nat.mul_div_cancel' ⟨M, hM⟩
    have hi : Set.InjOn f (F md) := by
      intro a ha b hb he
      have h₂ : a.2 = b.2 := (hf a ha).symm.trans (he ▸ hf b hb)
      have haA := (hS a (mem_filter.mp ha).1).1
      have hbA := (hS b (mem_filter.mp hb).1).1
      rw [← h₂] at hbA
      exact Prod.ext (mate_unique (amicable_symm haA) (amicable_symm hbA)) h₂
    have hC (a) (ha : a ∈ (F md).image f) :
        a ≤ N / md.2 ∧ (σ 1 md.1 * md.2) * a ≡ md.1 * σ 1 md.1 [MOD σ 1 md.2] := by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
      obtain ⟨hzS, M, hM, _, hmod⟩ := mem_filter.mp hz
      refine ⟨Nat.div_le_div_right (hS z hzS).2.1, ?_⟩
      simpa only [f, hM, Nat.mul_div_cancel_left M hd₀] using hmod
    have hdσ := sigma_pos 1 md.2 hd₀.ne'
    have count := card_linear_congruence hdσ ((F md).image f) hC
    rw [card_image_of_injOn hi] at count
    by_cases hne : (F md).Nonempty
    · obtain ⟨z, hz⟩ := hne
      have hσd := (mem_filter.mp hz).2.choose_spec.2.1
      have hgcd : (σ 1 md.2).gcd (σ 1 md.1 * md.2) ≤ σ 1 md.1 := by
        have hdvd : (σ 1 md.2).gcd (σ 1 md.1 * md.2) ∣ σ 1 md.1 := by
          have hcop := hσd.of_dvd_left (Nat.gcd_dvd_left (σ 1 md.2) (σ 1 md.1 * md.2))
          exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
        have hm₀ := (mem_Icc.mp (mem_product.mp hmd).1).1
        exact Nat.le_of_dvd (sigma_pos 1 _ (Nat.ne_of_gt hm₀)) hdvd
      apply count.trans
      unfold w
      have hdiv : ((N / md.2 : ℕ) : ℝ) ≤ (N : ℝ) / md.2 := by
        rw [le_div_iff₀ (by exact_mod_cast hd₀)]
        exact_mod_cast Nat.div_mul_le_self N md.2
      have hsig : (md.2 : ℝ) ≤ (σ 1 md.2 : ℝ) := by exact_mod_cast sigma_ge_self hd₀
      have hg : ((σ 1 md.2).gcd (σ 1 md.1 * md.2) : ℝ) ≤ (σ 1 md.1 : ℝ) := by exact_mod_cast hgcd
      have heq : (N : ℝ) * (σ 1 md.1 : ℝ) * ((md.2 : ℝ) ^ 2)⁻¹ =
          (N : ℝ) / md.2 * (σ 1 md.1 : ℝ) / md.2 := by ring
      rw [heq]
      gcongr
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne, w]; positivity
  have hcount := card_of_cover S (C ×ˢ D) F w hcov hf
  have hC : (C.card : ℝ) ≤ B := by
    simpa [C, Nat.card_Icc] using Nat.floor_le hB
  have hD : (D.card : ℝ) ≤ U := by
    have hcard : D.card ≤ (Icc 1 ⌊U⌋₊).card := card_filter_le _ _
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact (show (D.card : ℝ) ≤ ⌊U⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le hU)
  have hsumM : ∑ m ∈ C, (σ 1 m : ℝ) ≤ B ^ 2 * (1 + log N) := by
    have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN)
    calc
      _ ≤ ∑ _m ∈ C, B * (1 + log N) := by
        apply sum_le_sum
        intro m hm
        obtain ⟨hm₀, hmB⟩ := mem_Icc.mp hm
        have hmBR : (m : ℝ) ≤ B := (show (m : ℝ) ≤ ⌊B⌋₊ by exact_mod_cast hmB).trans (Nat.floor_le hB)
        apply (sigma_ratio_bound hm₀).trans
        have hmNR := hmBR.trans hBN
        gcongr
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, pow_two]
        nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hB (by linarith : 0 ≤ 1 + log N))]
  have hsumD : ∑ d ∈ D, ((d : ℝ) ^ 2)⁻¹ ≤ 2 / Y := by
    exact recip_square_tail hY (N := ⌊U⌋₊) (fun d hd => ⟨(mem_filter.mp hd).2,
      (mem_Icc.mp (mem_filter.mp hd).1).2⟩)
  have hm : ∑ md ∈ C ×ˢ D, w md = (C.card : ℝ) * D.card +
      (N : ℝ) * (∑ m ∈ C, (σ 1 m : ℝ)) * (∑ d ∈ D, ((d : ℝ) ^ 2)⁻¹) := by
    simp only [w, sum_add_distrib, sum_const, nsmul_eq_mul, card_product, Nat.cast_mul, sum_product]
    simp_rw [← mul_sum, mul_assoc (N : ℝ), mul_comm (σ 1 _ : ℝ), ← mul_assoc (N : ℝ), ← mul_sum]
    ring
  rw [hm] at hcount
  have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hM : (N : ℝ) * (∑ m ∈ C, (σ 1 m : ℝ)) ≤ (N : ℝ)*B^2*(1+log N) :=
    (mul_le_mul_of_nonneg_left hsumM (Nat.cast_nonneg N)).trans_eq (by ring)
  exact hcount.trans (add_le_add (mul_le_mul hC hD (by positivity) hB)
    (mul_le_mul hM hsumD (by positivity) (by positivity)))

private theorem recip_sum_multiples {N d : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ N ∧ d ∣ x) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ (1 + log N) / d := by
  apply recip_sum_congruence hd S (a := 0)
  intro x hx
  obtain ⟨hx₀, hxN, hxd⟩ := hS x hx
  exact ⟨Nat.le_of_dvd hx₀ hxd, hxN, Nat.modEq_zero_iff_dvd.mpr hxd⟩

private theorem recip_sum_shifted {N r : ℕ} (hr : 0 < r) (S : Finset ℕ)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ N ∧ r ∣ x + 1) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ 2 * (1 + log (N + 1 : ℕ)) / r := by
  have hi : Set.InjOn (fun x : ℕ => x + 1) S := by intro a _ b _ h; exact Nat.add_right_cancel h
  have h := recip_sum_multiples hr (S.image (· + 1)) (N := N + 1) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    exact ⟨by omega, Nat.succ_le_succ (hS y hy).2.1, (hS y hy).2.2⟩)
  calc
    _ ≤ ∑ x ∈ S, 2 * ((x + 1 : ℕ) : ℝ)⁻¹ := by
      apply sum_le_sum
      intro x hx
      have hx₀ : (0 : ℝ) < x := by exact_mod_cast (hS x hx).1
      have hx₁ : (1 : ℝ) ≤ x := by exact_mod_cast (hS x hx).1
      push_cast
      rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hx₀ (by positivity)]
      linarith
    _ ≤ _ := by
      have he : (∑ x ∈ S.image (fun x : ℕ => x + 1), (x : ℝ)⁻¹) =
          ∑ x ∈ S, ((x + 1 : ℕ) : ℝ)⁻¹ := by rw [sum_image hi]
      rw [← mul_sum, ← he]
      exact (mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 2 by norm_num)).trans_eq (by ring)

private theorem count_final_residue {N Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (g : ℕ) (r : ℕ → ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≤ N ∧ ∃ p m : ℕ, 0 < m ∧ d ∣ m ∧ Q ≤ p ∧
      n = p * m ∧ Q.gcd (σ 1 m - m) = g ∧ (σ 1 m - m) * p ≡ r m [MOD Q]) :
    (S.card : ℝ) ≤ 2 * (N : ℝ) * (g : ℝ) / Q * ((1 + log N) / d) := by
  classical
  let T := (Icc 1 N).filter (fun m => d ∣ m)
  let F (m : ℕ) := S.filter fun n => ∃ p : ℕ, Q ≤ p ∧ n = p * m ∧
    Q.gcd (σ 1 m - m) = g ∧ (σ 1 m - m) * p ≡ r m [MOD Q]
  let w (m : ℕ) := (2 * (N : ℝ) * (g : ℝ) / Q) * (m : ℝ)⁻¹
  have hc : ∀ n ∈ S, ∃ m ∈ T, n ∈ F m := by
    intro n hn
    obtain ⟨hnN, p, m, hm0, hdm, hqp, hnm, hg, hmod⟩ := hS n hn
    have hp0 := hQ.trans_le hqp
    have hmN : m ≤ N := (Nat.le_mul_of_pos_left m hp0).trans (hnm.symm.trans_le hnN)
    exact ⟨m, mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0, hmN⟩, hdm⟩,
      mem_filter.mpr ⟨hn, p, hqp, hnm, hg, hmod⟩⟩
  have hf (m : ℕ) (hm : m ∈ T) : ((F m).card : ℝ) ≤ w m := by
    have hm0 := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    let f (n : ℕ) := n / m
    have hfData (n : ℕ) (hn : n ∈ F m) : Q ≤ f n ∧ n = f n * m ∧ Q.gcd (σ 1 m - m) = g ∧
        (σ 1 m - m) * f n ≡ r m [MOD Q] := by
      obtain ⟨_, p, hp, he, hg, hmod⟩ := mem_filter.mp hn
      have hdiv : f n = p := by
        unfold f
        rw [he, mul_comm p m, Nat.mul_div_cancel_left p (show 0 < m from hm0)]
      simpa [hdiv] using (show Q ≤ p ∧ n = p * m ∧ Q.gcd (σ 1 m - m) = g ∧
        (σ 1 m - m) * p ≡ r m [MOD Q] from ⟨hp,he,hg,hmod⟩)
    have hinj : Set.InjOn f (F m) := by
      intro n hn n' hn' h
      exact (hfData n hn).2.1.trans (h ▸ (hfData n' hn').2.1.symm)
    have hcount := card_linear_congruence hQ ((F m).image f) (n := N / m) (by
      intro p hp
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
      exact ⟨Nat.div_le_div_right (hS n (mem_filter.mp hn).1).1, (hfData n hn).2.2.2⟩)
    rw [card_image_of_injOn hinj] at hcount
    by_cases hne : (F m).Nonempty
    · obtain ⟨n, hn⟩ := hne
      have ⟨hnQ, _, hg, _⟩ := hfData n hn
      have hg₀ : 1 ≤ g := by rw [← hg]; exact Nat.gcd_pos_of_pos_left _ hQ
      have hNQ : Q ≤ N / m := hnQ.trans (Nat.div_le_div_right (hS n (mem_filter.mp hn).1).1)
      rw [hg] at hcount
      have hdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := by
        rw [le_div_iff₀ hmR]; exact_mod_cast Nat.div_mul_le_self N m
      have hbase : 1 ≤ (N : ℝ) / m * (g : ℝ) / Q := by
        rw [le_div_iff₀ hQR, one_mul]
        have h₁ : (Q : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hNQ
        calc (Q : ℝ) ≤ (N : ℝ) / m := h₁.trans hdiv
             _ ≤ (N : ℝ) / m * (g : ℝ) := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hg₀)
      have hstep : ((N / m : ℕ) : ℝ) * (g : ℝ) / Q ≤ (N : ℝ) / m * (g : ℝ) / Q := by
        gcongr
      calc
        _ ≤ 1 + ((N / m : ℕ) : ℝ) * (g : ℝ) / Q := hcount
        _ ≤ 2 * ((N : ℝ) / m * (g : ℝ) / Q) := by linarith only [hbase, hstep]
        _ = w m := by unfold w; ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne, w]; positivity
  have hbound := card_of_cover S T F w hc hf
  rw [show (∑ m ∈ T, w m) = (2 * (N : ℝ) * (g : ℝ) / Q) * ∑ m ∈ T, (m : ℝ)⁻¹ by
    rw [mul_sum]] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (recip_sum_multiples hd T (fun m hm => ⟨(mem_Icc.mp (mem_filter.mp hm).1).1,
      (mem_Icc.mp (mem_filter.mp hm).1).2, (mem_filter.mp hm).2⟩)) (by positivity))

private def finalCondition (n q Q g : ℕ) : Prop :=
  ∃ p m : ℕ, 0 < m ∧ q * g ∣ m ∧ Q ≤ p ∧ n = p * m ∧
    Q.gcd (σ 1 m - m) = g ∧ (σ 1 m - m) * p ≡ Q - σ 1 m % Q [MOD Q]

private theorem final_condition_of_pair {p m n' q l j : ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) (hA : IsAmicable (p * m) n')
    (hq : q.Prime) (hqm : q ∣ m) (hl : l.Prime) (hqne : q ≠ l)
    (hQn : l ^ j ∣ n') (hpQ : l ^ j ≤ p) :
    ∃ g ∈ (l ^ j).divisors, finalCondition (p * m) q (l ^ j) g := by
  let Q := l ^ j
  let g := Q.gcd (σ 1 m - m)
  have hQ : 0 < Q := pow_pos hl.pos _
  have hgQ : g ∣ Q := Nat.gcd_dvd_left _ _
  have hgm : g ∣ m := gcd_sigma_sub_dvd hp hpm hA hQn
  have hqm' : q.Coprime g := by
    have hcop : q.Coprime l := hq.coprime_iff_not_dvd.mpr fun hd =>
      hqne ((Nat.prime_dvd_prime_iff_eq hq hl).mp hd)
    exact (hcop.pow_right j).of_dvd_right hgQ
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => hpm (h ▸ dvd_zero p))
  have hms := sigma_ge_self hm
  have hn' : n' = (σ 1 m - m) * p + σ 1 m := by
    have hl := amicable_factor_left hp hpm hA
    rw [← Int.natCast_sub hms, mul_comm] at hl
    exact_mod_cast hl
  have hres : (σ 1 m - m) * p ≡ Q - σ 1 m % Q [MOD Q] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have h0 : (n' : ZMod Q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hQn
    have hcast : ((Q - σ 1 m % Q : ℕ) : ZMod Q) = -(σ 1 m : ZMod Q) := by
      rw [Nat.cast_sub (Nat.mod_lt _ hQ).le, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
    rw [hcast]
    rw [hn'] at h0
    push_cast only [Nat.cast_add] at h0
    exact eq_neg_of_add_eq_zero_left h0
  exact ⟨g, Nat.mem_divisors.mpr ⟨hgQ, hQ.ne'⟩,
    p, m, hm, hqm'.mul_dvd_of_dvd_of_dvd hqm hgm, hpQ, rfl, rfl, hres⟩

set_option maxHeartbeats 1500000 in
private theorem count_final_for_prime {N r : ℕ} (hN : 1 ≤ N) (hr : r.Prime) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≤ N ∧ ∃ q ∈ N.primesLE, r ∣ q + 1 ∧
      ∃ j ∈ Icc 1 (Nat.log 2 N), ∃ l ∈ N.primesLE,
      r ∣ σ 1 (l ^ j) ∧ ∃ g ∈ (l ^ j).divisors, finalCondition n q (l ^ j) g) :
    (S.card : ℝ) ≤
      (4 * (N : ℝ) * (1 + log N) * (1 + log (N + 1 : ℕ)) *
      ((Nat.log 2 N : ℕ) + 1 : ℝ) ^ 3 * (3 + log N)) / (r : ℝ)^2 := by
  classical
  let Qs := N.primesLE.filter (fun q => r ∣ q + 1)
  let J := Icc 1 (Nat.log 2 N)
  let E (j : ℕ) := N.primesLE.filter (fun l => r ∣ σ 1 (l ^ j))
  let T (q : ℕ) := S.filter fun n => ∃ j ∈ J, ∃ l ∈ E j, ∃ g ∈ (l ^ j).divisors,
    finalCondition n q (l ^ j) g
  have hcover : ∀ n ∈ S, ∃ q ∈ Qs, n ∈ T q := by
    intro n hn
    obtain ⟨_, q, hq, hqr, j, hj, l, hl, hlr, g, hg, hw⟩ := hS n hn
    exact ⟨q, mem_filter.mpr ⟨hq, hqr⟩, mem_filter.mpr ⟨hn, j, hj, l, mem_filter.mpr ⟨hl, hlr⟩, g,hg,hw⟩⟩
  let W (q : ℕ) : ℝ := 2 * (N : ℝ) * (1 + log N) / q
  have hT (q : ℕ) (hq : q ∈ Qs) : ((T q).card : ℝ) ≤
      W q * ((Nat.log 2 N : ℕ) + 1 : ℝ) ^ 3 * ((3 + log N) / r) := by
    have hqP := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).2
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqP.pos
    have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hW : 0 ≤ W q := by dsimp [W]; positivity
    let Tj (j : ℕ) := (T q).filter fun n => ∃ l ∈ E j, ∃ g ∈ (l ^ j).divisors, finalCondition n q (l ^ j) g
    let Tl (j l : ℕ) := (Tj j).filter fun n => ∃ g ∈ (l ^ j).divisors, finalCondition n q (l ^ j) g
    have hcovj (n : ℕ) (hn : n ∈ T q) : ∃ j ∈ J, n ∈ Tj j := by
      obtain ⟨_, j, hj, h⟩ := mem_filter.mp hn
      exact ⟨j, hj, mem_filter.mpr ⟨hn,h⟩⟩
    have hJ (j : ℕ) (hj : j ∈ J) : ((Tj j).card : ℝ) ≤
      ∑ l ∈ E j, W q * ((Nat.log 2 N : ℕ) + 1 : ℝ) * ((l ^ j : ℕ) : ℝ)⁻¹ := by
      refine card_of_cover (Tj j) (E j) (Tl j) _ ?_ ?_
      · intro n hn
        obtain ⟨_, l, hl, h⟩ := mem_filter.mp hn
        exact ⟨l, hl, mem_filter.mpr ⟨hn,h⟩⟩
      · intro l hl
        have hp := (Nat.mem_primesLE.mp (mem_filter.mp hl).1).2
        have hL : 0 < l ^ j := pow_pos hp.pos _
        let G (g : ℕ) := (Tl j l).filter fun n => finalCondition n q (l ^ j) g
        have hcovg (n : ℕ) (hn : n ∈ Tl j l) : ∃ g ∈ (l ^ j).divisors, n ∈ G g := by
          obtain ⟨_,g,hg,h⟩ := mem_filter.mp hn
          exact ⟨g,hg,mem_filter.mpr ⟨hn,h⟩⟩
        have hG (g : ℕ) (hg : g ∈ (l ^ j).divisors) : ((G g).card : ℝ) ≤ W q * ((l ^ j : ℕ) : ℝ)⁻¹ := by
          have hg0 := Nat.pos_of_mem_divisors hg
          have hr := count_final_residue hL (mul_pos hqP.pos hg0) g (fun m => l ^ j - σ 1 m % l ^ j)
            (G g) (N := N) (by
              intro n hn
              obtain ⟨hT,hw⟩ := mem_filter.mp hn
              have hs : n ∈ S := (mem_filter.mp (mem_filter.mp (mem_filter.mp hT).1).1).1
              exact ⟨(hS n hs).1, hw⟩)
          apply hr.trans_eq
          dsimp [W]
          push_cast
          have hgr : (0 : ℝ) < g := by exact_mod_cast hg0
          field_simp
        have hfin := card_of_cover (Tl j l) (l ^ j).divisors G _ hcovg hG
        rw [sum_const, nsmul_eq_mul, Nat.divisors_prime_pow hp, card_map, card_range] at hfin
        have hj' : (j : ℝ) + 1 ≤ ((Nat.log 2 N : ℕ) + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (mem_Icc.mp hj).2
        have hj'' : ((j + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 N : ℕ) + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (mem_Icc.mp hj).2
        exact hfin.trans ((mul_le_mul_of_nonneg_right hj'' (mul_nonneg hW (by positivity))).trans_eq (by ring))
    have hfin := card_of_cover (T q) J Tj _ hcovj hJ
    simp only [← mul_sum] at hfin
    have hpow := prime_power_recip_total hN hr
    have hWp : 0 ≤ W q * ((Nat.log 2 N : ℕ) + 1 : ℝ) := mul_nonneg hW (by positivity)
    exact hfin.trans ((mul_le_mul_of_nonneg_left hpow hWp).trans_eq (by ring))
  have hz := card_of_cover S Qs T _ hcover hT
  have hqsum := recip_sum_shifted hr.pos Qs (by
    intro q hq
    obtain ⟨hq, hq'⟩ := mem_filter.mp hq
    exact ⟨(Nat.mem_primesLE.mp hq).2.pos, (Nat.mem_primesLE.mp hq).1, hq'⟩)
  let A : ℝ := 2 * (N : ℝ) * (1 + log N) * ((Nat.log 2 N : ℕ) + 1 : ℝ)^3 * ((3 + log N) / r)
  have hA : 0 ≤ A := by
    have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    dsimp [A]; positivity
  have hz' : (S.card : ℝ) ≤ A * ∑ q ∈ Qs, (q : ℝ)⁻¹ := by
    apply hz.trans_eq
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by dsimp [W,A]; ring
  exact hz'.trans ((mul_le_mul_of_nonneg_left hqsum hA).trans_eq (by dsimp [A]; ring))

private structure GoodSide (X L : ℝ) (n : ℕ) : Prop where
  size : X / L < n
  smooth : ∀ d : ℕ, d ∣ n → d ∈ (⌊L ^ 2⌋₊ + 1).smoothNumbers → (d : ℝ) ≤ X ^ (1 / 3 : ℝ)
  squarefull : ∀ d : ℕ, d ∣ n → 0 < d →
    (∀ q ∈ d.primeFactors, d.factorization q ≠ 1) → (d : ℝ) ≤ L ^ 2

private theorem good_side_decompose {X L : ℝ} {n : ℕ} (hX : 1 ≤ X)
    (hXL : X ^ (1 / 3 : ℝ) < X / L) (hgood : GoodSide X L n) :
    n.maxPrimeFac.Prime ∧ L ^ 2 < (n.maxPrimeFac : ℝ) ∧
      n = n.maxPrimeFac * (n / n.maxPrimeFac) ∧ ¬n.maxPrimeFac ∣ n / n.maxPrimeFac := by
  have h₁ : 1 < n := by
    have h := Real.one_le_rpow hX (by norm_num : (0 : ℝ) ≤ 1 / 3)
    exact_mod_cast (h.trans_lt (hXL.trans hgood.size))
  have hp := Nat.prime_maxPrimeFac_of_one_lt n h₁
  have hlarge : L ^ 2 < (n.maxPrimeFac : ℝ) := by
    by_contra! h
    have hS : n ∈ (⌊L ^ 2⌋₊ + 1).smoothNumbers := by
      rw [Nat.mem_smoothNumbers']
      intro q hq hqd
      have hq' := Nat.le_maxPrimeFac (by omega : n ≠ 0) hq hqd
      exact Nat.lt_succ_of_le (Nat.le_floor ((show (q : ℝ) ≤ n.maxPrimeFac by exact_mod_cast hq').trans h))
    exact (not_lt_of_ge (hgood.smooth n dvd_rfl hS)) (hXL.trans hgood.size)
  have h := prime_once_of_large hp Nat.maxPrimeFac_dvd hlarge hgood.squarefull
  exact ⟨hp, hlarge, h⟩

private theorem good_side_large_unitary {X L : ℝ} {n : ℕ} (hX : 1 ≤ X)
    (hXL : X ^ (1 / 3 : ℝ) * √X ≤ X / L) (hgood : GoodSide X L n) :
    ∃ d M : ℕ, n = d * M ∧ d.Coprime M ∧ √X < (d : ℝ) ∧
      (d : ℝ) ≤ √X * n.maxPrimeFac ∧ ∀ r : ℕ, r.Prime → r ∣ d → L ^ 2 < (r : ℝ) := by
  have hy : 1 ≤ √X := by simpa using Real.sqrt_le_sqrt hX
  have hz := Real.one_le_rpow hX (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hxL : 0 < X / L := lt_of_lt_of_le (mul_pos (by linarith) (by linarith)) hXL
  have hn₀ : 0 < n := by exact_mod_cast hxL.trans hgood.size
  let P (p : ℕ) := (p : ℝ) ≤ L ^ 2
  let a := primePart n P
  let b := primePart n (fun p => ¬ P p)
  have he : a * b = n := primePart_mul_complement hn₀.ne' P
  have ha : a ∣ n := he ▸ dvd_mul_right a b
  have hb : b ∣ n := he ▸ dvd_mul_left b a
  have haS : a ∈ (⌊L ^ 2⌋₊ + 1).smoothNumbers := by
    rw [Nat.mem_smoothNumbers']
    intro r hr hrd
    have hrle : (r : ℝ) ≤ L ^ 2 := ((prime_dvd_primePart_iff hn₀.ne' hr P).mp hrd).2
    exact Nat.lt_succ_of_le (Nat.le_floor hrle)
  have haU := hgood.smooth a ha haS
  have hbL : √X < (b : ℝ) := by
    by_contra! h
    have hmul := mul_le_mul haU h (Nat.cast_nonneg _) (hz.trans' (by norm_num : (0 : ℝ) ≤ 1))
    have hn : (n : ℝ) = (a : ℝ) * (b : ℝ) := by exact_mod_cast he.symm
    exact (not_lt_of_ge ((hn.le.trans hmul).trans hXL)) hgood.size
  have hpmax (r : ℕ) (hr : r.Prime) (hrd : r ∣ b) : (r : ℝ) ≤ (n.maxPrimeFac : ℝ) := by
    exact_mod_cast Nat.le_maxPrimeFac hn₀.ne' hr (hrd.trans hb)
  obtain ⟨d, hd, hdL, hdU⟩ := exists_divisor_in_window hy hbL hpmax
  let M := n / d
  have hd' : d ∣ n := hd.trans hb
  have he' : n = d * M := (Nat.mul_div_cancel' hd').symm
  have hlarge (r : ℕ) (hr : r.Prime) (hrd : r ∣ d) : L ^ 2 < (r : ℝ) :=
    lt_of_not_ge ((prime_dvd_primePart_iff hn₀.ne' hr (fun p => ¬ P p)).mp (hrd.trans hd)).2
  have hc : d.Coprime M := by
    refine Nat.coprime_of_dvd fun r hr hrd hrM => ?_
    have hrn := hrd.trans hd'
    have hb := (prime_once_of_large hr hrn (hlarge r hr hrd) hgood.squarefull).2
    apply hb
    have hdvd : r * r ∣ n := he'.symm ▸ Nat.mul_dvd_mul hrd hrM
    rw [← Nat.mul_div_cancel' hrn] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hr.pos hdvd
  exact ⟨d, M, he', hc, hdL, hdU, hlarge⟩

private theorem regular_witness {N p p' m n' : ℕ} {L : ℝ} (hL : 2 ≤ L)
    (hA : IsAmicable (p * m) n') (hmN : m ≤ N) (hn' : 0 < n') (hnN : n' ≤ N)
    (hP : p.Prime) (hpm : ¬p ∣ m) (hp : L ^ 2 < (p : ℝ))
    (hpp' : p' < p) (hp' : p' = n'.maxPrimeFac)
    (hs : ∀ d : ℕ, d ∣ n' → 0 < d →
      (∀ q ∈ d.primeFactors, d.factorization q ≠ 1) → (d : ℝ) ≤ L^2)
    (hc : ∀ r : ℕ, r.Prime → r ∣ p*m → r ∣ n' → (r : ℝ) ≤ L/2)
    (d a : ℕ) (ha : Squarefree a) (hm : m = d * a) (hda : d.Coprime a)
    (hbad : σ 1 a ∉ (⌊L⌋₊ + 1).smoothNumbers) :
    ∃ r ∈ (N + 1).primesLE, L < (r : ℝ) ∧ ∃ q ∈ N.primesLE, r ∣ q + 1 ∧
      ∃ j ∈ Icc 1 (Nat.log 2 N), ∃ l ∈ N.primesLE,
        r ∣ σ 1 (l ^ j) ∧ ∃ g ∈ (l ^ j).divisors, finalCondition (p*m) q (l ^ j) g := by
  have hs₀ := sigma_pos 1 a ha.ne_zero
  rw [Nat.mem_smoothNumbers'] at hbad
  push Not at hbad
  obtain ⟨r, hr, hra, hrL⟩ := hbad
  have hrL' : L < (r : ℝ) := by exact (Nat.floor_lt (by linarith)).mp (by omega)
  obtain ⟨q, hq, hrq⟩ := prime_dvd_sigma_prime_power hr ha.ne_zero hra
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hqm : q ∣ m := hm ▸ hqd.trans (dvd_mul_left a d)
  have he : a.factorization q = 1 := by
    have h₁ := hqP.factorization_pos_of_dvd ha.ne_zero hqd
    have h₂ := (Nat.squarefree_iff_factorization_le_one ha.ne_zero).mp ha q
    omega
  rw [he, pow_one] at hrq
  have hsigq : σ 1 q = q + 1 := by simpa using sigma_prime_mul hqP (m := 1) hqP.not_dvd_one
  rw [hsigq] at hrq
  have hqL : L/2 < (q : ℝ) := by
    have h := Nat.le_of_dvd (Nat.succ_pos q) hrq
    have h' : (r : ℝ) ≤ q + 1 := by exact_mod_cast h
    linarith
  have hm₀ : 0 < m := Nat.pos_of_ne_zero fun he => hpm (he ▸ dvd_zero p)
  have hqN := (Nat.le_of_dvd hm₀ hqm).trans hmN
  have hrN := (Nat.le_of_dvd (Nat.succ_pos q) hrq)
  have hrdσm : r ∣ σ 1 m := by
    rw [hm, isMultiplicative_sigma.map_mul_of_coprime hda]
    exact dvd_mul_of_dvd_right hra _
  have hrdσn' : r ∣ σ 1 n' := by
    rw [hA.right, ← hA.left, sigma_prime_mul hP hpm]
    exact dvd_mul_of_dvd_right hrdσm _
  obtain ⟨l, hl, hrl⟩ := prime_dvd_sigma_prime_power hr hn'.ne' hrdσn'
  have hlP := Nat.prime_of_mem_primeFactors hl
  have hld := Nat.dvd_of_mem_primeFactors hl
  have hne : q ≠ l := by
    intro h
    exact (not_le_of_gt hqL) (hc q hqP (hqm.trans (dvd_mul_left _ _)) (h.symm ▸ hld))
  obtain ⟨hlN, hj, hjd⟩ := pow_eq_primePower_data hn' hnN hl
  have hrN' : r ≤ N + 1 := hrN.trans (Nat.succ_le_succ hqN)
  refine ⟨r, Nat.mem_primesLE.mpr ⟨hrN', hr⟩, hrL', q, Nat.mem_primesLE.mpr ⟨hqN,hqP⟩,
    hrq, n'.factorization l, hj, l, hlN, hrl, ?_⟩
  apply final_condition_of_pair hP hpm hA hqP hqm hlP hne hjd
  by_cases h1 : n'.factorization l = 1
  · rw [h1,pow_one]
    exact (Nat.le_maxPrimeFac hn'.ne' hlP hld).trans (hp' ▸ hpp'.le)
  · have hpow : (l ^ n'.factorization l : ℕ) ≤ L^2 := by
      apply hs _ hjd (pow_pos hlP.pos _)
      intro u hu
      have huP := Nat.prime_of_mem_primeFactors hu
      have hule := Nat.dvd_of_mem_primeFactors hu
      have huEq := (Nat.prime_dvd_prime_iff_eq huP hlP).mp (huP.dvd_of_dvd_pow hule)
      subst u
      rwa [Nat.factorization_pow_self hlP]
    exact_mod_cast ((hpow.trans hp.le) : ((l ^ n'.factorization l : ℕ) : ℝ) ≤ p)

private theorem squarefull_count_bound {N : ℕ} {Y s : ℝ} (hY : 0 < Y) (hs : 1/2 < s) (hs₁ : s ≤ 1)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ ∃ d : ℕ, d ∣ n ∧ 0 < d ∧ Y < (d : ℝ) ∧
        ∀ p ∈ d.primeFactors, d.factorization p ≠ 1) :
    (S.card : ℝ) ≤ (N : ℝ) * (Y ^ (s - 1) * ((1 + 1 / (2 * s - 1)) * (1 + 1 / (3 * s - 1)))) := by
  classical
  let D := (Icc 1 N).filter (fun d : ℕ => Y < (d : ℝ) ∧ ∀ p ∈ d.primeFactors, d.factorization p ≠ 1)
  have hh := count_has_divisor D S (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1) (by
    intro n hn
    obtain ⟨hn0, hnN, d, hd, hd0, hdY, hsquare⟩ := hS n hn
    exact ⟨hn0, hnN, d, mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,
      (Nat.le_of_dvd hn0 hd).trans hnN⟩, hdY, hsquare⟩, hd⟩)
  exact hh.trans (mul_le_mul_of_nonneg_left (sum_squarefull_recip_tail hY hs hs₁) (by positivity))

private theorem count_shifted_part {N K : ℕ} {X U rate : ℝ} (hX : 0 < X) (hU : 0 < U)
    (hrate : 0 ≤ rate) (S : Finset ℕ)
    (hBound : ∀ z ≥ X / U, z ≤ X → ∀ T : Finset ℕ,
      (∀ a ∈ T, Squarefree a ∧ (a : ℝ) ≤ z ∧ σ 1 a ∈ K.smoothNumbers) → (T.card : ℝ) ≤ z * rate)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ (n : ℝ) ≤ X ∧
      ∃ p d a : ℕ, 0 < p ∧ 0 < d ∧ (p : ℝ) * d ≤ U ∧ Squarefree a ∧ σ 1 a ∈ K.smoothNumbers ∧ n = p*d*a) :
    (S.card : ℝ) ≤ X * rate * (1 + log N)^2 := by
  classical
  let C : Finset (ℕ × ℕ) := (Icc 1 N ×ˢ Icc 1 N).filter (fun z => (z.1 : ℝ) * z.2 ≤ U)
  let F (pd : ℕ × ℕ) := S.filter (fun n => ∃ a : ℕ, Squarefree a ∧ σ 1 a ∈ K.smoothNumbers ∧ n = pd.1*pd.2*a)
  let w (pd : ℕ × ℕ) : ℝ := X * rate * ((pd.1 : ℝ)⁻¹ * (pd.2 : ℝ)⁻¹)
  have hC : ∀ n ∈ S, ∃ pd ∈ C, n ∈ F pd := by
    intro n hn
    obtain ⟨_, hnN, _, p, d, a, hp, hd, hpd, ha, haS, hE⟩ := hS n hn
    have hpN : p ≤ N := by
      have hn0 := (hS n hn).1
      apply (Nat.le_of_dvd hn0 ?_).trans hnN
      rw [hE]
      exact (dvd_mul_right p d).trans (dvd_mul_right (p*d) a)
    have hdN : d ≤ N := by
      have hn0 := (hS n hn).1
      apply (Nat.le_of_dvd hn0 ?_).trans hnN
      rw [hE]
      exact (dvd_mul_left d p).trans (dvd_mul_right (p*d) a)
    exact ⟨(p,d),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hp,hpN⟩,
      mem_Icc.mpr ⟨hd,hdN⟩⟩,hpd⟩,mem_filter.mpr ⟨hn,a,ha,haS,hE⟩⟩
  have hf : ∀ pd ∈ C, ((F pd).card : ℝ) ≤ w pd := by
    intro pd hpd
    obtain ⟨hpd, hpU⟩ := mem_filter.mp hpd
    obtain ⟨hp, hd⟩ := mem_product.mp hpd
    let k := pd.1 * pd.2
    have hk : 0 < k := mul_pos (mem_Icc.mp hp).1 (mem_Icc.mp hd).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkU : (k : ℝ) ≤ U := by simpa [k] using hpU
    let f (n : ℕ) := n / k
    have hspec (n) (hn : n ∈ F pd) : Squarefree (f n) ∧ σ 1 (f n) ∈ K.smoothNumbers ∧ n = k * f n := by
      obtain ⟨_,a,ha,hσ,he⟩ := mem_filter.mp hn
      have hfa : f n = a := by
        change n / k = a
        change n = k * a at he
        rw [he, Nat.mul_div_cancel_left _ hk]
      rw [hfa]
      exact ⟨ha,hσ,he⟩
    have hinj : Set.InjOn f (F pd) := by
      intro n hn n' hn' he
      exact (hspec n hn).2.2.trans (he ▸ (hspec n' hn').2.2.symm)
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k from hk)
    have h := hBound (X / k) (div_le_div_of_nonneg_left hX.le hkR hkU)
      (div_le_self hX.le hk₁) ((F pd).image f) (by
      intro a ha
      obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
      obtain ⟨hsf,hσ,hnk⟩ := hspec n hn
      have hnX := (hS n (mem_filter.mp hn).1).2.2.1
      have hh : (n : ℝ) = (k : ℝ) * (f n : ℝ) := by exact_mod_cast hnk
      refine ⟨hsf,(le_div_iff₀ hkR).mpr ?_,hσ⟩
      linarith only [hh,hnX])
    rw [card_image_of_injOn hinj] at h
    exact h.trans_eq (by simp only [w,k,Nat.cast_mul]; ring)
  have h := card_of_cover S C F w hC hf
  have hmono : ∑ pd ∈ C, w pd ≤ ∑ pd ∈ Icc 1 N ×ˢ Icc 1 N, w pd :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by unfold w; positivity)
  have hlast : (∑ pd ∈ Icc 1 N ×ˢ Icc 1 N, w pd) =
      X * rate * (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹)^2 := by
    rw [show (∑ pd ∈ Icc 1 N ×ˢ Icc 1 N, w pd) =
      X * rate * ∑ pd ∈ Icc 1 N ×ˢ Icc 1 N, (pd.1 : ℝ)⁻¹ * (pd.2 : ℝ)⁻¹ by rw [mul_sum]]
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  have hh := harmonic_bound_finset (Icc 1 N) Subset.rfl
  rw [hlast] at hmono
  exact h.trans (hmono.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)))

private theorem card_le_list_biUnion {α : Type*} [DecidableEq α] (F : List (Finset α)) :
    (F.foldr (· ∪ ·) ∅).card ≤ (F.map Finset.card).sum := by
  induction F with
  | nil => simp
  | cons a F ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (card_union_le a (F.foldr (· ∪ ·) ∅)).trans (Nat.add_le_add_left ih _)

private theorem mem_list_biUnion {α : Type*} [DecidableEq α] (F : List (Finset α)) {x : α} :
    x ∈ F.foldr (· ∪ ·) ∅ ↔ ∃ T ∈ F, x ∈ T := by
  induction F with
  | nil => simp
  | cons a F ih => simp [ih, or_and_right, exists_or, and_assoc]

private theorem card_le_symmetric_cover (S : Finset (ℕ × ℕ)) (F : List (Finset (ℕ × ℕ)))
    (hS : ∀ z ∈ S, ∃ T ∈ F, z ∈ T ∨ z.swap ∈ T) :
    (S.card : ℝ) ≤ 2 * ((F.map Finset.card).sum : ℕ) := by
  let B := F.foldr (· ∪ ·) ∅
  let sw : ℕ × ℕ ↪ ℕ × ℕ := (Equiv.prodComm ℕ ℕ).toEmbedding
  have hsub : S ⊆ B ∪ B.map sw := by
    intro z hz
    obtain ⟨T,hT,hz'|hz'⟩ := hS z hz
    · exact mem_union.mpr (Or.inl ((mem_list_biUnion F).mpr ⟨T,hT,hz'⟩))
    · apply mem_union.mpr ∘ Or.inr
      exact mem_map.mpr ⟨z.swap, (mem_list_biUnion F).mpr ⟨T,hT,hz'⟩, by cases z; rfl⟩
  have hcnt : S.card ≤ 2 * (F.map Finset.card).sum := by
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_map] at hh
    have hb := card_le_list_biUnion F
    change B.card ≤ (F.map Finset.card).sum at hb
    omega
  exact_mod_cast hcnt

private def commonSmall (L : ℝ) (z : ℕ × ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ z.1 → r ∣ z.2 → (r : ℝ) ≤ L/2

private def cofactorCase (N : ℕ) (X L : ℝ) (z : ℕ × ℕ) : Prop :=
  ∃ p q m n : ℕ, p.Prime ∧ q.Prime ∧ ¬ p ∣ m ∧ ¬ q ∣ n ∧
    z = (p*m, q*n) ∧ z.1 ≤ N ∧ IsAmicable z.1 z.2 ∧ (m : ℝ)*n ≤ X/L

private def largeCase (X L : ℝ) (z : ℕ × ℕ) : Prop :=
  ∃ p m d M : ℕ, p.Prime ∧ ¬ p ∣ m ∧ (m : ℝ) ≤ X ^ (1/4 : ℝ)/L ∧
    √X < (d : ℝ) ∧ (d : ℝ) ≤ X ^ (3/4 : ℝ) ∧ d.Coprime M ∧ (σ 1 d).Coprime d ∧
    z = (p*m,d*M)

private def shiftedCase (X L : ℝ) (n : ℕ) : Prop :=
  ∃ p d a : ℕ, 0 < p ∧ 0 < d ∧ (p : ℝ) * d ≤ X ^ (3/4 : ℝ)*L^3 ∧
    Squarefree a ∧ σ 1 a ∈ (⌊L⌋₊ + 1).smoothNumbers ∧ n = p*d*a

private def regularCase (N : ℕ) (L : ℝ) (n : ℕ) : Prop :=
  ∃ r ∈ (N+1).primesLE, L < (r : ℝ) ∧ ∃ q ∈ N.primesLE, r ∣ q+1 ∧
    ∃ j ∈ Icc 1 (Nat.log 2 N), ∃ l ∈ N.primesLE,
      r ∣ σ 1 (l^j) ∧ ∃ g ∈ (l^j).divisors, finalCondition n q (l^j) g

set_option maxHeartbeats 1250000 in
private theorem classify_oriented {N : ℕ} {X L : ℝ} (hX : 1 ≤ X) (hL : 2 ≤ L)
    (hXL : X ^ (1 / 3 : ℝ) < X / L)
    (hStrong : X ^ (1 / 3 : ℝ) * √X ≤ X / L)
    (z : ℕ × ℕ) (h₁ : z.1 ≤ N) (h₂ : z.2 ≤ N) (hNX : (N : ℝ) ≤ X)
    (hA : IsAmicable z.1 z.2) (hG₁ : GoodSide X L z.1) (hG₂ : GoodSide X L z.2)
    (hC : commonSmall L z) (hOrder : z.2.maxPrimeFac < z.1.maxPrimeFac) :
    cofactorCase N X L z ∨ largeCase X L z ∨ shiftedCase X L z.1 ∨ regularCase N L z.1 := by
  obtain ⟨hp, hpL, hpE, hpm⟩ := good_side_decompose hX hXL hG₁
  obtain ⟨hq, hqL, hqE, hqn⟩ := good_side_decompose hX hXL hG₂
  let p := z.1.maxPrimeFac
  let q := z.2.maxPrimeFac
  let m := z.1 / p
  let n := z.2 / q
  change z.1 = p*m at hpE
  change z.2 = q*n at hqE
  change ¬p ∣ m at hpm
  change ¬q ∣ n at hqn
  change L^2 < (p : ℝ) at hpL
  change L^2 < (q : ℝ) at hqL
  have hz : z = (p*m,q*n) := Prod.ext hpE hqE
  by_cases hsmall : (m : ℝ)*n ≤ X/L
  · exact Or.inl ⟨p,q,m,n,hp,hq,hpm,hqn,hz,h₁,hA,hsmall⟩
  have hL0 : 0 < L := by linarith
  have hX0 : 0 < X := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpf : (p : ℝ) * m ≤ X := by
    have he : (z.1 : ℝ) = (p : ℝ)*m := by exact_mod_cast hpE
    rw [← he]; exact (by exact_mod_cast h₁ : (z.1 : ℝ) ≤ N).trans hNX
  have hqf : (q : ℝ) * n ≤ X := by
    have he : (z.2 : ℝ) = (q : ℝ)*n := by exact_mod_cast hqE
    rw [← he]; exact (by exact_mod_cast h₂ : (z.2 : ℝ) ≤ N).trans hNX
  have hpow : X ^ (1/4 : ℝ) * X ^ (3/4 : ℝ) = X := by
    rw [← Real.rpow_add hX0, show (1/4 : ℝ) + 3/4 = 1 by norm_num, Real.rpow_one]
  have hpow₁ : √X * X ^ (1/4 : ℝ) = X ^ (3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    congr 1
    norm_num
  by_cases hlarge : X ^ (3/4 : ℝ)*L < (p : ℝ)
  · right; left
    have hM : (m : ℝ) ≤ X ^ (1/4 : ℝ)/L := by
      rw [le_div_iff₀ hL0]
      apply le_of_mul_le_mul_left _ (show (0 : ℝ) < X ^ (3/4 : ℝ) by positivity)
      calc
        X ^ (3/4 : ℝ) * ((m : ℝ)*L) = (X ^ (3/4 : ℝ)*L) * m := by ring
        _ ≤ (p : ℝ)*m := mul_le_mul_of_nonneg_right hlarge.le (by positivity)
        _ ≤ X := hpf
        _ = X ^ (3/4 : ℝ)*X ^ (1/4 : ℝ) := by rw [mul_comm, hpow]
    have hn : X ^ (3/4 : ℝ) < (n : ℝ) := by
      by_contra! h
      have hle := mul_le_mul hM h (by positivity : (0 : ℝ) ≤ n) (by positivity)
      have he : X ^ (1/4 : ℝ)/L * X ^ (3/4 : ℝ) = X/L := by rw [div_mul_eq_mul_div, hpow]
      exact hsmall (hle.trans_eq he)
    have hQ : (q : ℝ) ≤ X ^ (1/4 : ℝ) := by
      apply le_of_mul_le_mul_right _ (show (0 : ℝ) < X ^ (3/4 : ℝ) by positivity)
      exact (mul_le_mul_of_nonneg_left hn.le hq0.le).trans (hqf.trans_eq hpow.symm)
    obtain ⟨d,M,hdE,hdM,hdL,hdU,hdP⟩ := good_side_large_unitary hX hStrong hG₂
    have hC' (r : ℕ) (hr : r.Prime) (hrd : r ∣ d) : ¬ r ∣ z.1 := by
      intro hr1
      have hr2 : r ∣ z.2 := hdE ▸ hrd.trans (dvd_mul_right d M)
      have hc := hC r hr hr1 hr2
      nlinarith [hdP r hr hrd]
    have hσ := amicable_unitary_coprime_sigma hA hdE hdM hC'
    exact ⟨p,m,d,M,hp,hpm,hM,hdL,hdU.trans (by rw [← hpow₁]; exact mul_le_mul_of_nonneg_left hQ (by positivity)),
      hdM,hσ,Prod.ext hpE hdE⟩
  · have hmp : 0 < m := Nat.pos_of_ne_zero (fun h => hpm (h ▸ dvd_zero p))
    obtain ⟨d,a,hd,ha,hdE,hdC,haS,hdS⟩ := squarefree_part_properties hmp.ne'
    have hdDiv : d ∣ z.1 := by rw [hpE,hdE]; exact (dvd_mul_right d a).trans (dvd_mul_left _ _)
    have hdu : (d : ℝ) ≤ L^2 := hG₁.squarefull d hdDiv hd hdS
    by_cases hsa : σ 1 a ∈ (⌊L⌋₊+1).smoothNumbers
    · exact Or.inr (Or.inr (Or.inl ⟨p,d,a,hp.pos,hd,by
        have ht := mul_le_mul (le_of_not_gt hlarge) hdu (by positivity) (by positivity)
        exact ht.trans_eq (by ring),haS,hsa,by rw [hpE,hdE]; ring⟩))
    · right; right; right
      have hmN : m ≤ N := by rw [hpE] at h₁; exact (Nat.le_mul_of_pos_left _ hp.pos).trans h₁
      have hn'0 : 0 < z.2 := by
        have h0 : (0 : ℝ) < z.2 := (div_pos hX0 hL0).trans hG₂.size
        exact_mod_cast h0
      have hAA : IsAmicable (p*m) z.2 := by simpa only [hpE] using hA
      rw [hpE]
      exact regular_witness hL hAA hmN hn'0 h₂ hp hpm hpL hOrder rfl hG₂.squarefull
        (fun r hr hr₁ hr₂ => hC r hr (hpE ▸ hr₁) hr₂) d a haS hdE hdC hsa

private theorem project_pair_bound (S : Finset (ℕ × ℕ)) (b : ℝ)
    (hA : ∀ z ∈ S, IsAmicable z.1 z.2)
    (hB : ∀ T : Finset ℕ, (∀ n ∈ T, ∃ z ∈ S, z.1 = n) → (T.card : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b := by
  apply le_trans _ (hB (S.image Prod.fst) (fun _ => mem_image.mp))
  exact_mod_cast pair_card_projection S (S.image Prod.fst)
    (fun z hz => ⟨hA z hz, mem_image_of_mem _ hz⟩)

private theorem count_cover_primes {N : ℕ} {Y C : ℝ} (hY : 0 < Y) (hC : 0 ≤ C)
    (S : Finset ℕ) (R : ℕ → ℕ → Prop)
    (hCover : ∀ n ∈ S, ∃ r ∈ N.primesLE, Y < (r : ℝ) ∧ R n r)
    (hB : ∀ r : ℕ, r.Prime → Y < (r : ℝ) → ∀ T : Finset ℕ,
      (∀ n ∈ T, n ∈ S ∧ R n r) → (T.card : ℝ) ≤ C * ((r : ℝ) ^ 2)⁻¹) :
    (S.card : ℝ) ≤ C * (2 / Y) := by
  classical
  let T := N.primesLE.filter (fun r : ℕ => Y < (r : ℝ))
  have h := card_of_cover S T (fun r => S.filter fun n => R n r) (fun r => C * ((r : ℝ)^2)⁻¹) (by
    intro n hn
    obtain ⟨r,hr,hy,hrn⟩ := hCover n hn
    exact ⟨r,mem_filter.mpr ⟨hr,hy⟩,mem_filter.mpr ⟨hn,hrn⟩⟩) (by
    intro r hr
    exact hB r (Nat.mem_primesLE.mp (mem_filter.mp hr).1).2 (mem_filter.mp hr).2 _
      (fun n h => mem_filter.mp h))
  rw [← mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left (recip_square_tail hY (N := N) fun r hr =>
    ⟨(mem_filter.mp hr).2,(Nat.mem_primesLE.mp (mem_filter.mp hr).1).1⟩) hC)

private noncomputable def countBudget (X L t s rate : ℝ) : ℝ :=
  let N := ⌊X⌋₊
  let H := 1 + log (N : ℝ)
  let J := (Nat.log 2 N : ℝ) + 1
  let B := X ^ (1/4 : ℝ)/L
  let U := X ^ (3/4 : ℝ)
  2 * (X/L + (N : ℝ) * ((X ^ (1/3 : ℝ)) ^ (-t) * smoothEuler (⌊L^2⌋₊ + 1) (1-t)) +
    (N : ℝ) * ((L^2) ^ (s - 1) * ((1 + 1/(2*s-1)) * (1 + 1/(3*s-1)))) +
    ((N : ℝ) * J^2 * (3 + log (N : ℝ))) * (2 / (L/2)) + (X/L)*H +
    (B*U + (N : ℝ)*B^2*H*(2/√X)) + X*rate*H^2 +
    (4*(N : ℝ)*H*(1 + log (N+1 : ℕ))*J^3*(3 + log (N : ℝ))) * (2/L))

set_option maxHeartbeats 4000000 in
private theorem finite_amicable_bound {X L t s rate : ℝ} (hX : 1 ≤ X) (hL : 2 ≤ L)
    (hXL : X ^ (1 / 3 : ℝ) < X/L) (hLong : X ^ (1/3 : ℝ)*√X ≤ X/L)
    (hB : X ^ (1/4 : ℝ)/L ≤ (⌊X⌋₊ : ℝ))
    (ht : 0 ≤ t) (ht' : t < 1) (hs : 1/2 < s) (hs' : s ≤ 1) (hrate : 0 ≤ rate)
    (hUniform : ∀ z ≥ X/(X^(3/4 : ℝ)*L^3), z ≤ X → ∀ T : Finset ℕ,
      (∀ a ∈ T, Squarefree a ∧ (a : ℝ) ≤ z ∧ σ 1 a ∈ (⌊L⌋₊ + 1).smoothNumbers) → (T.card : ℝ) ≤ z*rate) :
    Erdos830.A X ≤ countBudget X L t s rate := by
  classical
  let N := ⌊X⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hX)
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := by linarith
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  let P := (Icc 1 N ×ˢ Icc 1 N).filter fun z : ℕ × ℕ => IsAmicable z.1 z.2
  have hP (z) (hz : z ∈ P) : 0 < z.1 ∧ z.1 ≤ N ∧ 0 < z.2 ∧ z.2 ≤ N ∧ IsAmicable z.1 z.2 := by
    obtain ⟨hs,hA⟩ := mem_filter.mp hz
    exact ⟨(mem_Icc.mp (mem_product.mp hs).1).1,(mem_Icc.mp (mem_product.mp hs).1).2,
      (mem_Icc.mp (mem_product.mp hs).2).1,(mem_Icc.mp (mem_product.mp hs).2).2,hA⟩
  have hswap (z) (hz : z ∈ P) : z.swap ∈ P := by
    obtain ⟨ha,haN,hb,hbN,hA⟩ := hP z hz
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hb,hbN⟩,mem_Icc.mpr ⟨ha,haN⟩⟩,amicable_symm hA⟩
  let small := P.filter fun z : ℕ × ℕ => (z.1 : ℝ) ≤ X/L
  let smooth := P.filter fun z => ∃ d : ℕ, d ∣ z.1 ∧ d ∈ (⌊L^2⌋₊ + 1).smoothNumbers ∧ X^(1/3 : ℝ) < (d : ℝ)
  let squarefull := P.filter fun z => ∃ d : ℕ, d ∣ z.1 ∧ 0 < d ∧ L^2 < (d : ℝ) ∧
    ∀ p ∈ d.primeFactors, d.factorization p ≠ 1
  let shared := P.filter fun z => ¬ commonSmall L z
  let cof := P.filter (cofactorCase N X L)
  let large := P.filter (largeCase X L)
  let shifted := P.filter fun z => shiftedCase X L z.1
  let regular := P.filter fun z => regularCase N L z.1
  let f := [small,smooth,squarefull,shared,cof,large,shifted,regular]
  have cover : ∀ z ∈ P, ∃ T ∈ f, z ∈ T ∨ z.swap ∈ T := by
    intro z hz
    by_cases hz₁ : GoodSide X L z.1
    · by_cases hz₂ : GoodSide X L z.2
      · by_cases hc : commonSmall L z
        · have hneq : z.1.maxPrimeFac ≠ z.2.maxPrimeFac := by
            intro he
            have hp := good_side_decompose hX hXL hz₁
            have hdiv : z.1.maxPrimeFac ∣ z.2 := he.symm ▸ Nat.maxPrimeFac_dvd
            have hle := hc _ hp.1 Nat.maxPrimeFac_dvd hdiv
            nlinarith [hp.2.1]
          have hOr (v : ℕ × ℕ) (hv : v ∈ P)
              (h : cofactorCase N X L v ∨ largeCase X L v ∨ shiftedCase X L v.1 ∨ regularCase N L v.1) :
              ∃ T ∈ f, v ∈ T := by
            rcases h with h|h|h|h
            · exact ⟨cof, by simp [f], mem_filter.mpr ⟨hv,h⟩⟩
            · exact ⟨large, by simp [f], mem_filter.mpr ⟨hv,h⟩⟩
            · exact ⟨shifted, by simp [f], mem_filter.mpr ⟨hv,h⟩⟩
            · exact ⟨regular, by simp [f], mem_filter.mpr ⟨hv,h⟩⟩
          obtain ⟨_,hn,_,hm,hA⟩ := hP z hz
          rcases lt_or_gt_of_ne hneq with hlt | hgt
          · obtain ⟨T,hTf,hTs⟩ := hOr z.swap (hswap z hz)
              (classify_oriented hX hL hXL hLong z.swap hm hn hNX (amicable_symm hA) hz₂ hz₁
                (fun r hr hr₁ hr₂ => hc r hr hr₂ hr₁) hlt)
            exact ⟨T,hTf,Or.inr hTs⟩
          · obtain ⟨T,hTf,hTs⟩ := hOr z hz (classify_oriented hX hL hXL hLong z hn hm hNX hA hz₁ hz₂ hc hgt)
            exact ⟨T,hTf,Or.inl hTs⟩
        · exact ⟨shared, by simp [f], Or.inl (mem_filter.mpr ⟨hz,hc⟩)⟩
      · have bad (v : ℕ × ℕ) (hv : v ∈ P) (hg : ¬ GoodSide X L v.1) :
            ∃ T ∈ f, v ∈ T := by
          by_cases hsz : X/L < (v.1 : ℝ)
          · by_cases hsmooth : ∀ d : ℕ, d ∣ v.1 → d ∈ (⌊L^2⌋₊+1).smoothNumbers → (d : ℝ) ≤ X^(1/3 : ℝ)
            · have hsquare : ¬ ∀ d : ℕ, d ∣ v.1 → 0 < d →
                  (∀ p ∈ d.primeFactors, d.factorization p ≠ 1) → (d : ℝ) ≤ L^2 :=
                fun h => hg ⟨hsz,hsmooth,h⟩
              push Not at hsquare
              obtain ⟨d,hd,hd0,hdS,hdL⟩ := hsquare
              exact ⟨squarefull,by simp [f],mem_filter.mpr ⟨hv,d,hd,hd0,hdL,hdS⟩⟩
            · push Not at hsmooth
              exact ⟨smooth,by simp [f],mem_filter.mpr ⟨hv,hsmooth⟩⟩
          · exact ⟨small,by simp [f],mem_filter.mpr ⟨hv,le_of_not_gt hsz⟩⟩
        obtain ⟨T,hTf,hTv⟩ := bad z.swap (hswap z hz) hz₂
        exact ⟨T,hTf,Or.inr hTv⟩
    · by_cases hsz : X/L < (z.1 : ℝ)
      · by_cases hsmooth : ∀ d : ℕ, d ∣ z.1 → d ∈ (⌊L^2⌋₊+1).smoothNumbers → (d : ℝ) ≤ X^(1/3 : ℝ)
        · have hsquare : ¬ ∀ d : ℕ, d ∣ z.1 → 0 < d →
              (∀ p ∈ d.primeFactors, d.factorization p ≠ 1) → (d : ℝ) ≤ L^2 := fun h => hz₁ ⟨hsz,hsmooth,h⟩
          push Not at hsquare
          obtain ⟨d,hd,hd0,hdS,hdL⟩ := hsquare
          exact ⟨squarefull,by simp [f],Or.inl (mem_filter.mpr ⟨hz,d,hd,hd0,hdL,hdS⟩)⟩
        · push Not at hsmooth
          exact ⟨smooth,by simp [f],Or.inl (mem_filter.mpr ⟨hz,hsmooth⟩)⟩
      · exact ⟨small,by simp [f],Or.inl (mem_filter.mpr ⟨hz,le_of_not_gt hsz⟩)⟩
  have hAterm : Erdos830.A X ≤ (P.card : ℝ) := by
    apply Nat.cast_le.mpr (card_le_card _)
    intro z hz
    obtain ⟨ha,_,hb⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨ha,hb⟩
  have hm : (small.card : ℝ) ≤ X/L := by
    exact project_pair_bound _ _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT => by
      have hsub : T ⊆ Icc 1 ⌊X/L⌋₊ := by
        intro n hn
        obtain ⟨z,hz,rfl⟩ := hT n hn
        exact mem_Icc.mpr ⟨(hP z (mem_filter.mp hz).1).1,Nat.le_floor (mem_filter.mp hz).2⟩
      have hcard := card_le_card hsub
      simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
      exact (show (T.card : ℝ) ≤ ⌊X/L⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le (by positivity)))
  have hsm := project_pair_bound smooth _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT =>
    count_large_smooth_divisor (by positivity : 0 < X^(1/3 : ℝ)) ht ht' T (N := N) (by
      intro n hn
      obtain ⟨z,hz,rfl⟩ := hT n hn
      have hh := hP z (mem_filter.mp hz).1
      exact ⟨hh.1,hh.2.1,(mem_filter.mp hz).2⟩))
  have hsq := project_pair_bound squarefull _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT =>
    squarefull_count_bound (by positivity : 0 < L^2) hs hs' T (N := N) (by
      intro n hn
      obtain ⟨z,hz,rfl⟩ := hT n hn
      have hh := hP z (mem_filter.mp hz).1
      exact ⟨hh.1,hh.2.1,(mem_filter.mp hz).2⟩))
  have hlog : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog' : 0 ≤ log (N+1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos N)
  let C : ℝ := (N : ℝ) * (((Nat.log 2 N : ℕ) + 1 : ℝ)^2 * (3+log N))
  have hsh := project_pair_bound shared _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT =>
    count_cover_primes (show 0 < L/2 by positivity) (show 0 ≤ C by dsimp [C]; positivity) T
      (fun n r => r ∣ n ∧ r ∣ σ 1 n) (N := N) (by
        intro n hn
        obtain ⟨z,hz,rfl⟩ := hT n hn
        have ht := (mem_filter.mp hz).2
        unfold commonSmall at ht
        push Not at ht
        obtain ⟨r,hr,hr₁,hr₂,hrL⟩ := ht
        have hdata := hP z (mem_filter.mp hz).1
        exact ⟨r,Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hdata.1 hr₁).trans hdata.2.1,hr⟩,
          hrL,hr₁,hdata.2.2.2.2.left ▸ Nat.dvd_add hr₁ hr₂⟩) (by
        intro r hr _ V hV
        apply (count_sigma_shared_prime hN hr V (by
          intro n hn
          obtain ⟨z,hz,rfl⟩ := hT _ (hV n hn).1
          have hh := hP z (mem_filter.mp hz).1
          exact ⟨hh.1,hh.2.1,(hV z.1 hn).2⟩)).trans_eq
        dsimp [C]; ring))
  have hcof := count_small_cofactors (by positivity : 0 ≤ X/L) cof
    (fun z hz => (mem_filter.mp hz).2)
  have hlg := count_amicable_large_prime hN (by positivity : 0 ≤ X^(1/4 : ℝ)/L)
    (by positivity : 0 ≤ X^(3/4 : ℝ)) (by positivity : 0 < √X) hB large (by
      intro z hz
      have hh := hP z (mem_filter.mp hz).1
      exact ⟨hh.2.2.2.2,hh.2.2.2.1,(mem_filter.mp hz).2⟩)
  have hshift := project_pair_bound shifted _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT =>
    count_shifted_part hX0 (by positivity : 0 < X^(3/4 : ℝ)*L^3) hrate T hUniform (N := N) (by
      intro n hn
      obtain ⟨z,hz,rfl⟩ := hT n hn
      have hh := hP z (mem_filter.mp hz).1
      exact ⟨hh.1,hh.2.1,(by exact_mod_cast hh.2.1 : (z.1 : ℝ) ≤ N).trans hNX,(mem_filter.mp hz).2⟩))
  let C' : ℝ := 4*(N : ℝ)*(1+log N)*(1+log (N+1 : ℕ))*((Nat.log 2 N : ℕ)+1 : ℝ)^3*(3+log N)
  have hreg := project_pair_bound regular _ (fun z hz => (hP z (mem_filter.mp hz).1).2.2.2.2) (fun T hT =>
    count_cover_primes hL0 (show 0 ≤ C' by dsimp [C']; positivity) T
      (fun n r => ∃ q ∈ N.primesLE, r ∣ q+1 ∧ ∃ j ∈ Icc 1 (Nat.log 2 N), ∃ l ∈ N.primesLE,
        r ∣ σ 1 (l^j) ∧ ∃ g ∈ (l^j).divisors, finalCondition n q (l^j) g) (N := N+1) (by
        intro n hn
        obtain ⟨z,hz,rfl⟩ := hT n hn
        exact (mem_filter.mp hz).2) (by
        intro r hr _ V hV
        apply (count_final_for_prime hN hr V (by
          intro n hn
          obtain ⟨z,hz,rfl⟩ := hT _ (hV n hn).1
          exact ⟨(hP z (mem_filter.mp hz).1).2.1,(hV z.1 hn).2⟩)).trans_eq
        dsimp [C']; ring))
  have hcard := card_le_symmetric_cover P f cover
  simp only [f, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add] at hcard
  apply hAterm.trans (hcard.trans ?_)
  unfold countBudget
  dsimp only [C,C'] at hsh hreg
  dsimp only [N] at *
  linarith only [hm,hsm,hsq,hsh,hcof,hlg,hshift,hreg]

private theorem eventually_rpow_le_exp {c k : ℝ} (hc : 0 < c) (hk : 0 < k) (s C : ℝ) :
    ∀ᶠ b : ℝ in atTop, C * b ^ s ≤ c * exp (k*b) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s k hk).const_mul C
  rw [mul_zero] at h
  filter_upwards [h.eventually (Iio_mem_nhds hc)] with b hb
  change C * (b ^ s * exp (-k*b)) < c at hb
  have hp := exp_pos (k*b)
  apply (div_le_iff₀ hp).mp
  rw [show -k*b = -(k*b) by ring, Real.exp_neg] at hb
  simpa only [div_eq_mul_inv, mul_assoc] using hb.le

private theorem eventually_rpow_lt_rpow {s t : ℝ} (h : s < t) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, b ^ s ≤ c * b ^ t := by
  have h₁ := tendsto_rpow_neg_atTop (sub_pos.mpr h)
  filter_upwards [h₁.eventually (Iio_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with b hb hb0
  change b ^ (-(t-s)) < c at hb
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hb0 t)).mp
  rw [← Real.rpow_sub hb0, show s-t = -(t-s) by ring]
  exact hb.le

private theorem eventually_log_times_rpow_le {s t : ℝ} (h : s < t) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, (3 + log b) * b ^ s ≤ c * b ^ t := by
  let d := (t - s)/2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdiv := (isLittleO_log_rpow_atTop hd).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [hdiv, eventually_ge_atTop (1 : ℝ),
    eventually_rpow_lt_rpow (show s + d < t by dsimp [d]; linarith)
      (show 0 < c / 4 by positivity)] with b hb hb1 hp
  have hb0 : 0 < b := by linarith
  have hlog : 0 ≤ log b := Real.log_nonneg hb1
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity), one_mul] at hb
  have hbD := Real.one_le_rpow hb1 hd.le
  calc
    (3 + log b) * b ^ s ≤ (4 * b ^ d) * b ^ s := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 4 * b ^ (s + d) := by rw [Real.rpow_add hb0]; ring
    _ ≤ c * b ^ t := by linarith only [mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ 4 by norm_num)]

private theorem cutoff_log_bounds {v : ℝ} (hv : 0 ≤ v) :
    v ≤ log ((⌊exp v⌋₊ + 1 : ℕ) : ℝ) ∧ log ((⌊exp v⌋₊ + 1 : ℕ) : ℝ) ≤ v + 1 := by
  have hfloor := Nat.lt_floor_add_one (exp v)
  have hle := Nat.floor_le (exp_nonneg v)
  have hex : 1 ≤ exp v := by simpa using Real.exp_le_exp.mpr hv
  have hh : ((⌊exp v⌋₊ + 1 : ℕ) : ℝ) ≤ exp (v+1) := by
    rw [Real.exp_add, Nat.cast_add, Nat.cast_one]
    have h2 : (2 : ℝ) ≤ exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc (⌊exp v⌋₊ : ℝ)+1 ≤ exp v+1 := by linarith
         _ ≤ exp v*2 := by linarith
         _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hfloor' : exp v < ((⌊exp v⌋₊+1 : ℕ):ℝ) := by exact_mod_cast hfloor
  have hlow := Real.log_le_log (exp_pos v) hfloor'.le
  have hup := Real.log_le_log ((exp_pos v).trans hfloor') hh
  rw [Real.log_exp] at hlow hup
  exact ⟨hlow,hup⟩

private theorem smooth_component_weight {W b c : ℝ} (hW : 0 < W) (hb : 1 ≤ b) (hc : c = log b)
    (hc1 : 1 ≤ c) (hT : 3*c/(2*W) ≤ 1/2) (hW1 : 1 ≤ W)
    (hWdec : 5 + 12*(1+4*c)*b^4 ≤ W / 4) :
    let t := 3*c/(2*W)
    log (smoothEuler (⌊exp (2*W)⌋₊+1) (1-t)) ≤ W := by
  dsimp
  let K := ⌊exp (2*W)⌋₊+1
  let t := 3*c/(2*W)
  have hK2 : 2 ≤ K := by
    dsimp [K]
    have he : (1 : ℝ) ≤ exp (2*W) := by simpa using Real.exp_le_exp.mpr (by positivity : 0 ≤ 2*W)
    have hf : 1 ≤ ⌊exp (2*W)⌋₊ := Nat.le_floor (by simpa using he)
    omega
  have hKlog := cutoff_log_bounds (show 0 ≤ 2*W by positivity)
  change 2*W ≤ log (K : ℝ) ∧ log (K : ℝ) ≤ 2*W+1 at hKlog
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t ≤ 1/2 := hT
  have htc : t*(2*W) = 3*c := by dsimp [t]; field_simp
  have htb : t*log (K : ℝ) ≤ 4*c := by
    have hh := mul_le_mul_of_nonneg_left hKlog.2 ht
    rw [mul_add, htc, mul_one] at hh
    linarith
  have hpow : (K : ℝ)^t ≤ b^4 := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < K), show (b:ℝ)^4 = exp (log b * 4) by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith : 0 < b)]; norm_num]
    apply Real.exp_le_exp.mpr
    linarith
  have hsmall : log (1+log (K : ℝ)) ≤ 3*W/4 := by
    have hh := Real.log_le_rpow_div (show 0 ≤ 1+log (K : ℝ) by linarith [hKlog.1])
      (show (0:ℝ) < 1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    have hp := Real.sq_sqrt (show 0 ≤ 1+log (K : ℝ) by linarith [hKlog.1])
    have hpart : 0 ≤ 12*(1+4*c)*b^4 := by positivity
    have hW20 : 20 ≤ W := by linarith
    have hpow' : √(1+log (K : ℝ)) ≤ 3*W/8 := by
      apply le_of_sq_le_sq _ (by positivity)
      rw [hp]
      nlinarith [mul_nonneg (show 0 ≤ W - 20 by linarith) (show 0 ≤ W by positivity), hKlog.2]
    linarith
  have hlog := smoothEuler_log_le hK2 (show 1/2 ≤ 1-t by linarith) (show 1-t ≤ 1 by linarith)
  rw [sub_sub_cancel] at hlog
  have hextra : 12*(1+t*log (K:ℝ))*(K:ℝ)^t ≤ 12*(1+4*c)*b^4 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) htb) (by norm_num)) hpow
      (by positivity) (by positivity)
  change log (smoothEuler K (1-t)) ≤ W
  linarith only [hlog,hsmall,hextra,hWdec]

set_option maxHeartbeats 2000000 in
private theorem shifted_weight_small {N : ℕ} {δ W b c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/10) (hW : 1 ≤ W) (hb : 1 ≤ b) (hc : c = log b) (hc1 : 1 ≤ c)
    (hct : c/W ≤ 1/2) (hWup : W ≤ exp ((3/4 : ℝ)*b)) (hWlo : exp (b/2)/2 ≤ W)
    (hbExp : b ≤ exp (b/4))
    (hq : b^(1-δ/4) ≤ b/8)
    (hGap : 24*(3+c)*b^(1-δ/2) ≤ δ/4 * b^(1-δ/4))
    (hSmall : 3*(exp 1)^2*b ≤ δ/4 * exp ((3/8 : ℝ)*b))
    (hBig : exp (-(δ/4*b^(1-δ/4))) ≤ δ/12) :
    let K := ⌊exp W⌋₊+1
    let e := 1-(1-δ)*c/W
    ∑ p ∈ N.primesLE.filter (fun p => p+1 ∈ K.smoothNumbers), (p : ℝ)^(-e) ≤ δ*W := by
  dsimp only
  let K := ⌊exp W⌋₊+1
  let B := b^(1-δ/4)
  let V := W/c*B
  let T := ⌊exp V⌋₊+1
  let e := 1-(1-δ)*c/W
  let e' := 1-(1-δ/2)*c/W
  have hW0 : 0 < W := by linarith
  have hc0 : 0 < c := by linarith
  have hb0 : 0 < b := by linarith
  have hB1 : 1 ≤ B := Real.one_le_rpow hb (by linarith)
  have hV : 0 < V := by dsimp [V]; positivity
  have hcut (v : ℝ) (hv : 0 ≤ v) : 2 ≤ ⌊exp v⌋₊+1 := by
    have he : 1 ≤ exp v := by simpa using Real.exp_le_exp.mpr hv
    have hf : 1 ≤ ⌊exp v⌋₊ := Nat.le_floor (by simpa using he)
    omega
  obtain ⟨hK₁,hK₂⟩ := cutoff_log_bounds hW0.le
  obtain ⟨hT₁,hT₂⟩ := cutoff_log_bounds hV.le
  change W ≤ log (K : ℝ) at hK₁
  change log (K : ℝ) ≤ W+1 at hK₂
  change V ≤ log (T : ℝ) at hT₁
  change log (T : ℝ) ≤ V+1 at hT₂
  have hK0 : (0 : ℝ) < K := by positivity
  have hT0 : (0 : ℝ) < T := by positivity
  have heW : (1-e)*W = (1-δ)*c := by dsimp [e]; field_simp; ring
  have heW' : (1-e')*W = (1-δ/2)*c := by dsimp [e']; field_simp; ring
  have hde : e-e' = δ/2*c/W := by dsimp [e,e']; ring
  have hd₁ : 0 ≤ 1-δ := by linarith
  have hd₂ : 0 ≤ 1-δ/2 := by linarith
  have he'₁ : 1/2 ≤ e' := by
    have h : (1-δ/2)*(c/W) ≤ c/W := by
      exact mul_le_of_le_one_left (by positivity) (by linarith)
    dsimp [e']
    rw [mul_div_assoc]
    linarith
  have he'₂ : e' ≤ 1 := by dsimp [e']; exact sub_le_self _ (by positivity)
  have he₁ : 0 ≤ 1-e := by dsimp [e]; rw [sub_sub_cancel]; positivity
  have he₁' : 1-e ≤ 1 := by
    have h : (1-δ)*(c/W) ≤ c/W := mul_le_of_le_one_left (by positivity) (by linarith)
    dsimp [e]; rw [mul_div_assoc]; linarith
  have heord : e' ≤ e := sub_nonneg.mp (by rw [hde]; positivity)
  have hKpow : (K:ℝ)^(1-e') ≤ 2*b^(1-δ/2) := by
    have hprod := mul_le_mul_of_nonneg_left hK₂ (sub_nonneg.mpr he'₂)
    rw [mul_add,heW',mul_one] at hprod
    have hle : log (K:ℝ)*(1-e') ≤ log b*(1-δ/2)+1/2 := by rw [← hc]; nlinarith
    rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hb0]
    apply (Real.exp_le_exp.mpr hle).trans
    rw [Real.exp_add, mul_comm 2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlog2 : (1/2 : ℝ) ≤ log 2 := by
      have hh := Real.log_le_sub_one_of_pos (show (0:ℝ)<1/2 by norm_num)
      have h' : log (1/2:ℝ) = -log 2 := by rw [one_div,Real.log_inv]
      rw [h'] at hh
      linarith
    have hh := Real.exp_le_exp.mpr hlog2
    rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
    exact hh
  have hlogExp : log (smoothEuler K e') ≤ log (1+log (K:ℝ)) + δ/4*B := by
    have hh := smoothEuler_log_le (hcut W hW0.le) he'₁ he'₂
    have hprod := mul_le_mul_of_nonneg_left hK₂ (sub_nonneg.mpr he'₂)
    rw [mul_add,heW',mul_one] at hprod
    have hprod' : 1+(1-e')*log (K:ℝ) ≤ 3+c := by nlinarith
    have hterm : 12*(1+(1-e')*log (K:ℝ))*(K:ℝ)^(1-e') ≤ 24*(3+c)*b^(1-δ/2) := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hprod' (by norm_num : (0:ℝ) ≤ 12)) hKpow (by positivity) (by positivity)
      exact h.trans_eq (by ring)
    exact hh.trans (add_le_add (le_refl _) (hterm.trans hGap))
  have hE : smoothEuler K e' ≤ (1+log (K:ℝ))*exp (δ/4*B) := by
    have h := Real.exp_le_exp.mpr hlogExp
    have h₀ := smoothEuler_pos (N := K) (show 0 < e' by linarith)
    rw [Real.exp_log h₀,Real.exp_add,Real.exp_log (by linarith [hK₁])] at h
    exact h
  have hbig : 2*(T:ℝ)^(-(e-e'))*smoothEuler K e' ≤ δ*W/2 := by
    have hmul : (e-e')*V = δ/2*B := by rw [hde]; dsimp [V]; field_simp
    have hdec := mul_le_mul_of_nonneg_left hT₁ (sub_nonneg.mpr heord)
    rw [hmul] at hdec
    have hd : (T:ℝ)^(-(e-e')) ≤ exp (-(δ/2*B)) := by
      rw [Real.rpow_def_of_pos hT0]
      exact Real.exp_le_exp.mpr (by linarith)
    have hPos : 0 ≤ 1+log (K:ℝ) := by linarith [hK₁]
    calc
      _ ≤ (2*exp (-(δ/2*B)))*((1+log (K:ℝ))*exp (δ/4*B)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hE
          (smoothEuler_pos (show 0 < e' by linarith)).le (by positivity)
      _ = 2*(1+log (K:ℝ))*exp (-(δ/4*B)) := by
        rw [show -(δ/4*B) = -(δ/2*B)+(δ/4*B) by ring, Real.exp_add]
        ring
      _ ≤ 2*(3*W)*(δ/12) := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hK₂,hW]) (by norm_num)) hBig (by positivity) (by positivity)
      _ = _ := by ring
  have hsmall : (T:ℝ)^(1-e)*(exp 1*log (1+log (T:ℝ))) ≤ δ*W/2 := by
    have htV : (1-e)*V = (1-δ)*B := by dsimp [V,e]; field_simp; ring
    have hmul := mul_le_mul_of_nonneg_left hT₂ he₁
    rw [mul_add,htV,mul_one] at hmul
    have htExp : (T:ℝ)^(1-e) ≤ exp (b/8)*exp 1 := by
      rw [Real.rpow_def_of_pos hT0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hδ.le (show 0 ≤ B by linarith)]
    have hVle : V ≤ W*b := by
      have hwc : W/c ≤ W := div_le_self hW0.le hc1
      exact mul_le_mul hwc (by linarith only [hq,hb]) (by linarith) hW0.le
    have hVexp : V ≤ exp b := by
      refine hVle.trans ((mul_le_mul hWup hbExp (by linarith) (by positivity)).trans_eq ?_)
      rw [← Real.exp_add]
      congr 1
      ring
    have hlogT : log (1+log (T:ℝ)) ≤ 3*b := by
      have he : 1 ≤ exp b := by simpa using Real.exp_le_exp.mpr (show 0 ≤ b by linarith)
      have hd : 1+log (T:ℝ) ≤ 3*exp b := by linarith only [hT₂,hVexp,he]
      have hlog := Real.log_le_log (show 0 < 1+log (T:ℝ) by linarith [hT₁]) hd
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
      linarith only [hb,hlog,Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
    calc
      _ ≤ (exp (b/8)*exp 1)*(exp 1*(3*b)) :=
        mul_le_mul htExp (mul_le_mul_of_nonneg_left hlogT (by positivity))
          (mul_nonneg (by positivity) (Real.log_nonneg (by linarith [hT₁,hV]))) (by positivity)
      _ = (3*(exp 1)^2*b)*exp (b/8) := by ring
      _ ≤ (δ/4*exp ((3/8 : ℝ)*b))*exp (b/8) := mul_le_mul_of_nonneg_right hSmall (by positivity)
      _ = δ/4*exp (b/2) := by rw [mul_assoc,← Real.exp_add]; congr 1; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hWlo hδ.le]
  have hh := shifted_prime_weight (N := N) (K := K) (T := T) (hcut V hV.le) (by linarith : 0 < e') heord
    (by linarith : e ≤ 1)
  exact hh.trans (by linarith only [hsmall,hbig])

private theorem logTwo_pos : 0 < log (2:ℝ) := Real.log_pos (by norm_num)

private theorem logNatLog_bound {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ log (N : ℝ) / log 2 := by
  rw [le_div_iff₀ logTwo_pos, ← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)

private noncomputable def pseriesConstant (s : ℝ) : ℝ := (1+1/(2*s-1))*(1+1/(3*s-1))

private noncomputable def logConstant : ℝ := 1 + (log 2)⁻¹

private noncomputable def budgetPolynomial (s A : ℝ) : ℝ :=
  let D := 2 + A
  2 * (3 + pseriesConstant s + 8*logConstant^2*D^3 + 3*D + D^2 + 16*logConstant^3*D^6)

set_option maxHeartbeats 2000000 in
private theorem budget_le_polynomial {X L t s R : ℝ} (hX : 1 ≤ X) (hL : 1 ≤ L)
    (hs : 1/2 < s) (hR : L⁻¹ ≤ R)
    (hsmooth : (X^(1/3:ℝ))^(-t)*smoothEuler (⌊L^2⌋₊+1) (1-t) ≤ L⁻¹)
    (hsquare : (L^2) ^ (s-1) ≤ R) : countBudget X L t s R ≤ X*R*budgetPolynomial s (log X) := by
  let N := ⌊X⌋₊
  let H := 1+log (N:ℝ)
  let D := 2+log X
  let J := (Nat.log 2 N : ℝ)+1
  let c := logConstant
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := by linarith
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hX)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N from hN)
  have hNX : (N:ℝ) ≤ X := Nat.floor_le hX0.le
  have hA0 := Real.log_nonneg hX
  have hlogN : 0 ≤ log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hHD : H ≤ D := by dsimp [H,D]; linarith only [Real.log_le_log hN0 hNX]
  have hlogN1 : 1 + log (N+1 : ℕ) ≤ D := by
    have hNN : ((N+1:ℕ):ℝ) ≤ 2*X := by push_cast; linarith
    have hle := Real.log_le_log (by positivity : (0:ℝ)<(N+1:ℕ)) hNN
    rw [Real.log_mul (by norm_num) hX0.ne'] at hle
    dsimp [D]
    linarith only [hle,Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have h3 : 3 + log (N:ℝ) ≤ 2*D := by dsimp [D]; linarith only [hA0,Real.log_le_log hN0 hNX]
  have hc0 : 0 ≤ c := by dsimp [c,logConstant]; positivity
  have hz : 0 ≤ X*R := mul_nonneg hX0.le ((inv_pos.mpr hL0).le.trans hR)
  have hR0 : 0 ≤ R := (inv_pos.mpr hL0).le.trans hR
  have hJ : J ≤ c*D := by
    have hl := logNatLog_bound hN
    have hh := mul_le_mul_of_nonneg_right (Real.log_le_log hN0 hNX) (inv_nonneg.mpr logTwo_pos.le)
    dsimp [J,c,logConstant,D]
    rw [div_eq_mul_inv] at hl
    nlinarith only [hl,hh,inv_nonneg.mpr logTwo_pos.le,hA0]
  have hNx : (N:ℝ)*R ≤ X*R := mul_le_mul_of_nonneg_right hNX hR0
  have hSmall : X/L ≤ X*R := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hR hX0.le
  have hSm : (N:ℝ)*((X^(1/3:ℝ))^(-t)*smoothEuler (⌊L^2⌋₊+1) (1-t)) ≤ X*R := by
    exact (mul_le_mul_of_nonneg_left (hsmooth.trans hR) hN0.le).trans hNx
  have hcS : 0 ≤ pseriesConstant s := by
    unfold pseriesConstant
    exact mul_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
      (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
  have hSq : (N:ℝ)*((L^2)^(s-1)*pseriesConstant s) ≤ (X*R)*pseriesConstant s := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hsquare hN0.le).trans hNx) hcS
  have hShared : ((N:ℝ)*J^2*(3+log (N:ℝ)))*(2/(L/2)) ≤ (X*R)*(8*c^2*D^3) := by
    have h₁ := pow_le_pow_left₀ (show 0 ≤ J by dsimp [J]; positivity) hJ 2
    have h₂ := mul_le_mul h₁ h3 (by linarith) (by positivity)
    have he : (N:ℝ)*J^2*(3+log (N:ℝ))*(2/(L/2)) = ((N:ℝ)*L⁻¹)*(4*(J^2*(3+log (N:ℝ)))) := by ring
    rw [he]
    refine (mul_le_mul ((mul_le_mul_of_nonneg_left hR hN0.le).trans hNx)
      (mul_le_mul_of_nonneg_left h₂ (by norm_num)) (by positivity) hz).trans_eq ?_
    ring
  have hLarge : (X^(1/4:ℝ)/L)*X^(3/4:ℝ) + (N:ℝ)*(X^(1/4:ℝ)/L)^2*H*(2/√X) ≤ X*R + (X*R)*(2*D) := by
    have h₁ : (X^(1/4:ℝ)/L)*X^(3/4:ℝ) = X/L := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hX0, show (1/4:ℝ)+3/4=1 by norm_num, Real.rpow_one]
    have h₂ : (X^(1/4:ℝ))^2 = √X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, Real.sqrt_eq_rpow]
      norm_num
    have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    have hR' : L⁻¹ * L⁻¹ ≤ R := (mul_le_of_le_one_right (by positivity) hLinv).trans hR
    have he : (N:ℝ)*(X^(1/4:ℝ)/L)^2*H*(2/√X) = ((N:ℝ)*(L⁻¹*L⁻¹))*(2*H) := by
      rw [div_pow,h₂]
      field_simp [hL0.ne', (Real.sqrt_pos_of_pos hX0).ne'] <;> ring
    rw [h₁,he]
    exact add_le_add hSmall (mul_le_mul ((mul_le_mul_of_nonneg_left hR' hN0.le).trans hNx)
      (mul_le_mul_of_nonneg_left hHD (by norm_num)) (by dsimp [H]; positivity) hz)
  have hReg : (4*(N:ℝ)*H*(1+log (N+1:ℕ))*J^3*(3+log (N:ℝ)))*(2/L) ≤ (X*R)*(16*c^3*D^6) := by
    have h₁ := mul_le_mul hHD hlogN1 (by positivity) (by dsimp [D]; positivity)
    have h₂ := pow_le_pow_left₀ (show 0 ≤ J by dsimp [J]; positivity) hJ 3
    have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have h₄ := mul_le_mul h₃ h3 (by linarith) (by positivity)
    have he : (4*(N:ℝ)*H*(1+log (N+1:ℕ))*J^3*(3+log (N:ℝ)))*(2/L) =
        ((N:ℝ)*L⁻¹)*(8*(H*(1+log (N+1:ℕ))*J^3*(3+log (N:ℝ)))) := by ring
    rw [he]
    refine (mul_le_mul ((mul_le_mul_of_nonneg_left hR hN0.le).trans hNx)
      (mul_le_mul_of_nonneg_left h₄ (by norm_num)) (by positivity) hz).trans_eq ?_
    ring
  have hShift : (X*R)*H^2 ≤ (X*R)*D^2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by dsimp [H]; positivity) hHD _) hz
  have hCof : (X/L)*H ≤ (X*R)*D := mul_le_mul hSmall hHD (by dsimp [H]; positivity) hz
  unfold countBudget budgetPolynomial
  change 2 * (X/L + _ + _ + ((N:ℝ)*J^2*(3+log (N:ℝ)))*(2/(L/2)) + (X/L)*H +
    ((X^(1/4:ℝ)/L)*X^(3/4:ℝ)+(N:ℝ)*(X^(1/4:ℝ)/L)^2*H*(2/√X)) + (X*R)*H^2 + _) ≤
      X*R*(2*(3+pseriesConstant s+8*c^2*D^3+3*D+D^2+16*c^3*D^6))
  have hSh : ((N:ℝ)*J^2*(3+log (N:ℝ)))*(2/(L/2)) ≤ (X*R)*(8*c^2*D^3) := hShared
  have htotal := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add hSmall hSm) hSq) hSh) hCof) hLarge) hShift) hReg
  exact (mul_le_mul_of_nonneg_left htotal (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

private noncomputable def budgetConstant (s : ℝ) : ℝ :=
  2*(3 + pseriesConstant s + 8*logConstant^2*3^3 + 9 + 3^2 + 16*logConstant^3*3^6)

private theorem budgetPolynomial_bound {b s : ℝ} (hb : 0 ≤ b) (hs : 1/2 < s) :
    budgetPolynomial s (exp b) ≤ budgetConstant s * exp (6*b) := by
  let E := exp b
  have he : 1 ≤ E := by dsimp [E]; simpa using Real.exp_le_exp.mpr hb
  have hE : 0 < E := exp_pos _
  have hD : 2+E ≤ 3*E := by linarith
  have hE₆ (k : ℕ) (hk : k ≤ 6) : E^k ≤ E^6 := pow_le_pow_right₀ he hk
  have hPow (k : ℕ) (hk : k ≤ 6) : (2+E)^k ≤ 3^k * E^6 := by
    calc (2+E)^k ≤ (3*E)^k := pow_le_pow_left₀ (by positivity) hD _
         _ = 3^k * E^k := mul_pow _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_left (hE₆ k hk) (by positivity)
  have hc₁ : 0 ≤ logConstant := by unfold logConstant; positivity
  have hcs : 0 ≤ pseriesConstant s := by
    unfold pseriesConstant
    exact mul_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
      (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
  have h₁ := mul_le_mul_of_nonneg_left (hPow 3 (by decide))
    (show 0 ≤ 8*logConstant^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (hPow 1 (by decide)) (show (0:ℝ) ≤ 3 by norm_num)
  have h₃ := hPow 2 (by decide)
  have h₄ := mul_le_mul_of_nonneg_left (hPow 6 (by decide))
    (show 0 ≤ 16*logConstant^3 by positivity)
  have h₀ := mul_le_mul_of_nonneg_left (hE₆ 0 (by decide))
    (show 0 ≤ 3 + pseriesConstant s by linarith)
  have h := add_le_add (add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃) h₄
  simp only [pow_zero, pow_one, mul_one] at h
  unfold budgetPolynomial budgetConstant
  change 2*(3+pseriesConstant s+8*logConstant^2*(2+E)^3+3*(2+E)+(2+E)^2+16*logConstant^3*(2+E)^6) ≤ _
  have hex : exp (6*b) = E^6 := by exact_mod_cast Real.exp_nat_mul b 6
  rw [hex]
  nlinarith only [h]

set_option maxHeartbeats 4200000 in
private theorem asymptotic_count_bound {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1/10) :
    ∀ᶠ X : ℝ in atTop, Erdos830.A X ≤ X * exp (-(1-5*δ)*(scale X/2)) := by
  let α := 1-δ/4
  let s := 1/2+δ
  have hs : 1/2 < s := by dsimp [s]; linarith
  have hs₁ : s ≤ 1 := by dsimp [s]; linarith
  have hcK : 0 < budgetConstant s := by
    unfold budgetConstant
    have hcs : 0 ≤ pseriesConstant s := by
      unfold pseriesConstant
      exact mul_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
        (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith)))
    have hlc : 0 ≤ logConstant := by unfold logConstant; positivity
    positivity
  have hbTop : Tendsto (fun x : ℝ => log (log x)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hcut : ∀ᶠ b : ℝ in atTop, exp (-(δ/4*b^α)) ≤ δ/12 := by
    have hh := tendsto_rpow_atTop (show 0 < α by dsimp [α]; linarith)
    filter_upwards [hh.eventually (eventually_ge_atTop (-(log (δ/12))/(δ/4)))] with b hb
    have hδp : 0 < δ/4 := by positivity
    have hb' := (div_le_iff₀ hδp).mp hb
    rw [← Real.exp_log (show 0 < δ/12 by positivity)]
    exact Real.exp_le_exp.mpr (by linarith)
  filter_upwards [eventually_ge_atTop (2:ℝ),
    hbTop.eventually (eventually_ge_atTop (max 24 (exp 1))),
    hbTop.eventually (eventually_rpow_le_exp (show (0:ℝ)<1 by norm_num) (by norm_num : (0:ℝ)<1/4) 1 1),
    hbTop.eventually (eventually_rpow_le_exp (show (0:ℝ)<δ/2 by positivity) (by norm_num : (0:ℝ)<1/2) 1 3),
    hbTop.eventually (eventually_rpow_le_exp (show (0:ℝ)<1/8 by norm_num) (by norm_num : (0:ℝ)<1/2) 5 65),
    hbTop.eventually (eventually_rpow_lt_rpow (show α < 1 by dsimp [α]; linarith) (show (0:ℝ)<1/8 by norm_num)),
    hbTop.eventually (eventually_log_times_rpow_le (show 1-δ/2 < α by dsimp [α]; linarith) (show 0 < δ/96 by positivity)),
    hbTop.eventually (eventually_rpow_le_exp (show 0 < δ/4 by positivity) (by norm_num : (0:ℝ)<3/8) 1 (3*(exp 1)^2)),
    hbTop.eventually hcut,
    hbTop.eventually (eventually_rpow_le_exp (show 0 < δ/2 by positivity) (by norm_num : (0:ℝ)<1/2)
      1 (6 + |log (budgetConstant s)|))] with X hX hbig hbx h3 h65 hshort hgap hsm hLg hM
  let A := log X
  let b := log A
  let c := log b
  let W := scale X/2
  let L := exp W
  let t := 3*c/(2*W)
  let R := exp (-(1-4*δ)*W)
  have hX0 : 0 < X := by linarith
  have hA : 0 < A := Real.log_pos (by linarith)
  have heA : exp b = A := Real.exp_log hA
  have hxA : exp A = X := Real.exp_log hX0
  have hb24 : 24 ≤ b := (le_max_left _ _).trans hbig
  have hb1 : 1 ≤ b := by linarith
  have hc1 : 1 ≤ c := by
    have h := Real.log_le_log (exp_pos 1) ((le_max_right 24 (exp 1)).trans hbig)
    simpa [b,c] using h
  have hc0 : 0 < c := by linarith
  have hcb : c ≤ b := by dsimp [c]; linarith [Real.log_le_sub_one_of_pos (show 0 < b by linarith)]
  have hbExp : b ≤ exp (b/4) := by simpa [b,A,div_eq_mul_inv,mul_comm] using hbx
  have hW0 : 0 < W := by dsimp [W,scale]; positivity
  have hWsq : W^2 = A*c/4 := by
    change (√(A*c)/2)^2 = A*c/4
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hWlo : exp (b/2)/2 ≤ W := by
    apply le_of_sq_le_sq _ hW0.le
    rw [hWsq, div_pow, pow_two (exp (b/2)), ← Real.exp_add,
      show b/2 + b/2 = b by ring, heA]
    have h := mul_le_mul_of_nonneg_left hc1 hA.le
    nlinarith
  have hWup : W ≤ exp ((3/4:ℝ)*b) := by
    apply le_of_sq_le_sq _ (Real.exp_nonneg _)
    rw [hWsq, pow_two, ← Real.exp_add,
      show (3/4:ℝ)*b + (3/4:ℝ)*b = b+b/2 by ring, Real.exp_add, heA]
    have hcb' : c ≤ exp (b/2) := hcb.trans (hbExp.trans (Real.exp_le_exp.mpr (by linarith)))
    exact (div_le_self (mul_nonneg hA.le hc0.le) (by norm_num)).trans (mul_le_mul_of_nonneg_left hcb' hA.le)
  have hW1 : 1 ≤ W := by
    have hh := Real.add_one_le_exp (b/2)
    linarith
  have hL : 2 ≤ L := by dsimp [L]; linarith [Real.add_one_le_exp W]
  have hL0 : 0 < L := exp_pos _
  have hW6 : W ≤ A/6 := by
    have he : (6:ℝ) ≤ exp (b/4) := by linarith [Real.add_one_le_exp (b/4)]
    have ha : exp ((3/4:ℝ)*b)*exp (b/4) = A := by
      rw [← Real.exp_add,show (3/4:ℝ)*b+b/4=b by ring,heA]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<6)).mpr
    exact (mul_le_mul_of_nonneg_right hWup (by norm_num)).trans
      ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ha)
  have h3c : 3*c ≤ δ*W := by
    have h := mul_le_mul_of_nonneg_left hcb (show (0:ℝ) ≤ 3 by norm_num)
    have h' : 3*b ≤ δ/2 * exp (b/2) := by simpa [b,A,div_eq_mul_inv,mul_comm] using h3
    exact h.trans (h'.trans (by nlinarith [mul_le_mul_of_nonneg_left hWlo hδ.le]))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht₁ : t ≤ 1/2 := by
    dsimp [t]
    rw [div_le_iff₀ (by positivity)]
    have hh : δ*W ≤ W := mul_le_of_le_one_left hW0.le (by linarith)
    linarith
  have hct : c/W ≤ 1/2 := by
    rw [div_le_iff₀ hW0]
    have h := mul_le_of_le_one_left hW0.le (show δ ≤ 1 by linarith)
    linarith
  have htPoly : 5 + 12*(1+4*c)*b^4 ≤ W/4 := by
    have hb₄ : 1 ≤ b^4 := one_le_pow₀ hb1
    have hb₅ : 1 ≤ b^5 := one_le_pow₀ hb1
    have h₁ : 1+4*c ≤ 5*b := by linarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ (pow_nonneg (show 0 ≤ b by linarith) 4)
    have he : 5+12*(1+4*c)*b^4 ≤ 65*b^5 := by nlinarith only [h₂,hb₅]
    have h₃ : 65*b^5 ≤ exp (b/2)/8 := by
      simpa [b,A,Real.rpow_natCast,div_eq_mul_inv,mul_comm,mul_assoc] using h65
    exact he.trans (h₃.trans (by linarith))
  have hshort' : b^α ≤ b/8 := by simpa [b,A,div_eq_mul_inv,mul_comm] using hshort
  have hgap' : 24*(3+c)*b^(1-δ/2) ≤ δ/4*b^α := by
    have h : (3+c)*b^(1-δ/2) ≤ (δ/96)*b^α := hgap
    nlinarith only [h]
  have hsm' : 3*(exp 1)^2*b ≤ δ/4*exp ((3/8:ℝ)*b) := by simpa [b,A] using hsm
  have hLg' : exp (-(δ/4*b^α)) ≤ δ/12 := hLg
  have hsmoothLog := smooth_component_weight hW0 hb1 (show c=log b from rfl) hc1 ht₁ hW1 htPoly
  have hLsq : L^2 = exp (2*W) := by dsimp [L]; rw [pow_two,← Real.exp_add]; congr 1; ring
  have hsmoothExp : smoothEuler (⌊L^2⌋₊+1) (1-t) ≤ exp W := by
    rw [hLsq]
    have h := Real.exp_le_exp.mpr hsmoothLog
    rw [Real.exp_log (smoothEuler_pos (by change 0 < 1-t; linarith))] at h
    exact h
  have htA : A/3*t = 2*W := by
    dsimp [t]
    field_simp
    nlinarith only [hWsq]
  have hSmooth : (X^(1/3:ℝ))^(-t)*smoothEuler (⌊L^2⌋₊+1) (1-t) ≤ L⁻¹ := by
    have hpow : (X^(1/3:ℝ))^(-t) = exp (-(2*W)) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_rpow hX0]
      change exp (1/3*A*(-t)) = _
      congr 1
      nlinarith only [htA]
    rw [hpow]
    exact (mul_le_mul_of_nonneg_left hsmoothExp (by positivity)).trans_eq (by
      dsimp [L]; rw [← Real.exp_add,←Real.exp_neg]; congr 1; ring)
  have hXL : X^(1/3:ℝ) < X/L := by
    have he : X/L = exp (A-W) := by dsimp [L]; rw [Real.exp_sub,hxA]
    rw [Real.rpow_def_of_pos hX0, he]
    exact Real.exp_lt_exp.mpr (by change A*(1/3) < A-W; linarith)
  have hLong : X^(1/3:ℝ)*√X ≤ X/L := by
    have he : X/L = exp (A-W) := by dsimp [L]; rw [Real.exp_sub,hxA]
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX0,Real.rpow_def_of_pos hX0,← Real.exp_add,he]
    exact Real.exp_le_exp.mpr (by change A*(1/3)+A*(1/2) ≤ A-W; linarith)
  have hFloor : X^(1/4:ℝ)/L ≤ (⌊X⌋₊:ℝ) := by
    have hp : X^(1/4:ℝ) ≤ X := by simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ X by linarith) (by norm_num : (1/4:ℝ) ≤ 1)
    calc _ ≤ X/2 := div_le_div_of_nonneg_left (show 0 ≤ X by linarith) (by norm_num) hL |>.trans' (div_le_div_of_nonneg_right hp hL0.le)
         _ ≤ _ := by linarith [Nat.lt_floor_add_one X]
  have hR : L⁻¹ ≤ R := by
    dsimp [L,R]
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hδ.le hW0.le])
  have hSq : (L^2)^(s-1) ≤ R := by
    rw [hLsq, Real.rpow_def_of_pos (by positivity), Real.log_exp]
    dsimp [R,s]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hδ.le hW0.le])
  have hu : ∀ z ≥ X/(X^(3/4:ℝ)*L^3), z ≤ X → ∀ T : Finset ℕ,
      (∀ a ∈ T, Squarefree a ∧ (a:ℝ) ≤ z ∧ σ 1 a ∈ (⌊L⌋₊+1).smoothNumbers) → (T.card:ℝ) ≤ z*R := by
    intro z hz hzX T hT
    have hz0 : 0 < z := (div_pos hX0 (by positivity)).trans_le hz
    let e := 1-(1-δ)*c/W
    let U := (⌊X⌋₊ : ℕ).primesLE.filter (fun p => p+1 ∈ (⌊L⌋₊+1).smoothNumbers)
    have he₂ : 0 ≤ e := by
      have hh : (1-δ)*(c/W) ≤ c/W := mul_le_of_le_one_left (by positivity) (by linarith)
      dsimp [e]; rw [mul_div_assoc]; linarith
    have hd : 0 ≤ 1-δ := by linarith
    have he₁ : 0 ≤ 1-e := by dsimp [e]; rw [sub_sub_cancel]; positivity
    have hRank := rankin_squarefree_count hz0 he₂ T U (fun a ha => by
      obtain ⟨haS,haz,hσ⟩ := hT a ha
      refine ⟨haS,haz,?_⟩
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpA : (p:ℝ) ≤ a := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero haS.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpA.trans (haz.trans hzX)),hpp⟩,
        Nat.mem_smoothNumbers_of_dvd hσ (squarefree_sigma_dvd haS hp)⟩)
    have hw := shifted_weight_small (N := ⌊X⌋₊) hδ hδ₁ hW1 hb1 (show c=log b from rfl) hc1 hct hWup hWlo
      hbExp (show b^(1-δ/4) ≤ b/8 from hshort') hgap' hsm' hLg'
    have hlogz : A/4-3*W ≤ log z := by
      have hh := Real.log_le_log (div_pos hX0 (by positivity)) hz
      have hLlog : log L = W := Real.log_exp _
      rw [Real.log_div hX0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hX0, Real.log_pow, hLlog] at hh
      change A-(3/4*A+3*W) ≤ log z at hh
      linarith
    have hW4 : c/W*(A/4) = W := by field_simp; nlinarith only [hWsq]
    have htail : (1-e)*log z ≥ (1-2*δ)*W := by
      have hh := mul_le_mul_of_nonneg_left hlogz he₁
      have heq : (1-e)*(A/4-3*W) = (1-δ)*W - 3*(1-δ)*c := by
        have he' : 1-e = (1-δ)*(c/W) := by dsimp [e]; ring
        have hW3 : c/W*(3*W) = 3*c := by field_simp
        rw [he',mul_assoc,mul_sub,hW4,hW3]
        ring
      rw [heq] at hh
      nlinarith only [hh,h3c,mul_nonneg hδ.le hc0.le]
    have heq : z^e = z*exp (-(1-e)*log z) := by
      rw [Real.rpow_def_of_pos hz0,← Real.exp_log hz0,← Real.exp_add,Real.log_exp]
      congr 1
      ring
    calc
      (T.card:ℝ) ≤ z^e*exp (δ*W) := hRank.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw) (by positivity))
      _ = z*exp (-(1-e)*log z+δ*W) := by rw [heq,mul_assoc,←Real.exp_add]
      _ ≤ z*R := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hδ.le hW0.le])) hz0.le
  have hcnt := finite_amicable_bound (by linarith : 1 ≤ X) hL hXL hLong hFloor ht (lt_of_le_of_lt ht₁ (by norm_num)) hs hs₁
    (Real.exp_nonneg _) hu
  have hbP := budgetPolynomial_bound (show 0 ≤ b by linarith) hs
  rw [heA] at hbP
  have hBudget : budgetConstant s * exp (6*b) ≤ exp (δ*W) := by
    have hM' : (6+|log (budgetConstant s)|)*b ≤ δ/2*exp (b/2) := by
      simpa [b,A,div_eq_mul_inv,mul_comm] using hM
    have hlog : log (budgetConstant s) + 6*b ≤ δ*W := by
      have h := mul_le_mul_of_nonneg_left hWlo hδ.le
      nlinarith [abs_nonneg (log (budgetConstant s)),le_abs_self (log (budgetConstant s)),
        mul_nonneg (abs_nonneg (log (budgetConstant s))) (show 0 ≤ b-1 by linarith)]
    rw [← Real.exp_log hcK,←Real.exp_add]
    exact Real.exp_le_exp.mpr hlog
  have hnonneg : 0 ≤ X*R := by positivity
  refine hcnt.trans ((budget_le_polynomial (by linarith) (by linarith) hs hR hSmooth hSq).trans ?_)
  exact (mul_le_mul_of_nonneg_left (hbP.trans hBudget) hnonneg).trans_eq (by
    dsimp [R]; rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring)

end AmicableCount

-- Credits: AmicableCount is from @amp2600's merged proof of Erdos830.erdos_830.variants.pomerance_stronger (#6491);
-- exponent comparison adapts @Marcus-Buffett (#5684), @ivillar (#6157), and @MMexicann (note #38100).
theorem OMA.solution : type_of% @Erdos830.erdos_830.variants.pomerance := by
  have hcount := AmicableCount.asymptotic_count_bound (δ := 1 / 10) (by norm_num) le_rfl
  have hlog := Real.tendsto_log_atTop
  have hlog3 : Tendsto (fun x : ℝ => log (log (log x))) atTop atTop := hlog.comp (hlog.comp hlog)
  filter_upwards [hcount, hlog.eventually (eventually_ge_atTop 4096),
    hlog3.eventually (eventually_ge_atTop 1), eventually_ge_atTop (0 : ℝ)] with x hx hL hL3 hx0
  have hL0 : 0 < log x := by linarith
  have h6 : (4 : ℝ) ≤ log x ^ (((6 : ℕ) : ℝ)⁻¹) := by
    calc
      (4 : ℝ) = ((4 : ℝ) ^ (6 : ℕ)) ^ (((6 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ ≤ log x ^ (((6 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have hsplit : √(log x) = log x ^ (((3 : ℕ) : ℝ)⁻¹) * log x ^ (((6 : ℕ) : ℝ)⁻¹) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL0]
    congr 1
    norm_num
  have hc : Real.nthRoot 3 (log x) ≤ √(log x) / 4 := by
    rw [Real.nthRoot_of_nonneg hL0.le, hsplit]
    nlinarith [Real.rpow_nonneg hL0.le (((3 : ℕ) : ℝ)⁻¹),
      mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hL0.le (((3 : ℕ) : ℝ)⁻¹))]
  have hs : √(log x) ≤ AmicableCount.scale x :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hL3 hL0.le])
  apply hx.trans
  apply mul_le_mul_of_nonneg_left _ hx0
  apply Real.exp_le_exp.mpr
  linarith only [hc, hs]
