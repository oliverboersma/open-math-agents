import FormalConjectures.ErdosProblems.«694»
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Erdos Problem 694 (Infinitely Many Unique Totient Fibres)

We prove Erdos's 1958 theorem (`Erdos694.erdos_694.variants.inf_unique`): if there exists `n > 0`
whose totient fibre `{m | Nat.totient m = n}` is a singleton, then there are infinitely many such
integers.
-/

namespace Erdos694InfUnique

open Finset Real Nat
open scoped ArithmeticFunction.Moebius Chebyshev Topology

noncomputable section

/- ## Part 1: Fundamental Selberg Upper Bound on `BoundingSieve` -/

private lemma moebius_sq_cast_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ((μ m : ℝ)) ^ 2 = 1 := by
  exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hm

private lemma abs_moebius_cast_of_squarefree {m : ℕ} (hm : Squarefree m) :
    |(μ m : ℝ)| = 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hm

private lemma sum_div_moebius_eq_ite {t : ℕ} :
    (∑ k ∈ t.divisors, (μ (t / k) : ℝ)) = if t = 1 then 1 else 0 := by
  have h1 : (∑ k ∈ t.divisors, (μ (t / k) : ℝ)) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) t := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y =>
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) x * (μ : ArithmeticFunction ℝ) y)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
    simp [hk0]
  rw [h1, ArithmeticFunction.coe_zeta_mul_coe_moebius]
  simp [ArithmeticFunction.one_apply]

private def selbergDz (s : BoundingSieve) (z : ℝ) : Finset ℕ :=
  s.prodPrimes.divisors.filter (fun l : ℕ => (l : ℝ) ≤ z)

private def selbergSum (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ l ∈ selbergDz s z, s.selbergTerms l

private lemma one_mem_selbergDz (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    1 ∈ selbergDz s z := by
  simp [selbergDz, s.prodPrimes_ne_zero, hz]

private lemma one_le_selbergSum (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    1 ≤ selbergSum s z := by
  have h1 : (1 : ℝ) = s.selbergTerms 1 := s.selbergTerms_isMultiplicative.map_one.symm
  rw [h1, selbergSum]
  refine Finset.single_le_sum (fun l hl => ?_) (one_mem_selbergDz s hz)
  have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
  exact (s.selbergTerms_pos hlP).le

private lemma selbergSum_pos (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    0 < selbergSum s z :=
  lt_of_lt_of_le zero_lt_one (one_le_selbergSum s hz)

private def selbergY (s : BoundingSieve) (z : ℝ) (l : ℕ) : ℝ :=
  if l ∈ selbergDz s z then (μ l : ℝ) * s.selbergTerms l / selbergSum s z else 0

private def selbergW (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  if d ∈ s.prodPrimes.divisors then
    (s.nu d)⁻¹ * ∑ m ∈ (s.prodPrimes / d).divisors, (μ m : ℝ) * selbergY s z (d * m)
  else 0

private lemma selbergW_one (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    selbergW s z 1 = 1 := by
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_ne_zero
  have hS0 : selbergSum s z ≠ 0 := (selbergSum_pos s hz).ne'
  have h1mem : 1 ∈ s.prodPrimes.divisors := Nat.one_mem_divisors.mpr hP0
  rw [selbergW, if_pos h1mem, s.nu_mult.map_one, inv_one, one_mul, Nat.div_one]
  have hsub : selbergDz s z ⊆ s.prodPrimes.divisors := Finset.filter_subset _ _
  have hsum : (∑ m ∈ s.prodPrimes.divisors, (μ m : ℝ) * selbergY s z (1 * m)) =
      ∑ m ∈ selbergDz s z, s.selbergTerms m / selbergSum s z := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hmsq : Squarefree m :=
        s.squarefree_of_mem_divisors_prodPrimes (hsub hm)
      simp only [one_mul, selbergY, if_pos hm]
      calc (μ m : ℝ) * ((μ m : ℝ) * s.selbergTerms m / selbergSum s z)
        _ = ((μ m : ℝ) ^ 2) * s.selbergTerms m / selbergSum s z := by ring
        _ = s.selbergTerms m / selbergSum s z := by rw [moebius_sq_cast_of_squarefree hmsq, one_mul]
    · intro m _ hmnot
      simp [selbergY, hmnot]
  rw [hsum, ← Finset.sum_div]
  exact div_self hS0

private lemma sum_nu_mul_selbergW (s : BoundingSieve) (z : ℝ) {l : ℕ}
    (hl : l ∈ s.prodPrimes.divisors) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergW s z d else 0) =
      selbergY s z l := by
  have hP0 : s.prodPrimes ≠ 0 := s.prodPrimes_ne_zero
  have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := (Nat.pos_of_mem_divisors hl).ne'
  set Q := s.prodPrimes / l with hQ_def
  have hQ0 : Q ≠ 0 := by
    intro h
    have : s.prodPrimes = l * Q := (Nat.mul_div_cancel' hlP).symm
    rw [h, mul_zero] at this
    exact hP0 this
  have hbij : (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergW s z d else 0) =
      ∑ k ∈ Q.divisors, ∑ m ∈ (Q / k).divisors, (μ m : ℝ) * selbergY s z (l * (k * m)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun d => d / l) (fun k => l * k) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨?_, hQ0⟩
      have hdP : d ∣ s.prodPrimes := hd.1.1
      have hdl : d = l * (d / l) := (Nat.mul_div_cancel' hd.2).symm
      have hPQ : s.prodPrimes = l * Q := (Nat.mul_div_cancel' hlP).symm
      have hdvd : l * (d / l) ∣ l * Q := by rwa [← hdl, ← hPQ]
      exact (mul_dvd_mul_iff_left hl0).mp hdvd
    · intro k hk
      simp only [Finset.mem_filter, Nat.mem_divisors] at hk ⊢
      refine ⟨⟨?_, hP0⟩, dvd_mul_right l k⟩
      have hPQ : s.prodPrimes = l * Q := (Nat.mul_div_cancel' hlP).symm
      rw [hPQ]
      exact mul_dvd_mul_left l hk.1
    · intro d hd
      simp only [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro k _
      exact Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hl0)
    · intro d hd
      simp only [Finset.mem_filter] at hd
      have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd.1
      have hnu0 : s.nu d ≠ 0 := s.nu_ne_zero hdP
      have hdl : l * (d / l) = d := Nat.mul_div_cancel' hd.2
      have hQdiv : s.prodPrimes / d = Q / (d / l) := by
        rw [hQ_def, Nat.div_div_eq_div_mul, hdl]
      rw [selbergW, if_pos hd.1, ← mul_assoc, mul_inv_cancel₀ hnu0, one_mul, hQdiv]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← mul_assoc, hdl]
  rw [hbij]
  have hswap : (∑ k ∈ Q.divisors, ∑ m ∈ (Q / k).divisors,
        (μ m : ℝ) * selbergY s z (l * (k * m))) =
      ∑ t ∈ Q.divisors, selbergY s z (l * t) * (∑ k ∈ t.divisors, (μ (t / k) : ℝ)) := by
    rw [Finset.sum_sigma']
    symm
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 / p.2⟩) (fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨t, k⟩ htk
      simp only [Finset.mem_sigma, Nat.mem_divisors] at htk ⊢
      have htQ : t ∣ Q := htk.1.1
      have hkt : k ∣ t := htk.2.1
      have ht0 : t ≠ 0 := htk.2.2
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0] at hkt
        exact ht0 (zero_dvd_iff.mp hkt)
      have htk_eq : k * (t / k) = t := Nat.mul_div_cancel' hkt
      have hkQ : k ∣ Q := hkt.trans htQ
      have hQ_eq : Q = k * (Q / k) := (Nat.mul_div_cancel' hkQ).symm
      have hQk_ne : Q / k ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hQ_eq
        exact hQ0 hQ_eq
      refine ⟨⟨hkQ, hQ0⟩, ?_, hQk_ne⟩
      have hdvd : k * (t / k) ∣ k * (Q / k) := by rwa [htk_eq, ← hQ_eq]
      exact (mul_dvd_mul_iff_left hk0).mp hdvd
    · rintro ⟨k, m⟩ hkm
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hkm ⊢
      have hkQ : k ∣ Q := hkm.1.1
      have hmQk : m ∣ Q / k := hkm.2.1
      have hQk0 : Q / k ≠ 0 := hkm.2.2
      have hk_ne : k ≠ 0 := by
        intro h0
        rw [h0] at hkQ
        exact hQ0 (zero_dvd_iff.mp hkQ)
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0] at hmQk
        exact hQk0 (zero_dvd_iff.mp hmQk)
      have hkm_ne : k * m ≠ 0 := mul_ne_zero hk_ne hm0
      refine ⟨⟨?_, hQ0⟩, dvd_mul_right k m, hkm_ne⟩
      have hQ_eq : Q = k * (Q / k) := (Nat.mul_div_cancel' hkQ).symm
      rw [hQ_eq]
      exact mul_dvd_mul_left k hmQk
    · rintro ⟨t, k⟩ htk
      simp only [Finset.mem_sigma, Nat.mem_divisors] at htk
      ext <;> simp [Nat.mul_div_cancel' htk.2.1]
    · rintro ⟨k, m⟩ hkm
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hkm
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hkm.1.1 (Nat.pos_of_ne_zero hQ0)
      ext <;> simp [Nat.mul_div_cancel_left m hk_pos]
    · rintro ⟨t, k⟩ htk
      simp only [Finset.mem_sigma, Nat.mem_divisors] at htk
      rw [Nat.mul_div_cancel' htk.2.1, mul_comm]
  rw [hswap]
  have hcollapse : (∑ t ∈ Q.divisors, selbergY s z (l * t) *
      (∑ k ∈ t.divisors, (μ (t / k) : ℝ))) =
      ∑ t ∈ Q.divisors, if t = 1 then selbergY s z l else 0 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [sum_div_moebius_eq_ite]
    split_ifs with ht1
    · subst ht1; simp
    · simp
  rw [hcollapse, Finset.sum_ite_eq' Q.divisors 1]
  simp [Nat.one_mem_divisors.mpr hQ0]

private lemma selberg_mainSum_eq (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (selbergW s z)) = (selbergSum s z)⁻¹ := by
  have hS0 : selbergSum s z ≠ 0 := (selbergSum_pos s hz).ne'
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have h1 : (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergW s z d else 0) ^ 2) =
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ * (selbergY s z l) ^ 2 := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [sum_nu_mul_selbergW s z hl]
  rw [h1]
  have hsub : selbergDz s z ⊆ s.prodPrimes.divisors := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  · have h2 : (∑ l ∈ selbergDz s z, (s.selbergTerms l)⁻¹ * (selbergY s z l) ^ 2) =
        ∑ l ∈ selbergDz s z, s.selbergTerms l / (selbergSum s z) ^ 2 := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlP : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (hsub hl)
      have hl_pos : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos hlP).ne'
      have hlsq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
      simp only [selbergY, if_pos hl]
      calc (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.selbergTerms l / selbergSum s z) ^ 2
        _ = ((μ l : ℝ) ^ 2) * ((s.selbergTerms l)⁻¹ * s.selbergTerms l) *
            s.selbergTerms l / (selbergSum s z) ^ 2 := by ring
        _ = s.selbergTerms l / (selbergSum s z) ^ 2 := by
          rw [moebius_sq_cast_of_squarefree hlsq, inv_mul_cancel₀ hl_pos, one_mul, one_mul]
    rw [h2, ← Finset.sum_div]
    change selbergSum s z / (selbergSum s z) ^ 2 = (selbergSum s z)⁻¹
    rw [sq, div_mul_eq_div_div, div_self hS0, one_div]
  · intro l _ hlnot
    simp [selbergY, hlnot]

private lemma selbergW_eq_zero_of_gt (s : BoundingSieve) {z : ℝ} {d : ℕ} (hd : z < (d : ℝ)) :
    selbergW s z d = 0 := by
  by_cases hdP : d ∈ s.prodPrimes.divisors
  · rw [selbergW, if_pos hdP]
    suffices (∑ m ∈ (s.prodPrimes / d).divisors, (μ m : ℝ) * selbergY s z (d * m)) = 0 by
      rw [this, mul_zero]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm_pos : 1 ≤ m := Nat.pos_of_mem_divisors hm
    have hdm_gt : z < ((d * m : ℕ) : ℝ) := by
      calc z < (d : ℝ) := hd
        _ = (d : ℝ) * 1 := (mul_one _).symm
        _ ≤ (d : ℝ) * (m : ℝ) := by gcongr; exact_mod_cast hm_pos
        _ = ((d * m : ℕ) : ℝ) := by push_cast; rfl
    have hnot : d * m ∉ selbergDz s z := fun hmem =>
      not_le.mpr hdm_gt (Finset.mem_filter.mp hmem).2
    simp [selbergY, hnot]
  · simp [selbergW, hdP]

private lemma abs_selbergW_le_one (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) (d : ℕ) :
    |selbergW s z d| ≤ 1 := by
  by_cases hd_mem : d ∈ s.prodPrimes.divisors
  · have hdP : d ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hd_mem
    have hPsq : Squarefree s.prodPrimes := s.prodPrimes_squarefree
    have hdsq : Squarefree d := s.squarefree_of_dvd_prodPrimes hdP
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_mem
    have hPd_eq : d * (s.prodPrimes / d) = s.prodPrimes := Nat.mul_div_cancel' hdP
    have hcop_Pd : d.Coprime (s.prodPrimes / d) :=
      Nat.coprime_of_squarefree_mul (hPd_eq.symm ▸ hPsq)
    have hS_pos : 0 < selbergSum s z := selbergSum_pos s hz
    have hnu_pos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdP
    set M := ((s.prodPrimes / d).divisors).filter (fun m : ℕ => d * m ∈ selbergDz s z)
    have hw_eq : selbergW s z d =
        (μ d : ℝ) * ((s.nu d)⁻¹ * s.selbergTerms d *
          (∑ m ∈ M, s.selbergTerms m) / selbergSum s z) := by
      rw [selbergW, if_pos hd_mem]
      have hsub : M ⊆ (s.prodPrimes / d).divisors := Finset.filter_subset _ _
      have hsum : (∑ m ∈ (s.prodPrimes / d).divisors, (μ m : ℝ) * selbergY s z (d * m)) =
          ((μ d : ℝ) * s.selbergTerms d / selbergSum s z) * ∑ m ∈ M, s.selbergTerms m := by
        rw [← Finset.sum_subset hsub, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun m hm => ?_
          have hm_mem : m ∈ (s.prodPrimes / d).divisors := (Finset.mem_filter.mp hm).1
          have hm_dz : d * m ∈ selbergDz s z := (Finset.mem_filter.mp hm).2
          have hm_dvd : m ∣ s.prodPrimes / d := Nat.dvd_of_mem_divisors hm_mem
          have hcop_dm : d.Coprime m := hcop_Pd.coprime_dvd_right hm_dvd
          have hmsq : Squarefree m :=
            s.squarefree_of_dvd_prodPrimes (hm_dvd.trans ⟨d, by rw [mul_comm, hPd_eq]⟩)
          have hmu_mul : (μ (d * m) : ℝ) = (μ d : ℝ) * (μ m : ℝ) := by
            exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_dm
          have hg_mul : s.selbergTerms (d * m) = s.selbergTerms d * s.selbergTerms m :=
            s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop_dm
          simp only [selbergY, if_pos hm_dz, hmu_mul, hg_mul]
          calc (μ m : ℝ) * ((μ d : ℝ) * (μ m : ℝ) *
                (s.selbergTerms d * s.selbergTerms m) / selbergSum s z)
            _ = (μ d : ℝ) * ((μ m : ℝ) ^ 2) *
                (s.selbergTerms d * s.selbergTerms m) / selbergSum s z := by ring
            _ = ((μ d : ℝ) * s.selbergTerms d / selbergSum s z) * s.selbergTerms m := by
              rw [moebius_sq_cast_of_squarefree hmsq]; ring
        · intro m hmdiv hmnot
          have hnotdz : d * m ∉ selbergDz s z := fun h => hmnot (Finset.mem_filter.mpr ⟨hmdiv, h⟩)
          simp [selbergY, hnotdz]
      rw [hsum]
      ring
    rw [hw_eq, abs_mul, abs_moebius_cast_of_squarefree hdsq, one_mul]
    have hnonneg : 0 ≤ (s.nu d)⁻¹ * s.selbergTerms d *
        (∑ m ∈ M, s.selbergTerms m) / selbergSum s z := by
      refine div_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hnu_pos.le)
        (s.selbergTerms_pos hdP).le) ?_) hS_pos.le
      refine Finset.sum_nonneg fun m hm => ?_
      have hm_dvd : m ∣ s.prodPrimes / d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm).1
      exact (s.selbergTerms_pos (hm_dvd.trans ⟨d, by rw [mul_comm, hPd_eq]⟩)).le
    rw [abs_of_nonneg hnonneg, div_le_one hS_pos]
    have hid : (s.nu d)⁻¹ * s.selbergTerms d = ∑ a ∈ d.divisors, s.selbergTerms a := by
      rw [mul_comm, ← s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP,
        ← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP]
    rw [hid, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    have hprod_eq : (∑ p ∈ d.divisors ×ˢ M, s.selbergTerms p.1 * s.selbergTerms p.2) =
        ∑ p ∈ d.divisors ×ˢ M, s.selbergTerms (p.1 * p.2) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have ha : p.1 ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_product.mp hp).1
      have hm : p.2 ∣ s.prodPrimes / d :=
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
      exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime
        ((hcop_Pd.coprime_dvd_left ha).coprime_dvd_right hm)).symm
    rw [hprod_eq]
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(d.divisors ×ˢ M) := by
      rintro ⟨a1, m1⟩ h1 ⟨a2, m2⟩ h2 (heq : a1 * m1 = a2 * m2)
      rcases Finset.mem_product.mp (Finset.mem_coe.mp h1) with ⟨ha1_mem, hm1_mem⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp h2) with ⟨ha2_mem, hm2_mem⟩
      have ha1 : a1 ∣ d := Nat.dvd_of_mem_divisors ha1_mem
      have ha2 : a2 ∣ d := Nat.dvd_of_mem_divisors ha2_mem
      have hm1 : m1 ∣ s.prodPrimes / d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm1_mem).1
      have hm2 : m2 ∣ s.prodPrimes / d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm2_mem).1
      have hc1 : d.Coprime m1 := hcop_Pd.coprime_dvd_right hm1
      have hc2 : d.Coprime m2 := hcop_Pd.coprime_dvd_right hm2
      have hg1 : (a1 * m1).gcd d = a1 := by
        rw [mul_comm, hc1.symm.gcd_mul_left_cancel, Nat.gcd_eq_left ha1]
      have hg2 : (a2 * m2).gcd d = a2 := by
        rw [mul_comm, hc2.symm.gcd_mul_left_cancel, Nat.gcd_eq_left ha2]
      have ha_eq : a1 = a2 := by rw [← hg1, heq, hg2]
      subst ha_eq
      have ha1_pos : 0 < a1 := Nat.pos_of_mem_divisors ha1_mem
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left ha1_pos heq)
    rw [← Finset.sum_image (f := s.selbergTerms) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
    · intro l hl
      rcases Finset.mem_image.mp hl with ⟨⟨a, m⟩, ham, rfl⟩
      rcases Finset.mem_product.mp ham with ⟨ha_div, hm_M⟩
      have ha_dvd : a ∣ d := Nat.dvd_of_mem_divisors ha_div
      have hm_dvd : m ∣ s.prodPrimes / d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm_M).1
      have hdm_dz : d * m ∈ selbergDz s z := (Finset.mem_filter.mp hm_M).2
      have ham_dvd : a * m ∣ s.prodPrimes := by
        rw [← hPd_eq]
        exact mul_dvd_mul ha_dvd hm_dvd
      have ha_le : a ≤ d := Nat.le_of_dvd hd_pos ha_dvd
      have ham_le_z : ((a * m : ℕ) : ℝ) ≤ z := by
        calc ((a * m : ℕ) : ℝ) ≤ ((d * m : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_right m ha_le
          _ ≤ z := (Finset.mem_filter.mp hdm_dz).2
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨ham_dvd, s.prodPrimes_ne_zero⟩, ham_le_z⟩
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1)).le
  · simp [selbergW, hd_mem]

private lemma siftedSum_le_selberg (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / selbergSum s z +
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ 2),
        (d : ℝ) ^ 2 * |s.rem d| := by
  have hupper : BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared (selbergW s z)) :=
    BoundingSieve.upperMoebius_lambdaSquared _ (selbergW_one s hz)
  have hbase := s.siftedSum_le_mainSum_errSum_of_upperMoebius _ hupper
  rw [selberg_mainSum_eq s hz, ← div_eq_mul_inv] at hbase
  refine hbase.trans (add_le_add_right ?_ _)
  rw [BoundingSieve.errSum]
  set D2 := s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ 2)
  have hvanish : (∑ d ∈ s.prodPrimes.divisors,
        |BoundingSieve.lambdaSquared (selbergW s z) d| * |s.rem d|) =
      ∑ d ∈ D2, |BoundingSieve.lambdaSquared (selbergW s z) d| * |s.rem d| := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun d hd hdnot => ?_
    have hgt : z ^ 2 < (d : ℝ) := not_le.mp fun hle => hdnot (Finset.mem_filter.mpr ⟨hd, hle⟩)
    suffices BoundingSieve.lambdaSquared (selbergW s z) d = 0 by simp [this]
    rw [BoundingSieve.lambdaSquared]
    refine Finset.sum_eq_zero fun d1 hd1 => Finset.sum_eq_zero fun d2 hd2 => ?_
    split_ifs with hlcm
    · have hd1_pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
      have hd2_pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
      have hd_le_mul : d ≤ d1 * d2 := by
        rw [hlcm]
        exact Nat.le_of_dvd (mul_pos hd1_pos hd2_pos) (Nat.lcm_dvd_mul d1 d2)
      have hmul_gt : z ^ 2 < (d1 : ℝ) * (d2 : ℝ) :=
        lt_of_lt_of_le hgt (by exact_mod_cast hd_le_mul)
      by_cases h1 : z < (d1 : ℝ)
      · rw [selbergW_eq_zero_of_gt s h1, zero_mul]
      · have h2 : z < (d2 : ℝ) := by
          by_contra h2not
          have h1le : (d1 : ℝ) ≤ z := not_lt.mp h1
          have h2le : (d2 : ℝ) ≤ z := not_lt.mp h2not
          have hprod_le : (d1 : ℝ) * (d2 : ℝ) ≤ z ^ 2 := by
            rw [sq]
            exact mul_le_mul h1le h2le (Nat.cast_nonneg d2) (by linarith)
          linarith
        rw [selbergW_eq_zero_of_gt s h2, mul_zero]
    · rfl
  rw [hvanish]
  refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [BoundingSieve.lambdaSquared]
  calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = d1.lcm d2 then selbergW s z d1 * selbergW s z d2 else 0|
    _ ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors,
        if d = d1.lcm d2 then selbergW s z d1 * selbergW s z d2 else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        |if d = d1.lcm d2 then selbergW s z d1 * selbergW s z d2 else 0| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d1 ∈ d.divisors, ∑ _d2 ∈ d.divisors, (1 : ℝ) := by
      refine Finset.sum_le_sum fun d1 _ => Finset.sum_le_sum fun d2 _ => ?_
      split_ifs
      · rw [abs_mul]
        exact mul_le_one₀ (abs_selbergW_le_one s hz d1) (abs_nonneg _)
          (abs_selbergW_le_one s hz d2)
      · simp
    _ = (#d.divisors : ℝ) ^ 2 := by
      simp [Finset.sum_const, sq]
    _ ≤ (d : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast Nat.card_divisors_le_self d

/- ## Part 2: Elementary Totient, Harmonic, and Dyadic Prime-Reciprocal Estimates -/

private def primesLE (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

private lemma mem_primesLE {N r : ℕ} : r ∈ primesLE N ↔ r.Prime ∧ r ≤ N := by
  simp only [primesLE, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

private lemma card_primesLE (N : ℕ) : #(primesLE N) = N.primeCounting := by
  simp [primesLE, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private lemma one_half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.add_one_le_exp (-Real.log 2)
  rw [Real.exp_neg, Real.exp_log two_pos] at h
  linarith

private lemma odd_le_totient_sq : ∀ m : ℕ, Odd m → m ≤ (Nat.totient m) ^ 2 := by
  intro m
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ m
  · intro p e hp he hodd
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 he.ne'
      obtain ⟨k, hk⟩ := hodd
      omega
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rw [Nat.totient_prime_pow hp he, mul_pow, ← pow_mul]
    have hp_le : p ≤ (p - 1) ^ 2 := by
      have h1 : 1 ≤ p - 2 := by omega
      nlinarith [Nat.sub_add_cancel hp.one_le]
    have he_le : e - 1 ≤ (e - 1) * 2 := by omega
    calc p ^ e = p ^ (e - 1) * p := by
          rw [← pow_succ, Nat.sub_add_cancel he]
      _ ≤ p ^ ((e - 1) * 2) * (p - 1) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos he_le) hp_le
  · intro hodd
    simp at hodd
  · intro _
    simp
  · intro a b _ _ hcop iha ihb hodd
    rcases Nat.odd_mul.mp hodd with ⟨ha_odd, hb_odd⟩
    rw [Nat.totient_mul hcop, mul_pow]
    exact Nat.mul_le_mul (iha ha_odd) (ihb hb_odd)

private lemma self_le_two_mul_totient_sq (k : ℕ) : k ≤ 2 * (Nat.totient k) ^ 2 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  set a := k.factorization 2
  set m := k / 2 ^ a
  have hkm : 2 ^ a * m = k := Nat.ordProj_mul_ordCompl_eq_self k 2
  have hnot2 : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hk0
  have hm_odd : Odd m := Nat.not_even_iff_odd.mp (fun he => hnot2 (even_iff_two_dvd.mp he))
  have hcop : (2 ^ a).Coprime m :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2).pow_left a
  have h2a : 2 ^ a ≤ 2 * (Nat.totient (2 ^ a)) ^ 2 := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [ha0]; simp
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
      rw [Nat.totient_prime_pow Nat.prime_two ha_pos]
      simp only [Nat.reduceSub, mul_one, ← pow_mul]
      calc 2 ^ a ≤ 2 ^ (1 + (a - 1) * 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ ((a - 1) * 2) := by rw [pow_add, pow_one]
  calc k = 2 ^ a * m := hkm.symm
    _ ≤ (2 * (Nat.totient (2 ^ a)) ^ 2) * (Nat.totient m) ^ 2 :=
      Nat.mul_le_mul h2a (odd_le_totient_sq m hm_odd)
    _ = 2 * (Nat.totient (2 ^ a) * Nat.totient m) ^ 2 := by ring
    _ = 2 * (Nat.totient k) ^ 2 := by rw [← Nat.totient_mul hcop, hkm]

private lemma sum_inv_mul_totient_dyadic_block (j : ℕ) :
    (∑ k ∈ (Finset.Ico (2 * 4 ^ j) (2 * 4 ^ (j + 1)) : Finset ℕ),
      (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) ≤ (3 : ℝ) / (2 : ℝ) ^ j := by
  set B : Finset ℕ := Finset.Ico (2 * 4 ^ j) (2 * 4 ^ (j + 1))
  have hle : ∀ k ∈ B,
      (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ)) ≤
        (1 : ℝ) / ((2 * 4 ^ j : ℝ) * (2 ^ j : ℝ)) := by
    intro k hk
    have hk_ge : 2 * 4 ^ j ≤ k := (Finset.mem_Ico.mp hk).1
    have hsq : 2 * (2 ^ j) ^ 2 ≤ 2 * (Nat.totient k) ^ 2 := by
      calc 2 * (2 ^ j) ^ 2 = 2 * 4 ^ j := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
        _ ≤ k := hk_ge
        _ ≤ 2 * (Nat.totient k) ^ 2 := self_le_two_mul_totient_sq k
    have htot_sq : (2 ^ j) ^ 2 ≤ (Nat.totient k) ^ 2 := by omega
    have htot_ge : 2 ^ j ≤ Nat.totient k := (Nat.pow_le_pow_iff_left (by norm_num)).mp htot_sq
    have hpos : (0 : ℝ) < (2 * 4 ^ j : ℝ) * (2 ^ j : ℝ) := by positivity
    refine one_div_le_one_div_of_le hpos ?_
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact_mod_cast hk_ge
    · exact_mod_cast htot_ge
  calc (∑ k ∈ B, (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ)))
    _ ≤ ∑ _k ∈ B, (1 : ℝ) / ((2 * 4 ^ j : ℝ) * (2 ^ j : ℝ)) := Finset.sum_le_sum hle
    _ = ((#B : ℕ) : ℝ) * ((1 : ℝ) / ((2 * 4 ^ j : ℝ) * (2 ^ j : ℝ))) := by
      simp [Finset.sum_const]
    _ = (3 : ℝ) / (2 : ℝ) ^ j := by
      have hcard : #B = 6 * 4 ^ j := by
        dsimp [B]
        rw [Nat.card_Ico, pow_succ]
        omega
      rw [hcard]
      have h4_eq : ((4 ^ j : ℕ) : ℝ) = ((2 : ℝ) ^ j) ^ 2 := by
        have hnat : 4 ^ j = (2 ^ j) ^ 2 := by
          calc 4 ^ j = (2 ^ 2) ^ j := rfl
            _ = 2 ^ (2 * j) := (pow_mul 2 2 j).symm
            _ = 2 ^ (j * 2) := by rw [mul_comm]
            _ = (2 ^ j) ^ 2 := pow_mul 2 j 2
        exact_mod_cast hnat
      have h20 : (2 : ℝ) ^ j ≠ 0 := by positivity
      push_cast
      rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by exact_mod_cast h4_eq]
      field_simp [h20]
      ring

private lemma sum_inv_mul_totient_tail_gen (J N : ℕ) :
    (∑ k ∈ (Finset.Icc (2 * 4 ^ J + 1) N : Finset ℕ),
      (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) ≤ (6 : ℝ) / (2 : ℝ) ^ J := by
  let f : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))
  have hM : ∀ M : ℕ,
      (∑ k ∈ (Finset.Ico (2 * 4 ^ J) (2 * 4 ^ (J + M)) : Finset ℕ), f k) ≤
        ((6 : ℝ) / (2 : ℝ) ^ J) * (1 - (1 / 2 : ℝ) ^ M) := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
      have h1 : 2 * 4 ^ J ≤ 2 * 4 ^ (J + m) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : 2 * 4 ^ (J + m) ≤ 2 * 4 ^ (J + (m + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [← Finset.sum_Ico_consecutive f h1 h2]
      have hblk : (∑ k ∈ (Finset.Ico (2 * 4 ^ (J + m)) (2 * 4 ^ (J + (m + 1))) : Finset ℕ), f k) ≤
          (3 : ℝ) / (2 : ℝ) ^ (J + m) := by
        rw [← Nat.add_assoc J m 1]
        exact sum_inv_mul_totient_dyadic_block (J + m)
      have h2J : (2 : ℝ) ^ J ≠ 0 := by positivity
      have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
      calc (∑ k ∈ (Finset.Ico (2 * 4 ^ J) (2 * 4 ^ (J + m)) : Finset ℕ), f k) +
            (∑ k ∈ (Finset.Ico (2 * 4 ^ (J + m)) (2 * 4 ^ (J + (m + 1))) : Finset ℕ), f k)
        _ ≤ ((6 : ℝ) / (2 : ℝ) ^ J) * (1 - (1 / 2 : ℝ) ^ m) + (3 : ℝ) / (2 : ℝ) ^ (J + m) :=
          add_le_add ih hblk
        _ = ((6 : ℝ) / (2 : ℝ) ^ J) * (1 - (1 / 2 : ℝ) ^ (m + 1)) := by
          rw [one_div_pow, one_div_pow, pow_add, pow_succ]
          field_simp [h2J, h2m]
          ring
  have hsub : (Finset.Icc (2 * 4 ^ J + 1) N : Finset ℕ) ⊆
      Finset.Ico (2 * 4 ^ J) (2 * 4 ^ (J + N)) := by
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
    refine ⟨by omega, ?_⟩
    have hlt : N < 4 ^ N := by
      calc N < 2 ^ N := Nat.lt_two_pow_self
        _ ≤ 4 ^ N := Nat.pow_le_pow_left (by norm_num) N
    have hpow : 4 ^ N ≤ 2 * 4 ^ (J + N) := by
      have hJ_pos : 1 ≤ 2 * 4 ^ J := Nat.mul_pos two_pos (by positivity)
      calc 4 ^ N = 1 * 4 ^ N := (one_mul _).symm
        _ ≤ (2 * 4 ^ J) * 4 ^ N := Nat.mul_le_mul_right _ hJ_pos
        _ = 2 * 4 ^ (J + N) := by rw [pow_add, mul_assoc]
    omega
  change (∑ k ∈ Finset.Icc (2 * 4 ^ J + 1) N, f k) ≤ (6 : ℝ) / (2 : ℝ) ^ J
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [f]; positivity).trans ?_
  refine (hM N).trans ?_
  have h1 : (0 : ℝ) ≤ ((6 : ℝ) / (2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ N := by positivity
  linarith

private lemma totient_cast_real_eq_mul_prod (D : ℕ) :
    (Nat.totient D : ℝ) = (D : ℝ) * ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hq := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors D)
  simpa using hq

private lemma prod_one_sub_inv_mul_harmonic_le_coprime_sum (D N : ℕ) (hD : 1 ≤ D) :
    ((Nat.totient D : ℝ) / (D : ℝ)) * (∑ w ∈ Finset.Icc 1 N, (1 : ℝ) / (w : ℝ)) ≤
      ∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => u.Coprime D), (1 : ℝ) / (u : ℝ) := by
  let invR : ℕ → ℝ := fun u => (1 : ℝ) / (u : ℝ)
  have hind : ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime) →
      (∏ p ∈ F, (1 - (p : ℝ)⁻¹)) * (∑ w ∈ Finset.Icc 1 N, invR w) ≤
        ∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => ∀ p ∈ F, ¬ p ∣ u), invR u := by
    intro F
    induction F using Finset.cons_induction with
    | empty =>
      intro _
      simp
    | cons p F hpNotMem ih =>
      intro hFprime
      have hp : p.Prime := hFprime p (Finset.mem_cons_self p F)
      have hF' : ∀ q ∈ F, q.Prime := fun q hq => hFprime q (Finset.mem_cons_of_mem hq)
      set SF := (Finset.Icc 1 N).filter (fun u : ℕ => ∀ q ∈ F, ¬ q ∣ u)
      have hsplit : (∑ u ∈ SF.filter (fun u => p ∣ u), invR u) +
          (∑ u ∈ SF.filter (fun u => ¬ p ∣ u), invR u) = ∑ u ∈ SF, invR u :=
        Finset.sum_filter_add_sum_filter_not SF (fun u => p ∣ u) invR
      have hdvd_le : (∑ u ∈ SF.filter (fun u => p ∣ u), invR u) ≤
          (p : ℝ)⁻¹ * ∑ v ∈ SF, invR v := by
        have hrew : (∑ u ∈ SF.filter (fun u => p ∣ u), invR u) =
            (p : ℝ)⁻¹ * ∑ u ∈ SF.filter (fun u => p ∣ u), invR (u / p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          dsimp [invR]
          have hpdvd : p ∣ u := (Finset.mem_filter.mp hu).2
          have hup : (u : ℝ) = (p : ℝ) * ((u / p : ℕ) : ℝ) := by
            exact_mod_cast (Nat.mul_div_cancel' hpdvd).symm
          rw [hup]
          field_simp
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinj : Set.InjOn (fun u : ℕ => u / p) ↑(SF.filter (fun u => p ∣ u)) := by
          intro u1 hu1 u2 hu2 heq
          dsimp at heq
          have hd1 : p ∣ u1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu1)).2
          have hd2 : p ∣ u2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu2)).2
          calc u1 = p * (u1 / p) := (Nat.mul_div_cancel' hd1).symm
            _ = p * (u2 / p) := by rw [heq]
            _ = u2 := Nat.mul_div_cancel' hd2
        rw [← Finset.sum_image (f := invR) hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => by dsimp [invR]; positivity
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
        rcases Finset.mem_filter.mp hu with ⟨huSF, hpdvd⟩
        rcases Finset.mem_filter.mp huSF with ⟨huIcc, huF⟩
        rcases Finset.mem_Icc.mp huIcc with ⟨hu1, huN⟩
        have hup_pos : 1 ≤ u / p := by
          rcases hpdvd with ⟨c, rfl⟩
          rw [Nat.mul_div_cancel_left c hp.pos]
          by_contra hc0
          have hc_eq0 : c = 0 := Nat.lt_one_iff.mp (not_le.mp hc0)
          rw [hc_eq0, mul_zero] at hu1
          omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hup_pos, (Nat.div_le_self u p).trans huN⟩, ?_⟩
        intro q hq hqdvd
        exact huF q hq (hqdvd.trans (Nat.div_dvd_of_dvd hpdvd))
      have hstep : (1 - (p : ℝ)⁻¹) * (∑ u ∈ SF, invR u) ≤
          ∑ u ∈ SF.filter (fun u => ¬ p ∣ u), invR u := by
        linarith
      have h1sub_nonneg : 0 ≤ 1 - (p : ℝ)⁻¹ := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
        linarith
      rw [Finset.prod_cons, mul_assoc]
      calc (1 - (p : ℝ)⁻¹) * ((∏ q ∈ F, (1 - (q : ℝ)⁻¹)) * ∑ w ∈ Finset.Icc 1 N, invR w)
        _ ≤ (1 - (p : ℝ)⁻¹) * (∑ u ∈ SF, invR u) :=
          mul_le_mul_of_nonneg_left (ih hF') h1sub_nonneg
        _ ≤ ∑ u ∈ SF.filter (fun u => ¬ p ∣ u), invR u := hstep
        _ = ∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => ∀ q ∈ Finset.cons p F hpNotMem, ¬ q ∣ u),
              invR u := by
          congr 1
          ext u
          simp only [SF, Finset.mem_filter, Finset.mem_cons, forall_eq_or_imp]
          tauto
  have hD0 : D ≠ 0 := by omega
  have htot : ((Nat.totient D : ℝ) / (D : ℝ)) = ∏ p ∈ D.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hD_real : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
    rw [totient_cast_real_eq_mul_prod D, mul_div_cancel_left₀ _ hD_real]
  rw [htot]
  refine (hind D.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp).trans (le_of_eq ?_)
  congr 1
  ext u
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro _
  constructor
  · intro h
    refine Nat.coprime_of_dvd' fun p hp hpu hpD => ?_
    exact (h p (Nat.mem_primeFactors.mpr ⟨hp, hpD, hD0⟩) hpu).elim
  · intro hcop p hp hpu
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpD : p ∣ D := Nat.dvd_of_mem_primeFactors hp
    have hdvd1 : p ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hpu hpD
    exact hp_prime.not_dvd_one hdvd1

private lemma pi_four_pow_succ_le (k : ℕ) :
    ((4 ^ (k + 1)).primeCounting : ℝ) ≤ 3 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hx : (1 : ℝ) < ((4 ^ (k + 1) : ℕ) : ℝ) := by
    have : 1 < 4 ^ (k + 1) := Nat.one_lt_pow (Nat.succ_ne_zero k) (by norm_num)
    exact_mod_cast this
  have hpi := Chebyshev.pi_le_log4_mul_div hx
  rw [Nat.floor_natCast] at hpi
  have h4sq : ((4 ^ (k + 1) : ℕ) : ℝ) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
    have hnat : 4 ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := by
      calc 4 ^ (k + 1) = (2 ^ 2) ^ (k + 1) := rfl
        _ = 2 ^ (2 * (k + 1)) := (pow_mul 2 2 (k + 1)).symm
        _ = 2 ^ ((k + 1) * 2) := by rw [mul_comm]
        _ = (2 ^ (k + 1)) ^ 2 := pow_mul 2 (k + 1) 2
    exact_mod_cast hnat
  have hsqrt : Real.sqrt ((4 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [h4sq, Real.sqrt_sq (by positivity)]
  have hlog2_pos : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) one_half_le_log_two
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]; ring
  have hlog_sqrt : Real.log (Real.sqrt ((4 ^ (k + 1) : ℕ) : ℝ)) = ((k : ℝ) + 1) * Real.log 2 := by
    rw [hsqrt, Real.log_pow]; push_cast; ring
  rw [hlog4, hlog_sqrt, hsqrt] at hpi
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hterm1 : 2 * Real.log 2 * ((4 ^ (k + 1) : ℕ) : ℝ) / (((k : ℝ) + 1) * Real.log 2) =
      2 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
    push_cast
    field_simp [hlog2_pos.ne', hk1_pos.ne']
  have hterm2 : (2 : ℝ) ^ (k + 1) ≤ (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk1_pos]
    have hk_lt : k + 1 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self.le
    have hk_real : (k : ℝ) + 1 ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hk_lt
    calc (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left hk_real (by positivity)
      _ = ((2 : ℝ) ^ (k + 1)) ^ 2 := (sq _).symm
      _ = (4 : ℝ) ^ (k + 1) := by exact_mod_cast h4sq.symm
  calc ((4 ^ (k + 1)).primeCounting : ℝ)
    _ ≤ 2 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) + (2 : ℝ) ^ (k + 1) := by rwa [hterm1] at hpi
    _ ≤ 2 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) + (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by gcongr
    _ = 3 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by ring

private lemma sum_primesLE_four_pow (K : ℕ) :
    (∑ r ∈ primesLE (4 ^ K), (1 : ℝ) / (r : ℝ)) ≤ 12 * (1 + Real.log (K : ℝ)) := by
  let invR : ℕ → ℝ := fun r => (1 : ℝ) / (r : ℝ)
  have hind : ∀ M : ℕ,
      (∑ r ∈ primesLE (4 ^ M), invR r) ≤ 12 * (harmonic M : ℝ) := by
    intro M
    induction M with
    | zero =>
      have hemp : primesLE (4 ^ 0) = ∅ := by
        ext r
        simp only [mem_primesLE, Finset.notMem_empty, iff_false, not_and]
        intro hr
        have := hr.two_le
        omega
      rw [hemp]
      simp
    | succ k ih =>
      set P1 := primesLE (4 ^ (k + 1))
      have hsplit : (∑ r ∈ P1.filter (fun r => r ≤ 4 ^ k), invR r) +
          (∑ r ∈ P1.filter (fun r => ¬ r ≤ 4 ^ k), invR r) = ∑ r ∈ P1, invR r :=
        Finset.sum_filter_add_sum_filter_not P1 (fun r => r ≤ 4 ^ k) invR
      have hfilt1 : P1.filter (fun r => r ≤ 4 ^ k) = primesLE (4 ^ k) := by
        ext r
        simp only [P1, Finset.mem_filter, mem_primesLE]
        refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans ?_⟩, h.2⟩⟩
        exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
      have hfilt2_le : (∑ r ∈ P1.filter (fun r => ¬ r ≤ 4 ^ k), invR r) ≤
          12 / ((k : ℝ) + 1) := by
        have hterm_le : ∀ r ∈ P1.filter (fun r => ¬ r ≤ 4 ^ k),
            invR r ≤ (4 : ℝ) / (4 : ℝ) ^ (k + 1) := by
          intro r hr
          dsimp [invR]
          have hr_gt : 4 ^ k < r := not_le.mp (Finset.mem_filter.mp hr).2
          have hr_ge : (4 : ℝ) ^ k ≤ (r : ℝ) := by exact_mod_cast hr_gt.le
          calc (1 : ℝ) / (r : ℝ) ≤ (1 : ℝ) / (4 : ℝ) ^ k :=
                one_div_le_one_div_of_le (by positivity) hr_ge
            _ = (4 : ℝ) / (4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
        have hcard_le : (#(P1.filter (fun r => ¬ r ≤ 4 ^ k)) : ℝ) ≤
            ((4 ^ (k + 1)).primeCounting : ℝ) := by
          have h1 : #(P1.filter (fun r => ¬ r ≤ 4 ^ k)) ≤ #P1 :=
            Finset.card_filter_le _ _
          have hP1 : #P1 = (4 ^ (k + 1)).primeCounting := card_primesLE (4 ^ (k + 1))
          exact_mod_cast (hP1 ▸ h1)
        calc (∑ r ∈ P1.filter (fun r => ¬ r ≤ 4 ^ k), invR r)
          _ ≤ ∑ _r ∈ P1.filter (fun r => ¬ r ≤ 4 ^ k), (4 : ℝ) / (4 : ℝ) ^ (k + 1) :=
            Finset.sum_le_sum hterm_le
          _ = (#(P1.filter (fun r => ¬ r ≤ 4 ^ k)) : ℝ) * ((4 : ℝ) / (4 : ℝ) ^ (k + 1)) := by
            simp [Finset.sum_const]
          _ ≤ (3 * (4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) * ((4 : ℝ) / (4 : ℝ) ^ (k + 1)) :=
            mul_le_mul_of_nonneg_right (hcard_le.trans (pi_four_pow_succ_le k)) (by positivity)
          _ = 12 / ((k : ℝ) + 1) := by
            have h40 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
            field_simp [h40]
            ring
      have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
        rw [harmonic_succ]
        push_cast
        ring
      rw [← hsplit, hfilt1, hharm, mul_add, mul_one_div]
      exact add_le_add ih hfilt2_le
  exact (hind K).trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log K) (by norm_num))

private lemma ratio_div_totient_le_poly (L s D : ℕ) (hs : 1 ≤ s) (hD1 : 1 ≤ D)
    (hD_le : D ≤ 4 ^ (L * 4 ^ s)) :
    (D : ℝ) / (Nat.totient D : ℝ) ≤ Real.exp (24 + 2 * (L : ℝ)) * (s : ℝ) ^ 24 := by
  have htot_pos : 0 < Nat.totient D := Nat.totient_pos.mpr hD1
  have hprod_id : (D : ℝ) / (Nat.totient D : ℝ) =
      ∏ r ∈ D.primeFactors, ((r : ℝ) / ((r : ℝ) - 1)) := by
    have hreal := totient_cast_real_eq_mul_prod D
    have hinv : (∏ r ∈ D.primeFactors, (1 - (r : ℝ)⁻¹)) *
        (∏ r ∈ D.primeFactors, ((r : ℝ) / ((r : ℝ) - 1))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun r hr => ?_
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).two_le
      have hr0 : (r : ℝ) ≠ 0 := by linarith
      have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hr0, hr1]
    rw [div_eq_iff (by positivity)]
    calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
      _ = (D : ℝ) * ((∏ r ∈ D.primeFactors, (1 - (r : ℝ)⁻¹)) *
            (∏ r ∈ D.primeFactors, ((r : ℝ) / ((r : ℝ) - 1)))) := by rw [hinv]
      _ = (∏ r ∈ D.primeFactors, ((r : ℝ) / ((r : ℝ) - 1))) * (Nat.totient D : ℝ) := by
        rw [hreal]; ring
  rw [hprod_id]
  set F1 := D.primeFactors.filter (fun r => r ≤ 4 ^ s)
  set F2 := D.primeFactors.filter (fun r => ¬ r ≤ 4 ^ s)
  have hsplit : (∏ r ∈ D.primeFactors, ((r : ℝ) / ((r : ℝ) - 1))) =
      (∏ r ∈ F1, ((r : ℝ) / ((r : ℝ) - 1))) * (∏ r ∈ F2, ((r : ℝ) / ((r : ℝ) - 1))) :=
    (Finset.prod_filter_mul_prod_filter_not D.primeFactors (fun r => r ≤ 4 ^ s) _).symm
  rw [hsplit]
  have hF1_le : (∏ r ∈ F1, ((r : ℝ) / ((r : ℝ) - 1))) ≤
      Real.exp 24 * (s : ℝ) ^ 24 := by
    have hterm : ∀ r ∈ F1, ((r : ℝ) / ((r : ℝ) - 1)) ≤ Real.exp (2 / (r : ℝ)) := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrp.two_le
      have hle : (r : ℝ) / ((r : ℝ) - 1) ≤ 2 / (r : ℝ) + 1 := by
        have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
        have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
        rw [div_le_iff₀ hr1_pos]
        field_simp [hr_pos.ne']
        nlinarith
      exact hle.trans (Real.add_one_le_exp (2 / (r : ℝ)))
    have hsub : F1 ⊆ primesLE (4 ^ s) := by
      intro r hr
      rcases Finset.mem_filter.mp hr with ⟨hrD, hrs⟩
      exact mem_primesLE.mpr ⟨Nat.prime_of_mem_primeFactors hrD, hrs⟩
    have hsum_le : (∑ r ∈ F1, 2 / (r : ℝ)) ≤ 24 + 24 * Real.log (s : ℝ) := by
      have h1 : (∑ r ∈ F1, 2 / (r : ℝ)) = 2 * ∑ r ∈ F1, (1 : ℝ) / (r : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [h1]
      have h2 : (∑ r ∈ F1, (1 : ℝ) / (r : ℝ)) ≤
          ∑ r ∈ primesLE (4 ^ s), (1 : ℝ) / (r : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity
      linarith [sum_primesLE_four_pow s]
    calc (∏ r ∈ F1, ((r : ℝ) / ((r : ℝ) - 1)))
      _ ≤ ∏ r ∈ F1, Real.exp (2 / (r : ℝ)) :=
        Finset.prod_le_prod (fun r hr => by
          have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).two_le
          exact div_nonneg (by positivity) (by linarith)) hterm
      _ = Real.exp (∑ r ∈ F1, 2 / (r : ℝ)) := (Real.exp_sum F1 _).symm
      _ ≤ Real.exp (24 + 24 * Real.log (s : ℝ)) := Real.exp_le_exp.mpr hsum_le
      _ = Real.exp 24 * (Real.exp (Real.log (s : ℝ))) ^ 24 := by
        rw [Real.exp_add, show (24 : ℝ) * Real.log (s : ℝ) = ((24 : ℕ) : ℝ) * Real.log (s : ℝ) by norm_num,
          Real.exp_nat_mul]
      _ = Real.exp 24 * (s : ℝ) ^ 24 := by
        have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
        rw [Real.exp_log hs_pos]
  have hF2_le : (∏ r ∈ F2, ((r : ℝ) / ((r : ℝ) - 1))) ≤ Real.exp (2 * (L : ℝ)) := by
    have hcard_D : #D.primeFactors ≤ 2 * L * 4 ^ s := by
      have h2pow : 2 ^ (#D.primeFactors) ≤ D := by
        calc 2 ^ (#D.primeFactors) = ∏ _r ∈ D.primeFactors, 2 := by simp
          _ ≤ ∏ r ∈ D.primeFactors, r :=
            Finset.prod_le_prod' fun r hr => (Nat.prime_of_mem_primeFactors hr).two_le
          _ ≤ D := Nat.le_of_dvd hD1 (Nat.prod_primeFactors_dvd D)
      have h4eq : 4 ^ (L * 4 ^ s) = 2 ^ (2 * L * 4 ^ s) := by
        calc 4 ^ (L * 4 ^ s) = (2 ^ 2) ^ (L * 4 ^ s) := rfl
          _ = 2 ^ (2 * (L * 4 ^ s)) := (pow_mul 2 2 (L * 4 ^ s)).symm
          _ = 2 ^ (2 * L * 4 ^ s) := by rw [mul_assoc]
      have hpow_le : 2 ^ (#D.primeFactors) ≤ 2 ^ (2 * L * 4 ^ s) :=
        h2pow.trans (h4eq ▸ hD_le)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow_le
    have hcard_F2 : (#F2 : ℝ) ≤ (2 * L * 4 ^ s : ℕ) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans hcard_D
    have hterm2 : ∀ r ∈ F2, ((r : ℝ) / ((r : ℝ) - 1)) ≤ Real.exp (1 / (4 : ℝ) ^ s) := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
      have hr_gt : 4 ^ s < r := not_le.mp (Finset.mem_filter.mp hr).2
      have hr1_nat : 4 ^ s ≤ r - 1 := Nat.le_sub_one_of_lt hr_gt
      have hr1_ge : (4 : ℝ) ^ s ≤ (r : ℝ) - 1 := by
        have hcast : ((4 ^ s : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hr1_nat
        simpa [Nat.cast_sub hrp.one_le] using hcast
      have h1 : (r : ℝ) / ((r : ℝ) - 1) = 1 / ((r : ℝ) - 1) + 1 := by
        have : (r : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) ≤ (4 : ℝ) ^ s := one_le_pow₀ (by norm_num)
          linarith
        field_simp [this]
        ring
      rw [h1]
      have h2 : 1 / ((r : ℝ) - 1) + 1 ≤ 1 / (4 : ℝ) ^ s + 1 := by
        have := one_div_le_one_div_of_le (by positivity) hr1_ge
        linarith
      exact h2.trans (Real.add_one_le_exp (1 / (4 : ℝ) ^ s))
    calc (∏ r ∈ F2, ((r : ℝ) / ((r : ℝ) - 1)))
      _ ≤ ∏ _r ∈ F2, Real.exp (1 / (4 : ℝ) ^ s) :=
        Finset.prod_le_prod (fun r hr => by
          have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).two_le
          exact div_nonneg (by positivity) (by linarith)) hterm2
      _ = Real.exp ((#F2 : ℝ) * (1 / (4 : ℝ) ^ s)) := by
        rw [← Real.exp_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (2 * (L : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        calc (#F2 : ℝ) * (1 / (4 : ℝ) ^ s)
          _ ≤ ((2 * L * 4 ^ s : ℕ) : ℝ) * (1 / (4 : ℝ) ^ s) :=
            mul_le_mul_of_nonneg_right hcard_F2 (by positivity)
          _ = 2 * (L : ℝ) := by
            push_cast
            have h40 : (4 : ℝ) ^ s ≠ 0 := by positivity
            field_simp [h40]
  calc (∏ r ∈ F1, ((r : ℝ) / ((r : ℝ) - 1))) * (∏ r ∈ F2, ((r : ℝ) / ((r : ℝ) - 1)))
    _ ≤ (Real.exp 24 * (s : ℝ) ^ 24) * Real.exp (2 * (L : ℝ)) :=
      mul_le_mul hF1_le hF2_le (Finset.prod_nonneg fun r hr => by
        have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).two_le
        exact div_nonneg (by positivity) (by linarith)) (by positivity)
    _ = Real.exp (24 + 2 * (L : ℝ)) * (s : ℝ) ^ 24 := by
      rw [Real.exp_add]; ring

private lemma sum_geom_inv_le (r M : ℕ) (hr : 2 ≤ r) :
    (∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / (r : ℝ) ^ e) ≤ (1 : ℝ) / ((r : ℝ) - 1) := by
  have hr_real : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hr1_pos]
  have hident : ∀ k : ℕ, ((∑ e ∈ Finset.Icc 1 k, (1 : ℝ) / (r : ℝ) ^ e) * ((r : ℝ) - 1)) =
      1 - (1 : ℝ) / (r : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ihj =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 j), add_mul, ihj, pow_succ]
      have hr0 : (r : ℝ) ≠ 0 := by linarith
      field_simp [hr0]
      ring
  rw [hident M]
  have : (0 : ℝ) ≤ (1 : ℝ) / (r : ℝ) ^ M := by positivity
  linarith

private lemma sum_inv_bounded_omega_le (M R : ℕ) :
    (∑ z ∈ (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ R), (1 : ℝ) / (z : ℝ)) ≤
      (1 + ∑ r ∈ primesLE M, (2 : ℝ) / (r : ℝ)) ^ R := by
  let invR : ℕ → ℝ := fun z => (1 : ℝ) / (z : ℝ)
  set S := ∑ r ∈ primesLE M, (2 : ℝ) / (r : ℝ)
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun r _ => by positivity
  induction R with
  | zero =>
    have hsub : (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ 0) ⊆ {1} := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hz ⊢
      have hcard0 : z.primeFactors = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hz.2)
      by_contra hz1
      have hz_gt1 : 1 < z := by omega
      exact Finset.Nonempty.ne_empty (Nat.nonempty_primeFactors.mpr hz_gt1) hcard0
    calc (∑ z ∈ (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ 0), invR z)
      _ ≤ ∑ z ∈ ({1} : Finset ℕ), invR z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [invR]; positivity
      _ = 1 := by simp [invR]
      _ = (1 + S) ^ 0 := by simp
  | succ k ih =>
    set A := (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ k)
    set B := (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors = k + 1)
    have hunion : (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ k + 1) = A ∪ B := by
      ext z
      simp only [A, B, Finset.mem_union, Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => (Nat.le_succ_iff.mp h2).imp (fun h => ⟨h1, h⟩) (fun h => ⟨h1, h⟩),
        fun h => h.elim (fun ⟨h1, h2⟩ => ⟨h1, Nat.le_succ_of_le h2⟩)
          (fun ⟨h1, h2⟩ => ⟨h1, h2.le⟩)⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      have h1 := (Finset.mem_filter.mp hzA).2
      have h2 := (Finset.mem_filter.mp hzB).2
      omega
    change (∑ z ∈ (Finset.Icc 1 M).filter (fun z : ℕ => #z.primeFactors ≤ k + 1), invR z) ≤ _
    rw [hunion, Finset.sum_union hdisj]
    set T := (primesLE M ×ˢ Finset.Icc 1 M) ×ˢ A
    let mulMap : (ℕ × ℕ) × ℕ → ℕ := fun p => p.1.1 ^ p.1.2 * p.2
    have hB_sub : B ⊆ T.image mulMap := by
      intro z hzB
      rcases Finset.mem_filter.mp hzB with ⟨hzIcc, hzcard⟩
      rcases Finset.mem_Icc.mp hzIcc with ⟨hz1, hzM⟩
      have hz0 : z ≠ 0 := by omega
      set r := z.minFac
      have hrp : r.Prime := Nat.minFac_prime (by
        intro h
        subst h
        simp at hzcard)
      have hrdvd : r ∣ z := Nat.minFac_dvd z
      set e := z.factorization r
      set w := z / r ^ e
      have he_pos : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hrp hz0 hrdvd
      have hrew : r ^ e * w = z := Nat.ordProj_mul_ordCompl_eq_self z r
      have he_le_M : e ≤ M := by
        have h1 : e < 2 ^ e := Nat.lt_two_pow_self
        have h2 : 2 ^ e ≤ r ^ e := Nat.pow_le_pow_left hrp.two_le e
        have h3 : r ^ e ≤ z := Nat.le_of_dvd hz1 ⟨w, hrew.symm⟩
        omega
      have hw_pos : 1 ≤ w := by
        by_contra hw0
        have hw_eq0 : w = 0 := Nat.lt_one_iff.mp (not_le.mp hw0)
        rw [hw_eq0, mul_zero] at hrew
        exact hz0 hrew.symm
      have hw_le_M : w ≤ M := (Nat.div_le_self z (r ^ e)).trans hzM
      have hnot_r_w : ¬ r ∣ w := Nat.not_dvd_ordCompl hrp hz0
      have hpf_z : z.primeFactors = (r ^ e).primeFactors ∪ w.primeFactors := by
        rw [← hrew, Nat.primeFactors_mul (pow_ne_zero e hrp.ne_zero) (by omega)]
      have hpf_re : (r ^ e).primeFactors = {r} :=
        Nat.primeFactors_prime_pow (by omega) hrp
      have hr_not_w : r ∉ w.primeFactors := fun hmem => hnot_r_w (Nat.dvd_of_mem_primeFactors hmem)
      have hw_card : #w.primeFactors = k := by
        rw [hpf_z, hpf_re, Finset.singleton_union, Finset.card_insert_of_notMem hr_not_w] at hzcard
        omega
      have hr_le_M : r ≤ M := (Nat.le_of_dvd hz1 hrdvd).trans hzM
      refine Finset.mem_image.mpr ⟨((r, e), w), ?_, hrew⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨mem_primesLE.mpr ⟨hrp, hr_le_M⟩, Finset.mem_Icc.mpr ⟨he_pos, he_le_M⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hw_pos, hw_le_M⟩, hw_card.le⟩⟩
    have hB_le : (∑ z ∈ B, invR z) ≤ S * (1 + S) ^ k := by
      calc (∑ z ∈ B, invR z)
        _ ≤ ∑ z ∈ T.image mulMap, invR z :=
          Finset.sum_le_sum_of_subset_of_nonneg hB_sub fun x _ _ => by dsimp [invR]; positivity
        _ ≤ ∑ p ∈ T, invR (mulMap p) :=
          Finset.sum_image_le_of_nonneg fun p _ => by dsimp [invR]; positivity
        _ = (∑ r ∈ primesLE M, ∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / (r : ℝ) ^ e) *
            (∑ w ∈ A, invR w) := by
          simp only [T, invR, mulMap]
          rw [Finset.sum_product, Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          push_cast; ring
        _ ≤ S * (1 + S) ^ k := by
          have h1 : (∑ r ∈ primesLE M, ∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / (r : ℝ) ^ e) ≤ S := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hrp : r.Prime := (mem_primesLE.mp hr).1
            have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrp.two_le
            refine (sum_geom_inv_le r M hrp.two_le).trans ?_
            have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
            have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
            rw [div_le_div_iff₀ hr1_pos hr_pos]
            linarith
          exact mul_le_mul h1 ih (Finset.sum_nonneg fun w _ =>
            by dsimp [invR]; positivity) (by positivity)
    calc (∑ z ∈ A, invR z) + (∑ z ∈ B, invR z)
      _ ≤ (1 + S) ^ k + S * (1 + S) ^ k := add_le_add ih hB_le
      _ = (1 + S) ^ (k + 1) := by ring

/- ## Part 3: Periodic Counting, CRT via ZMod, and Sieve Corollaries 2A & 2B -/

private lemma abs_card_filter_Icc_sub_le (M d : ℕ) (hd : 0 < d) (P : ℕ → Prop) [DecidablePred P]
    (hper : ∀ t, P (t + d) ↔ P t) :
    |((#(Finset.Icc 1 M |>.filter P) : ℕ) : ℝ) -
      ((#(Finset.range d |>.filter P) : ℕ) : ℝ) / (d : ℝ) * (M : ℝ)| ≤
      ((#(Finset.range d |>.filter P) : ℕ) : ℝ) := by
  set c := #((Finset.range d).filter P)
  have hshift : ∀ a : ℕ, #((Finset.Ico a (a + d)).filter P) = c := by
    intro a
    induction a with
    | zero => simp [c]
    | succ k ih =>
      have hk1 : Finset.Ico k (k + d) = insert k (Finset.Ico (k + 1) (k + d)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hk2 : Finset.Ico (k + 1) (k + 1 + d) = insert (k + d) (Finset.Ico (k + 1) (k + d)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnot1 : k ∉ (Finset.Ico (k + 1) (k + d)).filter P := by simp
      have hnot2 : k + d ∉ (Finset.Ico (k + 1) (k + d)).filter P := by simp
      rw [hk2, Finset.filter_insert]
      rw [hk1, Finset.filter_insert] at ih
      by_cases hPk : P k
      · have hPkd : P (k + d) := (hper k).mpr hPk
        rw [if_pos hPkd, Finset.card_insert_of_notMem hnot2]
        rw [if_pos hPk, Finset.card_insert_of_notMem hnot1] at ih
        exact ih
      · have hPkd : ¬ P (k + d) := fun h => hPk ((hper k).mp h)
        rw [if_neg hPkd]
        rw [if_neg hPk] at ih
        exact ih
  have hmult : ∀ q : ℕ, #((Finset.Ico 1 (1 + d * q)).filter P) = c * q := by
    intro q
    induction q with
    | zero => simp
    | succ m ihm =>
      have hle1 : 1 ≤ 1 + d * m := Nat.le_add_right 1 _
      have hle2 : 1 + d * m ≤ 1 + d * m + d := Nat.le_add_right _ _
      have hunion : Finset.Ico 1 (1 + d * (m + 1)) =
          Finset.Ico 1 (1 + d * m) ∪ Finset.Ico (1 + d * m) (1 + d * m + d) := by
        rw [show 1 + d * (m + 1) = 1 + d * m + d by ring]
        exact (Finset.Ico_union_Ico_eq_Ico hle1 hle2).symm
      have hdisj : Disjoint (Finset.Ico 1 (1 + d * m)) (Finset.Ico (1 + d * m) (1 + d * m + d)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Ico] at hx1 hx2
        omega
      rw [hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj),
        ihm, hshift (1 + d * m), mul_add, mul_one]
  set q := M / d
  have hIcc : Finset.Icc 1 M = Finset.Ico 1 (1 + M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hsub_lo : (Finset.Ico 1 (1 + d * q)).filter P ⊆ (Finset.Icc 1 M).filter P := by
    rw [hIcc]
    refine Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right ?_)
    dsimp only [q]
    have := Nat.mul_div_le M d
    omega
  have hsub_hi : (Finset.Icc 1 M).filter P ⊆ (Finset.Ico 1 (1 + d * (q + 1))).filter P := by
    rw [hIcc]
    refine Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right ?_)
    dsimp only [q]
    have := Nat.lt_mul_div_succ M hd
    omega
  have hcard_lo : c * q ≤ #((Finset.Icc 1 M).filter P) := by
    rw [← hmult q]
    exact Finset.card_le_card hsub_lo
  have hcard_hi : #((Finset.Icc 1 M).filter P) ≤ c * q + c := by
    have := (Finset.card_le_card hsub_hi).trans_eq (hmult (q + 1))
    linarith
  have hA_lo : (c : ℝ) * (q : ℝ) ≤ ((#((Finset.Icc 1 M).filter P) : ℕ) : ℝ) := by
    exact_mod_cast hcard_lo
  have hA_hi : ((#((Finset.Icc 1 M).filter P) : ℕ) : ℝ) ≤ (c : ℝ) * (q : ℝ) + (c : ℝ) := by
    exact_mod_cast hcard_hi
  have hd_pos_real : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM_lo : (d : ℝ) * (q : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.mul_div_le M d
  have hM_hi : (M : ℝ) ≤ (d : ℝ) * ((q : ℝ) + 1) := by
    exact_mod_cast (Nat.lt_mul_div_succ M hd).le
  have hB_lo : (c : ℝ) * (q : ℝ) ≤ (c : ℝ) / (d : ℝ) * (M : ℝ) := by
    have := mul_le_mul_of_nonneg_left hM_lo (show (0 : ℝ) ≤ (c : ℝ) / (d : ℝ) by positivity)
    have hd0 : (d : ℝ) ≠ 0 := hd_pos_real.ne'
    have hsimp : (c : ℝ) / (d : ℝ) * ((d : ℝ) * (q : ℝ)) = (c : ℝ) * (q : ℝ) := by
      field_simp [hd0]
    linarith
  have hB_hi : (c : ℝ) / (d : ℝ) * (M : ℝ) ≤ (c : ℝ) * (q : ℝ) + (c : ℝ) := by
    have := mul_le_mul_of_nonneg_left hM_hi (show (0 : ℝ) ≤ (c : ℝ) / (d : ℝ) by positivity)
    have hd0 : (d : ℝ) ≠ 0 := hd_pos_real.ne'
    have hsimp : (c : ℝ) / (d : ℝ) * ((d : ℝ) * ((q : ℝ) + 1)) = (c : ℝ) * (q : ℝ) + (c : ℝ) := by
      field_simp [hd0]
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

private lemma squarefree_prod_primes {F : Finset ℕ} (hF : ∀ r ∈ F, r.Prime) :
    Squarefree (∏ r ∈ F, r) := by
  induction F using Finset.cons_induction with
  | empty => simp
  | cons p F hpNotMem ih =>
    have hp : p.Prime := hF p (Finset.mem_cons_self p F)
    have hF' : ∀ r ∈ F, r.Prime := fun r hr => hF r (Finset.mem_cons_of_mem hr)
    rw [Finset.prod_cons, Nat.squarefree_mul_iff]
    refine ⟨?_, hp.squarefree, ih hF'⟩
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases (hp.prime.dvd_finsetProd_iff _).mp hdvd with ⟨r, hrF, hpr⟩
    have hrp : r.Prime := hF' r hrF
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr
    subst heq
    exact hpNotMem hrF

private lemma card_range_dvd_linear_eq_one {d m : ℕ} (hd : 0 < d) (hcop : m.Coprime d) :
    #((Finset.range d).filter (fun t => d ∣ m * t + 1)) = 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  set u : (ZMod d)ˣ := ZMod.unitOfCoprime m hcop
  set x0 : ZMod d := -((↑u⁻¹ : ZMod d))
  have heq_set : (Finset.range d).filter (fun t => d ∣ m * t + 1) = {ZMod.val x0} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hdvd⟩
      have hz : (((m * t + 1 : ℕ) : ZMod d)) = 0 :=
        (ZMod.natCast_eq_zero_iff (m * t + 1) d).mpr hdvd
      push_cast at hz
      have hu : (u : ZMod d) = (m : ZMod d) := ZMod.coe_unitOfCoprime m hcop
      rw [← hu] at hz
      have hx : (t : ZMod d) = x0 := by
        have h1 : (↑u⁻¹ : ZMod d) * ((u : ZMod d) * (t : ZMod d) + 1) = 0 := by
          rw [hz, mul_zero]
        have h2 : (↑u⁻¹ : ZMod d) * (u : ZMod d) = 1 := Units.inv_mul u
        have h3 : (t : ZMod d) + (↑u⁻¹ : ZMod d) = 0 := by
          calc (t : ZMod d) + (↑u⁻¹ : ZMod d)
            _ = ((↑u⁻¹ : ZMod d) * (u : ZMod d)) * (t : ZMod d) + (↑u⁻¹ : ZMod d) * 1 := by
              rw [h2, one_mul, mul_one]
            _ = (↑u⁻¹ : ZMod d) * ((u : ZMod d) * (t : ZMod d) + 1) := by ring
            _ = 0 := h1
        exact eq_neg_of_add_eq_zero_left h3
      have hval := congrArg ZMod.val hx
      rwa [ZMod.val_natCast_of_lt ht] at hval
    · rintro rfl
      refine ⟨ZMod.val_lt x0, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val x0]
      have hu : (u : ZMod d) = (m : ZMod d) := ZMod.coe_unitOfCoprime m hcop
      rw [← hu]
      simp [x0]
  rw [heq_set, Finset.card_singleton]

private lemma card_range_eq_card_zmod_two_linear (a n0 d : ℕ) [NeZero d] :
    #((Finset.range d).filter (fun t => d ∣ (a * t + 1) * (n0 * t + 1))) =
      #(Finset.univ.filter (fun x : ZMod d =>
        ((a : ZMod d) * x + 1) * ((n0 : ZMod d) * x + 1) = 0)) := by
  set SZ := Finset.univ.filter (fun x : ZMod d =>
    ((a : ZMod d) * x + 1) * ((n0 : ZMod d) * x + 1) = 0)
  have himg : (Finset.range d).filter (fun t => d ∣ (a * t + 1) * (n0 * t + 1)) =
      SZ.image ZMod.val := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, SZ, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, hdvd⟩
      refine ⟨(t : ZMod d), ?_, ZMod.val_natCast_of_lt ht⟩
      have hz := (ZMod.natCast_eq_zero_iff ((a * t + 1) * (n0 * t + 1)) d).mpr hdvd
      simpa using hz
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ZMod.val_lt x, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rwa [ZMod.natCast_zmod_val]
  rw [himg, Finset.card_image_of_injective _ (ZMod.val_injective d)]

private lemma card_range_two_linear {a n0 d : ℕ} (hd : 0 < d) (hsq : Squarefree d)
    (hD : ∀ r ∈ d.primeFactors, ¬ r ∣ 2 * a * n0 * (max a n0 - min a n0)) :
    #((Finset.range d).filter (fun t => d ∣ (a * t + 1) * (n0 * t + 1))) =
      2 ^ (#d.primeFactors) := by
  revert hd hsq hD
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ d
  · intro r e hr _ _ hsq hD
    have he1 : e = 1 := by
      by_contra he_ne
      have he2 : 2 ≤ e := by
        rcases eq_or_ne e 0 with rfl | he0
        · simp at hsq; omega
        · omega
      have hdvd : r * r ∣ r ^ e := by
        calc r * r = r ^ 2 := (sq r).symm
          _ ∣ r ^ e := Nat.pow_dvd_pow r he2
      exact hr.ne_one (Nat.isUnit_iff.mp (hsq r hdvd))
    subst he1
    rw [pow_one] at hD ⊢
    have : Fact r.Prime := ⟨hr⟩
    have : NeZero r := ⟨hr.ne_zero⟩
    rw [card_range_eq_card_zmod_two_linear a n0 r]
    have hr_mem : r ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, dvd_refl r, hr.ne_zero⟩
    have hnotD : ¬ r ∣ 2 * a * n0 * (max a n0 - min a n0) := hD r hr_mem
    have ha0 : (a : ZMod r) ≠ 0 := by
      intro h0
      have hra : r ∣ a := (ZMod.natCast_eq_zero_iff a r).mp h0
      exact hnotD (hra.trans ⟨2 * n0 * (max a n0 - min a n0), by ring⟩)
    have hn0_ne : (n0 : ZMod r) ≠ 0 := by
      intro h0
      have hrn : r ∣ n0 := (ZMod.natCast_eq_zero_iff n0 r).mp h0
      exact hnotD (hrn.trans ⟨2 * a * (max a n0 - min a n0), by ring⟩)
    set x1 : ZMod r := -(a : ZMod r)⁻¹
    set x2 : ZMod r := -(n0 : ZMod r)⁻¹
    have hne : x1 ≠ x2 := by
      intro heq
      have hinv : (a : ZMod r)⁻¹ = (n0 : ZMod r)⁻¹ := neg_inj.mp heq
      have han : (a : ZMod r) = (n0 : ZMod r) := inv_inj.mp hinv
      have hdiff_zero : (((max a n0 - min a n0 : ℕ) : ZMod r)) = 0 := by
        rcases le_total a n0 with hle | hle
        · rw [max_eq_right hle, min_eq_left hle, Nat.cast_sub hle, han, sub_self]
        · rw [max_eq_left hle, min_eq_right hle, Nat.cast_sub hle, han, sub_self]
      have hrdiff : r ∣ max a n0 - min a n0 :=
        (ZMod.natCast_eq_zero_iff _ r).mp hdiff_zero
      exact hnotD (hrdiff.trans ⟨2 * a * n0, by ring⟩)
    have hset : Finset.univ.filter (fun x : ZMod r =>
        ((a : ZMod r) * x + 1) * ((n0 : ZMod r) * x + 1) = 0) = {x1, x2} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hmul
        rcases mul_eq_zero.mp hmul with h1 | h2
        · left
          have : (a : ZMod r)⁻¹ * ((a : ZMod r) * x + 1) = 0 := by rw [h1, mul_zero]
          have : x + (a : ZMod r)⁻¹ = 0 := by
            calc x + (a : ZMod r)⁻¹ = ((a : ZMod r)⁻¹ * (a : ZMod r)) * x + (a : ZMod r)⁻¹ * 1 := by
                  rw [inv_mul_cancel₀ ha0, one_mul, mul_one]
              _ = (a : ZMod r)⁻¹ * ((a : ZMod r) * x + 1) := by ring
              _ = 0 := this
          exact eq_neg_of_add_eq_zero_left this
        · right
          have : (n0 : ZMod r)⁻¹ * ((n0 : ZMod r) * x + 1) = 0 := by rw [h2, mul_zero]
          have : x + (n0 : ZMod r)⁻¹ = 0 := by
            calc x + (n0 : ZMod r)⁻¹ = ((n0 : ZMod r)⁻¹ * (n0 : ZMod r)) * x + (n0 : ZMod r)⁻¹ * 1 := by
                  rw [inv_mul_cancel₀ hn0_ne, one_mul, mul_one]
              _ = (n0 : ZMod r)⁻¹ * ((n0 : ZMod r) * x + 1) := by ring
              _ = 0 := this
          exact eq_neg_of_add_eq_zero_left this
      · rintro (rfl | rfl)
        · simp [x1, mul_neg, mul_inv_cancel₀ ha0]
        · simp [x2, mul_neg, mul_inv_cancel₀ hn0_ne]
    rw [hset, Finset.card_pair hne, hr.primeFactors, Finset.card_singleton, pow_one]
  · intro hd
    omega
  · intro _ _ _
    simp
  · intro d1 d2 hd1 hd2 hcop ih1 ih2 _ hsq hD
    have hd1_pos : 0 < d1 := by omega
    have hd2_pos : 0 < d2 := by omega
    have : NeZero d1 := ⟨hd1_pos.ne'⟩
    have : NeZero d2 := ⟨hd2_pos.ne'⟩
    have : NeZero (d1 * d2) := ⟨(mul_pos hd1_pos hd2_pos).ne'⟩
    have hsq1 : Squarefree d1 := hsq.squarefree_of_dvd (dvd_mul_right d1 d2)
    have hsq2 : Squarefree d2 := hsq.squarefree_of_dvd (dvd_mul_left d2 d1)
    have hpf_union : (d1 * d2).primeFactors = d1.primeFactors ∪ d2.primeFactors :=
      Nat.primeFactors_mul hd1_pos.ne' hd2_pos.ne'
    have hD1 : ∀ r ∈ d1.primeFactors, ¬ r ∣ 2 * a * n0 * (max a n0 - min a n0) :=
      fun r hr => hD r (hpf_union ▸ Finset.mem_union_left _ hr)
    have hD2 : ∀ r ∈ d2.primeFactors, ¬ r ∣ 2 * a * n0 * (max a n0 - min a n0) :=
      fun r hr => hD r (hpf_union ▸ Finset.mem_union_right _ hr)
    rw [card_range_eq_card_zmod_two_linear a n0 (d1 * d2)]
    set e := ZMod.chineseRemainder hcop
    set S12 := Finset.univ.filter (fun x : ZMod (d1 * d2) =>
      ((a : ZMod (d1 * d2)) * x + 1) * ((n0 : ZMod (d1 * d2)) * x + 1) = 0)
    set S1 := Finset.univ.filter (fun x : ZMod d1 =>
      ((a : ZMod d1) * x + 1) * ((n0 : ZMod d1) * x + 1) = 0)
    set S2 := Finset.univ.filter (fun x : ZMod d2 =>
      ((a : ZMod d2) * x + 1) * ((n0 : ZMod d2) * x + 1) = 0)
    have hcard_prod : #S12 = #(S1 ×ˢ S2) := by
      refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
      · intro x hx
        have hx0 : ((a : ZMod (d1 * d2)) * x + 1) * ((n0 : ZMod (d1 * d2)) * x + 1) = 0 :=
          (Finset.mem_filter.mp hx).2
        have hex : e (((a : ZMod (d1 * d2)) * x + 1) * ((n0 : ZMod (d1 * d2)) * x + 1)) = 0 := by
          rw [hx0, map_zero]
        simp only [map_mul, map_add, map_natCast, map_one] at hex
        rcases Prod.ext_iff.mp hex with ⟨h1, h2⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
      · intro x _ y _ hxy
        exact e.injective hxy
      · rintro ⟨y1, y2⟩ hy
        rcases Finset.mem_product.mp hy with ⟨hy1, hy2⟩
        refine ⟨e.symm (y1, y2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply _⟩
        apply e.injective
        rw [map_zero]
        simp only [map_mul, map_add, map_natCast, map_one, e.apply_symm_apply]
        exact Prod.ext (Finset.mem_filter.mp hy1).2 (Finset.mem_filter.mp hy2).2
    have hc1 : #S1 = 2 ^ (#d1.primeFactors) := by
      rw [← card_range_eq_card_zmod_two_linear a n0 d1]
      exact ih1 hd1_pos hsq1 hD1
    have hc2 : #S2 = 2 ^ (#d2.primeFactors) := by
      rw [← card_range_eq_card_zmod_two_linear a n0 d2]
      exact ih2 hd2_pos hsq2 hD2
    rw [hcard_prod, Finset.card_product, hc1, hc2,
      ← pow_add, hpf_union, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]

private lemma sum_inv_exact_primeFactors_le (N : ℕ) (F : Finset ℕ) (hF : ∀ r ∈ F, r.Prime) :
    (∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => u.primeFactors = F), (1 : ℝ) / (u : ℝ)) ≤
      ∏ r ∈ F, ((1 : ℝ) / ((r : ℝ) - 1)) := by
  let invR : ℕ → ℝ := fun u => (1 : ℝ) / (u : ℝ)
  induction F using Finset.cons_induction with
  | empty =>
    have hsub : (Finset.Icc 1 N).filter (fun u : ℕ => u.primeFactors = ∅) ⊆ {1} := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huIcc, hpf⟩
      rcases Finset.mem_Icc.mp huIcc with ⟨hu1, _⟩
      simp only [Finset.mem_singleton]
      by_contra hu_ne1
      have : 1 < u := by omega
      exact Finset.Nonempty.ne_empty (Nat.nonempty_primeFactors.mpr this) hpf
    calc (∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => u.primeFactors = ∅), invR u)
      _ ≤ ∑ u ∈ ({1} : Finset ℕ), invR u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [invR]; positivity
      _ = 1 := by simp [invR]
      _ = ∏ r ∈ (∅ : Finset ℕ), ((1 : ℝ) / ((r : ℝ) - 1)) := by simp
  | cons p F hpNotMem ih =>
    have hp : p.Prime := hF p (Finset.mem_cons_self p F)
    have hF' : ∀ r ∈ F, r.Prime := fun r hr => hF r (Finset.mem_cons_of_mem hr)
    set WF := (Finset.Icc 1 N).filter (fun w : ℕ => w.primeFactors = F)
    set T := Finset.Icc 1 N ×ˢ WF
    let mulMap : ℕ × ℕ → ℕ := fun ew => p ^ ew.1 * ew.2
    have hsub : (Finset.Icc 1 N).filter (fun u : ℕ => u.primeFactors = Finset.cons p F hpNotMem) ⊆
        T.image mulMap := by
      intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huIcc, hupf⟩
      rcases Finset.mem_Icc.mp huIcc with ⟨hu1, huN⟩
      have hu0 : u ≠ 0 := by omega
      have hp_mem : p ∈ u.primeFactors := by rw [hupf]; exact Finset.mem_cons_self p F
      have hpdvd : p ∣ u := Nat.dvd_of_mem_primeFactors hp_mem
      set e := u.factorization p
      set w := u / p ^ e
      have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp hu0 hpdvd
      have hrew : p ^ e * w = u := Nat.ordProj_mul_ordCompl_eq_self u p
      have heN : e ≤ N := by
        have h1 : e < 2 ^ e := Nat.lt_two_pow_self
        have h2 : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        have h3 : p ^ e ≤ u := Nat.le_of_dvd hu1 ⟨w, hrew.symm⟩
        omega
      have hw1 : 1 ≤ w := by
        by_contra hw0
        have hw_eq0 : w = 0 := Nat.lt_one_iff.mp (not_le.mp hw0)
        rw [hw_eq0, mul_zero] at hrew
        exact hu0 hrew.symm
      have hwN : w ≤ N := (Nat.div_le_self u (p ^ e)).trans huN
      have hnot_pw : ¬ p ∣ w := Nat.not_dvd_ordCompl hp hu0
      have hpf_u : u.primeFactors = {p} ∪ w.primeFactors := by
        rw [← hrew, Nat.primeFactors_mul (pow_ne_zero e hp.ne_zero) (by omega),
          Nat.primeFactors_prime_pow (by omega) hp]
      have hp_not_w : p ∉ w.primeFactors := fun hm => hnot_pw (Nat.dvd_of_mem_primeFactors hm)
      have hwpf : w.primeFactors = F := by
        have h1 : insert p w.primeFactors = insert p F := by
          simpa [Finset.singleton_union] using hpf_u.symm.trans hupf
        have h2 := congrArg (fun s => Finset.erase s p) h1
        rwa [Finset.erase_insert hp_not_w, Finset.erase_insert hpNotMem] at h2
      refine Finset.mem_image.mpr ⟨(e, w), ?_, hrew⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨he1, heN⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hw1, hwN⟩, hwpf⟩⟩
    calc (∑ u ∈ (Finset.Icc 1 N).filter (fun u : ℕ => u.primeFactors = Finset.cons p F hpNotMem),
          invR u)
      _ ≤ ∑ u ∈ T.image mulMap, invR u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [invR]; positivity
      _ ≤ ∑ ew ∈ T, invR (mulMap ew) :=
        Finset.sum_image_le_of_nonneg fun x _ => by dsimp [invR]; positivity
      _ = (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (p : ℝ) ^ e) * (∑ w ∈ WF, invR w) := by
        simp only [T, invR, mulMap, Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        push_cast; ring
      _ ≤ ((1 : ℝ) / ((p : ℝ) - 1)) * (∏ r ∈ F, ((1 : ℝ) / ((r : ℝ) - 1))) := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        have hp1_nonneg : (0 : ℝ) ≤ (1 : ℝ) / ((p : ℝ) - 1) :=
          div_nonneg zero_le_one (by linarith)
        exact mul_le_mul (sum_geom_inv_le p N hp.two_le) (ih hF')
          (Finset.sum_nonneg fun x _ => by dsimp [invR]; positivity) hp1_nonneg
      _ = ∏ r ∈ Finset.cons p F hpNotMem, ((1 : ℝ) / ((r : ℝ) - 1)) := by
        rw [Finset.prod_cons]

private lemma sum_inv_pair_exact_primeFactors_le (N : ℕ) (F : Finset ℕ)
    (hF : ∀ r ∈ F, r.Prime ∧ 3 ≤ r) :
    (∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = F),
      (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))) ≤
      ∏ r ∈ F, ((2 : ℝ) / ((r : ℝ) - 2)) := by
  let invR2 : ℕ × ℕ → ℝ := fun x => (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
  induction F using Finset.cons_induction with
  | empty =>
    have hsub : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = ∅) ⊆ {(1, 1)} := by
      rintro ⟨u1, u2⟩ hu
      rcases Finset.mem_filter.mp hu with ⟨huProd, hpf⟩
      rcases Finset.mem_product.mp huProd with ⟨hu1, hu2⟩
      have h1 : 1 ≤ u1 := (Finset.mem_Icc.mp hu1).1
      have h2 : 1 ≤ u2 := (Finset.mem_Icc.mp hu2).1
      simp only [Finset.mem_singleton]
      have hmul1 : u1 * u2 = 1 := by
        by_contra hne
        have hge1 : 1 ≤ u1 * u2 := Nat.mul_le_mul h1 h2
        have hgt : 1 < u1 * u2 := by omega
        exact Finset.Nonempty.ne_empty (Nat.nonempty_primeFactors.mpr hgt) hpf
      exact Prod.ext (Nat.eq_one_of_mul_eq_one_right hmul1) (Nat.eq_one_of_mul_eq_one_left hmul1)
    calc (∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
          (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = ∅), invR2 x)
      _ ≤ ∑ x ∈ ({(1, 1)} : Finset (ℕ × ℕ)), invR2 x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [invR2]; positivity
      _ = 1 := by simp [invR2]
      _ = ∏ r ∈ (∅ : Finset ℕ), ((2 : ℝ) / ((r : ℝ) - 2)) := by simp
  | cons p F hpNotMem ih =>
    rcases hF p (Finset.mem_cons_self p F) with ⟨hp, hp3⟩
    have hF' : ∀ r ∈ F, r.Prime ∧ 3 ≤ r := fun r hr => hF r (Finset.mem_cons_of_mem hr)
    set E2 := ((Finset.Icc 0 N ×ˢ Finset.Icc 0 N)).erase (0, 0)
    set WF := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun w : ℕ × ℕ => (w.1 * w.2).primeFactors = F)
    set T := E2 ×ˢ WF
    let mulMap2 : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun q => (p ^ q.1.1 * q.2.1, p ^ q.1.2 * q.2.2)
    have hsub : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = Finset.cons p F hpNotMem) ⊆
        T.image mulMap2 := by
      rintro ⟨u1, u2⟩ hu
      rcases Finset.mem_filter.mp hu with ⟨huProd, hupf⟩
      rcases Finset.mem_product.mp huProd with ⟨hu1, hu2⟩
      rcases Finset.mem_Icc.mp hu1 with ⟨hu1_lo, hu1_hi⟩
      rcases Finset.mem_Icc.mp hu2 with ⟨hu2_lo, hu2_hi⟩
      have hu10 : u1 ≠ 0 := by omega
      have hu20 : u2 ≠ 0 := by omega
      set e1 := u1.factorization p
      set e2 := u2.factorization p
      set w1 := u1 / p ^ e1
      set w2 := u2 / p ^ e2
      have hrew1 : p ^ e1 * w1 = u1 := Nat.ordProj_mul_ordCompl_eq_self u1 p
      have hrew2 : p ^ e2 * w2 = u2 := Nat.ordProj_mul_ordCompl_eq_self u2 p
      have he1_N : e1 ≤ N := by
        have h1 : e1 < 2 ^ e1 := Nat.lt_two_pow_self
        have h2 : 2 ^ e1 ≤ p ^ e1 := Nat.pow_le_pow_left hp.two_le e1
        have h3 : p ^ e1 ≤ u1 := Nat.le_of_dvd hu1_lo ⟨w1, hrew1.symm⟩
        omega
      have he2_N : e2 ≤ N := by
        have h1 : e2 < 2 ^ e2 := Nat.lt_two_pow_self
        have h2 : 2 ^ e2 ≤ p ^ e2 := Nat.pow_le_pow_left hp.two_le e2
        have h3 : p ^ e2 ≤ u2 := Nat.le_of_dvd hu2_lo ⟨w2, hrew2.symm⟩
        omega
      have hp_mem : p ∈ (u1 * u2).primeFactors := by rw [hupf]; exact Finset.mem_cons_self p F
      have hp_dvd_mul : p ∣ u1 * u2 := Nat.dvd_of_mem_primeFactors hp_mem
      have he_not00 : (e1, e2) ≠ (0, 0) := by
        intro h00
        rcases Prod.mk.inj h00 with ⟨he10, he20⟩
        rcases hp.dvd_mul.mp hp_dvd_mul with hd1 | hd2
        · have := Nat.Prime.factorization_pos_of_dvd hp hu10 hd1; omega
        · have := Nat.Prime.factorization_pos_of_dvd hp hu20 hd2; omega
      have hw1_lo : 1 ≤ w1 := by
        by_contra h0
        have hw1_0 : w1 = 0 := Nat.lt_one_iff.mp (not_le.mp h0)
        rw [hw1_0, mul_zero] at hrew1
        exact hu10 hrew1.symm
      have hw2_lo : 1 ≤ w2 := by
        by_contra h0
        have hw2_0 : w2 = 0 := Nat.lt_one_iff.mp (not_le.mp h0)
        rw [hw2_0, mul_zero] at hrew2
        exact hu20 hrew2.symm
      have hw1_hi : w1 ≤ N := (Nat.div_le_self u1 _).trans hu1_hi
      have hw2_hi : w2 ≤ N := (Nat.div_le_self u2 _).trans hu2_hi
      have hnot_pw1 : ¬ p ∣ w1 := Nat.not_dvd_ordCompl hp hu10
      have hnot_pw2 : ¬ p ∣ w2 := Nat.not_dvd_ordCompl hp hu20
      have hnot_pw12 : ¬ p ∣ w1 * w2 := fun hd =>
        (hp.dvd_mul.mp hd).elim hnot_pw1 hnot_pw2
      have hmul_eq : p ^ (e1 + e2) * (w1 * w2) = u1 * u2 := by
        calc p ^ (e1 + e2) * (w1 * w2) = (p ^ e1 * w1) * (p ^ e2 * w2) := by rw [pow_add]; ring
          _ = u1 * u2 := by rw [hrew1, hrew2]
      have he12_ne0 : e1 + e2 ≠ 0 := by
        intro h0
        exact he_not00 (Prod.ext (by omega) (by omega))
      have hpf_mul : (u1 * u2).primeFactors = {p} ∪ (w1 * w2).primeFactors := by
        rw [← hmul_eq, Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by positivity),
          Nat.primeFactors_prime_pow he12_ne0 hp]
      have hp_not_w12 : p ∉ (w1 * w2).primeFactors :=
        fun hm => hnot_pw12 (Nat.dvd_of_mem_primeFactors hm)
      have hwpf : (w1 * w2).primeFactors = F := by
        have h1 : insert p (w1 * w2).primeFactors = insert p F := by
          simpa [Finset.singleton_union] using hpf_mul.symm.trans hupf
        have h2 := congrArg (fun s => Finset.erase s p) h1
        rwa [Finset.erase_insert hp_not_w12, Finset.erase_insert hpNotMem] at h2
      refine Finset.mem_image.mpr ⟨((e1, e2), (w1, w2)), ?_, Prod.ext hrew1 hrew2⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨he_not00, Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, he1_N⟩, Finset.mem_Icc.mpr ⟨Nat.zero_le _, he2_N⟩⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hw1_lo, hw1_hi⟩, Finset.mem_Icc.mpr ⟨hw2_lo, hw2_hi⟩⟩, hwpf⟩⟩
    have hE2_le : (∑ e ∈ E2, (1 : ℝ) / ((p : ℝ) ^ e.1 * (p : ℝ) ^ e.2)) ≤
        (2 : ℝ) / ((p : ℝ) - 2) := by
      let fp : ℕ × ℕ → ℝ := fun e => (1 : ℝ) / ((p : ℝ) ^ e.1 * (p : ℝ) ^ e.2)
      have h00_mem : (0, 0) ∈ (Finset.Icc 0 N ×ˢ Finset.Icc 0 N : Finset (ℕ × ℕ)) := by simp
      have herase : (∑ e ∈ E2, fp e) + 1 =
          ∑ e ∈ (Finset.Icc 0 N ×ˢ Finset.Icc 0 N : Finset (ℕ × ℕ)), fp e := by
        have h := Finset.sum_erase_add (Finset.Icc 0 N ×ˢ Finset.Icc 0 N : Finset (ℕ × ℕ)) fp h00_mem
        have hf00 : fp (0, 0) = 1 := by simp [fp]
        rw [← h, hf00]
      have hprod_sq : (∑ e ∈ (Finset.Icc 0 N ×ˢ Finset.Icc 0 N : Finset (ℕ × ℕ)), fp e) =
          (∑ a ∈ Finset.Icc 0 N, (1 : ℝ) / (p : ℝ) ^ a) ^ 2 := by
        dsimp [fp]
        rw [Finset.sum_product, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by ring
      have hsum0 : (∑ a ∈ Finset.Icc 0 N, (1 : ℝ) / (p : ℝ) ^ a) ≤
          (p : ℝ) / ((p : ℝ) - 1) := by
        have hsplit0 : (Finset.Icc 0 N : Finset ℕ) = insert 0 (Finset.Icc 1 N) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hsplit0, Finset.sum_insert (by simp)]
        simp only [pow_zero, div_one]
        have hp_real3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        calc 1 + ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (p : ℝ) ^ e
          _ ≤ 1 + (1 : ℝ) / ((p : ℝ) - 1) := by linarith [sum_geom_inv_le p N hp.two_le]
          _ = (p : ℝ) / ((p : ℝ) - 1) := by field_simp [hp1_pos.ne']; ring
      have hp_real3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hsq_le : (∑ a ∈ Finset.Icc 0 N, (1 : ℝ) / (p : ℝ) ^ a) ^ 2 ≤
          ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => by positivity) hsum0 2
      have halg : ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1 ≤ (2 : ℝ) / ((p : ℝ) - 2) := by
        rw [sub_le_iff_le_add]
        field_simp [hp1_pos.ne', hp2_pos.ne']
        nlinarith
      linarith
    calc (∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
          (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = Finset.cons p F hpNotMem), invR2 x)
      _ ≤ ∑ x ∈ T.image mulMap2, invR2 x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by dsimp [invR2]; positivity
      _ ≤ ∑ q ∈ T, invR2 (mulMap2 q) :=
        Finset.sum_image_le_of_nonneg fun q _ => by dsimp [invR2]; positivity
      _ = (∑ e ∈ E2, (1 : ℝ) / ((p : ℝ) ^ e.1 * (p : ℝ) ^ e.2)) *
          (∑ w ∈ WF, invR2 w) := by
        simp only [T, invR2, mulMap2, Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        push_cast; ring
      _ ≤ ((2 : ℝ) / ((p : ℝ) - 2)) * (∏ r ∈ F, ((2 : ℝ) / ((r : ℝ) - 2))) := by
        have hp_real3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
        refine mul_le_mul hE2_le (ih hF') (Finset.sum_nonneg fun w _ => by dsimp [invR2]; positivity)
          (div_nonneg (by norm_num) (by linarith))
      _ = ∏ r ∈ Finset.cons p F hpNotMem, ((2 : ℝ) / ((r : ℝ) - 2)) := by
        rw [Finset.prod_cons]

/- Corollary 2A: 1-linear-form Selberg sieve for primes `p ≤ X` with `k ^ 2 ∣ p - 1`. -/
private lemma card_primes_mod_sq_le (k X z1 : ℕ) (hk : 2 ≤ k) (hz1 : 1 ≤ z1) :
    ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ) ≤
      (z1 : ℝ) +
      (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ)) +
      (z1 : ℝ) ^ 6 := by
  set M1 := X / k ^ 2
  set F1 := (primesLE z1).filter (fun r => ¬ r ∣ k)
  set P1 := ∏ r ∈ F1, r
  have hF1_prime : ∀ r ∈ F1, r.Prime :=
    fun r hr => (mem_primesLE.mp (Finset.mem_filter.mp hr).1).1
  have hP1_sq : Squarefree P1 := squarefree_prod_primes hF1_prime
  let s1 : BoundingSieve := {
    support := (Finset.Icc 1 M1).image (fun t => k ^ 2 * t + 1)
    prodPrimes := P1
    prodPrimes_squarefree := hP1_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (M1 : ℝ)
    nu := ArithmeticFunction.prodPrimeFactors (fun r => (1 : ℝ) / (r : ℝ))
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := by
      intro p hp _
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    nu_lt_one_of_prime := by
      intro p hp _
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      rw [div_lt_one (by linarith)]
      linarith
  }
  have hk2_pos : 0 < k ^ 2 := by positivity
  have hinj1 : Function.Injective (fun t : ℕ => k ^ 2 * t + 1) := by
    intro t1 t2 h
    dsimp at h
    have hmul : k ^ 2 * t1 = k ^ 2 * t2 := by omega
    exact Nat.eq_of_mul_eq_mul_left hk2_pos hmul
  have hrem1 : ∀ d ∈ P1.divisors, |s1.rem d| ≤ 1 := by
    intro d hd
    have hd_dvd : d ∣ P1 := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_sq : Squarefree d := hP1_sq.squarefree_of_dvd hd_dvd
    have hnu_d : s1.nu d = (1 : ℝ) / (d : ℝ) := by
      change ArithmeticFunction.prodPrimeFactors (fun r => (1 : ℝ) / (r : ℝ)) d = _
      rw [ArithmeticFunction.prodPrimeFactors_apply hd_pos.ne']
      calc (∏ r ∈ d.primeFactors, (1 : ℝ) / (r : ℝ))
        _ = (1 : ℝ) / (∏ r ∈ d.primeFactors, (r : ℝ)) := by simp
        _ = (1 : ℝ) / (d : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_sq]
    have hcop_dk2 : (k ^ 2).Coprime d := by
      refine (Nat.coprime_of_dvd' fun r hr hrk hrd => ?_).pow_left 2
      have hrP1 : r ∣ P1 := hrd.trans hd_dvd
      rcases (hr.prime.dvd_finsetProd_iff _).mp hrP1 with ⟨q, hqF1, hrq⟩
      have hqp : q.Prime := hF1_prime q hqF1
      have heq : r = q := (Nat.prime_dvd_prime_iff_eq hr hqp).mp hrq
      subst heq
      exact ((Finset.mem_filter.mp hqF1).2 hrk).elim
    have hmult_eq : s1.multSum d =
        ((#((Finset.Icc 1 M1).filter (fun t => d ∣ k ^ 2 * t + 1)) : ℕ) : ℝ) := by
      simp only [BoundingSieve.multSum, s1, Finset.sum_image hinj1.injOn, ← Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hper : ∀ t, d ∣ k ^ 2 * (t + d) + 1 ↔ d ∣ k ^ 2 * t + 1 := by
      intro t
      have hadd : k ^ 2 * (t + d) + 1 = (k ^ 2 * t + 1) + d * k ^ 2 := by ring
      rw [hadd]
      exact Nat.dvd_add_left ⟨k ^ 2, rfl⟩
    have hc1 := card_range_dvd_linear_eq_one hd_pos hcop_dk2
    have habs := abs_card_filter_Icc_sub_le M1 d hd_pos (fun t => d ∣ k ^ 2 * t + 1) hper
    rw [hc1, Nat.cast_one] at habs
    rw [BoundingSieve.rem, hmult_eq, hnu_d]
    exact habs
  have hS1_ge : ((Nat.totient k : ℝ) / (k : ℝ)) * Real.log ((z1 + 1 : ℕ) : ℝ) ≤
      selbergSum s1 (z1 : ℝ) := by
    set U1 := (Finset.Icc 1 z1).filter (fun u : ℕ => u.Coprime k)
    let rad : ℕ → ℕ := fun u => ∏ r ∈ u.primeFactors, r
    have hmaps : Set.MapsTo rad ↑U1 ↑(selbergDz s1 (z1 : ℝ)) := by
      intro u hu
      rcases Finset.mem_filter.mp (Finset.mem_coe.mp hu) with ⟨huIcc, hucop⟩
      rcases Finset.mem_Icc.mp huIcc with ⟨hu1, huz1⟩
      have hsub_pf : u.primeFactors ⊆ F1 := by
        intro r hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hru : r ∣ u := Nat.dvd_of_mem_primeFactors hr
        have hrz1 : r ≤ z1 := (Nat.le_of_dvd hu1 hru).trans huz1
        have hr_not_k : ¬ r ∣ k := fun hrk => by
          have hdvd1 : r ∣ 1 := hucop.gcd_eq_one ▸ Nat.dvd_gcd hru hrk
          exact hrp.not_dvd_one hdvd1
        exact Finset.mem_filter.mpr ⟨mem_primesLE.mpr ⟨hrp, hrz1⟩, hr_not_k⟩
      have hrad_dvd_P1 : rad u ∣ P1 := Finset.prod_dvd_prod_of_subset _ _ _ hsub_pf
      have hrad_le_u : rad u ≤ u := Nat.le_of_dvd hu1 (Nat.prod_primeFactors_dvd u)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hrad_dvd_P1, s1.prodPrimes_ne_zero⟩,
          by exact_mod_cast hrad_le_u.trans huz1⟩)
    have hfiber : ∀ l ∈ selbergDz s1 (z1 : ℝ),
        (∑ u ∈ U1.filter (fun u => rad u = l), (1 : ℝ) / (u : ℝ)) ≤ s1.selbergTerms l := by
      intro l hl
      have hl_dvd : l ∣ P1 := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
      have hl_pos : 0 < l := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hl).1
      have hsel_l : s1.selbergTerms l = ∏ r ∈ l.primeFactors, ((1 : ℝ) / ((r : ℝ) - 1)) := by
        rw [BoundingSieve.selbergTerms_apply]
        change ArithmeticFunction.prodPrimeFactors (fun r => (1 : ℝ) / (r : ℝ)) l * _ = _
        rw [ArithmeticFunction.prodPrimeFactors_apply hl_pos.ne', ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun r hr => ?_
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        change ((1 : ℝ) / (r : ℝ)) * (1 - ArithmeticFunction.prodPrimeFactors
          (fun q => (1 : ℝ) / (q : ℝ)) r)⁻¹ = _
        rw [ArithmeticFunction.prodPrimeFactors_apply hrp.ne_zero, hrp.primeFactors,
          Finset.prod_singleton]
        have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrp.two_le
        have hr0 : (r : ℝ) ≠ 0 := by linarith
        have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hr0, hr1]
      rw [hsel_l]
      have hsub_fib : U1.filter (fun u => rad u = l) ⊆
          (Finset.Icc 1 z1).filter (fun u : ℕ => u.primeFactors = l.primeFactors) := by
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huU1, hrad_eq⟩
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huU1).1, ?_⟩
        rw [← hrad_eq]
        have hu_sq_rad : Squarefree (rad u) :=
          squarefree_prod_primes (fun r hr => Nat.prime_of_mem_primeFactors hr)
        ext r
        simp only [Nat.mem_primeFactors, ne_eq]
        constructor
        · rintro ⟨hrp, hru, hu0⟩
          exact ⟨hrp, Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hrp, hru, hu0⟩),
            hu_sq_rad.ne_zero⟩
        · rintro ⟨hrp, hr_rad, _⟩
          rcases (hrp.prime.dvd_finsetProd_iff _).mp hr_rad with ⟨q, hq, hrq⟩
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
          have heq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hqp).mp hrq
          subst heq
          exact Nat.mem_primeFactors.mp hq
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_fib fun x _ _ => by positivity).trans
        (sum_inv_exact_primeFactors_le z1 l.primeFactors fun r hr => Nat.prime_of_mem_primeFactors hr)
    have hU1_le_S1 : (∑ u ∈ U1, (1 : ℝ) / (u : ℝ)) ≤ selbergSum s1 (z1 : ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      exact Finset.sum_le_sum hfiber
    have hlog_le : Real.log ((z1 + 1 : ℕ) : ℝ) ≤ ∑ w ∈ Finset.Icc 1 z1, (1 : ℝ) / (w : ℝ) := by
      have h := log_add_one_le_harmonic z1
      rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
      refine h.trans_eq (Finset.sum_congr rfl fun x _ => ?_)
      simp
    calc ((Nat.totient k : ℝ) / (k : ℝ)) * Real.log ((z1 + 1 : ℕ) : ℝ)
      _ ≤ ((Nat.totient k : ℝ) / (k : ℝ)) * (∑ w ∈ Finset.Icc 1 z1, (1 : ℝ) / (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ ≤ ∑ u ∈ U1, (1 : ℝ) / (u : ℝ) :=
        prod_one_sub_inv_mul_harmonic_le_coprime_sum k z1 (by omega)
      _ ≤ selbergSum s1 (z1 : ℝ) := hU1_le_S1
  have hz1_real : (1 : ℝ) ≤ (z1 : ℝ) := by exact_mod_cast hz1
  have hsifted := siftedSum_le_selberg s1 hz1_real
  have herr_le : (∑ d ∈ P1.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z1 : ℝ) ^ 2),
      (d : ℝ) ^ 2 * |s1.rem d|) ≤ (z1 : ℝ) ^ 6 := by
    have hsub_d : P1.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z1 : ℝ) ^ 2) ⊆
        Finset.Icc 1 (z1 ^ 2) := by
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd_div, hd_le⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd_div
      have hd_z2 : d ≤ z1 ^ 2 := by
        have : (d : ℝ) ≤ ((z1 ^ 2 : ℕ) : ℝ) := by push_cast; exact hd_le
        exact_mod_cast this
      exact Finset.mem_Icc.mpr ⟨hd_pos, hd_z2⟩
    calc (∑ d ∈ P1.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z1 : ℝ) ^ 2), (d : ℝ) ^ 2 * |s1.rem d|)
      _ ≤ ∑ d ∈ P1.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (z1 : ℝ) ^ 2), (d : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have h1 := hrem1 d (Finset.mem_filter.mp hd).1
        nlinarith [sq_nonneg (d : ℝ)]
      _ ≤ ∑ d ∈ Finset.Icc 1 (z1 ^ 2), (d : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_d fun x _ _ => by positivity
      _ ≤ ∑ _d ∈ Finset.Icc 1 (z1 ^ 2), ((z1 : ℝ) ^ 2) ^ 2 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_le : (d : ℝ) ≤ (z1 : ℝ) ^ 2 := by
          have := (Finset.mem_Icc.mp hd).2
          exact_mod_cast this
        exact pow_le_pow_left₀ (by positivity) hd_le 2
      _ = (z1 : ℝ) ^ 6 := by
        simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
        push_cast; ring
  have hmain_le : s1.totalMass / selbergSum s1 (z1 : ℝ) ≤
      (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ)) := by
    have hM1_le : s1.totalMass ≤ (X : ℝ) / ((k : ℝ) ^ 2) := by
      simp only [s1]
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast (mul_comm (k ^ 2) M1 ▸ Nat.mul_div_le X (k ^ 2))
    have hlog_pos : 0 < Real.log ((z1 + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z1 + 1 by omega))
    have htot_pos : (0 : ℝ) < (Nat.totient k : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hlow_pos : 0 < ((Nat.totient k : ℝ) / (k : ℝ)) * Real.log ((z1 + 1 : ℕ) : ℝ) := by
      positivity
    calc s1.totalMass / selbergSum s1 (z1 : ℝ)
      _ ≤ ((X : ℝ) / (k : ℝ) ^ 2) /
          (((Nat.totient k : ℝ) / (k : ℝ)) * Real.log ((z1 + 1 : ℕ) : ℝ)) :=
        div_le_div₀ (by positivity) hM1_le hlow_pos hS1_ge
      _ = (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ)) := by
        field_simp [hk_pos.ne', htot_pos.ne', hlog_pos.ne']
  set S_all := (primesLE X).filter (fun p => k ^ 2 ∣ p - 1)
  have hsplit_p : #S_all = #(S_all.filter (fun p => p ≤ z1)) +
      #(S_all.filter (fun p => ¬ p ≤ z1)) :=
    (Finset.card_filter_add_card_filter_not (fun p => p ≤ z1)).symm
  have hsmall_le : (#(S_all.filter (fun p => p ≤ z1)) : ℝ) ≤ (z1 : ℝ) := by
    have hsub : S_all.filter (fun p => p ≤ z1) ⊆ Finset.Icc 1 z1 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hpz1⟩
      have hpp : p.Prime := (mem_primesLE.mp (Finset.mem_filter.mp hpS).1).1
      exact Finset.mem_Icc.mpr ⟨hpp.one_le, hpz1⟩
    have hcard : #(S_all.filter (fun p => p ≤ z1)) ≤ z1 := by
      calc #(S_all.filter (fun p => p ≤ z1)) ≤ #(Finset.Icc 1 z1) := Finset.card_le_card hsub
        _ = z1 := by simp [Nat.card_Icc]
    exact_mod_cast hcard
  have hlarge_le : (#(S_all.filter (fun p => ¬ p ≤ z1)) : ℝ) ≤ s1.siftedSum := by
    have hsub : S_all.filter (fun p => ¬ p ≤ z1) ⊆
        s1.support.filter (fun d => Nat.Coprime P1 d) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hp_gt⟩
      rcases Finset.mem_filter.mp hpS with ⟨hpLE, hkdvd⟩
      rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
      have hpz_lt : z1 < p := not_le.mp hp_gt
      have hp1_pos : 0 < p - 1 := by
        have := hpp.two_le; omega
      rcases hkdvd with ⟨t, ht⟩
      have ht_pos : 1 ≤ t := by
        by_contra ht0
        have ht_eq0 : t = 0 := Nat.lt_one_iff.mp (not_le.mp ht0)
        rw [ht_eq0, mul_zero] at ht
        omega
      have hp_eq : k ^ 2 * t + 1 = p := by omega
      have ht_le : t ≤ M1 := by
        have hk2t : k ^ 2 * t ≤ X := by omega
        exact (Nat.le_div_iff_mul_le hk2_pos).mpr (mul_comm t (k ^ 2) ▸ hk2t)
      have hmem_supp : p ∈ s1.support :=
        Finset.mem_image.mpr ⟨t, Finset.mem_Icc.mpr ⟨ht_pos, ht_le⟩, hp_eq⟩
      have hcop_P1 : Nat.Coprime P1 p := by
        rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
        intro hdvd
        rcases (hpp.prime.dvd_finsetProd_iff _).mp hdvd with ⟨r, hrF1, hpr⟩
        have hrp : r.Prime := hF1_prime r hrF1
        have heq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr
        subst heq
        have hrz1 : p ≤ z1 := (mem_primesLE.mp (Finset.mem_filter.mp hrF1).1).2
        omega
      exact Finset.mem_filter.mpr ⟨hmem_supp, hcop_P1⟩
    have hsif_eq : s1.siftedSum = (#(s1.support.filter (fun d => Nat.Coprime P1 d)) : ℝ) := by
      simp [BoundingSieve.siftedSum, s1]
    rw [hsif_eq]
    exact_mod_cast Finset.card_le_card hsub
  rw [hsplit_p, Nat.cast_add]
  linarith

/- Corollary 2B: 2-linear-form Selberg sieve for `p = a' * t + 1` and `q = n' * t + 1` both prime. -/
private lemma card_primes_two_linear_le (a' n' M2 w2 : ℕ) (ha' : 1 ≤ a') (hn' : 1 ≤ n')
    (hne : a' ≠ n') (hw2 : 1 ≤ w2) :
    let D := 2 * a' * n' * (max a' n' - min a' n')
    ((#((Finset.Icc 1 M2).filter (fun t =>
        (a' * t + 1).Prime ∧ w2 < a' * t + 1 ∧ (n' * t + 1).Prime ∧ w2 < n' * t + 1)) : ℕ) : ℝ) ≤
      (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 / (Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2 +
      (w2 : ℝ) ^ 16 := by
  intro D
  have hdiff_pos : 1 ≤ max a' n' - min a' n' := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [max_eq_right hlt.le, min_eq_left hlt.le]; omega
    · rw [max_eq_left hgt.le, min_eq_right hgt.le]; omega
  have hD_pos : 1 ≤ D :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos ha') hn') hdiff_pos
  set F2 := (primesLE w2).filter (fun r => ¬ r ∣ D)
  set P2 := ∏ r ∈ F2, r
  have hF2_prime : ∀ r ∈ F2, r.Prime :=
    fun r hr => (mem_primesLE.mp (Finset.mem_filter.mp hr).1).1
  have hF2_ge3 : ∀ r ∈ F2, 3 ≤ r := by
    intro r hr
    have hrp : r.Prime := hF2_prime r hr
    have hnotD : ¬ r ∣ D := (Finset.mem_filter.mp hr).2
    have hr_ne2 : r ≠ 2 := by
      rintro rfl
      exact hnotD ⟨a' * n' * (max a' n' - min a' n'), by dsimp [D]; ring⟩
    have := hrp.two_le
    omega
  have hP2_sq : Squarefree P2 := squarefree_prod_primes hF2_prime
  have hinj2 : Function.Injective (fun t : ℕ => (a' * t + 1) * (n' * t + 1)) := by
    refine StrictMono.injective fun t1 t2 hlt => ?_
    have h1 : a' * t1 + 1 < a' * t2 + 1 := by nlinarith
    have h2 : n' * t1 + 1 < n' * t2 + 1 := by nlinarith
    exact Nat.mul_lt_mul'' h1 h2
  let s2 : BoundingSieve := {
    support := (Finset.Icc 1 M2).image (fun t => (a' * t + 1) * (n' * t + 1))
    prodPrimes := P2
    prodPrimes_squarefree := hP2_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (M2 : ℝ)
    nu := ArithmeticFunction.prodPrimeFactors (fun r => (2 : ℝ) / (r : ℝ))
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := by
      intro p hp _
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    nu_lt_one_of_prime := by
      intro p hp hpP2
      rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
        Finset.prod_singleton]
      rcases (hp.prime.dvd_finsetProd_iff _).mp hpP2 with ⟨r, hrF2, hpr⟩
      have hrp : r.Prime := hF2_prime r hrF2
      have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr
      subst heq
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hF2_ge3 p hrF2
      rw [div_lt_one (by linarith)]
      linarith
  }
  have hd_prime_F2 : ∀ d, d ∣ P2 → ∀ r ∈ d.primeFactors, r ∈ F2 := by
    intro d hd r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrP2 : r ∣ P2 := (Nat.dvd_of_mem_primeFactors hr).trans hd
    rcases (hrp.prime.dvd_finsetProd_iff _).mp hrP2 with ⟨q, hqF2, hrq⟩
    have hqp : q.Prime := hF2_prime q hqF2
    have heq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hqp).mp hrq
    rwa [heq]
  have hrem2 : ∀ d ∈ P2.divisors, |s2.rem d| ≤ (d : ℝ) := by
    intro d hd
    have hd_dvd : d ∣ P2 := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_sq : Squarefree d := hP2_sq.squarefree_of_dvd hd_dvd
    have hnu_d : s2.nu d = (2 : ℝ) ^ (#d.primeFactors) / (d : ℝ) := by
      change ArithmeticFunction.prodPrimeFactors (fun r => (2 : ℝ) / (r : ℝ)) d = _
      rw [ArithmeticFunction.prodPrimeFactors_apply hd_pos.ne', Finset.prod_div_distrib,
        Finset.prod_const, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_sq]
    have hmult_eq : s2.multSum d =
        ((#((Finset.Icc 1 M2).filter (fun t => d ∣ (a' * t + 1) * (n' * t + 1))) : ℕ) : ℝ) := by
      simp only [BoundingSieve.multSum, s2, Finset.sum_image hinj2.injOn, ← Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hper : ∀ t, d ∣ (a' * (t + d) + 1) * (n' * (t + d) + 1) ↔
        d ∣ (a' * t + 1) * (n' * t + 1) := by
      intro t
      have hadd : (a' * (t + d) + 1) * (n' * (t + d) + 1) =
          (a' * t + 1) * (n' * t + 1) + d * (a' * n' * (2 * t + d) + a' + n') := by ring
      rw [hadd]
      exact Nat.dvd_add_left ⟨a' * n' * (2 * t + d) + a' + n', rfl⟩
    have hc2 := card_range_two_linear hd_pos hd_sq
      (fun r hr => (Finset.mem_filter.mp (hd_prime_F2 d hd_dvd r hr)).2)
    have habs := abs_card_filter_Icc_sub_le M2 d hd_pos
      (fun t => d ∣ (a' * t + 1) * (n' * t + 1)) hper
    rw [hc2] at habs
    have h2pow_le_d : 2 ^ (#d.primeFactors) ≤ d := by
      calc 2 ^ (#d.primeFactors) = ∏ _r ∈ d.primeFactors, 2 := by simp
        _ ≤ ∏ r ∈ d.primeFactors, r :=
          Finset.prod_le_prod' fun r hr => (Nat.prime_of_mem_primeFactors hr).two_le
        _ = d := Nat.prod_primeFactors_of_squarefree hd_sq
    have hrem_le : |s2.rem d| ≤ ((2 ^ (#d.primeFactors) : ℕ) : ℝ) := by
      rw [BoundingSieve.rem, hmult_eq, hnu_d]
      simpa [s2] using habs
    exact hrem_le.trans (by exact_mod_cast h2pow_le_d)
  set z2 : ℝ := ((w2 ^ 2 : ℕ) : ℝ)
  have hz2_ge1 : (1 : ℝ) ≤ z2 := by
    have h1w : 1 ≤ w2 ^ 2 := Nat.one_le_pow 2 w2 hw2
    dsimp [z2]
    exact_mod_cast h1w
  have hS2_ge : (((Nat.totient D : ℝ) / (D : ℝ)) * Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2 ≤
      selbergSum s2 z2 := by
    set U2 := (Finset.Icc 1 w2).filter (fun u : ℕ => u.Coprime D)
    let rad2 : ℕ × ℕ → ℕ := fun x => ∏ r ∈ (x.1 * x.2).primeFactors, r
    have hmaps2 : Set.MapsTo rad2 ↑(U2 ×ˢ U2) ↑(selbergDz s2 z2) := by
      rintro ⟨u1, u2⟩ hu
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hu) with ⟨hu1, hu2⟩
      rcases Finset.mem_filter.mp hu1 with ⟨hu1Icc, hcop1⟩
      rcases Finset.mem_filter.mp hu2 with ⟨hu2Icc, hcop2⟩
      rcases Finset.mem_Icc.mp hu1Icc with ⟨hu1_lo, hu1_hi⟩
      rcases Finset.mem_Icc.mp hu2Icc with ⟨hu2_lo, hu2_hi⟩
      have hsub_pf : (u1 * u2).primeFactors ⊆ F2 := by
        intro r hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hrmul : r ∣ u1 * u2 := Nat.dvd_of_mem_primeFactors hr
        have hrw2 : r ≤ w2 := by
          rcases hrp.dvd_mul.mp hrmul with hd1 | hd2
          · exact (Nat.le_of_dvd hu1_lo hd1).trans hu1_hi
          · exact (Nat.le_of_dvd hu2_lo hd2).trans hu2_hi
        have hr_not_D : ¬ r ∣ D := by
          intro hrD
          rcases hrp.dvd_mul.mp hrmul with hd1 | hd2
          · have hdvd1 : r ∣ 1 := hcop1.gcd_eq_one ▸ Nat.dvd_gcd hd1 hrD
            exact hrp.not_dvd_one hdvd1
          · have hdvd1 : r ∣ 1 := hcop2.gcd_eq_one ▸ Nat.dvd_gcd hd2 hrD
            exact hrp.not_dvd_one hdvd1
        exact Finset.mem_filter.mpr ⟨mem_primesLE.mpr ⟨hrp, hrw2⟩, hr_not_D⟩
      have hrad_dvd : rad2 (u1, u2) ∣ P2 := Finset.prod_dvd_prod_of_subset _ _ _ hsub_pf
      have hrad_le : rad2 (u1, u2) ≤ w2 ^ 2 := by
        calc rad2 (u1, u2) ≤ u1 * u2 :=
              Nat.le_of_dvd (by positivity) (Nat.prod_primeFactors_dvd _)
          _ ≤ w2 * w2 := Nat.mul_le_mul hu1_hi hu2_hi
          _ = w2 ^ 2 := (sq w2).symm
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hrad_dvd, s2.prodPrimes_ne_zero⟩, by dsimp [z2]; exact_mod_cast hrad_le⟩)
    have hfiber2 : ∀ l ∈ selbergDz s2 z2,
        (∑ x ∈ (U2 ×ˢ U2).filter (fun x => rad2 x = l), (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))) ≤
        s2.selbergTerms l := by
      intro l hl
      have hl_dvd : l ∣ P2 := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
      have hl_pos : 0 < l := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hl).1
      have hsel_l : s2.selbergTerms l = ∏ r ∈ l.primeFactors, ((2 : ℝ) / ((r : ℝ) - 2)) := by
        rw [BoundingSieve.selbergTerms_apply]
        change ArithmeticFunction.prodPrimeFactors (fun r => (2 : ℝ) / (r : ℝ)) l * _ = _
        rw [ArithmeticFunction.prodPrimeFactors_apply hl_pos.ne', ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun r hr => ?_
        have hrF2 : r ∈ F2 := hd_prime_F2 l hl_dvd r hr
        have hrp : r.Prime := hF2_prime r hrF2
        have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hF2_ge3 r hrF2
        change ((2 : ℝ) / (r : ℝ)) * (1 - ArithmeticFunction.prodPrimeFactors
          (fun q => (2 : ℝ) / (q : ℝ)) r)⁻¹ = _
        rw [ArithmeticFunction.prodPrimeFactors_apply hrp.ne_zero, hrp.primeFactors,
          Finset.prod_singleton]
        have hr0 : (r : ℝ) ≠ 0 := by linarith
        have hr2 : (r : ℝ) - 2 ≠ 0 := by linarith
        field_simp [hr0, hr2]
      rw [hsel_l]
      have hsub_fib : (U2 ×ˢ U2).filter (fun x => rad2 x = l) ⊆
          (Finset.Icc 1 w2 ×ˢ Finset.Icc 1 w2).filter
            (fun x : ℕ × ℕ => (x.1 * x.2).primeFactors = l.primeFactors) := by
        rintro ⟨u1, u2⟩ hu
        rcases Finset.mem_filter.mp hu with ⟨huProd, hrad_eq⟩
        rcases Finset.mem_product.mp huProd with ⟨hu1, hu2⟩
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hu1).1, (Finset.mem_filter.mp hu2).1⟩, ?_⟩
        rw [← hrad_eq]
        have hsq_rad : Squarefree (rad2 (u1, u2)) :=
          squarefree_prod_primes (fun r hr => Nat.prime_of_mem_primeFactors hr)
        ext r
        simp only [Nat.mem_primeFactors, ne_eq]
        constructor
        · rintro ⟨hrp, hru, hu0⟩
          exact ⟨hrp, Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hrp, hru, hu0⟩),
            hsq_rad.ne_zero⟩
        · rintro ⟨hrp, hr_rad, _⟩
          rcases (hrp.prime.dvd_finsetProd_iff _).mp hr_rad with ⟨q, hq, hrq⟩
          have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
          have heq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hqp).mp hrq
          subst heq
          exact Nat.mem_primeFactors.mp hq
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_fib fun x _ _ => by positivity).trans
        (sum_inv_pair_exact_primeFactors_le w2 l.primeFactors fun r hr =>
          ⟨Nat.prime_of_mem_primeFactors hr, hF2_ge3 r (hd_prime_F2 l hl_dvd r hr)⟩)
    have hU2_sq_le : (∑ u ∈ U2, (1 : ℝ) / (u : ℝ)) ^ 2 ≤ selbergSum s2 z2 := by
      have hsq_eq : (∑ u ∈ U2, (1 : ℝ) / (u : ℝ)) ^ 2 =
          ∑ x ∈ U2 ×ˢ U2, (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) := by
        rw [Finset.sum_product, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by ring
      rw [hsq_eq, ← Finset.sum_fiberwise_of_maps_to hmaps2]
      exact Finset.sum_le_sum hfiber2
    have hlog_le : Real.log ((w2 + 1 : ℕ) : ℝ) ≤ ∑ w ∈ Finset.Icc 1 w2, (1 : ℝ) / (w : ℝ) := by
      have h := log_add_one_le_harmonic w2
      rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
      refine h.trans_eq (Finset.sum_congr rfl fun x _ => ?_)
      simp
    have hbase_le : ((Nat.totient D : ℝ) / (D : ℝ)) * Real.log ((w2 + 1 : ℕ) : ℝ) ≤
        ∑ u ∈ U2, (1 : ℝ) / (u : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog_le (by positivity)).trans
        (prod_one_sub_inv_mul_harmonic_le_coprime_sum D w2 hD_pos)
    have hlog_nonneg : 0 ≤ ((Nat.totient D : ℝ) / (D : ℝ)) * Real.log ((w2 + 1 : ℕ) : ℝ) := by
      have : 0 ≤ Real.log ((w2 + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ w2 + 1 by omega))
      positivity
    exact (pow_le_pow_left₀ hlog_nonneg hbase_le 2).trans hU2_sq_le
  have hsifted2 := siftedSum_le_selberg s2 hz2_ge1
  have herr2_le : (∑ d ∈ P2.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z2 ^ 2),
      (d : ℝ) ^ 2 * |s2.rem d|) ≤ (w2 : ℝ) ^ 16 := by
    have hsub_d : P2.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z2 ^ 2) ⊆ Finset.Icc 1 (w2 ^ 4) := by
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd_div, hd_le⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd_div
      have hd_w4 : d ≤ w2 ^ 4 := by
        have : (d : ℝ) ≤ ((w2 ^ 4 : ℕ) : ℝ) := by
          calc (d : ℝ) ≤ z2 ^ 2 := hd_le
            _ = ((w2 ^ 4 : ℕ) : ℝ) := by dsimp [z2]; push_cast; ring
        exact_mod_cast this
      exact Finset.mem_Icc.mpr ⟨hd_pos, hd_w4⟩
    calc (∑ d ∈ P2.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z2 ^ 2), (d : ℝ) ^ 2 * |s2.rem d|)
      _ ≤ ∑ d ∈ P2.divisors.filter (fun d : ℕ => (d : ℝ) ≤ z2 ^ 2), (d : ℝ) ^ 3 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have h1 := hrem2 d (Finset.mem_filter.mp hd).1
        calc (d : ℝ) ^ 2 * |s2.rem d| ≤ (d : ℝ) ^ 2 * (d : ℝ) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (d : ℝ) ^ 3 := by ring
      _ ≤ ∑ d ∈ Finset.Icc 1 (w2 ^ 4), (d : ℝ) ^ 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_d fun x _ _ => by positivity
      _ ≤ ∑ _d ∈ Finset.Icc 1 (w2 ^ 4), ((w2 : ℝ) ^ 4) ^ 3 := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_le : (d : ℝ) ≤ (w2 : ℝ) ^ 4 := by
          have := (Finset.mem_Icc.mp hd).2
          exact_mod_cast this
        exact pow_le_pow_left₀ (by positivity) hd_le 3
      _ = (w2 : ℝ) ^ 16 := by
        simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
        push_cast; ring
  have hmain2_le : s2.totalMass / selbergSum s2 z2 ≤
      (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 / (Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2 := by
    have hlog_pos : 0 < Real.log ((w2 + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < w2 + 1 by omega))
    have htot_pos : (0 : ℝ) < (Nat.totient D : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hD_pos
    have hD_real_pos : (0 : ℝ) < (D : ℝ) := by positivity
    have hlow_pos : 0 < (((Nat.totient D : ℝ) / (D : ℝ)) * Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2 := by
      positivity
    calc s2.totalMass / selbergSum s2 z2
      _ ≤ (M2 : ℝ) / ((((Nat.totient D : ℝ) / (D : ℝ)) * Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2) :=
        div_le_div₀ (by positivity) (le_refl _) hlow_pos hS2_ge
      _ = (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 / (Real.log ((w2 + 1 : ℕ) : ℝ)) ^ 2 := by
        field_simp [htot_pos.ne', hD_real_pos.ne', hlog_pos.ne']
  set T_good := (Finset.Icc 1 M2).filter (fun t =>
    (a' * t + 1).Prime ∧ w2 < a' * t + 1 ∧ (n' * t + 1).Prime ∧ w2 < n' * t + 1)
  have hcard_le_sifted : ((#T_good : ℕ) : ℝ) ≤ s2.siftedSum := by
    have hsif_eq : s2.siftedSum = (#(s2.support.filter (fun m => Nat.Coprime P2 m)) : ℝ) := by
      simp [BoundingSieve.siftedSum, s2]
    rw [hsif_eq]
    have hcard_nat : #T_good ≤ #(s2.support.filter (fun m => Nat.Coprime P2 m)) := by
      refine Finset.card_le_card_of_injOn (fun t => (a' * t + 1) * (n' * t + 1)) ?_ hinj2.injOn
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htIcc, hp_prime, hp_gt, hq_prime, hq_gt⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t, htIcc, rfl⟩, ?_⟩
      refine Nat.Coprime.mul_right ?_ ?_
      · rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
        intro hdvd
        rcases (hp_prime.prime.dvd_finsetProd_iff _).mp hdvd with ⟨r, hrF2, hpr⟩
        have hrp : r.Prime := hF2_prime r hrF2
        have heq : a' * t + 1 = r := (Nat.prime_dvd_prime_iff_eq hp_prime hrp).mp hpr
        have hrw2 : r ≤ w2 := (mem_primesLE.mp (Finset.mem_filter.mp hrF2).1).2
        omega
      · rw [Nat.coprime_comm, hq_prime.coprime_iff_not_dvd]
        intro hdvd
        rcases (hq_prime.prime.dvd_finsetProd_iff _).mp hdvd with ⟨r, hrF2, hqr⟩
        have hrp : r.Prime := hF2_prime r hrF2
        have heq : n' * t + 1 = r := (Nat.prime_dvd_prime_iff_eq hq_prime hrp).mp hqr
        have hrw2 : r ≤ w2 := (mem_primesLE.mp (Finset.mem_filter.mp hrF2).1).2
        omega
    exact_mod_cast hcard_nat
  linarith

end

noncomputable section Part4And5
open Classical

/- ## Part 4: Structural Decomposition and Upper Bounds on Bad Primes -/

private lemma sum_inv_pred_mul_le (A B : ℕ) (hA : 2 ≤ A) :
    (∑ k ∈ Finset.Icc A B, (1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) ≤
      (1 : ℝ) / ((A - 1 : ℕ) : ℝ) := by
  let g : ℕ → ℝ := fun k => (1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ))
  have hA1_pos : (0 : ℝ) < ((A - 1 : ℕ) : ℝ) := by
    have : 1 ≤ A - 1 := by omega
    exact_mod_cast this
  by_cases hlt : B < A
  · rw [Finset.Icc_eq_empty (not_le.mpr hlt), Finset.sum_empty]
    positivity
  · have hAB : A ≤ B := not_lt.mp hlt
    have htele : ∀ m : ℕ,
        (∑ k ∈ Finset.Icc A (A + m), g k) =
          (1 : ℝ) / ((A - 1 : ℕ) : ℝ) - (1 : ℝ) / ((A + m : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero =>
        simp only [add_zero, Finset.Icc_self, Finset.sum_singleton, g]
        have hA_pos : (0 : ℝ) < (A : ℝ) := by positivity
        have hsub : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hsub]
        have hA1_ne : (A : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hA1_ne, hA_pos.ne']
        ring
      | succ j ih =>
        rw [← Nat.add_assoc A j 1, Finset.sum_Icc_succ_top (by omega : A ≤ A + j + 1), ih]
        dsimp [g]
        have hAj_pos : (0 : ℝ) < ((A + j : ℕ) : ℝ) := by
          have : 1 ≤ A + j := by omega
          exact_mod_cast this
        have hAj1_pos : (0 : ℝ) < ((A + j + 1 : ℕ) : ℝ) := by
          have : 1 ≤ A + j + 1 := by omega
          exact_mod_cast this
        have hadd1 : ((A + j + 1 : ℕ) : ℝ) = ((A + j : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hadd1]
        have h1_ne : ((A + j : ℕ) : ℝ) ≠ 0 := hAj_pos.ne'
        have h2_ne : ((A + j : ℕ) : ℝ) + 1 ≠ 0 := by linarith
        field_simp [hA1_pos.ne', h1_ne, h2_ne]
        ring
    have hBeq : B = A + (B - A) := (Nat.add_sub_of_le hAB).symm
    change (∑ k ∈ Finset.Icc A B, g k) ≤ _
    rw [hBeq, htele (B - A)]
    have : (0 : ℝ) ≤ (1 : ℝ) / ((A + (B - A) : ℕ) : ℝ) := by positivity
    linarith

private lemma good_prime_gives_unique {n m0 B p : ℕ} (hn : 0 < n)
    (hm0 : ∀ m, Nat.totient m = n ↔ m = m0)
    (hp : p.Prime) (hp_gt : max m0 (max (n + 1) (B + 2)) < p)
    (hgood : ¬ ∃ y, ¬ p ∣ y ∧ Nat.totient y = (p - 1) * n) :
    B < (p - 1) * n ∧ ∃! y, Nat.totient y = (p - 1) * n := by
  have hp_gt_m0 : m0 < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt_n1 : n + 1 < p :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp_gt
  have hp_gt_B2 : B + 2 < p :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp_gt
  have hp1_pos : 0 < p - 1 := by omega
  have hgtB : B < (p - 1) * n := by
    calc B < B + 1 := Nat.lt_succ_self B
      _ ≤ p - 1 := by omega
      _ = (p - 1) * 1 := (mul_one _).symm
      _ ≤ (p - 1) * n := Nat.mul_le_mul_left _ hn
  have hm0_tot : Nat.totient m0 = n := (hm0 m0).mpr rfl
  have hm0_pos : 0 < m0 := by
    by_contra hm0_0
    have : m0 = 0 := Nat.le_zero.mp (not_lt.mp hm0_0)
    rw [this, Nat.totient_zero] at hm0_tot
    omega
  have hnot_p_m0 : ¬ p ∣ m0 := Nat.not_dvd_of_pos_of_lt hm0_pos hp_gt_m0
  have hcop_pm0 : p.Coprime m0 := hp.coprime_iff_not_dvd.mpr hnot_p_m0
  have hexists : Nat.totient (p * m0) = (p - 1) * n := by
    rw [Nat.totient_mul hcop_pm0, Nat.totient_prime hp, hm0_tot]
  refine ⟨hgtB, p * m0, hexists, fun y hy => ?_⟩
  have hpy : p ∣ y := by
    by_contra hnot
    exact hgood ⟨y, hnot, hy⟩
  have hnot_p2 : ¬ p ^ 2 ∣ y := by
    intro hp2
    have htdvd : Nat.totient (p ^ 2) ∣ Nat.totient y := Nat.totient_dvd_of_dvd hp2
    rw [Nat.totient_prime_pow hp two_pos] at htdvd
    simp only [Nat.reduceSub, pow_one] at htdvd
    rw [hy, mul_comm p (p - 1)] at htdvd
    have hpn : p ∣ n := (mul_dvd_mul_iff_left hp1_pos.ne').mp htdvd
    have hple : p ≤ n := Nat.le_of_dvd hn hpn
    omega
  set l := y / p
  have hyl : p * l = y := Nat.mul_div_cancel' hpy
  have hnot_pl : ¬ p ∣ l := by
    intro hpl
    apply hnot_p2
    rw [sq, ← hyl]
    exact mul_dvd_mul_left p hpl
  have hcop_pl : p.Coprime l := hp.coprime_iff_not_dvd.mpr hnot_pl
  have htot_l : (p - 1) * Nat.totient l = (p - 1) * n := by
    calc (p - 1) * Nat.totient l = Nat.totient p * Nat.totient l := by rw [Nat.totient_prime hp]
      _ = Nat.totient (p * l) := (Nat.totient_mul hcop_pl).symm
      _ = (p - 1) * n := hyl ▸ hy
  have hl_eq : l = m0 := (hm0 l).mp (Nat.eq_of_mul_eq_mul_left hp1_pos htot_l)
  rw [← hyl, hl_eq]

private lemma prime_pow_bound_of_no_large_sq {T n m q d : ℕ} (_hT : 1 ≤ T) (hn : 1 ≤ n)
    (hno_sq : ∀ k > T, ¬ k ^ 2 ∣ m) (hq : q.Prime) (hdvd : q ^ d ∣ m * n) :
    q ^ d ≤ T ^ 2 * q * n := by
  set g := (q ^ d).gcd m
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m (pow_pos hq.pos d)
  have hg_dvd_qd : g ∣ q ^ d := Nat.gcd_dvd_left (q ^ d) m
  have hg_dvd_m : g ∣ m := Nat.gcd_dvd_right (q ^ d) m
  have hqd_eq : g * (q ^ d / g) = q ^ d := Nat.mul_div_cancel' hg_dvd_qd
  have hm_eq : g * (m / g) = m := Nat.mul_div_cancel' hg_dvd_m
  have hcop_div : (q ^ d / g).Coprime (m / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have hdiv_dvd_mul : g * (q ^ d / g) ∣ g * ((m / g) * n) := by
    rwa [hqd_eq, ← mul_assoc, hm_eq]
  have hdiv_dvd : q ^ d / g ∣ (m / g) * n :=
    (mul_dvd_mul_iff_left hg_pos.ne').mp hdiv_dvd_mul
  have hdiv_dvd_n : q ^ d / g ∣ n := hcop_div.dvd_of_dvd_mul_left hdiv_dvd
  have hdiv_le_n : q ^ d / g ≤ n := Nat.le_of_dvd hn hdiv_dvd_n
  have hqd_le_gn : q ^ d ≤ g * n := by
    rw [← hqd_eq]
    exact Nat.mul_le_mul_left g hdiv_le_n
  rcases (Nat.dvd_prime_pow hq).mp hg_dvd_qd with ⟨j, _, hgj⟩
  have hsq_dvd_m : (q ^ (j / 2)) ^ 2 ∣ m := by
    have h2j : 2 * (j / 2) ≤ j := Nat.mul_div_le j 2
    have hpow : (q ^ (j / 2)) ^ 2 = q ^ (2 * (j / 2)) := by
      rw [← pow_mul, mul_comm]
    rw [hpow]
    exact (Nat.pow_dvd_pow q h2j).trans (hgj ▸ hg_dvd_m)
  have hqj2_le_T : q ^ (j / 2) ≤ T := by
    by_contra hgt
    exact hno_sq (q ^ (j / 2)) (not_le.mp hgt) hsq_dvd_m
  have hmod_le : q ^ (j % 2) ≤ q := by
    have hlt2 : j % 2 ≤ 1 := by omega
    calc q ^ (j % 2) ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hlt2
      _ = q := pow_one q
  have hg_le : g ≤ T ^ 2 * q := by
    have hj_split : 2 * (j / 2) + j % 2 = j := Nat.div_add_mod j 2
    have hqj_eq : q ^ j = (q ^ (j / 2)) ^ 2 * q ^ (j % 2) := by
      conv_lhs => rw [← hj_split]
      rw [pow_add, mul_comm 2 (j / 2), pow_mul]
    rw [hgj, hqj_eq]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hqj2_le_T 2) hmod_le
  exact hqd_le_gn.trans (Nat.mul_le_mul_right n hg_le)

private lemma self_le_two_pow_omega_mul_totient {z R0 : ℕ} (_hz : 1 ≤ z)
    (hcard : #z.primeFactors ≤ R0) :
    z ≤ 2 ^ R0 * Nat.totient z := by
  have hid := Nat.totient_mul_prod_primeFactors z
  have hprod_pos : 0 < ∏ r ∈ z.primeFactors, (r - 1) :=
    Finset.prod_pos fun r hr => by
      have := (Nat.prime_of_mem_primeFactors hr).two_le
      omega
  have hprod_le : (∏ r ∈ z.primeFactors, r) ≤
      2 ^ (#z.primeFactors) * ∏ r ∈ z.primeFactors, (r - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun r hr => ?_
    have := (Nat.prime_of_mem_primeFactors hr).two_le
    omega
  have hpow_le : 2 ^ (#z.primeFactors) ≤ 2 ^ R0 :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hmul : z * ∏ r ∈ z.primeFactors, (r - 1) ≤
      (2 ^ R0 * Nat.totient z) * ∏ r ∈ z.primeFactors, (r - 1) := by
    calc z * ∏ r ∈ z.primeFactors, (r - 1)
      _ = Nat.totient z * ∏ r ∈ z.primeFactors, r := hid.symm
      _ ≤ Nat.totient z * (2 ^ (#z.primeFactors) * ∏ r ∈ z.primeFactors, (r - 1)) :=
        Nat.mul_le_mul_left _ hprod_le
      _ ≤ Nat.totient z * (2 ^ R0 * ∏ r ∈ z.primeFactors, (r - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow_le)
      _ = (2 ^ R0 * Nat.totient z) * ∏ r ∈ z.primeFactors, (r - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmul hprod_pos

private lemma bad_prime_dichotomy {n T u p y : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hu_ge : max (T ^ 2 * n) (2 ^ (2 * T ^ 2 * n + 3) * n) ≤ u)
    (hp : p.Prime)
    (hp_lo : u ^ (48 * (2 * T ^ 2 * n + 2)) < p)
    (hp_hi : p ≤ u ^ (96 * (2 * T ^ 2 * n + 2)))
    (hno_sq : ∀ k > T, ¬ k ^ 2 ∣ p - 1)
    (hnot_py : ¬ p ∣ y) (htot : Nat.totient y = (p - 1) * n) :
    let R0 := 2 * T ^ 2 * n + 2
    let X := u ^ (96 * R0)
    (∃ q : ℕ, u ^ 20 ≤ q ∧ q ≤ X * n + 1 ∧ q * (q - 1) ∣ (p - 1) * n) ∨
    (∃ z ∈ (Finset.Icc 1 X).filter (fun z : ℕ =>
        #z.primeFactors ≤ R0 ∧ Nat.totient z ≠ n ∧ u ^ 20 * Nat.totient z ≤ 2 * n * X),
      ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z) := by
  intro R0 X
  change u ^ (48 * R0) < p at hp_lo
  change p ≤ X at hp_hi
  have hp_two_le : 2 ≤ p := hp.two_le
  have hR0_pos : 1 ≤ R0 := by dsimp [R0]; omega
  have hu_T2n : T ^ 2 * n ≤ u := (le_max_left _ _).trans hu_ge
  have hu_2R0 : 2 ^ (R0 + 1) * n ≤ u := by
    dsimp [R0]
    exact (le_max_right _ _).trans hu_ge
  have hu2 : 2 ≤ u := by
    have : 2 ≤ 2 ^ (R0 + 1) * n :=
      Nat.le_mul_of_pos_right _ hn |>.trans' (by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (R0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hu48_ge2 : 2 ≤ u ^ (48 * R0) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (48 * R0) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ u ^ (48 * R0) := Nat.pow_le_pow_left hu2 _
  have hy_tot_gt1 : 1 < Nat.totient y := by
    rw [htot]
    have hp1_ge2 : 2 ≤ p - 1 := by omega
    calc 1 < 2 * 1 := by norm_num
      _ ≤ (p - 1) * n := Nat.mul_le_mul hp1_ge2 hn
  have hy_gt1 : 1 < y := by
    by_contra hy_le1
    have : y = 0 ∨ y = 1 := by omega
    rcases this with rfl | rfl <;> simp at hy_tot_gt1
  have hy0 : y ≠ 0 := by omega
  have hy_omega : #y.primeFactors ≤ R0 := by
    set OddPF := y.primeFactors.erase 2
    have h2_dvd_prod : 2 ^ (#OddPF) ∣ ∏ r ∈ OddPF, (r - 1) := by
      rw [← Finset.prod_const]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun r hr => ?_
      have hr_ne2 : r ≠ 2 := Finset.ne_of_mem_erase hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr)
      rcases hrp.eq_two_or_odd with rfl | hrodd
      · exact (hr_ne2 rfl).elim
      · exact ⟨(r - 1) / 2, by omega⟩
    have hprod_dvd_tot : (∏ r ∈ OddPF, (r - 1)) ∣ (p - 1) * n := by
      have h1 : (∏ r ∈ OddPF, (r - 1)) ∣ ∏ r ∈ y.primeFactors, (r - 1) :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset 2 y.primeFactors)
      have h2 : (∏ r ∈ y.primeFactors, (r - 1)) ∣ Nat.totient y := by
        rw [Nat.totient_eq_div_primeFactors_mul y]
        exact dvd_mul_left _ _
      exact h1.trans (htot ▸ h2)
    have h2pow_le : 2 ^ (#OddPF) ≤ T ^ 2 * 2 * n :=
      prime_pow_bound_of_no_large_sq hT hn hno_sq Nat.prime_two (h2_dvd_prod.trans hprod_dvd_tot)
    have hcard_lt : #OddPF < 2 * T ^ 2 * n := by
      calc #OddPF < 2 ^ (#OddPF) := Nat.lt_two_pow_self
        _ ≤ T ^ 2 * 2 * n := h2pow_le
        _ = 2 * T ^ 2 * n := by ring
    have hcard_le_add1 : #y.primeFactors ≤ #OddPF + 1 := by
      by_cases h2mem : 2 ∈ y.primeFactors
      · exact (Finset.card_erase_add_one h2mem).symm.le
      · dsimp [OddPF]
        rw [Finset.erase_eq_of_notMem h2mem]
        omega
    dsimp [R0]
    omega
  have hpf_ne : y.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hy_gt1
  set q := y.primeFactors.max' hpf_ne
  have hq_mem : q ∈ y.primeFactors := Finset.max'_mem _ hpf_ne
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_y : q ∣ y := Nat.dvd_of_mem_primeFactors hq_mem
  have hq_ge : u ^ 20 ≤ q := by
    have htot_prod : Nat.totient y =
        ∏ r ∈ y.primeFactors, (r ^ (y.factorization r - 1) * (r - 1)) := by
      rw [Nat.totient_eq_prod_factorization hy0, Finsupp.prod]
      rfl
    have hfactor_le : ∀ r ∈ y.primeFactors,
        r ^ (y.factorization r - 1) * (r - 1) ≤ T ^ 2 * n * q ^ 2 := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hr_le_q : r ≤ q := Finset.le_max' _ r hr
      have hrdvd_tot : r ^ (y.factorization r - 1) ∣ (p - 1) * n := by
        have h1 : r ^ (y.factorization r - 1) ∣ r ^ (y.factorization r - 1) * (r - 1) :=
          dvd_mul_right _ _
        have h2 : r ^ (y.factorization r - 1) * (r - 1) ∣ Nat.totient y := by
          rw [htot_prod]
          exact Finset.dvd_prod_of_mem _ hr
        exact h1.trans (htot ▸ h2)
      have hrpow_le : r ^ (y.factorization r - 1) ≤ T ^ 2 * r * n :=
        prime_pow_bound_of_no_large_sq hT hn hno_sq hrp hrdvd_tot
      calc r ^ (y.factorization r - 1) * (r - 1)
        _ ≤ (T ^ 2 * r * n) * q :=
          Nat.mul_le_mul hrpow_le ((Nat.sub_le r 1).trans hr_le_q)
        _ ≤ (T ^ 2 * q * n) * q :=
          Nat.mul_le_mul_right q (Nat.mul_le_mul_right n (Nat.mul_le_mul_left _ hr_le_q))
        _ = T ^ 2 * n * q ^ 2 := by ring
    have hbase_ge1 : 1 ≤ T ^ 2 * n * q ^ 2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hT) hn) (Nat.pow_pos hq_prime.pos)
    have htot_le : (p - 1) * n ≤ (T ^ 2 * n) ^ R0 * q ^ (2 * R0) := by
      calc (p - 1) * n = Nat.totient y := htot.symm
        _ = ∏ r ∈ y.primeFactors, (r ^ (y.factorization r - 1) * (r - 1)) := htot_prod
        _ ≤ ∏ _r ∈ y.primeFactors, (T ^ 2 * n * q ^ 2) := Finset.prod_le_prod' hfactor_le
        _ = (T ^ 2 * n * q ^ 2) ^ (#y.primeFactors) := by simp
        _ ≤ (T ^ 2 * n * q ^ 2) ^ R0 := Nat.pow_le_pow_right hbase_ge1 hy_omega
        _ = (T ^ 2 * n) ^ R0 * q ^ (2 * R0) := by rw [mul_pow, ← pow_mul]
    have hu48_le : u ^ (8 * R0) * (u ^ 20) ^ (2 * R0) ≤ u ^ (8 * R0) * q ^ (2 * R0) := by
      have hlhs : u ^ (8 * R0) * (u ^ 20) ^ (2 * R0) = u ^ (48 * R0) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
      have hrhs1 : (T ^ 2 * n) ^ R0 ≤ u ^ (8 * R0) := by
        calc (T ^ 2 * n) ^ R0 ≤ u ^ R0 := Nat.pow_le_pow_left hu_T2n R0
          _ ≤ u ^ (8 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [hlhs]
      calc u ^ (48 * R0) ≤ p - 1 := by omega
        _ = (p - 1) * 1 := (mul_one _).symm
        _ ≤ (p - 1) * n := Nat.mul_le_mul_left _ hn
        _ ≤ (T ^ 2 * n) ^ R0 * q ^ (2 * R0) := htot_le
        _ ≤ u ^ (8 * R0) * q ^ (2 * R0) := Nat.mul_le_mul_right _ hrhs1
    have hpow_le : (u ^ 20) ^ (2 * R0) ≤ q ^ (2 * R0) :=
      Nat.le_of_mul_le_mul_left hu48_le (by positivity)
    exact (Nat.pow_le_pow_iff_left (by omega)).mp hpow_le
  have hq_hi : q ≤ X * n + 1 := by
    have hq1_dvd : q - 1 ∣ (p - 1) * n := by
      have h1 : Nat.totient q ∣ Nat.totient y := Nat.totient_dvd_of_dvd hq_dvd_y
      rwa [Nat.totient_prime hq_prime, htot] at h1
    have hq1_le : q - 1 ≤ (p - 1) * n :=
      Nat.le_of_dvd (Nat.mul_pos (by omega) hn) hq1_dvd
    have hp1_le : (p - 1) * n ≤ X * n := Nat.mul_le_mul_right n (by omega)
    omega
  by_cases hq2 : q ^ 2 ∣ y
  · left
    refine ⟨q, hq_ge, hq_hi, ?_⟩
    have htdvd : Nat.totient (q ^ 2) ∣ Nat.totient y := Nat.totient_dvd_of_dvd hq2
    rw [Nat.totient_prime_pow hq_prime two_pos] at htdvd
    simp only [Nat.reduceSub, pow_one, htot] at htdvd
    exact htdvd
  · right
    set z := y / q
    have hyz : q * z = y := Nat.mul_div_cancel' hq_dvd_y
    have hz_pos : 1 ≤ z := by
      by_contra hz0
      have hzeq0 : z = 0 := Nat.lt_one_iff.mp (not_le.mp hz0)
      rw [hzeq0, mul_zero] at hyz
      exact hy0 hyz.symm
    have hnot_qz : ¬ q ∣ z := by
      intro hqz
      apply hq2
      rw [sq, ← hyz]
      exact mul_dvd_mul_left q hqz
    have hcop_qz : q.Coprime z := hq_prime.coprime_iff_not_dvd.mpr hnot_qz
    have htot_eq : (p - 1) * n = (q - 1) * Nat.totient z := by
      rw [← htot, ← hyz, Nat.totient_mul hcop_qz, Nat.totient_prime hq_prime]
    have hz_omega : #z.primeFactors ≤ R0 := by
      have hz_sub : z.primeFactors ⊆ y.primeFactors :=
        Nat.primeFactors_mono ⟨q, by rw [← hyz, mul_comm]⟩ hy0
      exact (Finset.card_le_card hz_sub).trans hy_omega
    have ha_ne_n : Nat.totient z ≠ n := by
      intro ha_eq
      rw [ha_eq] at htot_eq
      have hpq1 : p - 1 = q - 1 := Nat.eq_of_mul_eq_mul_right hn htot_eq
      have hpq : p = q := by
        have := hq_prime.two_le
        omega
      exact hnot_py (hpq ▸ hq_dvd_y)
    have hu20_a : u ^ 20 * Nat.totient z ≤ 2 * n * X := by
      have hq_le_2q1 : q ≤ 2 * (q - 1) := by
        have := hq_prime.two_le
        omega
      calc u ^ 20 * Nat.totient z ≤ q * Nat.totient z := Nat.mul_le_mul_right _ hq_ge
        _ ≤ (2 * (q - 1)) * Nat.totient z := Nat.mul_le_mul_right _ hq_le_2q1
        _ = 2 * ((q - 1) * Nat.totient z) := by ring
        _ = 2 * ((p - 1) * n) := by rw [← htot_eq]
        _ ≤ 2 * (X * n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right n (by omega))
        _ = 2 * n * X := by ring
    have hz_le_a : z ≤ 2 ^ R0 * Nat.totient z :=
      self_le_two_pow_omega_mul_totient hz_pos hz_omega
    have hz_le_X : z ≤ X := by
      have hu20_pos : 0 < u ^ 20 := by positivity
      have hmul_z : u ^ 20 * z ≤ u ^ 20 * X := by
        calc u ^ 20 * z ≤ u ^ 20 * (2 ^ R0 * Nat.totient z) := Nat.mul_le_mul_left _ hz_le_a
          _ = 2 ^ R0 * (u ^ 20 * Nat.totient z) := by ring
          _ ≤ 2 ^ R0 * (2 * n * X) := Nat.mul_le_mul_left _ hu20_a
          _ = (2 ^ (R0 + 1) * n) * X := by rw [pow_succ]; ring
          _ ≤ u * X := Nat.mul_le_mul_right X hu_2R0
          _ ≤ u ^ 20 * X := Nat.mul_le_mul_right X (by
            calc u = u ^ 1 := (pow_one u).symm
              _ ≤ u ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num))
      exact Nat.le_of_mul_le_mul_left hmul_z hu20_pos
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hz_pos, hz_le_X⟩,
      hz_omega, ha_ne_n, hu20_a⟩, q, hq_prime, hq_ge, htot_eq⟩

private lemma card_bad1_le {J R0 u : ℕ} (_hJ1 : 1 ≤ J)
    (hJ_tail : (6 : ℝ) / (2 : ℝ) ^ J ≤ 3 / 256) (hR0 : 1 ≤ R0) (hu2 : 2 ≤ u) :
    let T := 2 * 4 ^ J
    let X := u ^ (96 * R0)
    ((#((primesLE X).filter (fun p => ∃ k > T, k ^ 2 ∣ p - 1)) : ℕ) : ℝ) ≤
      (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 3 * (u : ℝ) ^ (88 * R0) := by
  intro T X
  have hT_ge2 : 2 ≤ T := Nat.le_mul_of_pos_right 2 (by positivity)
  have hX_ge2 : 2 ≤ X := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (96 * R0) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ u ^ (96 * R0) := Nat.pow_le_pow_left hu2 _
  have hlog_u_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < u by omega))
  have hlog_X_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  set B1 := (primesLE X).filter (fun p => ∃ k > T, k ^ 2 ∣ p - 1)
  set K_mid := u ^ (8 * R0)
  set K_max := u ^ (48 * R0)
  have hB1_sub : B1 ⊆
      (Finset.Icc (T + 1) K_mid).biUnion (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) ∪
      (Finset.Icc (K_mid + 1) K_max).biUnion (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpLE, k, hk_gt, hkdvd⟩
    rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
    have hp1_pos : 0 < p - 1 := by
      by_contra h0
      have hp1_0 : p - 1 = 0 := Nat.le_zero.mp (not_lt.mp h0)
      have h0dvd : k ^ 2 ∣ 0 := hp1_0 ▸ hkdvd
      have := hpp.two_le
      omega
    have hk2_le : k ^ 2 ≤ K_max ^ 2 := by
      have h1 : k ^ 2 ≤ p - 1 := Nat.le_of_dvd hp1_pos hkdvd
      have h2 : K_max ^ 2 = X := by
        dsimp [K_max, X]
        rw [← pow_mul]
        congr 1; ring
      rw [h2]; omega
    have hk_le_max : k ≤ K_max := (Nat.pow_le_pow_iff_left (by norm_num)).mp hk2_le
    by_cases hk_mid : k ≤ K_mid
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_Icc.mpr ⟨hk_gt, hk_mid⟩, Finset.mem_filter.mpr ⟨hpLE, hkdvd⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_Icc.mpr ⟨by omega, hk_le_max⟩, Finset.mem_filter.mpr ⟨hpLE, hkdvd⟩⟩)
  have hcard_union : (#B1 : ℝ) ≤
      (∑ k ∈ Finset.Icc (T + 1) K_mid,
        ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ)) +
      (∑ k ∈ Finset.Icc (K_mid + 1) K_max,
        ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ)) := by
    have hnat : #B1 ≤
        (∑ k ∈ Finset.Icc (T + 1) K_mid, #((primesLE X).filter (fun p => k ^ 2 ∣ p - 1))) +
        (∑ k ∈ Finset.Icc (K_mid + 1) K_max, #((primesLE X).filter (fun p => k ^ 2 ∣ p - 1))) := by
      calc #B1 ≤ #((Finset.Icc (T + 1) K_mid).biUnion
              (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) ∪
            (Finset.Icc (K_mid + 1) K_max).biUnion
              (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1))) :=
            Finset.card_le_card hB1_sub
        _ ≤ #((Finset.Icc (T + 1) K_mid).biUnion
              (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1))) +
            #((Finset.Icc (K_mid + 1) K_max).biUnion
              (fun k => (primesLE X).filter (fun p => k ^ 2 ∣ p - 1))) :=
            Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    exact_mod_cast hnat
  set z1 := u ^ (12 * R0)
  have hz1_ge1 : 1 ≤ z1 := Nat.one_le_pow _ _ (by omega)
  have hlog_z1_ge : (1 / 8 : ℝ) * Real.log (X : ℝ) ≤ Real.log ((z1 + 1 : ℕ) : ℝ) := by
    have h1 : (1 / 8 : ℝ) * Real.log (X : ℝ) = Real.log (z1 : ℝ) := by
      dsimp [X, z1]
      push_cast
      rw [Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [h1]
    exact Real.log_le_log (by exact_mod_cast hz1_ge1) (by exact_mod_cast Nat.le_succ z1)
  have hsum1_le : (∑ k ∈ Finset.Icc (T + 1) K_mid,
      ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ)) ≤
      (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 2 * (u : ℝ) ^ (80 * R0) := by
    have hterm1 : ∀ k ∈ Finset.Icc (T + 1) K_mid,
        ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ) ≤
          (8 * (X : ℝ) / Real.log (X : ℝ)) * ((1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) +
          2 * (u : ℝ) ^ (72 * R0) := by
      intro k hk
      have hk_ge2 : 2 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      have hc := card_primes_mod_sq_le k X z1 hk_ge2 hz1_ge1
      have htot_pos : (0 : ℝ) < (Nat.totient k : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      have hmain : (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ)) ≤
          (8 * (X : ℝ) / Real.log (X : ℝ)) * ((1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) := by
        have hden_ge : (k : ℝ) * (Nat.totient k : ℝ) * ((1 / 8 : ℝ) * Real.log (X : ℝ)) ≤
            (k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlog_z1_ge (by positivity)
        calc (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ))
          _ ≤ (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * ((1 / 8 : ℝ) * Real.log (X : ℝ))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
          _ = (8 * (X : ℝ) / Real.log (X : ℝ)) * ((1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) := by
            field_simp [hk_pos.ne', htot_pos.ne', hlog_X_pos.ne']
      have hz1_le_u72 : (z1 : ℝ) ≤ (u : ℝ) ^ (72 * R0) := by
        have hnat : u ^ (12 * R0) ≤ u ^ (72 * R0) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast hnat
      have hz1_6_eq : (z1 : ℝ) ^ 6 = (u : ℝ) ^ (72 * R0) := by
        dsimp [z1]; push_cast; rw [← pow_mul]; congr 1; ring
      set M_k : ℝ := (X : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ) * Real.log ((z1 + 1 : ℕ) : ℝ))
      set M_k' : ℝ := (8 * (X : ℝ) / Real.log (X : ℝ)) * ((1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ)))
      linarith
    calc (∑ k ∈ Finset.Icc (T + 1) K_mid,
          ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ))
      _ ≤ ∑ k ∈ Finset.Icc (T + 1) K_mid,
          ((8 * (X : ℝ) / Real.log (X : ℝ)) * ((1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) +
            2 * (u : ℝ) ^ (72 * R0)) := Finset.sum_le_sum hterm1
      _ = (8 * (X : ℝ) / Real.log (X : ℝ)) *
            (∑ k ∈ (Finset.Icc (T + 1) K_mid : Finset ℕ),
              (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) +
          ((#(Finset.Icc (T + 1) K_mid) : ℕ) : ℝ) * (2 * (u : ℝ) ^ (72 * R0)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (8 * (X : ℝ) / Real.log (X : ℝ)) * (3 / 256 : ℝ) +
          ((K_mid : ℝ)) * (2 * (u : ℝ) ^ (72 * R0)) := by
        have htail : (∑ k ∈ (Finset.Icc (T + 1) K_mid : Finset ℕ),
            (1 : ℝ) / ((k : ℝ) * (Nat.totient k : ℝ))) ≤ 3 / 256 :=
          (sum_inv_mul_totient_tail_gen J K_mid).trans hJ_tail
        have hcard_K : ((#(Finset.Icc (T + 1) K_mid) : ℕ) : ℝ) ≤ (K_mid : ℝ) := by
          have : #(Finset.Icc (T + 1) K_mid) ≤ K_mid := by simp [Nat.card_Icc]
          exact_mod_cast this
        exact _root_.add_le_add (mul_le_mul_of_nonneg_left htail (by positivity))
          (mul_le_mul_of_nonneg_right hcard_K (by positivity))
      _ = (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 2 * (u : ℝ) ^ (80 * R0) := by
        have hK_eq : (K_mid : ℝ) * (2 * (u : ℝ) ^ (72 * R0)) = 2 * (u : ℝ) ^ (80 * R0) := by
          dsimp [K_mid]; push_cast; rw [mul_comm, mul_assoc, ← pow_add]; congr 2; ring
        rw [hK_eq]; ring
  have hsum2_le : (∑ k ∈ Finset.Icc (K_mid + 1) K_max,
      ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ)) ≤
      (u : ℝ) ^ (88 * R0) := by
    have hterm2 : ∀ k ∈ Finset.Icc (K_mid + 1) K_max,
        ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ) ≤
          (X : ℝ) * ((1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) := by
      intro k hk
      have hk_ge2 : 2 ≤ k := by
        have hK1 : 1 ≤ K_mid := Nat.one_le_pow _ _ (by omega)
        have := (Finset.mem_Icc.mp hk).1
        omega
      have hk2_pos : 0 < k ^ 2 := by positivity
      have hcard_div : #((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) ≤ X / k ^ 2 := by
        have hinj : Set.InjOn (fun p : ℕ => (p - 1) / k ^ 2)
            ↑((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) := by
          intro p1 hp1 p2 hp2 heq
          dsimp at heq
          have hp1p : p1.Prime := (mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).1).1
          have hp2p : p2.Prime := (mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).1).1
          have hd1 : k ^ 2 ∣ p1 - 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).2
          have hd2 : k ^ 2 ∣ p2 - 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).2
          have heq1 : p1 - 1 = p2 - 1 := by
            rw [← Nat.mul_div_cancel' hd1, heq, Nat.mul_div_cancel' hd2]
          have := hp1p.two_le; have := hp2p.two_le; omega
        have hmaps : ∀ p ∈ (primesLE X).filter (fun p => k ^ 2 ∣ p - 1),
            (p - 1) / k ^ 2 ∈ Finset.Icc 1 (X / k ^ 2) := by
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpLE, hkdvd⟩
          rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
          have hp1_pos : 0 < p - 1 := by
            by_contra h0
            have hp1_0 : p - 1 = 0 := Nat.le_zero.mp (not_lt.mp h0)
            have h0dvd : k ^ 2 ∣ 0 := hp1_0 ▸ hkdvd
            have := hpp.two_le; omega
          rcases hkdvd with ⟨t, ht⟩
          have ht_eq : (p - 1) / k ^ 2 = t := by rw [ht, Nat.mul_div_cancel_left t hk2_pos]
          rw [ht_eq]
          have ht_pos : 1 ≤ t := by
            by_contra ht0
            have ht0' : t = 0 := Nat.lt_one_iff.mp (not_le.mp ht0)
            rw [ht0', mul_zero] at ht; omega
          have ht_hi : t ≤ X / k ^ 2 := by
            have hk2t : t * k ^ 2 ≤ X := by rw [mul_comm, ← ht]; omega
            exact (Nat.le_div_iff_mul_le hk2_pos).mpr hk2t
          exact Finset.mem_Icc.mpr ⟨ht_pos, ht_hi⟩
        calc #((primesLE X).filter (fun p => k ^ 2 ∣ p - 1))
          _ ≤ #(Finset.Icc 1 (X / k ^ 2)) := Finset.card_le_card_of_injOn _ hmaps hinj
          _ = X / k ^ 2 := by simp [Nat.card_Icc]
      have hreal1 : ((X / k ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((k : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast (mul_comm (k ^ 2) (X / k ^ 2) ▸ Nat.mul_div_le X (k ^ 2))
      have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) * (k : ℝ) := by
        have : 1 ≤ k - 1 := by omega
        have h1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast this
        positivity
      have hreal2 : (X : ℝ) / ((k : ℝ) ^ 2) ≤
          (X : ℝ) * ((1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) := by
        rw [mul_one_div]
        refine div_le_div_of_nonneg_left (by positivity) hk1_pos ?_
        rw [sq]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.sub_le k 1
      exact (show ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ) ≤
        ((X / k ^ 2 : ℕ) : ℝ) by exact_mod_cast hcard_div).trans (hreal1.trans hreal2)
    have hKmid_ge2 : 2 ≤ K_mid + 1 := by
      have : 1 ≤ K_mid := Nat.one_le_pow _ _ (by omega)
      omega
    calc (∑ k ∈ Finset.Icc (K_mid + 1) K_max,
          ((#((primesLE X).filter (fun p => k ^ 2 ∣ p - 1)) : ℕ) : ℝ))
      _ ≤ ∑ k ∈ Finset.Icc (K_mid + 1) K_max,
          (X : ℝ) * ((1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) := Finset.sum_le_sum hterm2
      _ = (X : ℝ) * ∑ k ∈ Finset.Icc (K_mid + 1) K_max,
          (1 : ℝ) / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ (X : ℝ) * ((1 : ℝ) / ((K_mid : ℝ))) := by
        have htel := sum_inv_pred_mul_le (K_mid + 1) K_max hKmid_ge2
        rw [Nat.add_sub_cancel] at htel
        exact mul_le_mul_of_nonneg_left htel (by positivity)
      _ = (u : ℝ) ^ (88 * R0) := by
        dsimp [X, K_mid]
        have hu8 : (u : ℝ) ^ (8 * R0) ≠ 0 := by positivity
        have hsplit_u : ((u ^ (96 * R0) : ℕ) : ℝ) = (u : ℝ) ^ (88 * R0) * (u : ℝ) ^ (8 * R0) := by
          push_cast; rw [← pow_add]; congr 1; ring
        rw [hsplit_u]
        push_cast
        field_simp [hu8]
  have hu80_le_u88 : (u : ℝ) ^ (80 * R0) ≤ (u : ℝ) ^ (88 * R0) := by
    have : u ^ (80 * R0) ≤ u ^ (88 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  calc (#B1 : ℝ)
    _ ≤ ((3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 2 * (u : ℝ) ^ (80 * R0)) +
          (u : ℝ) ^ (88 * R0) := hcard_union.trans (_root_.add_le_add hsum1_le hsum2_le)
    _ = (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) +
          (2 * (u : ℝ) ^ (80 * R0) + (u : ℝ) ^ (88 * R0)) := by ring
    _ ≤ (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 3 * (u : ℝ) ^ (88 * R0) := by
      have h23 : 2 * (u : ℝ) ^ (80 * R0) + (u : ℝ) ^ (88 * R0) ≤ 3 * (u : ℝ) ^ (88 * R0) := by
        linarith only [hu80_le_u88]
      gcongr

private lemma card_bad2_le {n R0 u : ℕ} (hn : 1 ≤ n) (hu2 : 2 ≤ u) :
    let X := u ^ (96 * R0)
    ((#((primesLE X).filter (fun p =>
        ∃ q : ℕ, u ^ 20 ≤ q ∧ q ≤ X * n + 1 ∧ q * (q - 1) ∣ (p - 1) * n)) : ℕ) : ℝ) ≤
      2 * (n : ℝ) * (X : ℝ) / (u : ℝ) ^ 20 := by
  intro X
  set B2 := (primesLE X).filter (fun p =>
    ∃ q : ℕ, u ^ 20 ≤ q ∧ q ≤ X * n + 1 ∧ q * (q - 1) ∣ (p - 1) * n)
  have hB2_sub : B2 ⊆ (Finset.Icc (u ^ 20) (X * n + 1)).biUnion
      (fun q => (primesLE X).filter (fun p => q * (q - 1) ∣ (p - 1) * n)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpLE, q, hq_lo, hq_hi, hqdvd⟩
    exact Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_Icc.mpr ⟨hq_lo, hq_hi⟩, Finset.mem_filter.mpr ⟨hpLE, hqdvd⟩⟩
  have hcard_sum : (#B2 : ℝ) ≤ ∑ q ∈ Finset.Icc (u ^ 20) (X * n + 1),
      ((#((primesLE X).filter (fun p => q * (q - 1) ∣ (p - 1) * n)) : ℕ) : ℝ) := by
    have hnat : #B2 ≤ ∑ q ∈ Finset.Icc (u ^ 20) (X * n + 1),
        #((primesLE X).filter (fun p => q * (q - 1) ∣ (p - 1) * n)) :=
      (Finset.card_le_card hB2_sub).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  have hu20_ge4 : 4 ≤ u ^ 20 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ u ^ 20 := Nat.pow_le_pow_left hu2 20
  have hterm : ∀ q ∈ Finset.Icc (u ^ 20) (X * n + 1),
      ((#((primesLE X).filter (fun p => q * (q - 1) ∣ (p - 1) * n)) : ℕ) : ℝ) ≤
        ((n : ℝ) * (X : ℝ)) * ((1 : ℝ) / (((q - 1 : ℕ) : ℝ) * (q : ℝ))) := by
    intro q hq
    have hq_lo : u ^ 20 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq_ge4 : 4 ≤ q := hu20_ge4.trans hq_lo
    have hqq1_pos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
    set Sq := (primesLE X).filter (fun p => q * (q - 1) ∣ (p - 1) * n)
    have hcard_Sq : #Sq ≤ (X * n) / (q * (q - 1)) := by
      have hinj : Set.InjOn (fun p : ℕ => ((p - 1) * n) / (q * (q - 1))) ↑Sq := by
        intro p1 hp1 p2 hp2 heq
        dsimp at heq
        have hp1p : p1.Prime := (mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).1).1
        have hp2p : p2.Prime := (mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).1).1
        have hd1 : q * (q - 1) ∣ (p1 - 1) * n := (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).2
        have hd2 : q * (q - 1) ∣ (p2 - 1) * n := (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).2
        have hmul_eq : (p1 - 1) * n = (p2 - 1) * n := by
          rw [← Nat.mul_div_cancel' hd1, heq, Nat.mul_div_cancel' hd2]
        have hp12 : p1 - 1 = p2 - 1 := Nat.eq_of_mul_eq_mul_right hn hmul_eq
        have := hp1p.two_le; have := hp2p.two_le; omega
      have hmaps : ∀ p ∈ Sq, ((p - 1) * n) / (q * (q - 1)) ∈
          Finset.Icc 1 ((X * n) / (q * (q - 1))) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpLE, hqdvd⟩
        rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
        have hp1n_pos : 0 < (p - 1) * n := Nat.mul_pos (by have := hpp.two_le; omega) hn
        rcases hqdvd with ⟨t, ht⟩
        have ht_eq : ((p - 1) * n) / (q * (q - 1)) = t := by
          rw [ht, Nat.mul_div_cancel_left t hqq1_pos]
        rw [ht_eq]
        have ht_pos : 1 ≤ t := by
          by_contra ht0
          have ht0' : t = 0 := Nat.lt_one_iff.mp (not_le.mp ht0)
          rw [ht0', mul_zero] at ht; omega
        have ht_hi : t ≤ (X * n) / (q * (q - 1)) := by
          refine (Nat.le_div_iff_mul_le hqq1_pos).mpr ?_
          have h1 : (p - 1) * n ≤ X * n := Nat.mul_le_mul_right n (by omega)
          linarith
        exact Finset.mem_Icc.mpr ⟨ht_pos, ht_hi⟩
      calc #Sq ≤ #(Finset.Icc 1 ((X * n) / (q * (q - 1)))) :=
            Finset.card_le_card_of_injOn _ hmaps hinj
        _ = (X * n) / (q * (q - 1)) := by simp [Nat.card_Icc]
    have hreal : (((X * n) / (q * (q - 1)) : ℕ) : ℝ) ≤
        ((n : ℝ) * (X : ℝ)) * ((1 : ℝ) / (((q - 1 : ℕ) : ℝ) * (q : ℝ))) := by
      have hden_pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) * (q : ℝ) := by
        have : 1 ≤ q - 1 := by omega
        have h1 : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
        positivity
      rw [mul_one_div, le_div_iff₀ hden_pos]
      have hnat_le := Nat.mul_div_le (X * n) (q * (q - 1))
      have hcast : (((X * n) / (q * (q - 1)) : ℕ) : ℝ) * (((q : ℝ) * ((q - 1 : ℕ) : ℝ))) ≤
          ((X : ℝ) * (n : ℝ)) := by exact_mod_cast (mul_comm (q * (q - 1)) _ ▸ hnat_le)
      linarith
    exact (show ((#Sq : ℕ) : ℝ) ≤ _ by exact_mod_cast hcard_Sq).trans hreal
  calc (#B2 : ℝ)
    _ ≤ ∑ q ∈ Finset.Icc (u ^ 20) (X * n + 1),
          ((n : ℝ) * (X : ℝ)) * ((1 : ℝ) / (((q - 1 : ℕ) : ℝ) * (q : ℝ))) :=
      hcard_sum.trans (Finset.sum_le_sum hterm)
    _ = ((n : ℝ) * (X : ℝ)) * ∑ q ∈ Finset.Icc (u ^ 20) (X * n + 1),
          (1 : ℝ) / (((q - 1 : ℕ) : ℝ) * (q : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((n : ℝ) * (X : ℝ)) * ((1 : ℝ) / ((u ^ 20 - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_pred_mul_le (u ^ 20) (X * n + 1) (by omega)) (by positivity)
    _ ≤ 2 * (n : ℝ) * (X : ℝ) / (u : ℝ) ^ 20 := by
      have hu20_sub : (u : ℝ) ^ 20 ≤ 2 * ((u ^ 20 - 1 : ℕ) : ℝ) := by
        have hnat : u ^ 20 ≤ 2 * (u ^ 20 - 1) := by omega
        exact_mod_cast hnat
      have hpos1 : (0 : ℝ) < ((u ^ 20 - 1 : ℕ) : ℝ) := by
        have : 1 ≤ u ^ 20 - 1 := by omega
        exact_mod_cast this
      have hpos2 : (0 : ℝ) < (u : ℝ) ^ 20 := by positivity
      rw [mul_one_div]
      have hdiv : ((n : ℝ) * (X : ℝ)) / ((u ^ 20 - 1 : ℕ) : ℝ) ≤
          ((n : ℝ) * (X : ℝ)) / ((u : ℝ) ^ 20 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      refine hdiv.trans_eq ?_
      field_simp [hpos2.ne']

private lemma self_le_four_pow (k : ℕ) : k ≤ 4 ^ k := by
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k

private lemma card_bad3_le {n R0 s : ℕ} (hn : 1 ≤ n) (hR0 : 4 ≤ R0) (hs : 1 ≤ s)
    (hu_large : max (8 * n ^ 3) (2 ^ (R0 + 1) * n) ≤ 4 ^ (4 ^ s)) :
    let u := 4 ^ (4 ^ s)
    let X := u ^ (96 * R0)
    let Z_set := (Finset.Icc 1 X).filter (fun z : ℕ =>
      #z.primeFactors ≤ R0 ∧ Nat.totient z ≠ n ∧ u ^ 20 * Nat.totient z ≤ 2 * n * X)
    let B3 := ((primesLE X).filter (fun p => u < p)).filter (fun p =>
      ∃ z ∈ Z_set, ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)
    let C_exp := Real.exp (24 + 2 * ((288 * R0 : ℕ) : ℝ))
    let C_main := (n : ℝ) * (2 : ℝ) ^ R0 * C_exp ^ 2 + 1
    let C_om := (25 + 24 * Real.log ((384 * R0 : ℕ) : ℝ)) ^ R0
    ((#B3 : ℕ) : ℝ) ≤ C_main * C_om * (X : ℝ) * (s : ℝ) ^ (48 + R0) / ((4 : ℝ) ^ s) ^ 2 := by
  intro u X Z_set B3 C_exp C_main C_om
  have h4s_le_u : 4 ^ s ≤ u := self_le_four_pow (4 ^ s)
  have hu_ge4 : 4 ≤ u := by
    have : 4 ^ 1 ≤ 4 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  have h8n3_le_X : 8 * n ^ 3 ≤ X := by
    calc 8 * n ^ 3 ≤ u := (le_max_left _ _).trans hu_large
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ (96 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2R0_le_u : 2 ^ (R0 + 1) * n ≤ u := (le_max_right _ _).trans hu_large
  have hX_eq_4pow : X = 4 ^ ((96 * R0) * 4 ^ s) := by
    dsimp [X, u]
    rw [← pow_mul, mul_comm (4 ^ s) (96 * R0)]
  have hlog4_ge1 : (1 : ℝ) ≤ Real.log 4 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    linarith [one_half_le_log_two]
  have hlog_u1_ge : (4 : ℝ) ^ s ≤ Real.log ((u + 1 : ℕ) : ℝ) := by
    have h1 : (4 : ℝ) ^ s ≤ Real.log (u : ℝ) := by
      dsimp [u]
      push_cast
      rw [Real.log_pow]
      push_cast
      calc (4 : ℝ) ^ s = (4 : ℝ) ^ s * 1 := (mul_one _).symm
        _ ≤ (4 : ℝ) ^ s * Real.log 4 := mul_le_mul_of_nonneg_left hlog4_ge1 (by positivity)
    exact h1.trans (Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ u))
  set P_cand := (primesLE X).filter (fun p => u < p)
  have hB3_sub : B3 ⊆ Z_set.biUnion (fun z => P_cand.filter (fun p =>
      ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpC, z, hzZ, hqex⟩
    exact Finset.mem_biUnion.mpr ⟨z, hzZ, Finset.mem_filter.mpr ⟨hpC, hqex⟩⟩
  have hB3_sum : ((#B3 : ℕ) : ℝ) ≤ ∑ z ∈ Z_set,
      ((#(P_cand.filter (fun p =>
        ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)) : ℕ) : ℝ) := by
    have hnat : #B3 ≤ ∑ z ∈ Z_set, #(P_cand.filter (fun p =>
        ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)) :=
      (Finset.card_le_card hB3_sub).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  have hz_bound : ∀ z ∈ Z_set,
      ((#(P_cand.filter (fun p =>
        ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)) : ℕ) : ℝ) ≤
      (C_main * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) := by
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzIcc, hz_om, ha_ne_n, hu20_a⟩
    rcases Finset.mem_Icc.mp hzIcc with ⟨hz_pos, hz_hi⟩
    set a := Nat.totient z
    have ha_pos : 1 ≤ a := Nat.totient_pos.mpr hz_pos
    set g := n.gcd a
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left a hn
    set n' := n / g
    set a' := a / g
    have hn_eq : g * n' = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n a)
    have ha_eq : g * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_right n a)
    have hcop_na' : n'.Coprime a' := Nat.coprime_div_gcd_div_gcd hg_pos
    have hn'_pos : 1 ≤ n' := by
      by_contra h0
      rw [Nat.lt_one_iff.mp (not_le.mp h0), mul_zero] at hn_eq; omega
    have ha'_pos : 1 ≤ a' := by
      by_contra h0
      rw [Nat.lt_one_iff.mp (not_le.mp h0), mul_zero] at ha_eq; omega
    have ha'_ne_n' : a' ≠ n' := fun heq => ha_ne_n (by rw [← ha_eq, heq, hn_eq])
    set M2 := X / a'
    set Pz := P_cand.filter (fun p => ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * a)
    set Tg := (Finset.Icc 1 M2).filter (fun t =>
      (a' * t + 1).Prime ∧ u < a' * t + 1 ∧ (n' * t + 1).Prime ∧ u < n' * t + 1)
    have hcard_Pz_Tg : #Pz ≤ #Tg := by
      have hinj : Set.InjOn (fun p : ℕ => (p - 1) / a') ↑Pz := by
        intro p1 hp1 p2 hp2 heq
        dsimp at heq
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp hp1) with ⟨hp1C, q1, _, _, heq1⟩
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp hp2) with ⟨hp2C, q2, _, _, heq2⟩
        have hp1_gt : u < p1 := (Finset.mem_filter.mp hp1C).2
        have hp2_gt : u < p2 := (Finset.mem_filter.mp hp2C).2
        have hd1 : a' ∣ p1 - 1 := by
          have : g * ((p1 - 1) * n') = g * ((q1 - 1) * a') := by
            calc g * ((p1 - 1) * n') = (p1 - 1) * (g * n') := by ring
              _ = (p1 - 1) * n := by rw [hn_eq]
              _ = (q1 - 1) * a := heq1
              _ = (q1 - 1) * (g * a') := by rw [ha_eq]
              _ = g * ((q1 - 1) * a') := by ring
          have h1 : (p1 - 1) * n' = (q1 - 1) * a' := Nat.eq_of_mul_eq_mul_left hg_pos this
          exact hcop_na'.symm.dvd_of_dvd_mul_right ⟨q1 - 1, by rw [h1, mul_comm]⟩
        have hd2 : a' ∣ p2 - 1 := by
          have : g * ((p2 - 1) * n') = g * ((q2 - 1) * a') := by
            calc g * ((p2 - 1) * n') = (p2 - 1) * (g * n') := by ring
              _ = (p2 - 1) * n := by rw [hn_eq]
              _ = (q2 - 1) * a := heq2
              _ = (q2 - 1) * (g * a') := by rw [ha_eq]
              _ = g * ((q2 - 1) * a') := by ring
          have h1 : (p2 - 1) * n' = (q2 - 1) * a' := Nat.eq_of_mul_eq_mul_left hg_pos this
          exact hcop_na'.symm.dvd_of_dvd_mul_right ⟨q2 - 1, by rw [h1, mul_comm]⟩
        have hp12 : p1 - 1 = p2 - 1 := by
          rw [← Nat.mul_div_cancel' hd1, heq, Nat.mul_div_cancel' hd2]
        omega
      have hmaps : ∀ p ∈ Pz, (p - 1) / a' ∈ Tg := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpC, q, hqp, hq_lo, heq_pq⟩
        rcases Finset.mem_filter.mp hpC with ⟨hpLE, hp_gt⟩
        rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
        have h1 : (p - 1) * n' = (q - 1) * a' := by
          apply Nat.eq_of_mul_eq_mul_left hg_pos
          calc g * ((p - 1) * n') = (p - 1) * (g * n') := by ring
            _ = (p - 1) * n := by rw [hn_eq]
            _ = (q - 1) * a := heq_pq
            _ = (q - 1) * (g * a') := by rw [ha_eq]
            _ = g * ((q - 1) * a') := by ring
        have hd_a' : a' ∣ p - 1 :=
          hcop_na'.symm.dvd_of_dvd_mul_right ⟨q - 1, by rw [h1, mul_comm]⟩
        set t := (p - 1) / a'
        have hat : a' * t = p - 1 := Nat.mul_div_cancel' hd_a'
        have hp_eq : a' * t + 1 = p := by omega
        have hnt : n' * t = q - 1 := by
          apply Nat.eq_of_mul_eq_mul_right ha'_pos
          calc (n' * t) * a' = (a' * t) * n' := by ring
            _ = (p - 1) * n' := by rw [hat]
            _ = (q - 1) * a' := h1
        have hq_gt_u : u < q := by
          calc u = u ^ 1 := (pow_one u).symm
            _ < u ^ 20 := Nat.pow_lt_pow_right (by omega) (by norm_num)
            _ ≤ q := hq_lo
        have hq_eq : n' * t + 1 = q := by omega
        have ht_pos : 1 ≤ t := by
          by_contra ht0
          have ht0' : t = 0 := Nat.lt_one_iff.mp (not_le.mp ht0)
          rw [ht0', mul_zero] at hat; omega
        have ht_hi : t ≤ M2 :=
          (Nat.le_div_iff_mul_le ha'_pos).mpr (by rw [mul_comm, hat]; omega)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht_pos, ht_hi⟩,
          hp_eq ▸ hpp, hp_eq ▸ hp_gt, hq_eq ▸ hqp, hq_eq ▸ hq_gt_u⟩
      exact Finset.card_le_card_of_injOn _ hmaps hinj
    set D := 2 * a' * n' * (max a' n' - min a' n')
    have hdiff_pos : 1 ≤ max a' n' - min a' n' := by
      rcases lt_or_gt_of_ne ha'_ne_n' with hlt | hgt
      · rw [max_eq_right hlt.le, min_eq_left hlt.le]; omega
      · rw [max_eq_left hgt.le, min_eq_right hgt.le]; omega
    have hD1 : 1 ≤ D :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos ha'_pos) hn'_pos) hdiff_pos
    have ha_le_2nX : a ≤ 2 * n * X := by
      calc a = 1 * a := (one_mul a).symm
        _ ≤ u ^ 20 * a := Nat.mul_le_mul_right a (Nat.one_le_pow _ _ (by omega))
        _ ≤ 2 * n * X := hu20_a
    have hD_le : D ≤ 4 ^ ((288 * R0) * 4 ^ s) := by
      have ha'_le : a' ≤ 2 * n * X := (Nat.div_le_self a g).trans ha_le_2nX
      have hn'_le : n' ≤ 2 * n * X := (Nat.div_le_self n g).trans
        (by calc n ≤ 2 * n * 1 := by omega
              _ ≤ 2 * n * X := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))
      have hmax_le : max a' n' - min a' n' ≤ 2 * n * X :=
        (Nat.sub_le _ _).trans (max_le ha'_le hn'_le)
      have hD_le_X3 : D ≤ X ^ 3 := by
        calc D = 2 * a' * n' * (max a' n' - min a' n') := rfl
          _ ≤ 2 * (2 * n * X) * n * (2 * n * X) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha'_le) (Nat.div_le_self n g)) hmax_le
          _ = (8 * n ^ 3) * X ^ 2 := by ring
          _ ≤ X * X ^ 2 := Nat.mul_le_mul_right _ h8n3_le_X
          _ = X ^ 3 := by ring
      have hX3_eq : X ^ 3 = 4 ^ ((288 * R0) * 4 ^ s) := by
        rw [hX_eq_4pow, ← pow_mul]
        congr 1; ring
      exact hD_le_X3.trans_eq hX3_eq
    have hD_poly := ratio_div_totient_le_poly (288 * R0) s D hs hD1 hD_le
    have hsieve2 := card_primes_two_linear_le a' n' M2 u ha'_pos hn'_pos ha'_ne_n' (by omega)
    have hM2_le : (M2 : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ R0 * (X : ℝ) / (z : ℝ) := by
      have hg_le_n : g ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n a)
      have hz_le_2R0a : z ≤ 2 ^ R0 * a := self_le_two_pow_omega_mul_totient hz_pos hz_om
      have hnat_mul : M2 * z ≤ n * 2 ^ R0 * X := by
        calc M2 * z ≤ M2 * (2 ^ R0 * a) := Nat.mul_le_mul_left M2 hz_le_2R0a
          _ = 2 ^ R0 * g * (a' * M2) := by rw [← ha_eq]; ring
          _ ≤ 2 ^ R0 * n * X :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hg_le_n) (Nat.mul_div_le X a')
          _ = n * 2 ^ R0 * X := by ring
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast hnat_mul
    have hu16_le : (u : ℝ) ^ 16 ≤ ((X : ℝ) / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) := by
      have hnat16 : u ^ 16 * ((4 ^ s) ^ 2 * z) ≤ X := by
        have hstep1 : u ^ 2 * (u ^ 16 * ((4 ^ s) ^ 2 * z)) ≤ u ^ 2 * X := by
          calc u ^ 2 * (u ^ 16 * ((4 ^ s) ^ 2 * z))
            _ ≤ u ^ 2 * (u ^ 16 * (u ^ 2 * z)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
                (Nat.mul_le_mul_right z (Nat.pow_le_pow_left h4s_le_u 2)))
            _ = u ^ 20 * z := by ring
            _ ≤ u ^ 20 * (2 ^ R0 * a) :=
              Nat.mul_le_mul_left _ (self_le_two_pow_omega_mul_totient hz_pos hz_om)
            _ = 2 ^ R0 * (u ^ 20 * a) := by ring
            _ ≤ 2 ^ R0 * (2 * n * X) := Nat.mul_le_mul_left _ hu20_a
            _ = (2 ^ (R0 + 1) * n) * X := by rw [pow_succ]; ring
            _ ≤ u * X := Nat.mul_le_mul_right X h2R0_le_u
            _ ≤ u ^ 2 * X := Nat.mul_le_mul_right X (by
              calc u = u ^ 1 := (pow_one u).symm
                _ ≤ u ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num))
        exact Nat.le_of_mul_le_mul_left hstep1 (by positivity)
      have hden_pos : (0 : ℝ) < ((4 : ℝ) ^ s) ^ 2 * (z : ℝ) := by positivity
      rw [_root_.div_mul_div_comm, mul_one, le_div_iff₀ hden_pos]
      exact_mod_cast hnat16
    have hmain_z : (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 /
        (Real.log ((u + 1 : ℕ) : ℝ)) ^ 2 ≤
        ((n : ℝ) * (2 : ℝ) ^ R0 * C_exp ^ 2 * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) *
          ((1 : ℝ) / (z : ℝ)) := by
      have hD_sq : ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 ≤ C_exp ^ 2 * (s : ℝ) ^ 48 := by
        calc ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2
          _ ≤ (C_exp * (s : ℝ) ^ 24) ^ 2 := pow_le_pow_left₀ (by positivity) hD_poly 2
          _ = C_exp ^ 2 * (s : ℝ) ^ 48 := by ring
      have hlog_sq : ((4 : ℝ) ^ s) ^ 2 ≤ (Real.log ((u + 1 : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlog_u1_ge 2
      have hnum : (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 ≤
          ((n : ℝ) * (2 : ℝ) ^ R0 * (X : ℝ) / (z : ℝ)) * (C_exp ^ 2 * (s : ℝ) ^ 48) :=
        mul_le_mul hM2_le hD_sq (by positivity) (by positivity)
      calc (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 / (Real.log ((u + 1 : ℕ) : ℝ)) ^ 2
        _ ≤ (((n : ℝ) * (2 : ℝ) ^ R0 * (X : ℝ) / (z : ℝ)) * (C_exp ^ 2 * (s : ℝ) ^ 48)) /
            (((4 : ℝ) ^ s) ^ 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hlog_sq
        _ = ((n : ℝ) * (2 : ℝ) ^ R0 * C_exp ^ 2 * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) *
            ((1 : ℝ) / (z : ℝ)) := by
          have hz0 : (z : ℝ) ≠ 0 := by positivity
          have h40 : ((4 : ℝ) ^ s) ^ 2 ≠ 0 := by positivity
          field_simp [hz0, h40]
    have hs48_ge1 : (1 : ℝ) ≤ (s : ℝ) ^ 48 := one_le_pow₀ (by exact_mod_cast hs)
    have hu16_le' : (u : ℝ) ^ 16 ≤
        ((X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) := by
      refine hu16_le.trans ?_
      have h1 : (X : ℝ) / ((4 : ℝ) ^ s) ^ 2 ≤ (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc (X : ℝ) = (X : ℝ) * 1 := (mul_one _).symm
          _ ≤ (X : ℝ) * (s : ℝ) ^ 48 := mul_le_mul_of_nonneg_left hs48_ge1 (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hPz_le : ((#Pz : ℕ) : ℝ) ≤ ((#Tg : ℕ) : ℝ) := by exact_mod_cast hcard_Pz_Tg
    calc ((#Pz : ℕ) : ℝ)
      _ ≤ (M2 : ℝ) * ((D : ℝ) / (Nat.totient D : ℝ)) ^ 2 / (Real.log ((u + 1 : ℕ) : ℝ)) ^ 2 +
          (u : ℝ) ^ 16 := hPz_le.trans hsieve2
      _ ≤ ((n : ℝ) * (2 : ℝ) ^ R0 * C_exp ^ 2 * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) *
            ((1 : ℝ) / (z : ℝ)) +
          ((X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) :=
        add_le_add hmain_z hu16_le'
      _ = (C_main * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) := by
        dsimp [C_main]; ring
  have hZ_sub : Z_set ⊆ (Finset.Icc 1 X).filter (fun z : ℕ => #z.primeFactors ≤ R0) :=
    fun z hz => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.1⟩
  have hZ_sum_le : (∑ z ∈ Z_set, (1 : ℝ) / (z : ℝ)) ≤ C_om * (s : ℝ) ^ R0 := by
    have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hZ_sub fun x _ _ => by positivity).trans
      (sum_inv_bounded_omega_le X R0)
    have hprimes_X : (1 + ∑ r ∈ primesLE X, (2 : ℝ) / (r : ℝ)) ≤
        (25 + 24 * Real.log ((384 * R0 : ℕ) : ℝ)) * (s : ℝ) := by
      have h2r : (∑ r ∈ primesLE X, (2 : ℝ) / (r : ℝ)) =
          2 * ∑ r ∈ primesLE (4 ^ ((96 * R0) * 4 ^ s)), (1 : ℝ) / (r : ℝ) := by
        rw [hX_eq_4pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => by ring
      have hp4 := sum_primesLE_four_pow ((96 * R0) * 4 ^ s)
      have hlog_bound : Real.log (((96 * R0) * 4 ^ s : ℕ) : ℝ) ≤
          (s : ℝ) * Real.log ((384 * R0 : ℕ) : ℝ) := by
        have hnat_pow : (96 * R0) * 4 ^ s ≤ (384 * R0) ^ s := by
          have h96_pow : 96 * R0 ≤ (96 * R0) ^ s :=
            calc 96 * R0 = (96 * R0) ^ 1 := (pow_one _).symm
              _ ≤ (96 * R0) ^ s := Nat.pow_le_pow_right (by omega) hs
          calc (96 * R0) * 4 ^ s ≤ (96 * R0) ^ s * 4 ^ s := Nat.mul_le_mul_right _ h96_pow
            _ = (96 * R0 * 4) ^ s := (mul_pow _ _ _).symm
            _ = (384 * R0) ^ s := by ring_nf
        calc Real.log (((96 * R0) * 4 ^ s : ℕ) : ℝ)
          _ ≤ Real.log (((384 * R0) ^ s : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hnat_pow)
          _ = (s : ℝ) * Real.log ((384 * R0 : ℕ) : ℝ) := by
            push_cast; rw [Real.log_pow]
      have hs_ge1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      have hlog384_nonneg : 0 ≤ Real.log ((384 * R0 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 384 * R0 by omega))
      nlinarith
    have hpow_R0 : (1 + ∑ r ∈ primesLE X, (2 : ℝ) / (r : ℝ)) ^ R0 ≤
        ((25 + 24 * Real.log ((384 * R0 : ℕ) : ℝ)) * (s : ℝ)) ^ R0 :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => by positivity))
        hprimes_X R0
    refine h1.trans (hpow_R0.trans_eq ?_)
    dsimp [C_om]
    rw [mul_pow]
  calc ((#B3 : ℕ) : ℝ)
    _ ≤ ∑ z ∈ Z_set, (C_main * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * ((1 : ℝ) / (z : ℝ)) :=
      hB3_sum.trans (Finset.sum_le_sum hz_bound)
    _ = (C_main * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * (∑ z ∈ Z_set, (1 : ℝ) / (z : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C_main * (X : ℝ) * (s : ℝ) ^ 48 / ((4 : ℝ) ^ s) ^ 2) * (C_om * (s : ℝ) ^ R0) :=
      mul_le_mul_of_nonneg_left hZ_sum_le (by dsimp [C_main]; positivity)
    _ = C_main * C_om * (X : ℝ) * (s : ℝ) ^ (48 + R0) / ((4 : ℝ) ^ s) ^ 2 := by
      rw [pow_add]; ring

/- ## Part 5: Asymptotic Comparison and Proof of Main Theorem -/

private lemma exists_larger_unique_totient {n m0 : ℕ} (hn : 0 < n)
    (hm0 : ∀ m, Nat.totient m = n ↔ m = m0) (B : ℕ) :
    ∃ N > B, ∃! m, Nat.totient m = N := by
  have hJ_ex : ∃ J : ℕ, 1 ≤ J ∧ (6 : ℝ) / (2 : ℝ) ^ J ≤ 3 / 256 :=
    ⟨9, by norm_num, by norm_num⟩
  rcases hJ_ex with ⟨J, hJ1, hJ_tail⟩
  set T : ℕ := 2 * 4 ^ J
  have hT1 : 1 ≤ T := by
    have : 2 ≤ T := Nat.le_mul_of_pos_right 2 (Nat.pow_pos (by norm_num : 0 < 4))
    omega
  set R0 : ℕ := 2 * T ^ 2 * n + 2
  have hR0_4 : 4 ≤ R0 := by
    have h1 : 1 ≤ T ^ 2 * n := Nat.mul_pos (Nat.pow_pos hT1) hn
    have h2 : 2 * T ^ 2 * n + 2 = 2 * (T ^ 2 * n) + 2 := by ring
    dsimp [R0]; rw [h2]; omega
  set B0 : ℕ := max m0 (max (n + 1) (B + 2))
  let C_exp : ℝ := Real.exp (24 + 2 * ((288 * R0 : ℕ) : ℝ))
  let C_main : ℝ := (n : ℝ) * (2 : ℝ) ^ R0 * C_exp ^ 2 + 1
  let C_om : ℝ := (25 + 24 * Real.log ((384 * R0 : ℕ) : ℝ)) ^ R0
  let K3 : ℝ := C_main * C_om * ((96 * R0 : ℕ) : ℝ) * Real.log 4
  have hK3_pos : 0 < K3 := by
    have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlog384 : 0 ≤ Real.log ((384 * R0 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 384 * R0 by omega))
    dsimp [K3, C_main, C_om, C_exp]
    positivity
  have htend : Filter.Tendsto (fun s : ℕ => (s : ℝ) ^ (48 + R0) / (4 : ℝ) ^ s)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt (48 + R0) (by norm_num)
  have hev : ∀ᶠ s : ℕ in Filter.atTop,
      (s : ℝ) ^ (48 + R0) / (4 : ℝ) ^ s < (1 / 8 : ℝ) / K3 :=
    htend.eventually (gt_mem_nhds (by positivity))
  rcases Filter.eventually_atTop.mp hev with ⟨S0, hS0⟩
  set U_req : ℕ := max (max (T ^ 2 * n) (2 ^ (R0 + 1) * n))
    (max (8 * n ^ 3) (max B0 ((2 + B0 + 4) * 288 * R0 * 8 + 16 * n * 288 * R0 + 4)))
  have hs_ex : ∃ s : ℕ, 1 ≤ s ∧ S0 ≤ s ∧ U_req ≤ s :=
    ⟨max 1 (max S0 U_req), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  rcases hs_ex with ⟨s, hs1, hs_S0, hs_U⟩
  set u : ℕ := 4 ^ (4 ^ s)
  have hs_le_u : s ≤ u := (self_le_four_pow s).trans (self_le_four_pow (4 ^ s))
  have hU_le_u : U_req ≤ u := hs_U.trans hs_le_u
  have hu_ge4 : 4 ≤ u := by
    have : 4 ≤ U_req := by
      have : 4 ≤ (2 + B0 + 4) * 288 * R0 * 8 + 16 * n * 288 * R0 + 4 := by omega
      exact this.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    omega
  set X : ℕ := u ^ (96 * R0)
  have hX_pos_nat : 0 < X := Nat.pow_pos (by omega : 0 < u)
  have hB0_le_u48 : B0 ≤ u ^ (48 * R0) := by
    have hB0_u : B0 ≤ u :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hU_le_u
    calc B0 ≤ u := hB0_u
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ (48 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
  set Cand := (primesLE X).filter (fun p => u ^ (48 * R0) < p)
  by_contra hnone
  have hall_bad : ∀ p ∈ Cand, ∃ y, ¬ p ∣ y ∧ Nat.totient y = (p - 1) * n := by
    intro p hp
    by_contra hgood
    rcases Finset.mem_filter.mp hp with ⟨hpLE, hp_gt⟩
    have hpp : p.Prime := (mem_primesLE.mp hpLE).1
    have hp_B0 : B0 < p := lt_of_le_of_lt hB0_le_u48 hp_gt
    rcases good_prime_gives_unique hn hm0 hpp hp_B0 hgood with ⟨hgtB, huniq⟩
    exact hnone ⟨(p - 1) * n, hgtB, huniq⟩
  set B1 := (primesLE X).filter (fun p => ∃ k > T, k ^ 2 ∣ p - 1)
  set B2 := (primesLE X).filter (fun p =>
    ∃ q : ℕ, u ^ 20 ≤ q ∧ q ≤ X * n + 1 ∧ q * (q - 1) ∣ (p - 1) * n)
  set Z_set := (Finset.Icc 1 X).filter (fun z : ℕ =>
    #z.primeFactors ≤ R0 ∧ Nat.totient z ≠ n ∧ u ^ 20 * Nat.totient z ≤ 2 * n * X)
  set B3 := ((primesLE X).filter (fun p => u < p)).filter (fun p =>
    ∃ z ∈ Z_set, ∃ q : ℕ, q.Prime ∧ u ^ 20 ≤ q ∧ (p - 1) * n = (q - 1) * Nat.totient z)
  have hCand_sub : Cand ⊆ B1 ∪ (B2 ∪ B3) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpLE, hp_lo⟩
    rcases mem_primesLE.mp hpLE with ⟨hpp, hpX⟩
    rcases hall_bad p hp with ⟨y, hnot_py, htot_y⟩
    by_cases h1 : ∃ k > T, k ^ 2 ∣ p - 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpLE, h1⟩)
    · have hno_sq : ∀ k > T, ¬ k ^ 2 ∣ p - 1 := fun k hk hkd => h1 ⟨k, hk, hkd⟩
      have hu_dicho : max (T ^ 2 * n) (2 ^ (2 * T ^ 2 * n + 3) * n) ≤ u :=
        (le_max_left _ _).trans hU_le_u
      rcases bad_prime_dichotomy hn hT1 hu_dicho hpp hp_lo hpX hno_sq hnot_py htot_y with h2 | h3
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hpLE, h2⟩))
      · have hp_gt_u : u < p := by
          calc u = u ^ 1 := (pow_one u).symm
            _ < u ^ (48 * R0) := Nat.pow_lt_pow_right (by omega) (by omega)
            _ < p := hp_lo
        exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpLE, hp_gt_u⟩, h3⟩))
  have hCand_le_sum : ((#Cand : ℕ) : ℝ) ≤ ((#B1 : ℕ) : ℝ) + ((#B2 : ℕ) : ℝ) + ((#B3 : ℕ) : ℝ) := by
    have hnat : #Cand ≤ #B1 + #B2 + #B3 := by
      calc #Cand ≤ #(B1 ∪ (B2 ∪ B3)) := Finset.card_le_card hCand_sub
        _ ≤ #B1 + #(B2 ∪ B3) := Finset.card_union_le _ _
        _ ≤ #B1 + (#B2 + #B3) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = #B1 + #B2 + #B3 := by omega
    exact_mod_cast hnat
  set LX : ℝ := Real.log (X : ℝ)
  have hX_eq_4pow : X = 4 ^ ((96 * R0) * 4 ^ s) := by
    dsimp [X, u]; rw [← pow_mul, mul_comm (4 ^ s) (96 * R0)]
  have hLX_eq : LX = ((96 * R0 : ℕ) : ℝ) * (4 : ℝ) ^ s * Real.log 4 := by
    dsimp [LX]
    rw [hX_eq_4pow]
    push_cast
    rw [Real.log_pow]
    push_cast; ring
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLX_pos : 0 < LX := by rw [hLX_eq]; positivity
  have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX_pos_nat
  set QXL : ℝ := (X : ℝ) / LX
  have hQXL_pos : 0 < QXL := div_pos hX_pos hLX_pos
  have hlog4_le3 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hLX_le_u : LX ≤ ((288 * R0 : ℕ) : ℝ) * (u : ℝ) := by
    have h4s_u : (4 : ℝ) ^ s ≤ (u : ℝ) :=
      (Nat.cast_pow 4 s).symm.trans_le (Nat.cast_le.mpr (self_le_four_pow (4 ^ s)))
    have h96_nonneg : (0 : ℝ) ≤ ((96 * R0 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hu_nonneg : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg _
    calc LX = ((96 * R0 : ℕ) : ℝ) * ((4 : ℝ) ^ s * Real.log 4) := by rw [hLX_eq]; ring
      _ ≤ ((96 * R0 : ℕ) : ℝ) * ((u : ℝ) * 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h4s_u hlog4_le3 hlog4_pos.le hu_nonneg) h96_nonneg
      _ = ((288 * R0 : ℕ) : ℝ) * (u : ℝ) := by push_cast; ring
  have hCand_ge : (1 / 2 : ℝ) * QXL - (2 + (u : ℝ) ^ (48 * R0)) ≤ ((#Cand : ℕ) : ℝ) := by
    have hsplit : #(primesLE X) = #(primesLE X |>.filter (fun p => p ≤ u ^ (48 * R0))) + #Cand := by
      have h := (Finset.card_filter_add_card_filter_not
        (s := primesLE X) (fun p => p ≤ u ^ (48 * R0))).symm
      have heq_c : (primesLE X).filter (fun p => ¬ p ≤ u ^ (48 * R0)) = Cand := by
        ext p; simp only [Cand, Finset.mem_filter, not_le]
      rwa [heq_c] at h
    have hsmall : (#(primesLE X |>.filter (fun p => p ≤ u ^ (48 * R0))) : ℝ) ≤
        (u : ℝ) ^ (48 * R0) := by
      have hsub : (primesLE X).filter (fun p => p ≤ u ^ (48 * R0)) ⊆
          Finset.Icc 1 (u ^ (48 * R0)) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpLE, hple⟩
        exact Finset.mem_Icc.mpr ⟨(mem_primesLE.mp hpLE).1.one_le, hple⟩
      have hc : #((primesLE X).filter (fun p => p ≤ u ^ (48 * R0))) ≤ u ^ (48 * R0) :=
        (Finset.card_le_card hsub).trans_eq (by simp [Nat.card_Icc])
      exact (Nat.cast_le.mpr hc).trans_eq (Nat.cast_pow u (48 * R0))
    have hpi := Chebyshev.pi_ge X
    rw [← card_primesLE X] at hpi
    have hX_ge2 : (2 : ℝ) ≤ (X : ℝ) := by
      have h2X : 2 ≤ X := by
        calc 2 ≤ u := by omega
          _ = u ^ 1 := (pow_one u).symm
          _ ≤ u ^ (96 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast h2X
    have hlogX1_le : Real.log ((X : ℝ) + 1) ≤ 2 * LX := by
      have h1 : (X : ℝ) + 1 ≤ (X : ℝ) ^ 2 := by nlinarith only [hX_ge2]
      calc Real.log ((X : ℝ) + 1) ≤ Real.log ((X : ℝ) ^ 2) :=
            Real.log_le_log (by linarith only [hX_pos]) h1
        _ = 2 * LX := by rw [Real.log_pow]; dsimp [LX]
    have hpi' : (1 / 2 : ℝ) * QXL - 2 ≤ ((#(primesLE X) : ℕ) : ℝ) := by
      calc (1 / 2 : ℝ) * QXL - 2
        _ ≤ Real.log 2 * QXL - Real.log ((X : ℝ) + 1) / LX :=
          sub_le_sub (mul_le_mul_of_nonneg_right one_half_le_log_two hQXL_pos.le)
            ((div_le_iff₀ hLX_pos).mpr hlogX1_le)
        _ = ((X : ℝ) * Real.log 2 - Real.log ((X : ℝ) + 1)) / LX := by
          dsimp [QXL]; field_simp [hLX_pos.ne']
        _ ≤ ((#(primesLE X) : ℕ) : ℝ) := hpi
    have hcast_split : ((#(primesLE X) : ℕ) : ℝ) =
        ((#(primesLE X |>.filter (fun p => p ≤ u ^ (48 * R0))) : ℕ) : ℝ) + ((#Cand : ℕ) : ℝ) := by
      exact_mod_cast hsplit
    linarith only [hpi', hsmall, hcast_split]
  have hB1_le := card_bad1_le hJ1 hJ_tail (by omega : 1 ≤ R0) (by omega : 2 ≤ u)
  have hB2_le := card_bad2_le hn (by omega : 2 ≤ u) (R0 := R0)
  have hu_for_B3 : max (8 * n ^ 3) (2 ^ (R0 + 1) * n) ≤ u := by
    refine max_le ?_ ?_
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hU_le_u
    · exact ((le_max_right _ _).trans (le_max_left _ _)).trans hU_le_u
  have hB3_le := card_bad3_le hn hR0_4 hs1 hu_for_B3
  have hB3_lt : ((#B3 : ℕ) : ℝ) < (1 / 8 : ℝ) * QXL := by
    have hs_small : (s : ℝ) ^ (48 + R0) / (4 : ℝ) ^ s < (1 / 8 : ℝ) / K3 := hS0 s hs_S0
    have hrew : C_main * C_om * (X : ℝ) * (s : ℝ) ^ (48 + R0) / ((4 : ℝ) ^ s) ^ 2 =
        QXL * K3 * ((s : ℝ) ^ (48 + R0) / (4 : ℝ) ^ s) := by
      dsimp [QXL, K3]
      rw [hLX_eq]
      have h40 : (4 : ℝ) ^ s ≠ 0 := by positivity
      have h96 : ((96 * R0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 96 * R0 ≠ 0 by omega)
      field_simp [h40, h96, hlog4_pos.ne']
    calc ((#B3 : ℕ) : ℝ)
      _ ≤ QXL * K3 * ((s : ℝ) ^ (48 + R0) / (4 : ℝ) ^ s) := hB3_le.trans_eq hrew
      _ < QXL * K3 * ((1 / 8 : ℝ) / K3) :=
        mul_lt_mul_of_pos_left hs_small (mul_pos hQXL_pos hK3_pos)
      _ = ((1 / 8 : ℝ) * QXL) * (K3 / K3) := by ring
      _ = (1 / 8 : ℝ) * QXL := by rw [div_self hK3_pos.ne', mul_one]
  have h8_eq : (1 / 8 : ℝ) * QXL = (X : ℝ) / (8 * LX) := by
    dsimp [QXL]
    calc (1 / 8 : ℝ) * ((X : ℝ) / LX) = (X : ℝ) / 8 / LX := by ring
      _ = (X : ℝ) / (8 * LX) := div_div (X : ℝ) 8 LX
  have herr1_lt : 2 + (u : ℝ) ^ (48 * R0) + 3 * (u : ℝ) ^ (88 * R0) <
      (1 / 8 : ℝ) * QXL := by
    have hu_big : (2 + B0 + 4) * 288 * R0 * 8 < u := by
      have : (2 + B0 + 4) * 288 * R0 * 8 <
          (2 + B0 + 4) * 288 * R0 * 8 + 16 * n * 288 * R0 + 4 := by omega
      exact lt_of_lt_of_le this
        (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hU_le_u)
    have hu48_le_u88 : (u : ℝ) ^ (48 * R0) ≤ (u : ℝ) ^ (88 * R0) := by
      rw [← Nat.cast_pow, ← Nat.cast_pow]
      exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by omega) (by omega))
    have h1_le_u88 : (1 : ℝ) ≤ (u : ℝ) ^ (88 * R0) :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ u by omega))
    have hlhs_le : 2 + (u : ℝ) ^ (48 * R0) + 3 * (u : ℝ) ^ (88 * R0) ≤
        6 * (u : ℝ) ^ (88 * R0) := by linarith only [hu48_le_u88, h1_le_u88]
    have hnat_lt : 6 * u ^ (88 * R0) * (8 * ((288 * R0) * u)) < X := by
      have h6_lt_u : 6 * 8 * (288 * R0) < u := by
        have h6B : 6 ≤ 2 + B0 + 4 := by omega
        calc 6 * 8 * (288 * R0) = 6 * (288 * R0 * 8) := by ring
          _ ≤ (2 + B0 + 4) * (288 * R0 * 8) := Nat.mul_le_mul_right _ h6B
          _ = (2 + B0 + 4) * 288 * R0 * 8 := by ring
          _ < u := hu_big
      calc 6 * u ^ (88 * R0) * (8 * ((288 * R0) * u))
        _ = (6 * 8 * (288 * R0)) * u ^ (88 * R0 + 1) := by rw [pow_succ]; ring
        _ < u * u ^ (88 * R0 + 1) :=
          Nat.mul_lt_mul_of_pos_right h6_lt_u (Nat.pow_pos (by omega : 0 < u))
        _ = u ^ (88 * R0 + 2) := (_root_.pow_succ' u (88 * R0 + 1)).symm
        _ ≤ u ^ (96 * R0) := Nat.pow_le_pow_right (by omega) (by omega)
    have hreal_lt : (6 * (u : ℝ) ^ (88 * R0)) * (8 * (((288 * R0 : ℕ) : ℝ) * (u : ℝ))) < (X : ℝ) := by
      have hc : (((6 * u ^ (88 * R0) * (8 * ((288 * R0) * u))) : ℕ) : ℝ) < (X : ℝ) :=
        Nat.cast_lt.mpr hnat_lt
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    rw [h8_eq, lt_div_iff₀ (mul_pos (by norm_num) hLX_pos)]
    calc (2 + (u : ℝ) ^ (48 * R0) + 3 * (u : ℝ) ^ (88 * R0)) * (8 * LX)
      _ ≤ (6 * (u : ℝ) ^ (88 * R0)) * (8 * (((288 * R0 : ℕ) : ℝ) * (u : ℝ))) :=
        mul_le_mul hlhs_le (mul_le_mul_of_nonneg_left hLX_le_u (by norm_num))
          (mul_nonneg (by norm_num) hLX_pos.le)
          (mul_nonneg (by norm_num) (by linarith only [h1_le_u88]))
      _ < (X : ℝ) := hreal_lt
  have hB2_lt : ((#B2 : ℕ) : ℝ) < (1 / 8 : ℝ) * QXL := by
    have hu_big2 : 16 * n * (288 * R0) < u := by
      have : 16 * n * (288 * R0) <
          (2 + B0 + 4) * 288 * R0 * 8 + 16 * n * 288 * R0 + 4 := by
        calc 16 * n * (288 * R0) = 16 * n * 288 * R0 := by ring
          _ < (2 + B0 + 4) * 288 * R0 * 8 + 16 * n * 288 * R0 + 4 := by omega
      exact lt_of_lt_of_le this
        (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hU_le_u)
    have hnat_u20 : 16 * n * ((288 * R0) * u) < u ^ 20 := by
      calc 16 * n * ((288 * R0) * u) = (16 * n * (288 * R0)) * u := by ring
        _ < u * u := Nat.mul_lt_mul_of_pos_right hu_big2 (by omega)
        _ = u ^ 2 := (sq u).symm
        _ ≤ u ^ 20 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hreal_u20 : 16 * (n : ℝ) * (((288 * R0 : ℕ) : ℝ) * (u : ℝ)) < (u : ℝ) ^ 20 := by
      have hc : (((16 * n * ((288 * R0) * u)) : ℕ) : ℝ) < (((u ^ 20) : ℕ) : ℝ) :=
        Nat.cast_lt.mpr hnat_u20
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    have h16LX : 16 * (n : ℝ) * LX < (u : ℝ) ^ 20 := by
      calc 16 * (n : ℝ) * LX ≤ 16 * (n : ℝ) * (((288 * R0 : ℕ) : ℝ) * (u : ℝ)) :=
            mul_le_mul_of_nonneg_left hLX_le_u (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        _ < (u : ℝ) ^ 20 := hreal_u20
    have h2n_lt : 2 * (n : ℝ) * (X : ℝ) / (u : ℝ) ^ 20 < (1 / 8 : ℝ) * QXL := by
      have hu20_pos : (0 : ℝ) < (u : ℝ) ^ 20 :=
        pow_pos (Nat.cast_pos.mpr (by omega : 0 < u)) 20
      rw [h8_eq, div_lt_div_iff₀ hu20_pos (mul_pos (by norm_num) hLX_pos)]
      calc (2 * (n : ℝ) * (X : ℝ)) * (8 * LX)
        _ = (X : ℝ) * (16 * (n : ℝ) * LX) := by ring
        _ < (X : ℝ) * (u : ℝ) ^ 20 := mul_lt_mul_of_pos_left h16LX hX_pos
    exact lt_of_le_of_lt hB2_le h2n_lt
  have hB1_le' : ((#B1 : ℕ) : ℝ) ≤ (3 / 32 : ℝ) * QXL + 3 * (u : ℝ) ^ (88 * R0) := by
    calc ((#B1 : ℕ) : ℝ)
      _ ≤ (3 / 32 : ℝ) * (X : ℝ) / Real.log (X : ℝ) + 3 * (u : ℝ) ^ (88 * R0) := hB1_le
      _ = (3 / 32 : ℝ) * QXL + 3 * (u : ℝ) ^ (88 * R0) := by dsimp [QXL, LX]; ring
  linarith only [hCand_ge, hCand_le_sum, hB1_le', hB2_lt, hB3_lt, herr1_lt, hQXL_pos]

end Part4And5
end Erdos694InfUnique

theorem OMA.solution : type_of% @Erdos694.erdos_694.variants.inf_unique := by
  intro h
  rcases h with ⟨n, hn, m0, hm0_tot, hm0_uniq⟩
  have hm0_iff : ∀ m, Nat.totient m = n ↔ m = m0 :=
    fun m => ⟨fun hm => hm0_uniq m hm, fun hm => hm ▸ hm0_tot⟩
  rw [Set.infinite_iff_exists_gt]
  intro B
  rcases Erdos694InfUnique.exists_larger_unique_totient hn hm0_iff B with ⟨N, hNB, hN_uniq⟩
  exact ⟨N, hN_uniq, hNB⟩

