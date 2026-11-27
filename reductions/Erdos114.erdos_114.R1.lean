import FormalConjectures.ErdosProblems.«114»

/-! # Reduction of Erdős 114 to two or more distinct unit critical values

Eremenko and Hayman prove existence of an extremal monic polynomial in each degree
(Lemma 4) and existence of one with every critical value on the unit circle (Lemma 5)
in *On the length of lemniscates*, Michigan Math. J. 46 (1999), 409–415,
https://arxiv.org/html/0805.2295v2 . These two results imply the domination in H1.

The fiber multiplicity count below proves that a single common critical value gives
a translated pure power plus a constant. When that value has modulus one, an
explicit Euclidean isometry identifies its lemniscate with the model in the target.
H2 therefore concerns only configurations with at least two distinct critical values.

Wang and Peng treated the full translated pure-power family in *The arc length of
the lemniscate |wⁿ+c|=1*, Rocky Mountain J. Math. 36 (2006), 337–347,
https://doi.org/10.1216/rmjm/1181069502 . Tao proved the inequality for all sufficiently
large degrees, https://arxiv.org/abs/2512.12455 . Teng Zhang's preprint of 9 November 2026
claims the all-degree inequality and characterizes its equality cases (Theorem 1.3,
https://arxiv.org/html/2611.12830v1 ). This reduction leaves H1 and H2 as separate
formal obligations and does not use Zhang's claimed theorem. -/
open Polynomial MeasureTheory
open scoped ENNReal

namespace OMA.R_Erdos114_erdos_114_R1

/-- In each positive degree there is a unit-critical-value majorant of any monic input. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : ℂ[X], p.Monic → p.natDegree = n →
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = n ∧
      Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength q ∧
      ∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1

/-- The model bounds every monic polynomial with all critical values on the unit circle
and at least two distinct critical values. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ q : ℂ[X], q.Monic → q.natDegree = n →
    (∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1) →
    (∃ x y : ℂ, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y) →
    Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1)

section Algebra
variable {F : Type*} [Field F] [CharZero F]

/-- A root of multiplicity m contributes one distinct root and m−1 derivative roots. -/
theorem fiber_roots [DecidableEq F] (q : F[X]) :
    q.roots = q.roots.dedup + q.derivative.roots.filter (· ∈ q.roots) := by
  classical
  apply Multiset.ext.mpr
  intro x
  rw [Multiset.count_add, Multiset.count_dedup, Multiset.count_filter]
  split_ifs with hx
  · have hm := Multiset.count_pos.mpr hx
    rw [count_roots] at hm
    have hr := (Polynomial.mem_roots'.mp hx).2
    rw [count_roots, count_roots, derivative_rootMultiplicity_of_root hr]
    omega
  · simpa using Multiset.count_eq_zero.mpr hx

variable [IsAlgClosed F]

/-- The number of distinct points of a fiber plus the total critical multiplicity
over the fiber equals the polynomial degree. -/
theorem fiber_count [DecidableEq F] (p : F[X]) (v : F) :
    (p - C v).roots.dedup.card +
      (p.derivative.roots.filter (· ∈ (p - C v).roots)).card = p.natDegree := by
  have h := congrArg Multiset.card (fiber_roots (p - C v))
  simpa [Multiset.card_add, IsAlgClosed.card_roots_eq_natDegree, natDegree_sub_C] using h.symm

/-- A nonconstant monic polynomial with every critical value equal to v
is a translated pure power plus v. -/
theorem eq_translated_power_of_one_critical_value (p : F[X]) (hp : p.Monic)
    (hn : 0 < p.natDegree) (v : F)
    (hv : ∀ x : F, p.derivative.IsRoot x → p.eval x = v) :
    ∃ c : F, p = (X - C c) ^ p.natDegree + C v := by
  classical
  let q := p - C v
  have hdq : q.natDegree = p.natDegree := natDegree_sub_C
  have hq : q.Monic := hp.sub_of_left <| degree_C_le.trans_lt <| by
    rw [degree_eq_natDegree hp.ne_zero]
    exact_mod_cast hn
  have hf : p.derivative.roots.filter (· ∈ q.roots) = p.derivative.roots := by
    apply Multiset.filter_eq_self.mpr
    intro x hx
    apply (mem_roots hq.ne_zero).mpr
    simpa [q, IsRoot] using sub_eq_zero.mpr (hv x (mem_roots'.mp hx).2)
  have hc := fiber_count p v
  change q.roots.dedup.card + (p.derivative.roots.filter (· ∈ q.roots)).card = _ at hc
  rw [hf, IsAlgClosed.card_roots_eq_natDegree, natDegree_derivative] at hc
  obtain ⟨c, hsingle⟩ := Multiset.card_eq_one.mp (show q.roots.dedup.card = 1 by omega)
  have hr : q.roots = Multiset.replicate q.roots.card c := by
    apply Multiset.eq_replicate_card.mpr
    intro x hx
    have : x ∈ q.roots.dedup := Multiset.mem_dedup.mpr hx
    simpa [hsingle] using this
  rw [IsAlgClosed.card_roots_eq_natDegree, hdq] at hr
  have hfac := (IsAlgClosed.splits q).eq_prod_roots_of_monic hq
  rw [hr] at hfac
  refine ⟨c, ?_⟩
  have : p - C v = (X - C c) ^ p.natDegree := by simpa [q] using hfac
  exact sub_eq_iff_eq_add.mp this

end Algebra

/-- Translation and a phase of norm one preserve the exact lemniscate length in every degree. -/
theorem model_length (n : ℕ) (hn : 0 < n) (c v : ℂ) (hv : ‖v‖ = 1) :
    Erdos114.lemniscateLength ((X - C c) ^ n + C v) =
      Erdos114.lemniscateLength (X ^ n - 1) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-v) hn
  have hnu : ‖u‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg u) hn.ne').mp <| by
    rw [← norm_pow, hu, norm_neg, hv]
  have hune : u ≠ 0 := fun h => by simp [h] at hnu
  let e : ℂ ≃ᵢ ℂ :=
    { toFun := fun z => (z - c) / u
      invFun := fun z => z * u + c
      left_inv := fun z => by field_simp; ring
      right_inv := fun z => by field_simp; ring
      isometry_toFun := Isometry.of_dist_eq fun z w => by
        rw [dist_eq_norm, dist_eq_norm, ← sub_div, norm_div, hnu, div_one]
        congr 1
        ring }
  have hset : Erdos114.lemniscate ((X - C c) ^ n + C v) =
      e ⁻¹' Erdos114.lemniscate (X ^ n - 1) := by
    ext z
    change ‖((X - C c) ^ n + C v).eval z‖ = 1 ↔ ‖(X ^ n - 1 : ℂ[X]).eval ((z - c) / u)‖ = 1
    simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C, eval_one, div_pow]
    have heq : (z - c) ^ n + v = (((z - c) ^ n / u ^ n) - 1) * u ^ n := by
      rw [sub_mul, div_mul_cancel₀ _ (pow_ne_zero _ hune), one_mul, hu, sub_neg_eq_add]
    rw [heq, norm_mul, norm_pow, hnu, one_pow, mul_one]
  rw [Erdos114.lemniscateLength, Erdos114.lemniscateLength, hset,
    IsometryEquiv.hausdorffMeasure_preimage]

/-- The model bound is an equality for any monic polynomial with one common unit critical value. -/
theorem length_eq_of_one_unit_critical_value (p : ℂ[X]) (hp : p.Monic) (hn : 0 < p.natDegree)
    (v : ℂ) (hunit : ‖v‖ = 1) (hv : ∀ x : ℂ, p.derivative.IsRoot x → p.eval x = v) :
    Erdos114.lemniscateLength p = Erdos114.lemniscateLength (X ^ p.natDegree - 1) := by
  obtain ⟨c, hc⟩ := eq_translated_power_of_one_critical_value p hp hn v hv
  calc Erdos114.lemniscateLength p = _ := congrArg Erdos114.lemniscateLength hc
       _ = _ := model_length _ hn c v hunit

theorem main : H1 → H2 → type_of% @Erdos114.erdos_114 := by
  intro hEH hmulti n hn p hp hdeg
  obtain ⟨q, hq, hdq, hL, hcrit⟩ := hEH n hn p hp hdeg
  apply hL.trans
  by_cases hm : ∃ x y, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y
  · exact hmulti n hn q hq hdq hcrit hm
  have hv : ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ x, q.derivative.IsRoot x → q.eval x = v := by
    by_cases he : ∃ y, q.derivative.IsRoot y
    · obtain ⟨y, hy⟩ := he
      exact ⟨q.eval y, hcrit y hy, fun x hx => by
        by_contra hne
        exact hm ⟨x, y, hx, hy, hne⟩⟩
    · exact ⟨1, norm_one, fun x hx => (he ⟨x, hx⟩).elim⟩
  obtain ⟨v, huv, hv⟩ := hv
  simpa [hdq] using (length_eq_of_one_unit_critical_value q hq (hdq ▸ hn) v huv hv).le

end OMA.R_Erdos114_erdos_114_R1
