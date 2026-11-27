import FormalConjectures.ErdosProblems.«517»

/-! Reduction of the Fejér-gap preimage theorem after M. Biernacki, Sur les équations algébriques contenant des paramètres arbitraires (1928), pp. 20–23. The finite root-propagation bound is independent of all tail coefficients. Its radius product is bounded uniformly by the reciprocal gap sum. The second hypothesis is a multiplicity-sensitive zero-count limit theorem on disks. -/

/-! Shifted polynomial sections converge uniformly on closed disks, and their limit is entire. -/
open Polynomial Finset Filter
noncomputable section
namespace OMA.Section517

theorem convergence (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ) (v : ℂ)
    (hf : ∀ z, HasSum (fun j => a j*z^(n j)) (f z)) :
    (∀ R : ℝ, TendstoUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z) (fun z => f z-v)
      atTop (Metric.closedBall 0 R)) ∧ AnalyticOnNhd ℂ (fun z => f z-v) Set.univ := by
  have uniform (R : ℝ) : TendstoUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z)
      (fun z => f z-v) atTop (Metric.closedBall 0 R) := by
    let T := max R 0
    have hT : 0 ≤ T := le_max_right _ _
    have hs := (hf (T:ℂ)).summable.norm
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT] at hs
    have hu := tendstoUniformlyOn_tsum_nat (f := fun j (z:ℂ) => a j*z^(n j))
      (s := Metric.closedBall 0 R) hs (by
        intro j z hz
        have hR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hz
        rw [norm_mul,norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hR.trans (le_max_left _ _)) _) (norm_nonneg _))
    have eqf : (fun z => ∑' j, a j*z^(n j)) = f := funext fun z => (hf z).tsum_eq
    rw [eqf] at hu
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε he
    filter_upwards [hu ε he] with K hK
    intro z hz
    simpa [eval_finsetSum,dist_eq_norm,sub_sub_sub_cancel_right] using hK z hz
  refine ⟨uniform, ?_⟩
  have hl : TendstoLocallyUniformlyOn (fun j z => (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).eval z)
      (fun z => f z-v) atTop Set.univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro C _ hc
    obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hc.isBounded
    exact (uniform R).mono hR
  exact (hl.differentiableOn (Eventually.of_forall fun j =>
    (((∑ j ∈ Finset.range j, Polynomial.monomial (n j) (a j)) - Polynomial.C v)).differentiable.differentiableOn) isOpen_univ).analyticOnNhd isOpen_univ

end OMA.Section517
end

/-! A degree-uniform bound on the factors in Biernacki's gap-polynomial
theorem. The reciprocal Fejér sum controls even nonconsecutive sections. -/
namespace OMA.Product517
open Finset Real

theorem bound {n : ℕ → ℕ} (gaps : HasFejerGaps n) (p : ℕ) (S : Finset ℕ)
    (tail : ∀ j ∈ S, p < n j) :
    ∏ j ∈ S, ((n j:ℝ)/((n j:ℝ)-p)) ≤
      exp (((p:ℝ)*((p:ℝ)+1))*(∑' j, (n j:ℝ)⁻¹)) := by
  have cmp (j : ℕ) (hj : j∈S) : ((n j:ℝ)/((n j:ℝ)-p)) ≤
      exp (((p:ℝ)*((p:ℝ)+1))*(n j:ℝ)⁻¹) := by
    have high : (p:ℝ)+1 ≤ n j := by exact_mod_cast tail j hj
    have dp : 0 < (n j:ℝ)-p := by linarith
    have np : (0:ℝ)<n j := by linarith [Nat.cast_nonneg (α:=ℝ) p]
    have less : (p:ℝ)/((n j:ℝ)-p) ≤ ((p:ℝ)*((p:ℝ)+1))*(n j:ℝ)⁻¹ := by
      rw [← div_eq_mul_inv,div_le_div_iff₀ dp np]
      have hh : (n j:ℝ) ≤ ((p:ℝ)+1)*((n j:ℝ)-p) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) p) (sub_nonneg.mpr high)]
      nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) p)]
    have eqn : (n j:ℝ)/((n j:ℝ)-p) = (p:ℝ)/((n j:ℝ)-p)+1 := by field_simp; ring
    linarith [eqn,add_one_le_exp (((p:ℝ)*((p:ℝ)+1))*(n j:ℝ)⁻¹)]
  calc
    _ ≤ ∏ j ∈ S, exp (((p:ℝ)*((p:ℝ)+1))*(n j:ℝ)⁻¹) := by
      apply prod_le_prod _ cmp
      intro i hi
      exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (tail i hi).le))
    _ = exp (((p:ℝ)*((p:ℝ)+1))*∑ j ∈ S, (n j:ℝ)⁻¹) := by rw [mul_sum,exp_sum]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (gaps.2.sum_le_tsum _ (fun j _ => by positivity)) (by positivity)

end OMA.Product517

/-! Reduction to a coefficient-independent finite root bound and a
multiplicity form of the analytic limit theorem; neither involves the
original infinite lacunary-series assertion. -/
namespace OMA.R_Erdos517_erdos_517_variants_fejer_R1
open Finset Filter Polynomial Real
open OMA.Section517
open scoped Classical

def H1 : Prop := ∀ (P : ℂ[X]) (n : ℕ → ℕ) (a : ℕ → ℂ) (s K : ℕ)
    (R : ℝ), StrictMono n → s < K → P.natDegree=n s → 0≤R →
    (∀ z ∈ P.roots, ‖z‖≤R) →
    n s ≤ ((P + ∑ j ∈ Ico (s+1) K, monomial (n j) (a j)).roots.filter
      (fun z => ‖z‖≤R*∏ j ∈ Ico (s+1) K, (n j:ℝ)/((n j:ℝ)-n s))).card

def H2 : Prop := ∀ (P : ℕ → ℂ[X]) (f : ℂ → ℂ), AnalyticOnNhd ℂ f Set.univ →
    (∀ R : ℝ, TendstoUniformlyOn (fun j z => (P j).eval z) f atTop (Metric.closedBall 0 R)) →
    (∀ m : ℕ, ∃ R : ℝ, ∀ᶠ j : ℕ in atTop, m ≤ ((P j).roots.filter (fun z => ‖z‖≤R)).card) →
    {z | f z=0}.Infinite

private theorem degree {n : ℕ → ℕ} (h : StrictMono n) (a : ℕ → ℂ) (v : ℂ) (s : ℕ)
    (hp : 0<n s) (ha : a s≠0) : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).natDegree=n s := by
  classical
  have up : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).natDegree ≤ n s := by
    apply (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (h.monotone (by have := mem_range.mp hj; omega))
  apply le_antisymm up
  apply le_natDegree_of_ne_zero
  have eqn : (((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)).coeff (n s) = a s := by
    rw [coeff_sub,finsetSum_coeff,coeff_C_of_ne_zero hp.ne',sub_zero,sum_eq_single s]
    · simp
    · intro b _ ne; exact coeff_monomial_of_ne _ (fun e => ne (h.injective e.symm))
    · simp
  rwa [eqn]

theorem main : H1 → H2 → type_of% @Erdos517.erdos_517.variants.fejer := by
  intro finite transfer
  classical
  intro f n gaps a ha hf v
  obtain ⟨uniform,analytic⟩ := convergence n a f v hf
  have result := transfer (fun K : ℕ => ((∑ j ∈ Finset.range K, Polynomial.monomial (n j) (a j)) - Polynomial.C v)) (fun z => f z-v) analytic uniform
  simp only [sub_eq_zero] at result
  apply result
  intro m
  let s := m+1
  let p := n s
  have ps : s≤p := gaps.1.id_le s
  have pp : 0<p := by dsimp [s] at ps; omega
  let P := ((∑ j ∈ Finset.range (s+1), Polynomial.monomial (n j) (a j)) - Polynomial.C v)
  have deg : P.natDegree=p := degree gaps.1 a v s pp (ha s)
  let R := ∑ z ∈ P.roots.toFinset, ‖z‖
  have r0 : 0≤R := sum_nonneg fun z _ => norm_nonneg z
  have rad (z) (hz : z ∈ P.roots) : ‖z‖≤R := single_le_sum (f:=fun x : ℂ => ‖x‖)
    (fun _ _ => norm_nonneg _) (Multiset.mem_toFinset.mpr hz)
  refine ⟨R*exp (((p:ℝ)*((p:ℝ)+1))*(∑' j,(n j:ℝ)⁻¹)),?_⟩
  filter_upwards [eventually_gt_atTop s] with K hK
  have cut := finite P n a s K R gaps.1 hK deg r0 rad
  have comb : P + ∑ j ∈ Ico (s+1) K, monomial (n j) (a j) = ((∑ j ∈ Finset.range K, Polynomial.monomial (n j) (a j)) - Polynomial.C v) := by
    unfold P
    rw [← Finset.sum_range_add_sum_Ico (fun j => monomial (n j) (a j)) hK]
    abel
  rw [comb] at cut
  have hb := OMA.Product517.bound gaps p (Ico (s+1) K)
    (fun j hj => gaps.1 (by have := (mem_Ico.mp hj).1; omega))
  have hle := mul_le_mul_of_nonneg_left hb r0
  have mm : m≤n s := (Nat.le_succ m).trans ps
  exact (mm.trans cut).trans (Multiset.card_le_card (Multiset.monotone_filter_right _ (fun z hz => hz.trans hle)))

end OMA.R_Erdos517_erdos_517_variants_fejer_R1
