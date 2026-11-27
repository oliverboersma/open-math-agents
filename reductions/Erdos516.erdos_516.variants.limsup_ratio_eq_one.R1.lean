import FormalConjectures.ErdosProblems.«516»

/-! # Finite radial windows for Kővári's gap theorem

The first step asks for a small-values estimate for finite lacunary polynomials,
uniform in their degrees and coefficients when the disk bounds and one nonzero
coefficient are fixed. The second step concerns growth of the maximum modulus.
Uniform convergence on disks then gives the result without any order assumption. -/

namespace OMA.SectionApprox516
open Finset Filter Polynomial
open scoped Topology

theorem uniform {n : ℕ → ℕ} {a : ℕ → ℂ} {f : ℂ → ℂ} (h : (∀ z : ℂ, HasSum (fun k => a k*z^(n k)) (f z))) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun K z => ∑ j ∈ range K, a j*z^(n j)) f atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hs := (h (R:ℂ)).summable.norm
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR] at hs
  have hu := tendstoUniformlyOn_tsum_nat (f := fun k (z : ℂ) => a k*z^(n k))
    (s := {z : ℂ | ‖z‖ ≤ R}) hs (by
      intro k z hz; rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _))
  have eqf : (fun z => ∑' k, a k*z^(n k)) = f := funext fun z => (h z).tsum_eq
  rwa [eqf] at hu

end OMA.SectionApprox516

/- Reduce the entire-function problem to a degree-uniform estimate on finite
lacunary polynomials in a bounded radial window. Without uniformity in degree
the polynomial assertion would follow just by letting the top monomial win. -/
namespace OMA.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1
open Finset Filter Real
open scoped Topology
open OMA.SectionApprox516


/-- The small-values problem involves finite sums only. Radii are uniform in
the degree and coefficients when integer-disk majorants and an anchor are fixed. -/
def H1 : Prop := ∀ (n : ℕ → ℕ), StrictMono n → (∃ c > (0:ℝ), ∀ k : ℕ, (k:ℝ)*(log k)^(2+c) < n k) →
  ∀ (B : ℕ → ℝ) (d R s : ℝ), 0<d → 1≤R → 0<s → s<1 →
  ∃ U : ℝ, R≤U ∧ ∀ (K : ℕ), 2≤K → ∀ a : ℕ → ℂ, d≤‖a 1‖ →
    (∀ m : ℕ, ∑ j ∈ range K, ‖a j‖*(m:ℝ)^(n j) ≤ B m) →
    ∃ r ∈ Set.Icc R U, ∀ z w : ℂ, ‖z‖=r → ‖w‖=r →
      1 + (1 + ‖(∑ j ∈ range K, a j*w^(n j))‖)^s ≤ ‖(∑ j ∈ range K, a j*z^(n j))‖

def H2 : Prop := ∀ (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ), StrictMono n →
  a 1 ≠ 0 → (∀ z : ℂ, HasSum (fun k => a k*z^(n k)) (f z)) → ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖=r ∧ 1 < ‖f z‖


private theorem bounded {n : ℕ → ℕ} {a : ℕ → ℂ} {f : ℂ → ℂ} (hf : (∀ z : ℂ, HasSum (fun k => a k*z^(n k)) (f z))) {r : ℝ} (_hr : 0≤r) :
    BddAbove (Set.range fun z : {z : ℂ // ‖z‖=r} => ‖f z‖) := by
  refine ⟨∑' i, ‖a i‖ * r^(n i), ?_⟩
  rintro _ ⟨z,rfl⟩
  change ‖f z‖ ≤ _
  rw [← (hf z).tsum_eq]
  simpa [norm_mul,norm_pow,z.property] using
    (norm_tsum_le_tsum_norm (hf z).summable.norm)

theorem upper {n : ℕ → ℕ} {a : ℕ → ℂ} {f : ℂ → ℂ} (hf : (∀ z : ℂ, HasSum (fun k => a k*z^(n k)) (f z))) {r : ℝ} {w : ℂ} (hw : ‖w‖=r)
    (hw' : 1 < ‖f w‖) : Erdos516.ratio r f ≤ 1 := by
  let w' : {z : ℂ // ‖z‖=r} := ⟨w,hw⟩
  have hm : (⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖) ≤ ‖f w‖ := ciInf_le ⟨0,by rintro _ ⟨z,rfl⟩; positivity⟩ w'
  have hM : ‖f w‖ ≤ (⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖) := le_ciSup (bounded hf (hw ▸ norm_nonneg _)) w'
  have hp := hw'.trans_le hM
  change log ((⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖)) / log ((⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖)) ≤ 1
  apply (div_le_one (log_pos hp)).mpr
  have hne : Nonempty {z : ℂ // ‖z‖ = r} := ⟨w'⟩
  have hnon : 0 ≤ (⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖) := le_ciInf fun _ => norm_nonneg _
  rcases hnon.eq_or_lt with h|h
  · rw [← h,log_zero]; exact (log_pos hp).le
  · exact log_le_log h (hm.trans hM)

private theorem lower {f : ℂ → ℂ} {r s : ℝ} (hs : 0<s) {u : ℂ} (hu : ‖u‖=r)
    (hu' : 1 < ‖f u‖) (hB : BddAbove (Set.range fun z : {z : ℂ // ‖z‖=r} => ‖f z‖))
    (hp : ∀ z w : ℂ, ‖z‖=r → ‖w‖=r → ‖f w‖^s ≤ ‖f z‖) :
    s ≤ Erdos516.ratio r f := by
  let u' : {z : ℂ // ‖z‖=r} := ⟨u,hu⟩
  have hn : Nonempty {z : ℂ // ‖z‖=r} := ⟨u'⟩
  have hl (w : {z : ℂ // ‖z‖=r}) : ‖f w‖^s ≤ (⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖) :=
    le_ciInf fun z => hp z w z.property w.property
  have hm : 0 < (⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖) :=
    (rpow_pos_of_pos (lt_trans zero_lt_one hu') s).trans_le (hl u')
  have hM : 1 < (⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖) := hu'.trans_le (le_ciSup hB u')
  have hMax : (⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖) ≤ ((⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖))^(1/s) := by
    apply ciSup_le; intro w
    have hh := rpow_le_rpow (rpow_nonneg (norm_nonneg _) s) (hl w) (by positivity : 0≤1/s)
    rwa [← rpow_mul (norm_nonneg _),mul_one_div_cancel hs.ne',rpow_one] at hh
  have hlog := log_le_log (zero_lt_one.trans hM) hMax
  rw [log_rpow hm] at hlog
  change s ≤ log ((⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖)) / log ((⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖))
  apply (le_div_iff₀ (log_pos hM)).mpr
  field_simp [hs.ne'] at hlog
  nlinarith

theorem main : H1 → H2 → type_of% @Erdos516.erdos_516.variants.limsup_ratio_eq_one := by
  intro windows grows f n hmono hgap a ha hf
  let B (m : ℕ) := ∑' j, ‖a j‖*(m:ℝ)^(n j)
  have sums (m : ℕ) : Summable (fun j => ‖a j‖*(m:ℝ)^(n j)) := by
    simpa [norm_mul,norm_pow] using (hf (m:ℂ)).summable.norm
  have caps (m K : ℕ) : ∑ j ∈ range K, ‖a j‖*(m:ℝ)^(n j) ≤ B m :=
    (sums m).sum_le_tsum _ (fun _ _ => by positivity)
  have hgr := grows n a f hmono (ha 1) hf
  have hu : ∀ᶠ r : ℝ in atTop, Erdos516.ratio r f ≤ 1 := hgr.mono (by
    rintro r ⟨w,hw,hb⟩; exact upper hf hw hb)
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp hgr
  have hits (s : ℝ) (hs : 0<s) (hs' : s<1) :
      ∃ᶠ r : ℝ in atTop, s ≤ Erdos516.ratio r f := by
    rw [frequently_atTop]
    intro R
    let R' := max (max R R₀) 1
    have hR : R≤R' := (le_max_left R R₀).trans (le_max_left _ _)
    have hR1 : 1≤R' := le_max_right _ _
    have hR0 : R₀≤R' := (le_max_right R R₀).trans (le_max_left _ _)
    obtain ⟨U,hU,hpoly⟩ := windows n hmono hgap B ‖a 1‖ R' s (norm_pos_iff.mpr (ha 1)) hR1 hs hs'
    obtain ⟨K,huK,hK⟩ := ((Metric.tendstoUniformlyOn_iff.mp (uniform hf U (by linarith)) 1
      (by norm_num)).and (eventually_ge_atTop 2)).exists
    obtain ⟨r,hr,good⟩ := hpoly K hK a le_rfl (fun m => caps m K)
    obtain ⟨u,hur,hu'⟩ := hR₀ r (hR0.trans hr.1)
    refine ⟨r,hR.trans hr.1,lower hs hur hu' (bounded hf (by linarith [hr.1])) ?_⟩
    intro z w hz hw
    have err (x : ℂ) (hx : ‖x‖=r) :
        |‖f x‖ - ‖(∑ j ∈ range K, a j*x^(n j))‖| < 1 := by
      exact (abs_norm_sub_norm_le _ _).trans_lt (show ‖f x-(∑ j ∈ range K, a j*x^(n j))‖ < 1 from
        by simpa only [dist_eq_norm] using huK x (hx.trans_le hr.2))
    have ez := (abs_lt.mp (err z hz)).1
    have ew := (abs_lt.mp (err w hw)).2
    have pw := rpow_le_rpow (norm_nonneg (f w)) (show ‖f w‖ ≤ 1+‖(∑ j ∈ range K, a j*w^(n j))‖ by linarith) hs.le
    linarith [good z w hz hw]
  have hbound := isBoundedUnder_of_eventually_le hu
  have hc := IsCoboundedUnder.of_frequently_ge (hits (1/2) (by norm_num) (by norm_num))
  refine le_antisymm (limsup_le_of_le hc hu) ?_
  rw [← forall_lt_iff_le]
  intro y hy
  obtain ⟨s,hs,hs'⟩ := exists_between (show max y 0 < 1 from max_lt_iff.mpr ⟨hy,zero_lt_one⟩)
  exact ((le_max_left _ _).trans_lt hs).trans_le
    (le_limsup_of_frequently_le (hits s ((le_max_right _ _).trans_lt hs) hs') hbound)

end OMA.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1
