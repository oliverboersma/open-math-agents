import FormalConjectures.ErdosProblems.«516»

/-! A proof of Kővári’s gap theorem (Michigan Math. J. 12, 1965). We control the minimum modulus on a common circle by sampling the sparse section, excluding root neighborhoods, and uniformly bounding its discarded tail. -/

/-! Finite sections on expanding disks and a coefficient lower bound for the
maximum modulus; no assumption on the order of the entire function. -/

namespace OMA.Circle516
open Finset Filter Polynomial
open scoped Topology

def sectionSum (n : ℕ → ℕ) (a : ℕ → ℂ) (K : ℕ) (z : ℂ) :=
  ∑ k ∈ range K, a k * z^(n k)

def expansion (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ) :=
  ∀ z, HasSum (fun k => a k * z^(n k)) (f z)

theorem uniform {n a f} (h : expansion n a f) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (sectionSum n a) f atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hs := (h (R:ℂ)).summable.norm
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR] at hs
  have hu := tendstoUniformlyOn_tsum_nat (f := fun k (z : ℂ) => a k*z^(n k))
    (s := {z : ℂ | ‖z‖ ≤ R}) hs (by
      intro k z hz; rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _))
  have eqf : (fun z => ∑' k, a k*z^(n k)) = f := funext fun z => (h z).tsum_eq
  rwa [eqf] at hu

theorem poly_coeff_le (P : ℂ[X]) (j : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ b) : ‖P.coeff j‖ ≤ b := by
  classical
  by_cases hj : j ∈ P.support
  · have hm := single_le_sum (f := fun i => ‖P.coeff i‖^2)
        (fun i _ => sq_nonneg _) hj
    rw [P.sum_sq_norm_coeff_eq_circleAverage] at hm
    have h₂ : Real.circleAverage (fun z : ℂ => ‖P.eval z‖^2) 0 1 ≤ b^2 := by
      apply Real.circleAverage_mono_on_of_le_circle
      · exact (P.continuous.norm.pow 2).continuousOn.circleIntegrable'
      · intro z hz
        have hz' : ‖z‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hz
        exact pow_le_pow_left₀ (norm_nonneg _) (h z hz') _
    nlinarith [hm.trans h₂]
  · simp [notMem_support_iff.mp hj,hb]

theorem coeff_bound {n a f} (hmono : StrictMono n) (h : expansion n a f)
    (j : ℕ) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hbound : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ b) : ‖a j‖*r^(n j) ≤ b := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K,hK,hjK⟩ := ((Metric.tendstoUniformlyOn_iff.mp (uniform h r hr) ε hε).and
    (eventually_gt_atTop j)).exists
  let P : ℂ[X] := ∑ k ∈ range K, monomial (n k) (a k*(r:ℂ)^(n k))
  have hc : P.coeff (n j) = a j*(r:ℂ)^(n j) := by
    simp only [P,finsetSum_coeff,coeff_monomial, hmono.injective.eq_iff]
    simp [hjK]
  have he (z : ℂ) : P.eval z = sectionSum n a K ((r:ℂ)*z) := by
    simp [P,sectionSum,eval_finsetSum,mul_pow,mul_assoc]
  have hv := poly_coeff_le P (n j) (add_nonneg hb hε.le) (fun z hz => by
    have hn : ‖(r:ℂ)*z‖ = r := by simp [hz, abs_of_nonneg hr]
    have hu := hK ((r:ℂ)*z) hn.le
    have hf := hbound ((r:ℂ)*z) hn
    rw [he]
    have ht := norm_sub_norm_le (sectionSum n a K ((r:ℂ)*z)) (f ((r:ℂ)*z))
    rw [dist_comm,dist_eq_norm] at hu
    linarith)
  simpa [hc,abs_of_nonneg hr] using hv

end OMA.Circle516

/-! Reduce the entire-function problem to a degree-uniform estimate on finite
lacunary polynomials in a bounded radial window. Without uniformity in degree
the polynomial assertion would follow just by letting the top monomial win. -/
namespace OMA.Window516
open Finset Filter Real
open scoped Topology
open OMA.Circle516

def Gap (n : ℕ → ℕ) := ∃ c > (0:ℝ), ∀ k : ℕ, (k:ℝ)*(log k)^(2+c) < n k

/-- The small-values problem involves finite sums only. Radii are uniform in
the degree and coefficients when integer-disk majorants and an anchor are fixed. -/
def FiniteWindows : Prop := ∀ (n : ℕ → ℕ), StrictMono n → Gap n →
  ∀ (B : ℕ → ℝ) (d R s : ℝ), 0<d → 1≤R → 0<s → s<1 →
  ∃ U : ℝ, R≤U ∧ ∀ (K : ℕ), 2≤K → ∀ a : ℕ → ℂ, d≤‖a 1‖ →
    (∀ m : ℕ, ∑ j ∈ range K, ‖a j‖*(m:ℝ)^(n j) ≤ B m) →
    ∃ r ∈ Set.Icc R U, ∀ z w : ℂ, ‖z‖=r → ‖w‖=r →
      1 + (1 + ‖sectionSum n a K w‖)^s ≤ ‖sectionSum n a K z‖

def Growth : Prop := ∀ (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ), StrictMono n →
  a 1 ≠ 0 → expansion n a f → ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖=r ∧ 1 < ‖f z‖

theorem growth : Growth := by
  intro n a f hmono ha hf
  have positive := norm_pos_iff.mpr ha
  have hn : 0 < n 1 := by have := hmono (show 0 < 1 by decide); omega
  filter_upwards [eventually_gt_atTop (max 1 (1 / ‖a 1‖))] with r hr
  have hr1 := (le_max_left 1 (1/‖a 1‖)).trans hr.le
  by_contra! h
  have hh := coeff_bound hmono hf 1 (by linarith : 0≤r) (by norm_num : (0:ℝ)≤1) h
  have hr' := (div_lt_iff₀ positive).mp ((le_max_right 1 (1/‖a 1‖)).trans_lt hr)
  have hp : r ≤ r^(n 1) := by simpa using pow_le_pow_right₀ hr1 hn
  nlinarith [mul_le_mul_of_nonneg_left hp positive.le]

noncomputable def maxMod (f : ℂ → ℂ) (r : ℝ) := ⨆ z : {z : ℂ // ‖z‖=r}, ‖f z‖
noncomputable def minMod (f : ℂ → ℂ) (r : ℝ) := ⨅ z : {z : ℂ // ‖z‖=r}, ‖f z‖

private theorem bounded {n a f} (hf : expansion n a f) {r : ℝ} (_hr : 0≤r) :
    BddAbove (Set.range fun z : {z : ℂ // ‖z‖=r} => ‖f z‖) := by
  refine ⟨∑' i, ‖a i‖ * r^(n i), ?_⟩
  rintro _ ⟨z,rfl⟩
  change ‖f z‖ ≤ _
  rw [← (hf z).tsum_eq]
  simpa [norm_mul,norm_pow,z.property] using
    (norm_tsum_le_tsum_norm (hf z).summable.norm)

theorem upper {n a f} (hf : expansion n a f) {r : ℝ} {w : ℂ} (hw : ‖w‖=r)
    (hw' : 1 < ‖f w‖) : Erdos516.ratio r f ≤ 1 := by
  let w' : {z : ℂ // ‖z‖=r} := ⟨w,hw⟩
  have hm : minMod f r ≤ ‖f w‖ := ciInf_le ⟨0,by rintro _ ⟨z,rfl⟩; positivity⟩ w'
  have hM : ‖f w‖ ≤ maxMod f r := le_ciSup (bounded hf (hw ▸ norm_nonneg _)) w'
  have hp := hw'.trans_le hM
  change log (minMod f r) / log (maxMod f r) ≤ 1
  apply (div_le_one (log_pos hp)).mpr
  have hne : Nonempty {z : ℂ // ‖z‖ = r} := ⟨w'⟩
  have hnon : 0 ≤ minMod f r := le_ciInf fun _ => norm_nonneg _
  rcases hnon.eq_or_lt with h|h
  · rw [← h,log_zero]; exact (log_pos hp).le
  · exact log_le_log h (hm.trans hM)

private theorem lower {f : ℂ → ℂ} {r s : ℝ} (hs : 0<s) {u : ℂ} (hu : ‖u‖=r)
    (hu' : 1 < ‖f u‖) (hB : BddAbove (Set.range fun z : {z : ℂ // ‖z‖=r} => ‖f z‖))
    (hp : ∀ z w : ℂ, ‖z‖=r → ‖w‖=r → ‖f w‖^s ≤ ‖f z‖) :
    s ≤ Erdos516.ratio r f := by
  let u' : {z : ℂ // ‖z‖=r} := ⟨u,hu⟩
  have hn : Nonempty {z : ℂ // ‖z‖=r} := ⟨u'⟩
  have hl (w : {z : ℂ // ‖z‖=r}) : ‖f w‖^s ≤ minMod f r :=
    le_ciInf fun z => hp z w z.property w.property
  have hm : 0 < minMod f r :=
    (rpow_pos_of_pos (lt_trans zero_lt_one hu') s).trans_le (hl u')
  have hM : 1 < maxMod f r := hu'.trans_le (le_ciSup hB u')
  have hMax : maxMod f r ≤ (minMod f r)^(1/s) := by
    apply ciSup_le; intro w
    have hh := rpow_le_rpow (rpow_nonneg (norm_nonneg _) s) (hl w) (by positivity : 0≤1/s)
    rwa [← rpow_mul (norm_nonneg _),mul_one_div_cancel hs.ne',rpow_one] at hh
  have hlog := log_le_log (zero_lt_one.trans hM) hMax
  rw [log_rpow hm] at hlog
  change s ≤ log (minMod f r) / log (maxMod f r)
  apply (le_div_iff₀ (log_pos hM)).mpr
  field_simp [hs.ne'] at hlog
  nlinarith

theorem finish (windows : FiniteWindows) (grows : Growth) :
    type_of% @Erdos516.erdos_516.variants.limsup_ratio_eq_one := by
  intro f n hmono hgap a ha hf
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
        |‖f x‖ - ‖sectionSum n a K x‖| < 1 := by
      exact (abs_norm_sub_norm_le _ _).trans_lt (show ‖f x-sectionSum n a K x‖ < 1 from
        by simpa only [dist_eq_norm] using huK x (hx.trans_le hr.2))
    have ez := (abs_lt.mp (err z hz)).1
    have ew := (abs_lt.mp (err w hw)).2
    have pw := rpow_le_rpow (norm_nonneg (f w)) (show ‖f w‖ ≤ 1+‖sectionSum n a K w‖ by linarith) hs.le
    linarith [good z w hz hw]
  have hbound := isBoundedUnder_of_eventually_le hu
  have hc := IsCoboundedUnder.of_frequently_ge (hits (1/2) (by norm_num) (by norm_num))
  refine le_antisymm (limsup_le_of_le hc hu) ?_
  rw [← forall_lt_iff_le]
  intro y hy
  obtain ⟨s,hs,hs'⟩ := exists_between (show max y 0 < 1 from max_lt_iff.mpr ⟨hy,zero_lt_one⟩)
  exact ((le_max_left _ _).trans_lt hs).trans_le
    (le_limsup_of_frequently_le (hits s ((le_max_right _ _).trans_lt hs) hs') hbound)

end OMA.Window516

/-! Finite angular sampling for lacunary polynomials by annihilating rotations. -/
namespace OMA.Turan516
open Finset Real
open scoped Classical

private theorem extract (S : Finset ℕ) (v : ℕ → ℂ) (anchor : ℂ) (hv : ∀ i, ‖v i‖=1) :
    ∀ (b : ℕ → ℂ) (c : ℂ) (M : ℝ),
      (∀ j ≤ S.card, ‖c*anchor^j + ∑ i ∈ S, b i*(v i)^j‖ ≤ M) →
      ‖c‖ * ∏ i ∈ S, ‖anchor-v i‖ ≤ (2:ℝ)^S.card*M := by
  induction S using Finset.induction_on with
  | empty => intro b c M he; simpa using he 0 (by simp)
  | @insert i S hi ih =>
    intro b c M h
    let val (j : ℕ) := c*anchor^j + ∑ l ∈ insert i S, b l*(v l)^j
    have elim (j : ℕ) :
        (c*(anchor-v i))*anchor^j + ∑ l ∈ S, (b l*(v l-v i))*(v l)^j =
          val (j+1)-v i*val j := by
      dsimp [val]
      rw [sum_insert hi,sum_insert hi]
      simp only [pow_succ,mul_add,mul_sum]
      have hsum : ∑ l ∈ S, b l*(v l-v i)*v l^j =
          (∑ l ∈ S, b l*(v l^j*v l))-(∑ l ∈ S, v i*(b l*v l^j)) := by
        rw [←sum_sub_distrib]; exact sum_congr rfl (fun _ _ => by ring)
      rw [hsum]
      ring
    have val_bound (j) (hj : j ≤ S.card) :
        ‖(c*(anchor-v i))*anchor^j + ∑ l ∈ S, (b l*(v l-v i))*(v l)^j‖ ≤ 2*M := by
      rw [elim]
      have h₁ : ‖val (j+1)‖ ≤ M := h _ (by rw [card_insert_of_notMem hi]; omega)
      have h₀ : ‖val j‖ ≤ M := h _ (by rw [card_insert_of_notMem hi]; omega)
      calc
        _ ≤ ‖val (j+1)‖+‖v i*val j‖ := norm_sub_le ..
        _ ≤ 2*M := by rw [norm_mul,hv,one_mul]; linarith
    have bb := ih _ _ _ val_bound
    rw [norm_mul] at bb
    rw [prod_insert hi,card_insert_of_notMem hi,pow_succ]
    linarith only [bb]

private noncomputable def rot (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

private lemma rot_norm (x : ℝ) : ‖rot x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma rot_add (x y : ℝ) : rot (x+y) = rot x*rot y := by
  simp [rot,add_mul,Complex.exp_add]

private lemma rot_pow (x : ℝ) (n : ℕ) : rot x ^ n = rot (n*x) := by
  induction n with
  | zero => simp [rot]
  | succ n ih => rw [pow_succ,ih, Nat.cast_succ,add_mul,one_mul,rot_add]

private lemma chord {x y : ℝ} (h : x ≤ y) (hπ : y-x ≤ π) :
    2/π*(y-x) ≤ ‖rot y-rot x‖ := by
  let a := (x+y)/2
  let b := (y-x)/2
  have hi : rot b - rot (-b) = (2*Real.sin b:ℝ)*Complex.I := by
    unfold rot; rw [Complex.exp_mul_I,Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg,Complex.sin_neg]
    ring
  have eq : rot y-rot x = rot a*(rot b - rot (-b)) := by
    rw [mul_sub,←rot_add,←rot_add]
    dsimp [a,b]; congr 2 <;> ring
  have hp : 0 ≤ b := by dsimp [b]; linarith
  have hq : b ≤ π/2 := by dsimp [b]; linarith
  rw [eq, norm_mul,rot_norm,one_mul,hi,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi hp (by linarith [pi_pos])))]
  have lower := Real.mul_le_sin hp hq
  dsimp [b] at lower
  linarith only [lower]

private lemma spread (n : ℕ → ℕ) (hm : StrictMono n) (N i j : ℕ) (hn : 0 < N)
    (hi : n i ≤ N) (hj : n j ≤ N) :
    (2/(N:ℝ))*(Nat.dist i j : ℝ) ≤
      ‖rot ((n i:ℝ)*(π/N))-rot ((n j:ℝ)*(π/N))‖ := by
  wlog h : i ≤ j generalizing i j
  · rw [Nat.dist_comm,norm_sub_rev]
    exact this _ _ hj hi (by omega)
  rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,norm_sub_rev]
  have d := hm.add_le_nat (j-i) i
  rw [Nat.sub_add_cancel h] at d
  have dr : (j:ℝ)-i ≤ (n j:ℝ)-n i := by
    have := (show ((j-i:ℕ):ℝ)+n i ≤ n j by exact_mod_cast d)
    rw [Nat.cast_sub h] at this
    linarith
  have rr : 0 ≤ π/(N:ℝ) := by positivity
  have hsub : (n j:ℝ)*(π/N)-(n i:ℝ)*(π/N) = ((n j:ℝ)-n i)*(π/N) := by ring
  have scale : (N:ℝ)*(π/N)=π := by field_simp
  have arg := chord (x := (n i:ℝ)*(π/N)) (y := (n j:ℝ)*(π/N))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hm.monotone h) rr)
    (by rw [hsub]; calc
          _ ≤ (N:ℝ)*(π/N) := mul_le_mul_of_nonneg_right (by
            have hj' : (n j:ℝ) ≤ N := by exact_mod_cast hj
            linarith [Nat.cast_nonneg (α:=ℝ) (n i)]) rr
          _ = _ := scale)
  rw [hsub] at arg
  calc
    _ ≤ (2/(N:ℝ))*((n j:ℝ)-n i) := mul_le_mul_of_nonneg_left dr (by positivity)
    _ = _ := by field_simp
    _ ≤ _ := arg

private lemma diffs (K i : ℕ) (hi : i < K) :
    (∏ j ∈ (range K).erase i, Nat.dist i j) = i.factorial*(K-1-i).factorial := by
  have sets : (range K).erase i = range i ∪ Ico (i+1) K := by
    ext j; simp; omega
  have disj : Disjoint (range i) (Ico (i+1) K) := disjoint_left.mpr (by
    intro j hj hk; have := mem_range.mp hj; have := (mem_Ico.mp hk).1; omega)
  rw [sets, prod_union disj]
  congr 1
  · calc
      _ = ∏ j ∈ range i, ((i-1-j)+1) := prod_congr rfl fun j hj => by
        have := mem_range.mp hj; rw [Nat.dist_eq_sub_of_le_right (by omega)]; omega
      _ = ∏ j ∈ range i, (j+1) := prod_range_reflect (·+1) _
      _ = _ := prod_range_add_one_eq_factorial _
  · rw [prod_Ico_eq_prod_range]
    simp only [show K-(i+1)=K-1-i by omega]
    rw [←prod_range_add_one_eq_factorial]
    apply prod_congr rfl
    intro j _
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega

/-- For K occupied exponents up to N, some one of K consecutive angular
samples controls each particular coefficient. The two factorials record the
integer separation from the anchor on its left and right. -/
theorem angular (n : ℕ → ℕ) (hm : StrictMono n) (a : ℕ → ℂ) (K N i : ℕ)
    (hi : i < K) (hn : 0 < N) (up : ∀ j < K, n j ≤ N) (z : ℂ) :
    ∃ j < K,
      (i.factorial:ℝ)*(K-1-i).factorial*‖a i*z^(n i)‖ ≤
        (N:ℝ)^(K-1) * ‖OMA.Circle516.sectionSum n a K
          (z*Complex.exp (((j:ℝ)*(π/N):ℝ)*Complex.I))‖ := by
  let V (k : ℕ) := rot ((n k:ℝ)*(π/N))
  let b (k : ℕ) := a k*z^(n k)
  let S := (range K).erase i
  let val (j : ℕ) := OMA.Circle516.sectionSum n a K (z*rot ((j:ℝ)*(π/N)))
  have sc : S.card = K-1 := by simp [S,card_erase_of_mem (mem_range.mpr hi)]
  have same (j : ℕ) : b i*V i^j + ∑ k ∈ S, b k*V k^j = val j := by
    dsimp only [S]
    rw [add_sum_erase (range K) (fun l => b l*V l^j) (mem_range.mpr hi)]
    apply sum_congr rfl
    intro k _
    dsimp [V,b]
    rw [mul_pow,rot_pow,rot_pow]
    ring_nf
  obtain ⟨j,hj,hmax⟩ := (range K).exists_max_image (fun k => ‖val k‖) ⟨i,mem_range.mpr hi⟩
  have e := extract S V (V i) (fun k => rot_norm _) b (b i) ‖val j‖ (fun l hl => by
    rw [same]
    apply hmax _ (mem_range.mpr (by rw [sc] at hl; omega)))
  have prod : (2/(N:ℝ))^S.card*((i.factorial:ℝ)*(K-1-i).factorial) ≤
      ∏ k ∈ S, ‖V i - V k‖ := by
    have aa : (∏ k ∈ S, (Nat.dist i k : ℝ)) =
        (i.factorial:ℝ)*(K-1-i).factorial := by exact_mod_cast diffs K i hi
    rw [←aa,←Finset.prod_const,←prod_mul_distrib]
    apply prod_le_prod
    · intro k _; positivity
    · intro k hk
      exact spread n hm N i k hn (up _ hi) (up _ (mem_range.mp (mem_erase.mp hk).2))
  have tot := (mul_le_mul_of_nonneg_left prod (norm_nonneg (b i))).trans e
  rw [sc,div_pow] at tot
  have pos : 0 < (2:ℝ)^(K-1) := by positivity
  refine ⟨j,mem_range.mp hj,?_⟩
  change _ ≤ (N:ℝ)^(K-1)*‖val j‖
  change _*_*‖b i‖ ≤ _
  field_simp at tot
  nlinarith only [tot,mul_pos pos (show 0 < (N:ℝ)^(K-1) by positivity)]

/-- A convenient logarithmic form of the factorial loss in angular sampling. -/
theorem log_loss (K N i : ℕ) (hK : 2 ≤ K) (hN : K ≤ N) (hi : i < K) :
    (K-1:ℕ)*log (N:ℝ) - log (i.factorial:ℝ) - log ((K-1-i).factorial:ℝ)
      ≤ (K:ℝ)*(1+log (4*N/K:ℝ)) := by
  let m := K-1
  have hm : 0 < m := by dsimp [m]; omega
  have im : i ≤ m := by dsimp [m]; omega
  have hmk : (m:ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have h2 : (K:ℝ) ≤ 2*m := by exact_mod_cast (show K ≤ 2*m by dsimp [m]; omega)
  have sp : (0:ℝ) < m := by positivity
  have nn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have kp : 0 < (K:ℝ) := by positivity
  have hf := Real.pow_div_factorial_le_exp (m:ℝ) sp.le m
  have ft := Real.log_le_log (show 0 < (m:ℝ)^m/m.factorial by positivity) hf
  rw [log_div (by positivity) (by positivity),log_pow,Real.log_exp] at ft
  have prod : (m.factorial:ℝ) ≤ 2^m*((i.factorial:ℝ)*(m-i).factorial) := by
    exact_mod_cast (calc
      m.factorial = m.choose i*i.factorial*(m-i).factorial :=
        (Nat.choose_mul_factorial_mul_factorial im).symm
      _ ≤ (2^m)*(i.factorial*(m-i).factorial) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow ..))
  have fc := Real.log_le_log (by positivity : 0 < (m.factorial:ℝ)) prod
  rw [log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),log_pow] at fc
  have ratio : 2*(N:ℝ)/m ≤ 4*N/K := by
    apply (div_le_div_iff₀ sp kp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2*(N:ℝ) by positivity)]
  have rat := log_le_log (by positivity : (0:ℝ) < 2*N/m) ratio
  rw [log_div (by positivity) sp.ne',log_mul (by norm_num) nn.ne'] at rat
  have hp : 0 ≤ log (4*N/K:ℝ) := log_nonneg ((one_le_div kp).mpr (by
    have hr : (K:ℝ) ≤ N := by exact_mod_cast hN
    linarith))
  change (m:ℝ)*Real.log N-Real.log (i.factorial:ℝ)-Real.log ((m-i).factorial:ℝ) ≤ _
  calc
    _ ≤ (m:ℝ)*(1+log (4*N/K:ℝ)) := by
      nlinarith only [ft,fc,mul_le_mul_of_nonneg_left rat sp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmk (by linarith)

end OMA.Turan516

/-! A local minimum-modulus estimate from factoring out the nearby zeros. -/
namespace OMA.Disk516
open Polynomial Complex Metric InnerProductSpace Real
open scoped Topology Classical

private lemma harnack {u : ℂ → ℝ} {w z : ℂ} {h : ℝ} (hh : 0 < h)
    (harm : HarmonicOnNhd u (closedBall w (2*h)))
    (nonneg : ∀ x ∈ sphere w (2*h), 0 ≤ u x) (hz : dist z w ≤ h) :
    u z ≤ 3*u w := by
  have hr : 0 < 2*h := by positivity
  have inball : z ∈ ball w (2*h) := by rw [mem_ball]; linarith
  have hcont : ContinuousOn u (sphere w (2*h)) := harm.continuousOn.mono sphere_subset_closedBall
  let f := (Complex.re ∘ herglotzRieszKernel w z) • u
  have hc := continuousOn_herglotzRieszKernel_sphere inball
  rw [abs_of_pos hr] at hc
  have c₁ : ContinuousOn f (sphere w (2*h)) :=
    (Complex.continuous_re.comp_continuousOn hc).smul hcont
  have c₂ : ContinuousOn ((3:ℝ) • u) (sphere w (2*h)) := continuousOn_const.smul hcont
  have bd := circleAverage_mono (c₁.circleIntegrable hr.le) (c₂.circleIntegrable hr.le) (by
    intro x hx
    rw [abs_of_pos hr] at hx
    have ker := re_herglotzRieszKernel_le hx inball
    rw [dist_eq_norm] at hz
    have rat : (2*h+‖z-w‖)/(2*h-‖z-w‖) ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    exact mul_le_mul_of_nonneg_right (ker.trans rat) (nonneg _ hx))
  have avg := (show HarmonicOnNhd u (closedBall w |2*h|) by rwa [abs_of_pos hr]).circleAverage_eq
  rw [show f = poissonKernel w z • u by rw [poissonKernel_eq_re_herglotzRieszKernel],
    harm.circleAverage_poissonKernel_smul inball,circleAverage_smul,
    avg] at bd
  exact bd

private lemma factor_lower {s : Multiset ℂ} (x : ℂ) (b : ℝ) (hb : 0 ≤ b)
    (lo : ∀ a ∈ s, b ≤ ‖x-a‖) :
    b^s.card ≤ ‖(s.map (x-·)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,norm_mul,pow_succ']
    exact mul_le_mul (lo a (by simp)) (ih fun y hy => lo y (by simp [hy]))
      (pow_nonneg hb _) (norm_nonneg _)

private lemma factor_upper {s : Multiset ℂ} (x : ℂ) (b : ℝ)
    (hi : ∀ a ∈ s, ‖x-a‖ ≤ b) :
    ‖(s.map (x-·)).prod‖ ≤ b^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,norm_mul,pow_succ']
    exact mul_le_mul (hi a (by simp)) (ih fun y hy => hi y (by simp [hy]))
      (norm_nonneg _) ((norm_nonneg _).trans (hi a (by simp)))

theorem local_bound (P : ℂ[X]) {w z : ℂ} {h g M : ℝ} (hh : 0 < h) (hg : 0 < g)
    (gh : g ≤ h) (hz : dist z w ≤ h) (pw : P.eval w ≠ 0)
    (away : ∀ a ∈ P.roots, g ≤ ‖z-a‖)
    (cap : ∀ x ∈ sphere w (5*h), ‖P.eval x‖ ≤ M) :
    P.eval z ≠ 0 ∧ Real.log M - Real.log ‖P.eval z‖ ≤
      (3+Real.log (3*h/g)/Real.log (3/2:ℝ))*(Real.log M-Real.log ‖P.eval w‖) := by
  have p0 : P ≠ 0 := fun e => pw (by simp [e])
  let near := P.roots.filter fun a => dist w a ≤ 2*h
  let far := P.roots.filter fun a => ¬dist w a ≤ 2*h
  let nm := near.card
  let Q : ℂ[X] := C ((3*(h:ℂ))^nm*P.leadingCoeff)*(far.map fun a => X-C a).prod
  have qval (x : ℂ) : Q.eval x = (3*(h:ℂ))^nm*P.leadingCoeff*(far.map (x-·)).prod := by
    simp [Q,eval_multiset_prod,Multiset.map_map]
  have fac (x : ℂ) : (3*h)^nm*‖P.eval x‖ = ‖Q.eval x‖*‖(near.map (x-·)).prod‖ := by
    have eq : near+far=P.roots := Multiset.filter_add_not ..
    rw [(IsAlgClosed.splits P).eval_eq_prod_roots,←eq,Multiset.map_add,Multiset.prod_add,qval]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    norm_num; ring
  have nsub {a : ℂ} (ha : a ∈ near) : dist w a ≤ 2*h := (Multiset.mem_filter.mp ha).2
  have Qcap (x : ℂ) (hx : x ∈ sphere w (5*h)) : ‖Q.eval x‖ ≤ M := by
    have low := factor_lower (s := near) x (3*h) (by positivity) (by
      intro a ha
      have tri := dist_triangle x a w
      rw [dist_comm a w,mem_sphere.mp hx] at tri
      rw [←dist_eq_norm]
      linarith [nsub ha])
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < (3*h)^nm)).mp
    calc
      _ ≤ ‖Q.eval x‖*‖(near.map (x-·)).prod‖ := mul_le_mul_of_nonneg_left low (norm_nonneg _)
      _ = _ := (fac x).symm
      _ ≤ (3*h)^nm*M := mul_le_mul_of_nonneg_left (cap x hx) (by positivity)
      _ = _ := by ring
  have cap' (x : ℂ) (hx : x ∈ closedBall w (5*h)) : ‖Q.eval x‖ ≤ M := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball w (5*h)) isBounded_ball
      Q.differentiable.diffContOnCl
    · rw [frontier_ball _ (by positivity : 0 < 5*h).ne']; exact Qcap
    · rwa [closure_ball _ (by positivity : 0 < 5*h).ne']
  have nz (x : ℂ) (hx : x ∈ closedBall w (2*h)) : Q.eval x ≠ 0 := by
    rw [qval]
    apply mul_ne_zero (mul_ne_zero (by exact pow_ne_zero _ (by exact_mod_cast
      (by positivity : (3:ℝ)*h ≠ 0))) (leadingCoeff_ne_zero.mpr p0))
    apply Multiset.prod_ne_zero
    intro e
    obtain ⟨a,ha,eq⟩ := Multiset.mem_map.mp e
    have xa : x = a := sub_eq_zero.mp eq
    exact (Multiset.mem_filter.mp ha).2 (by simpa [←xa,dist_comm] using mem_closedBall.mp hx)
  have ss : closedBall w (2*h) ⊆ closedBall w (5*h) := closedBall_subset_closedBall (by linarith)
  have ww : w ∈ closedBall w (2*h) := mem_closedBall_self (by positivity)
  have zz : z ∈ closedBall w (2*h) := mem_closedBall.mpr (by linarith)
  have mp : 0 < M := (norm_pos_iff.mpr (nz _ ww)).trans_le (cap' _ (ss ww))
  let u (x : ℂ) := Real.log M-Real.log ‖Q.eval x‖
  have har : HarmonicOnNhd u (closedBall w (2*h)) := by
    intro x hx
    exact (harmonicAt_const _).sub ((Q.differentiable.analyticAt x).harmonicAt_log_norm (nz x hx))
  have H := harnack hh har (fun x hx =>
    sub_nonneg.mpr (log_le_log (norm_pos_iff.mpr (nz x (sphere_subset_closedBall hx)))
      (cap' _ (ss (sphere_subset_closedBall hx))))) hz
  have near_w := factor_upper (s := near) w (2*h) (fun a ha => by
    rw [←dist_eq_norm]; exact nsub ha)
  have near_z := factor_lower (s := near) z g hg.le (fun a ha => away a (Multiset.mem_filter.mp ha).1)
  have w_cmp : (3*h)^nm*‖P.eval w‖ ≤ ‖Q.eval w‖*(2*h)^nm :=
    (fac w).le.trans (mul_le_mul_of_nonneg_left near_w (norm_nonneg _))
  have z_cmp : ‖Q.eval z‖*g^nm ≤ (3*h)^nm*‖P.eval z‖ :=
    (mul_le_mul_of_nonneg_left near_z (norm_nonneg _)).trans (fac z).ge
  have posQw := norm_pos_iff.mpr (nz _ ww)
  have posQz := norm_pos_iff.mpr (nz _ zz)
  have posPw := norm_pos_iff.mpr pw
  have posPz : 0 < ‖P.eval z‖ := by
    have := (mul_pos posQz (pow_pos hg nm)).trans_le z_cmp
    exact pos_of_mul_pos_right this (by positivity)
  have Lw := log_le_log (mul_pos (pow_pos (by positivity) nm) posPw) w_cmp
  have Lz := log_le_log (mul_pos posQz (pow_pos hg nm)) z_cmp
  rw [log_mul (by positivity) posPw.ne',log_mul posQw.ne' (by positivity),log_pow,log_pow] at Lw
  rw [log_mul posQz.ne' (by positivity),log_mul (by positivity) posPz.ne',log_pow,log_pow] at Lz
  have dif : Real.log (3*h)-Real.log (2*h)=Real.log (3/2:ℝ) := by
    rw [←log_div (by positivity) (by positivity)]; congr 1; field_simp
  have QwM := log_le_log posQw (cap' _ (ss ww))
  have ratio : 0 < Real.log (3/2:ℝ) := log_pos (by norm_num)
  have nle : (nm:ℝ) ≤ (Real.log M-Real.log ‖P.eval w‖)/Real.log (3/2:ℝ) := by
    apply (le_div_iff₀ ratio).mpr
    nlinarith only [Lw,QwM,dif]
  have logQ : Real.log ‖P.eval w‖ ≤ Real.log ‖Q.eval w‖ := by
    nlinarith only [Lw,mul_nonneg (Nat.cast_nonneg (α:=ℝ) nm) ratio.le,dif]
  have rat : 0 ≤ Real.log (3*h/g) := log_nonneg ((one_le_div hg).mpr (by linarith))
  have loss := mul_le_mul_of_nonneg_right nle rat
  rw [log_div (by positivity) hg.ne'] at loss ⊢
  dsimp [u] at H
  refine ⟨norm_pos_iff.mp posPz,?_⟩
  calc
    _ ≤ 3*(Real.log M-Real.log ‖P.eval w‖)+(nm:ℝ)*(Real.log (3*h)-Real.log g) := by
      nlinarith only [Lz,H,logQ]
    _ ≤ 3*(Real.log M-Real.log ‖P.eval w‖)+_ := add_le_add_right loss _
    _ = _ := by ring

end OMA.Disk516

/-! Uniform loss of minimum modulus on a short annulus for a sparse polynomial. -/
namespace OMA.Sample516
open Finset Polynomial Metric Real
open OMA.Circle516
open scoped Classical

private lemma avoid_roots (P : ℂ[X]) {N : ℕ} (hd : P.natDegree ≤ N) (r δ : ℝ) (hp : 0 < δ) :
    ∃ ρ ∈ Set.Icc r (r+δ), ∀ a ∈ P.roots, δ/(4*(N+1:ℝ)) ≤ |ρ-‖a‖| := by
  let gap := δ/(4*(N+1:ℝ))
  have gp : 0 < gap := by dsimp [gap]; positivity
  let sample (i : ℕ) := r+4*gap*i
  have inside (i : ℕ) (hi : i ≤ N) : sample i ∈ Set.Icc r (r+δ) := by
    have b : (i:ℝ) ≤ N+1 := by exact_mod_cast (show i ≤ N+1 by omega)
    have lim : 4*gap*((N:ℝ)+1)=δ := by dsimp [gap]; field_simp
    have := mul_le_mul_of_nonneg_left b (show 0 ≤ 4*gap by positivity)
    dsimp [sample]; constructor <;> nlinarith [mul_nonneg gp.le (Nat.cast_nonneg (α:=ℝ) i)]
  by_contra! h
  let I := range (N+1)
  have hit (i : I) : ∃ a ∈ P.roots, |sample i-‖a‖| < gap :=
    h _ (inside _ (by have := mem_range.mp i.property; omega))
  choose root hr close using hit
  have inj : Function.Injective root := by
    intro i j eq
    have lo := abs_lt.mp (close i)
    have hi := abs_lt.mp (close j)
    rw [eq] at lo
    dsimp [sample] at lo hi
    apply Subtype.ext
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · have d : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast hij
      nlinarith only [mul_le_mul_of_nonneg_left d gp.le,lo.1,hi.2,gp]
    · exact hij
    · have d : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast hij
      nlinarith only [mul_le_mul_of_nonneg_left d gp.le,lo.2,hi.1,gp]
  have card := card_le_card_of_injOn root (s := univ) (t := P.roots.toFinset)
    (fun i _ => Multiset.mem_toFinset.mpr (hr i)) inj.injOn
  simp [I] at card
  have ct : P.roots.toFinset.card ≤ N :=
    (Multiset.toFinset_card_le _).trans (P.card_roots'.trans hd)
  omega

private noncomputable def poly (n : ℕ → ℕ) (a : ℕ → ℂ) (K : ℕ) : ℂ[X] :=
  ∑ j ∈ range K, monomial (n j) (a j)

private lemma poly_eval (n a K z) : (poly n a K).eval z = sectionSum n a K z := by
  simp [poly,sectionSum,eval_finsetSum]

private lemma cap {K N : ℕ} (n : ℕ → ℕ) (a : ℕ → ℂ)
    (up : ∀ j < K,n j ≤ N) {r mass t : ℝ} (_hr : 0 < r) (hmass : 0 ≤ mass) (ht : 0 ≤ t)
    (peak : ∀ j < K, ‖a j‖*r^(n j) ≤ mass) {z : ℂ} (hz : ‖z‖ ≤ r*(1+t)) :
    ‖sectionSum n a K z‖ ≤ K*mass*exp (N*t) := by
  calc
    _ ≤ ∑ i ∈ range K, ‖a i*z^(n i)‖ := norm_sum_le ..
    _ ≤ ∑ _i ∈ range K, mass*exp (N*t) := sum_le_sum fun i hi => by
      have hi' := mem_range.mp hi
      rw [norm_mul,norm_pow]
      calc
        _ ≤ ‖a i‖*(r*(1+t))^(n i) := by gcongr
        _ = (‖a i‖*r^(n i))*(1+t)^(n i) := by rw [mul_pow,mul_assoc]
        _ ≤ mass*(exp t)^N := mul_le_mul (peak _ hi') (calc
          _ ≤ (exp t)^(n i) := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) _
          _ ≤ _ := pow_le_pow_right₀ (by simpa using Real.exp_le_exp.mpr ht) (up _ hi'))
          (pow_nonneg (by linarith) _) hmass
        _ = _ := by rw [←Real.exp_nat_mul]
    _ = _ := by simp [mul_assoc]

/-- A lower bound for every value on one circle in [r, r(1+K/N)], where K
is the number of permitted terms and N bounds their degrees. The logarithm
of the largest term controls both extrema, uniformly in the coefficients. -/
theorem local_estimate (n : ℕ → ℕ) (hm : StrictMono n) (a : ℕ → ℂ)
    (K N i : ℕ) (hK : 2 ≤ K) (hN : K ≤ N) (hi : i<K)
    (up : ∀ j < K,n j ≤ N) (r mass : ℝ) (hr : 0 < r) (hmass : 0 < mass)
    (anchor : ‖a i‖*r^(n i)=mass) (peak : ∀ j < K, ‖a j‖*r^(n j) ≤ mass) :
    ∃ ρ ∈ Set.Icc r (r*(1+(K:ℝ)/N)), ∀ z : ℂ, ‖z‖=ρ →
      sectionSum n a K z ≠ 0 ∧
      log mass-log ‖sectionSum n a K z‖ ≤
        (3+log (60*((N:ℝ)+1))/log (3/2:ℝ)) *
          (log K+26*K+K*log (4*(N:ℝ)/K)) ∧
      log ‖sectionSum n a K z‖ ≤ log mass + log K + K := by
  let P := poly n a K
  let δ := r*((K:ℝ)/N)
  have kp : (0:ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have np : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have dp : 0 < δ := by dsimp [δ]; positivity
  have pd : P.natDegree ≤ N := natDegree_sum_le_of_forall_le _ _
    (fun j hj => (natDegree_monomial_le _).trans (up _ (mem_range.mp hj)))
  obtain ⟨ρ,hρ,hgap⟩ := avoid_roots P pd r δ dp
  have hrho : r+δ = r*(1+(K:ℝ)/N) := by dsimp [δ]; ring
  refine ⟨ρ,hrho ▸ hρ,?_⟩
  intro z hz
  have rhop : 0 < ρ := hr.trans_le hρ.1
  let base := (r/ρ) • z
  have baseNorm : ‖base‖ = r := by
    rw [show base=(r/ρ) • z from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ r/ρ),hz,div_mul_cancel₀ _ rhop.ne']
  have baseDist : dist z base ≤ δ := by
    change dist z ((r/ρ) • z) ≤ _
    rw [dist_eq_norm,show z-(r/ρ) • z = (1-r/ρ) • z by rw [sub_smul,one_smul],norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ((div_le_one rhop).mpr hρ.1))]
    rw [hz]
    have := div_mul_cancel₀ r rhop.ne'
    nlinarith only [hρ.2,this]
  obtain ⟨j,hj,jlarge⟩ := OMA.Turan516.angular n hm a K N i hi (by omega) up base
  let θ : ℝ := j*(π/N)
  let w := base*Complex.exp ((θ:ℂ)*Complex.I)
  have wn : ‖w‖=r := by simp [w,Complex.norm_exp_ofReal_mul_I,baseNorm]
  have dist_w : dist z w ≤ 5*δ := by
    have dθ : 0 ≤ θ := by dsimp [θ]; positivity
    have bnd := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    rw [mul_comm Complex.I,Real.norm_eq_abs,abs_of_nonneg dθ] at bnd
    have jw : dist w base ≤ r*θ := by
      rw [dist_eq_norm,show w-base=base*(Complex.exp ((θ:ℂ)*Complex.I)-1) by dsimp [w]; ring,
        norm_mul,baseNorm]
      exact mul_le_mul_of_nonneg_left bnd hr.le
    have θlim : θ ≤ 4*((K:ℝ)/N) := by
      dsimp [θ]
      calc
        _ ≤ (K:ℝ)*(4/N) := by gcongr; exact Real.pi_lt_four.le
        _ = _ := by ring
    calc
      _ ≤ dist z base+dist w base := by simpa [dist_comm base w] using dist_triangle z base w
      _ ≤ δ + r*θ := add_le_add baseDist jw
      _ ≤ _ := by dsimp [δ] at *; nlinarith only [mul_le_mul_of_nonneg_left θlim hr.le]
  change (i.factorial:ℝ)*(K-1-i).factorial*‖a i*base^(n i)‖ ≤
      (N:ℝ)^(K-1)*‖sectionSum n a K w‖ at jlarge
  rw [norm_mul,norm_pow,baseNorm,anchor,←poly_eval] at jlarge
  have wp : 0 < ‖P.eval w‖ := by
    have := (show 0 < (i.factorial:ℝ)*(K-1-i).factorial*mass by positivity).trans_le jlarge
    exact pos_of_mul_pos_right this (by positivity)
  have Lj := log_le_log (show 0 < (i.factorial:ℝ)*(K-1-i).factorial*mass by positivity) jlarge
  rw [log_mul (by positivity) hmass.ne',log_mul (by positivity) (by positivity),
      log_mul (by positivity) wp.ne',log_pow] at Lj
  have sample : log mass-log ‖P.eval w‖ ≤ (K:ℝ)*(1+log (4*N/K:ℝ)) := by
    linarith [OMA.Turan516.log_loss K N i hK hN hi]
  have ew : (N:ℝ)*(25*((K:ℝ)/N))=25*K := by field_simp
  let M := (K:ℝ)*mass*exp (25*K)
  have mp : 0 < M := by dsimp [M]; positivity
  have sphereCap (x : ℂ) (hx : x ∈ sphere w (5*(5*δ))) : ‖P.eval x‖ ≤ M := by
    have xx := norm_le_norm_add_norm_sub' x w
    rw [←dist_eq_norm,mem_sphere.mp hx,wn] at xx
    rw [show M=K*mass*exp (25*K) from rfl,←ew,poly_eval]
    apply cap n a up hr hmass.le (by positivity) peak
    dsimp [δ] at xx; linarith only [xx]
  let g := δ/(4*((N:ℝ)+1))
  have gp : 0 < g := by dsimp [g]; positivity
  have gh : g ≤ 5*δ := (div_le_iff₀ (by positivity)).mpr (by nlinarith [mul_nonneg dp.le np.le])
  obtain ⟨nz,L⟩ := OMA.Disk516.local_bound P (by positivity) gp gh dist_w (norm_pos_iff.mp wp)
    (fun x hx => (hgap x hx).trans (hz ▸ abs_norm_sub_norm_le z x)) sphereCap
  have constant : 3*(5*δ)/g=60*((N:ℝ)+1) := by dsimp [g]; field_simp; ring
  rw [constant] at L
  have lm : log M=log K+log mass+25*K := by
    dsimp [M]; rw [log_mul (by positivity) (by positivity),log_mul kp.ne' hmass.ne',log_exp]
  have μM : mass ≤ M := by
    dsimp [M]
    calc
      _ = 1*mass*1 := by ring
      _ ≤ _ := by gcongr <;> first | exact_mod_cast (show 1≤K by omega) | simp
  have nonneg : 0 ≤ 3+log (60*((N:ℝ)+1))/log (3/2:ℝ) := by
    have a := log_nonneg (show 1 ≤ 60*((N:ℝ)+1) by linarith)
    have b := log_pos (by norm_num : (1:ℝ)<3/2); positivity
  have lower := mul_le_mul_of_nonneg_left (show log M-log ‖P.eval w‖ ≤
      log K+26*K+K*log (4*(N:ℝ)/K) by rw [lm]; linarith only [sample]) nonneg
  have ew' : (N:ℝ)*((K:ℝ)/N)=K := by field_simp
  have upper := cap n a up hr hmass.le (show 0 ≤ (K:ℝ)/N by positivity) peak (hz ▸ (hrho ▸ hρ).2)
  rw [ew'] at upper
  rw [←poly_eval] at upper ⊢
  refine ⟨nz,(sub_le_sub_right (log_le_log hmass μM) _).trans (L.trans lower),?_⟩
  have H := log_le_log (norm_pos_iff.mpr nz) upper
  rwa [log_mul (by positivity) (by positivity),log_mul kp.ne' hmass.ne',log_exp,
    add_comm (log K) (log mass)] at H

end OMA.Sample516

/-! Quantify the number of frequencies in an initial segment from the
exponent growth hypothesis of Kővári's theorem. -/
namespace OMA.Support516
open Real Filter
open scoped Topology

theorem logarithm_vs_sqrt (p : ℝ) :
    ∀ᶠ D : ℝ in atTop, (log D)^p ≤ sqrt D := by
  have h := (isLittleO_log_rpow_rpow_atTop p (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with D hD h1
  simpa only [Real.norm_eq_abs, one_mul,abs_of_nonneg (rpow_nonneg (log_nonneg h1.le) p),
    abs_of_nonneg (rpow_nonneg (by linarith : 0≤D) (1/2:ℝ)), ← sqrt_eq_rpow,
    abs_of_nonneg (sqrt_nonneg D)] using hD

theorem count {n : ℕ → ℕ} {p : ℝ} (hp : 0<p)
    (gap : ∀ k : ℕ, (k:ℝ)*(log k)^p < n k) :
    ∀ᶠ D : ℝ in atTop, ∀ k : ℕ, (n k : ℝ) ≤ D →
      ((k:ℝ)+1) ≤ (2+2^p)*D/(log D)^p := by
  filter_upwards [logarithm_vs_sqrt p,eventually_gt_atTop (1:ℝ)] with D hd h1
  intro k hk
  have h0 : 0<D := by linarith
  have lp := log_pos h1
  have hsq := sq_sqrt h0.le
  have hsqp := sqrt_nonneg D
  have hs1 : 1 ≤ sqrt D := by nlinarith
  apply (le_div_iff₀ (rpow_pos_of_pos lp p)).mpr
  rcases le_or_gt (k:ℝ) (sqrt D) with sk|sk
  · have hsmall := mul_le_mul (by linarith : (k:ℝ)+1≤2*sqrt D) hd
        (rpow_nonneg lp.le p) (by positivity : 0≤2*sqrt D)
    nlinarith [mul_nonneg (rpow_nonneg (by norm_num : (0:ℝ)≤2) p) h0.le]
  · have hl := log_le_log (sqrt_pos.mpr h0) sk.le
    rw [log_sqrt h0.le] at hl
    have pp := rpow_le_rpow (by linarith : 0≤log D/2) hl hp.le
    have fact : (log D)^p = (log D/2)^p * (2:ℝ)^p := by
      rw [← mul_rpow (by positivity) (by norm_num),div_mul_cancel₀ _ (by norm_num)]
    have mid := mul_le_mul_of_nonneg_left pp (Nat.cast_nonneg k : (0:ℝ)≤k)
    have main := mul_le_mul_of_nonneg_right (mid.trans ((gap k).le.trans hk)) (rpow_nonneg (by norm_num : (0:ℝ)≤2) p)
    rw [mul_assoc,← fact] at main
    have hsD : sqrt D ≤ D := by nlinarith
    nlinarith

end OMA.Support516

/-! A normal log-radius and a uniform truncation estimate for finite
lacunary polynomials. The length of the search window is independent of
the degree, and the tail estimate remains valid on a smaller disk. -/
namespace OMA.Normal516
open Finset Filter Real

noncomputable def step (q : ℝ) (j : ℕ) := ((j:ℝ)+1)^(-q)

theorem step_sum {q : ℝ} (hq : 1<q) : Summable (step q) := by
  have h := (summable_nat_rpow.mpr (by linarith : -q < -1))
  apply ((summable_nat_add_iff 1).mpr h).congr
  intro j
  simp [step]

/-- If every short forward step were bad, the heights would double forever
before a fixed finite time. The first good step retains a quantitative
relation between its length and the accumulated height. -/
theorem normal {q : ℝ} (hq : 1<q) (T : ℝ) (Y : ℝ → ℝ) (hY : 1 ≤ Y T)
    (bounded : ∃ B : ℝ, ∀ t ∈ Set.Icc T (T+∑' j, step q j), Y t ≤ B) :
    ∃ j : ℕ, ∃ t ∈ Set.Icc T (T+∑' i, step q i),
      2^(j:ℕ)*Y T ≤ Y t ∧ Y (t+step q j) ≤ 2*Y t := by
  classical
  let t (j : ℕ) := T + ∑ i ∈ range j, step q i
  have pos (j : ℕ) : 0 ≤ step q j := (rpow_nonneg (by positivity) _)
  have hmem (j : ℕ) : t j ∈ Set.Icc T (T+∑' i, step q i) := by
    refine ⟨le_add_of_nonneg_right (sum_nonneg (fun i _ => pos i)),?_⟩
    exact add_le_add_right ((step_sum hq).sum_le_tsum _ (fun i _ => pos i)) _
  have hsucc (j : ℕ) : t (j+1) = t j + step q j := by simp [t,sum_range_succ,add_assoc]
  have doubled (m : ℕ) (h : ∀ j < m, ¬Y (t j + step q j) ≤ 2*Y (t j)) :
      (2:ℝ)^m*Y T ≤ Y (t m) := by
    induction m with
    | zero => simp [t]
    | succ m ih =>
      have hh := ih (fun j hj => h j (by omega))
      have hh' := lt_of_not_ge (h m (by omega))
      rw [hsucc,pow_succ]
      nlinarith
  have good : ∃ j, Y (t j+step q j) ≤ 2*Y (t j) := by
    by_contra! fail
    obtain ⟨B,hB⟩ := bounded
    obtain ⟨m,hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<(2:ℝ))).eventually_gt_atTop B).exists
    have hh := doubled m (fun j _ => not_le.mpr (fail j))
    have hb := hB (t m) (hmem m)
    nlinarith [mul_nonneg (by positivity : (0:ℝ)≤2^m) (sub_nonneg.mpr hY)]
  exact ⟨Nat.find good,t (Nat.find good),hmem _,doubled _ (fun _ hj => Nat.find_min good hj),Nat.find_spec good⟩

/-- Bound the entire discarded tail, independently of the number of monomials.
The geometric majorant is summed over distinct exponents, not coefficient indices. -/
theorem truncate {n : ℕ → ℕ} (hn : StrictMono n) (v : ℕ → ℝ)
    (K D : ℕ) {t δ u Y : ℝ} (hδ : 0 < δ)
    (hu : u ≤ t+δ/2) (hD : 8*Y ≤ δ*(D:ℝ))
    (future : ∀ i < K, v i * exp ((n i:ℝ)*(t+δ)) ≤ exp (2*Y)) :
    ∑ i ∈ (range K).filter (fun i => D < n i), v i * exp ((n i:ℝ)*u)
      ≤ exp (-2*Y) / (1-exp (-δ/2)) := by
  classical
  let S := (range K).filter (fun i => D < n i)
  let g := fun i => n i - D
  have hinj : Set.InjOn g (S : Set ℕ) := by
    intro i hi j hj h
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    apply hn.injective
    change n i-D=n j-D at h
    omega
  have hpt (i : ℕ) (hi : i ∈ S) : v i * exp ((n i:ℝ)*u) ≤
      exp (-2*Y) * (exp (-δ/2))^(g i) := by
    have hi' := mem_filter.mp hi
    have e : (g i : ℝ) = (n i:ℝ) - D := Nat.cast_sub hi'.2.le
    have f := future i (mem_range.mp hi'.1)
    have hu' := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (n i) : (0:ℝ)≤n i)
    calc
      _ = (v i * exp ((n i:ℝ)*(t+δ))) * exp ((n i:ℝ)*(u-(t+δ))) := by
        rw [mul_assoc, ← exp_add]; congr 2; ring
      _ ≤ exp (2*Y) * exp ((n i:ℝ)*(u-(t+δ))) :=
        mul_le_mul_of_nonneg_right f (exp_pos _).le
      _ ≤ _ := by
        rw [← exp_nat_mul, ← exp_add, ← exp_add, exp_le_exp, e]
        nlinarith
  have hlt : exp (-δ/2) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hgeom := (summable_geometric_of_lt_one (exp_pos _).le hlt).sum_le_tsum
    (S.image g) (fun i _ => pow_nonneg (exp_pos _).le i)
  rw [tsum_geometric_of_lt_one (exp_pos _).le hlt, sum_image hinj] at hgeom
  calc
    _ ≤ ∑ i ∈ S, exp (-2*Y) * (exp (-δ/2))^(g i) := sum_le_sum hpt
    _ = exp (-2*Y) * ∑ i ∈ S, (exp (-δ/2))^(g i) := (mul_sum ..).symm
    _ ≤ _ := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hgeom (exp_pos (-2*Y)).le

end OMA.Normal516

namespace OMA.Param516
open Real Filter
open scoped Topology

noncomputable def C (q : ℝ) := (1+1/log 2)^q

theorem C_pos (q : ℝ) : 0<C q := by
  have : 0 < log 2 := log_pos (by norm_num)
  exact rpow_pos_of_pos (by positivity) _

theorem tail_one {δ Y : ℝ} (hd : 0<δ) (hy : δ⁻¹ ≤ Y) :
    exp (-2*Y)/(1-exp (-δ/2)) ≤ 1 := by
  have he : 0<exp (δ/2) := exp_pos _
  have h1 : 0<1-exp (-δ/2) := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  apply (div_le_one h1).mpr
  have hE := add_one_le_exp (δ/2)
  have down : exp (-δ/2) ≤ (1+δ/2)⁻¹ := by
    rw [neg_div,exp_neg]; exact inv_anti₀ (by positivity) (by linarith)
  have up := add_one_le_exp (2*Y)
  have hY : 0<Y := (inv_pos.mpr hd).trans_le hy
  have hh : (1+2*Y)⁻¹ ≤ (1+2/δ)⁻¹ := by
    apply inv_anti₀ (by positivity)
    rw [div_eq_mul_inv]; linarith
  rw [show -2*Y = -(2*Y) by ring, exp_neg]
  have ex : (exp (2*Y))⁻¹ ≤ (1+2*Y)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have alg : (1+2/δ)⁻¹ = 1-(1+δ/2)⁻¹ := by field_simp; ring
  linarith

theorem scale {q : ℝ} (hq : 0<q) : ∀ᶠ Y : ℝ in atTop, ∀ j : ℕ,
    (2:ℝ)^j ≤ Y →
    let δ := OMA.Normal516.step q j
    let D := ⌈8*Y/δ⌉₊
    0<δ ∧ δ≤1 ∧ 8*Y ≤ δ*(D:ℝ) ∧ Y≤(D:ℝ) ∧
    (D:ℝ) ≤ (8*C q+1)*Y*(log Y)^q ∧ 1/(C q*(log Y)^q) ≤ δ ∧
    exp (-2*Y)/(1-exp (-δ/2)) ≤ 1 := by
  filter_upwards [OMA.Support516.logarithm_vs_sqrt q,eventually_ge_atTop (exp 1),
    eventually_ge_atTop ((C q)^2)] with Y hlog hY hC
  have cp := C_pos q
  have yp := (exp_pos 1).trans_le hY
  have ly : 1≤log Y := by simpa using log_le_log (exp_pos 1) hY
  have ly' : 0<log Y := by linarith
  have y1 : 1≤Y := (one_le_exp (by norm_num : (0:ℝ)≤1)).trans hY
  have l2 : 0 < log 2 := log_pos (by norm_num)
  intro j hj
  dsimp only
  let δ := OMA.Normal516.step q j
  let D := ⌈8*Y/δ⌉₊
  have jp : 0 < (j:ℝ)+1 := by positivity
  have dp : 0 < δ := rpow_pos_of_pos jp _
  have di : δ⁻¹ = ((j:ℝ)+1)^q := by rw [show δ=((j:ℝ)+1)^(-q) from rfl,rpow_neg jp.le,inv_inv]
  have d1 : δ ≤ 1 := by
    exact rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α:=ℝ) j] : 1≤(j:ℝ)+1) (by linarith)
  have lj := log_le_log (pow_pos (by norm_num : (0:ℝ)<2) j) hj
  rw [log_pow] at lj
  have jb := (le_div_iff₀ l2).mpr lj
  have jbound : (j:ℝ)+1 ≤ (1+1/log 2)*log Y := by rw [add_mul,one_mul,one_div,mul_comm (log 2)⁻¹,← div_eq_mul_inv]; linarith
  have cc : δ⁻¹ ≤ C q * (log Y)^q := by
    rw [di,C,← mul_rpow (by positivity) ly'.le]
    exact rpow_le_rpow jp.le jbound hq.le
  have dy : δ⁻¹ ≤ Y := by
    have hs := sq_sqrt yp.le
    have hs' := sqrt_nonneg Y
    have c_le : C q ≤ sqrt Y := by nlinarith
    exact cc.trans ((mul_le_mul c_le hlog (rpow_nonneg ly'.le _) hs').trans (by nlinarith))
  have ce := Nat.le_ceil (8*Y/δ)
  have cl := Nat.ceil_lt_add_one (by positivity : 0≤8*Y/δ)
  have dc : 8*Y ≤ δ*(D:ℝ) := by simpa only [mul_comm δ] using (div_le_iff₀ dp).mp ce
  have dc' : Y≤(D:ℝ) := by nlinarith [mul_le_mul_of_nonneg_right d1 (Nat.cast_nonneg D : (0:ℝ)≤D)]
  have dd : (D:ℝ) ≤ (8*C q+1)*Y*(log Y)^q := by
    have p1 := one_le_rpow ly hq.le
    have aa := mul_le_mul_of_nonneg_left cc (by positivity : 0≤8*Y)
    rw [← div_eq_mul_inv] at aa
    nlinarith [one_le_mul_of_one_le_of_one_le y1 p1]
  exact ⟨dp,d1,dc,dc',dd,by
    simpa [one_div] using inv_anti₀ (inv_pos.mpr dp) cc,tail_one dp dy⟩

end OMA.Param516

/-! The entropy loss for the sparse polynomial is sublinear in its log maximum. -/
namespace OMA.Error516
open Filter Real
open scoped Topology

private lemma log_power (C p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    ∀ᶠ y : ℝ in atTop, C+p*log y ≤ y^a := by
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop (2*C),
    (isLittleO_log_rpow_atTop ha).bound (by positivity : 0 < 1/(2*p)),
    eventually_ge_atTop (1:ℝ)] with y h₁ h₂ hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs,abs_of_nonneg (log_nonneg hy),
    abs_of_nonneg (rpow_nonneg (by linarith) _)] at h₂
  have b : p*log y ≤ (1/2)*y^a := by
    calc
      _ ≤ p*(1/(2*p)*y^a) := mul_le_mul_of_nonneg_left h₂ hp.le
      _ = _ := by field_simp
  linarith

theorem bounds (A c ε : ℝ) (hA : 0 < A) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop, ∀ D K : ℝ, Y ≤ D → D ≤ A*Y*(log Y)^(1+c/4) →
      2 ≤ K → K ≤ D → K ≤ A*D/(log D)^(2+c) →
      (3+log (60*(D+1))/log (3/2:ℝ))*(log K+26*K+K*log (4*D/K)) ≤ ε*Y ∧
      K/D ≤ ε/(log Y)^(1+c/4) := by
  let a := c/4
  let q := 1+a
  let p := 2+c
  let s := 1+2*a
  have ap : 0 < a := by dsimp [a]; positivity
  have qp : 0 < q := by dsimp [q]; positivity
  have pp : 0 < p := by dsimp [p]; positivity
  have sp : 0 < s := by dsimp [s]; positivity
  have rest : 0 < p-q := by dsimp [p,q,a]; linarith
  have lograt := log_pos (by norm_num : (1:ℝ)<3/2)
  have cutoff : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ log x ∧
      log 120 ≤ log x ∧ 3+2/log (3/2:ℝ) ≤ (log x)^a ∧
      28+|log (4/A)|+p*log (log x) ≤ (log x)^a := by
    filter_upwards [eventually_ge_atTop (1:ℝ),tendsto_log_atTop.eventually_ge_atTop 1,
      tendsto_log_atTop.eventually_ge_atTop (log 120),
      ((tendsto_rpow_atTop ap).comp tendsto_log_atTop).eventually_ge_atTop (3+2/log (3/2:ℝ)),
      tendsto_log_atTop.eventually (log_power (28+|log (4/A)|) p a pp ap)] with x h1 h2 h3 h4 h5
    exact ⟨h1,h2,h3,h4,h5⟩
  obtain ⟨X,hX⟩ := eventually_atTop.mp cutoff
  filter_upwards [eventually_ge_atTop X,
    ((tendsto_rpow_atTop ap).comp tendsto_log_atTop).eventually_ge_atTop (A^2/ε),
    ((tendsto_rpow_atTop rest).comp tendsto_log_atTop).eventually_ge_atTop (A/ε)]
      with Y hY₀ Ygrowth Ygrowth'
  intro D K YD Du Klo _KD Ku
  obtain ⟨Y1,ly1,_,_,_⟩ := hX Y hY₀
  obtain ⟨D1,ld1,lb,outer,inner⟩ := hX D (hY₀.trans YD)
  have Yp : 0<Y := by linarith
  have Dp : 0<D := by linarith
  have Kp : 0<K := by linarith
  let ly := log Y
  let ld := log D
  have yp : 0 < ly := lt_of_lt_of_le zero_lt_one ly1
  have dp : 0 < ld := lt_of_lt_of_le zero_lt_one ld1
  have yd : ly ≤ ld := log_le_log Yp YD
  let J := A*D/ld^p
  have Jp : 0 < J := by dsimp [J]; positivity
  change K ≤ J at Ku
  change D ≤ A*Y*ly^q at Du
  change A^2/ε ≤ ly^a at Ygrowth
  change A/ε ≤ ly^(p-q) at Ygrowth'
  have lD : log (60*(D+1)) ≤ 2*ld := calc
    _ ≤ log (120*D) := log_le_log (by positivity) (by linarith)
    _ = log 120+ld := log_mul (by norm_num) Dp.ne'
    _ ≤ _ := by dsimp [ld]; linarith
  have out' : 3+log (60*(D+1))/log (3/2:ℝ) ≤ ld^q := calc
    _ ≤ 3+(2*ld)/log (3/2:ℝ) := by gcongr
    _ = 3+(2/log (3/2:ℝ))*ld := by ring
    _ ≤ 3*ld+(2/log (3/2:ℝ))*ld := by dsimp [ld]; linarith only [ld1]
    _ = (3+2/log (3/2:ℝ))*ld := by ring
    _ ≤ ld^a*ld := mul_le_mul_of_nonneg_right outer dp.le
    _ = ld^q := by rw [←rpow_add_one dp.ne']; congr 1; dsimp [q]; ring
  have posout : 0 ≤ 3+log (60*(D+1))/log (3/2:ℝ) := by
    have : 0 ≤ log (60*(D+1)) := log_nonneg (by linarith)
    positivity
  have logid : log (4*D/K)=log (4/A)+p*log ld+log (J/K) := by
    dsimp [J]
    rw [log_div (by positivity) Kp.ne',log_mul (by norm_num) Dp.ne',
      log_div (by norm_num) hA.ne',log_div (by positivity) Kp.ne',
      log_div (by positivity) (by positivity),log_mul hA.ne' Dp.ne',log_rpow dp]
    ring
  have extra : K*log (J/K) ≤ J := calc
    _ ≤ K*(J/K-1) := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by positivity)) Kp.le
    _ ≤ _ := by field_simp; linarith
  have coeff : 0 ≤ 27+|log (4/A)|+p*log ld := by
    have h := log_nonneg ld1
    positivity
  have entropy : log K+26*K+K*log (4*D/K) ≤ J*ld^a := by
    rw [logid]
    calc
      _ ≤ K*(27+|log (4/A)|+p*log ld)+J := by
        nlinarith only [log_le_sub_one_of_pos Kp,extra,mul_le_mul_of_nonneg_left (le_abs_self (log (4/A))) Kp.le]
      _ ≤ J*(27+|log (4/A)|+p*log ld)+J :=
        add_le_add_left (mul_le_mul_of_nonneg_right Ku coeff) _
      _ = J*(28+|log (4/A)|+p*log ld) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left inner Jp.le
  have part : ld^p = ld^q*ld^a*ld^s := by
    rw [←rpow_add dp,←rpow_add dp]; congr 1; dsimp [p,q,s,a]; ring
  have ys : ly^s = ly^q*ly^a := by
    rw [←rpow_add yp]; congr 1; dsimp [q,s]; ring
  constructor
  · calc
      _ ≤ (3+log (60*(D+1))/log (3/2:ℝ))*(J*ld^a) :=
        mul_le_mul_of_nonneg_left entropy posout
      _ ≤ ld^q*(J*ld^a) := mul_le_mul_of_nonneg_right out' (by positivity)
      _ = A*D/ld^s := by dsimp [J]; rw [part]; field_simp
      _ ≤ A*(A*Y*ly^q)/ly^s := by gcongr
      _ = (A^2/ly^a)*Y := by rw [ys]; field_simp
      _ ≤ ε*Y := by
        apply mul_le_mul_of_nonneg_right _ Yp.le
        exact (div_le_iff₀ (by positivity)).mpr (by
          have := (div_le_iff₀ hε).mp Ygrowth; linarith)
  · calc
      K/D ≤ J/D := by gcongr
      _ = A/ld^p := by dsimp [J]; field_simp
      _ ≤ A/ly^p := by gcongr
      _ ≤ ε/ly^q := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        rw [show ly^p = ly^(p-q)*ly^q by rw [←rpow_add yp,sub_add_cancel]]
        have := (div_le_iff₀ hε).mp Ygrowth'
        calc
          A*ly^q ≤ (ly^(p-q)*ε)*ly^q := mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring

end OMA.Error516

/-! Turning logarithmic bounds for a finite section into a strict modulus
estimate, allowing an additive error of one at both ends of the comparison. -/
namespace OMA.Value516
open Filter Real

theorem upper_error {K D : ℝ} (hK : 2 ≤ K) (hD : K ≤ D) :
    log K+K ≤ (3+log (60*(D+1))/log (3/2:ℝ))*(log K+26*K+K*log (4*D/K)) := by
  have kp : 0 < K := by linarith
  have lk := log_nonneg (show 1 ≤ K by linarith)
  have arg := log_nonneg ((one_le_div kp).mpr (show K ≤ 4*D by linarith))
  have lD := log_nonneg (show 1 ≤ 60*(D+1) by linarith)
  have ratio := div_nonneg lD (log_nonneg (by norm_num : (1:ℝ) ≤ 3/2))
  calc
    log K+K = 1*(log K+K) := by ring
    _ ≤ _ := mul_le_mul (by linarith) (by nlinarith [mul_nonneg kp.le arg])
      (by linarith) (by linarith)

theorem finish {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ ε > (0:ℝ), ∀ᶠ Y : ℝ in atTop, ∀ x y X W : ℝ,
      0 < x → 0 < y → log x ≥ Y-ε*Y → log y ≤ Y+ε*Y →
      x-1 ≤ X → W ≤ y+1 → 0 ≤ W → 1+(1+W)^s ≤ X := by
  let ε := (1-s)/4
  have ep : 0 < ε := by dsimp [ε]; linarith
  let g := 1-ε-s*(1+ε)
  have gp : 0 < g := by
    dsimp [g,ε]
    nlinarith only [sq_nonneg (1-s),hs']
  refine ⟨ε,ep,?_⟩
  have growing : Tendsto (fun Y : ℝ => exp (g*Y)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop gp)
  filter_upwards [eventually_ge_atTop (0:ℝ), growing.eventually_ge_atTop ((3:ℝ)^s+2)]
    with Y Yp sep
  intro x y X W xp yp hx hy Xlo Wup Wlo
  let t := Y+ε*Y
  have tp : 0 ≤ t := by dsimp [t]; positivity
  have dy : y ≤ exp t := (log_le_iff_le_exp yp).mp hy
  have dx : exp (Y-ε*Y) ≤ x := (le_log_iff_exp_le xp).mp hx
  have et : 1 ≤ exp t := one_le_exp tp
  have ew : (1+W)^s ≤ (3:ℝ)^s*exp (t*s) := calc
    _ ≤ (3*exp t)^s := rpow_le_rpow (by linarith) (by linarith) hs.le
    _ = _ := by rw [mul_rpow (by norm_num) (exp_pos _).le,←exp_mul]
  have fac : exp (g*Y)*exp (t*s) = exp (Y-ε*Y) := by
    rw [←exp_add]; congr 1; dsimp [g,t]; ring
  have et' : 1 ≤ exp (t*s) := one_le_exp (mul_nonneg tp hs.le)
  have scale : ((3:ℝ)^s+2)*exp (t*s) ≤ x :=
    (mul_le_mul_of_nonneg_right sep (exp_pos _).le).trans (fac ▸ dx)
  nlinarith only [ew,scale,et',Xlo]

end OMA.Value516

/-! Select a normal radius, retain the initial segment of frequencies through
the cutoff, and bound the rest of the polynomial on the sampling circle. -/
namespace OMA.Assemble516
open Finset Filter Real
open scoped Topology
open OMA.Circle516 OMA.Window516 OMA.Normal516

private noncomputable def term (n : ℕ → ℕ) (a : ℕ → ℂ) (i : ℕ) (t : ℝ) :=
  ‖a i‖ * exp ((n i : ℝ)*t)

private lemma growth {n : ℕ → ℕ} (hm : StrictMono n) {a : ℕ → ℂ}
    {d T : ℝ} (hd : 0<d) (hd' : d≤‖a 1‖) (hT : 0≤T) :
    exp (log d+T) ≤ term n a 1 T := by
  have e : 1 ≤ n 1 := by have := hm (show 0<1 by decide); omega
  have h : (1:ℝ) ≤ n 1 := by exact_mod_cast e
  rw [exp_add,exp_log hd]
  apply mul_le_mul hd' _ (exp_pos T).le (norm_nonneg _)
  apply exp_le_exp.mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hT

private lemma normal_peak {n : ℕ → ℕ} {a : ℕ → ℂ} {K : ℕ} (hK : 2≤K)
    {q T X : ℝ} (hq : 1<q) (hX : 1≤X) (anch : exp X ≤ term n a 1 T) :
    ∃ j : ℕ, ∃ t ∈ Set.Icc T (T+∑' l, step q l), ∃ Y : ℝ, ∃ i < K,
      X≤Y ∧ (2:ℝ)^j≤Y ∧ term n a i t=exp Y ∧
      (∀ l<K, term n a l t≤exp Y) ∧ (∀ l<K, term n a l (t+step q j)≤exp (2*Y)) := by
  classical
  have peaks (u : ℝ) : ∃ i<K, ∀ l<K, term n a l u ≤ term n a i u := by
    obtain ⟨i,hi,hh⟩ := (range K).exists_max_image (fun l => term n a l u)
      (nonempty_range_iff.mpr (by omega))
    exact ⟨i,mem_range.mp hi,fun l hl => hh l (mem_range.mpr hl)⟩
  choose I hI peak using peaks
  let F (u:ℝ) := log (term n a (I u) u)
  have a1 : 0<‖a 1‖ := by
    have h := (exp_pos X).trans_le anch
    exact pos_of_mul_pos_left h (exp_pos _).le
  have pos (u:ℝ) : 0<term n a (I u) u :=
    (mul_pos a1 (exp_pos _)).trans_le (peak u 1 (by omega))
  have pf (u:ℝ) : exp (F u)=term n a (I u) u := exp_log (pos u)
  have lower : X≤F T := exp_le_exp.mp ((anch.trans (peak T 1 (by omega))).trans_eq (pf T).symm)
  have mono : Monotone F := by
    intro x y hxy
    apply log_le_log (pos x)
    refine le_trans ?_ (peak y (I x) (hI x))
    unfold term
    gcongr
  obtain ⟨j,t,ht,grows,smooth⟩ := normal hq T F (hX.trans lower)
    ⟨_,fun u hu => mono hu.2⟩
  have dbl : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
  refine ⟨j,t,ht,F t,I t,hI t,lower.trans (mono ht.1),?_,(pf t).symm,?_,?_⟩
  · nlinarith only [grows, mul_nonneg (zero_le_one.trans dbl) (sub_nonneg.mpr (hX.trans lower))]
  · intro l hl; rw [pf]; exact peak t l hl
  · intro l hl
    exact (peak _ l hl).trans ((pf _).symm.trans_le (exp_le_exp.mpr smooth))

private lemma segment {n : ℕ → ℕ} (hm : StrictMono n) (h0 : 0<n 0)
    (K D : ℕ) (hK : 2≤K) (h1 : n 1≤D) :
    ∃ L : ℕ, 2 ≤ L ∧ L ≤ K ∧ L ≤ D ∧ (∀ i < L, n i ≤ D) ∧ (∀ i < K, D < n i ↔ L ≤ i) := by
  have grow (i : ℕ) : i+1 ≤ n i := by
    induction i with
    | zero => omega
    | succ i ih => exact (Nat.succ_le_succ ih).trans (hm (Nat.lt_succ_self i))
  have ex : ∃ r, D<n r := ⟨D,grow D⟩
  let r := Nat.find ex
  have high : D<n r := Nat.find_spec ex
  have low (i:ℕ) (hi:i<r) : n i≤D := le_of_not_gt (Nat.find_min ex hi)
  have above (i:ℕ) (hi:r ≤ i) := high.trans_le (hm.monotone hi)
  have r2 : 2≤r := by by_contra! h; have := above 1 (by omega); omega
  let L := min K r
  have l2 : 2≤L := le_min hK r2
  have lk : L≤K := min_le_left _ _
  have lr : L≤r := min_le_right _ _
  have prev := low (L-1) (by omega)
  have incr := grow (L-1)
  refine ⟨L,l2,lk,by omega,fun i hi => low i (lt_of_lt_of_le hi lr),?_⟩
  intro i hi
  constructor
  · intro h; by_contra! h'; have := low i (lt_of_lt_of_le h' lr); omega
  · intro h; apply above
    change min K r ≤ i at h
    omega

private lemma tail {n : ℕ → ℕ} (hm : StrictMono n) (a : ℕ → ℂ)
    {K L D : ℕ} (lk : L≤K) (cut : ∀ i < K, D < n i ↔ L ≤ i)
    {t δ Y ρ : ℝ} (hδ : 0<δ) (hρ : 0<ρ) (hu : log ρ≤t+δ/2)
    (hD : 8*Y≤δ*(D:ℝ)) (future : ∀ i<K, term n a i (t+δ) ≤ exp (2*Y))
    (tiny : exp (-2*Y)/(1-exp (-δ/2))≤1) {z:ℂ} (hz : ‖z‖=ρ) :
    ‖sectionSum n a K z-sectionSum n a L z‖≤1 := by
  classical
  have eq : (range K).filter (fun i => ¬ D<n i) = range L := by
    ext i
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨iK,il⟩; exact lt_of_not_ge (fun h => il ((cut _ iK).mpr h))
    · intro il; have iK := il.trans_le lk
      exact ⟨iK,fun hi => (Nat.not_le_of_lt il) ((cut _ iK).mp hi)⟩
  have partition := sum_filter_add_sum_filter_not (range K) (fun i => D<n i) (fun i => a i*z^(n i))
  rw [eq] at partition
  change ‖(∑ i ∈ range K, a i*z^(n i))-(∑ i ∈ range L, a i*z^(n i))‖≤1
  rw [←partition,add_sub_cancel_right]
  apply (norm_sum_le ..).trans
  have tr := truncate hm (fun i => ‖a i‖) K D hδ hu hD future
  simpa only [norm_mul,norm_pow,hz,exp_nat_mul,exp_log hρ] using tr.trans tiny

theorem windows : FiniteWindows := by
  classical
  intro n hm gap _B d R s hd hR hs hs'
  obtain ⟨c,hc,hgap⟩ := gap
  let q := 1+c/4
  let p := 2+c
  let C := OMA.Param516.C q
  let A := max (8*C+1) (2+2^p)
  have qp : 1<q := by dsimp [q]; linarith
  have pp : 0<p := by dsimp [p]; linarith
  have cp : 0<C := OMA.Param516.C_pos q
  have Ap : 0<A := lt_of_lt_of_le (by positivity : 0<8*C+1) (le_max_left ..)
  obtain ⟨e,ep,finish⟩ := OMA.Value516.finish hs hs'
  let ε := min e (1/(2*C))
  have εp : 0<ε := lt_min ep (by positivity)
  have small : ε≤e := min_le_left ..
  obtain ⟨D₀,count⟩ := eventually_atTop.mp (OMA.Support516.count pp hgap)
  have large := (finish.and (OMA.Param516.scale (zero_lt_one.trans qp))).and
    (OMA.Error516.bounds A c ε Ap hc εp)
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp large
  let X := max (max X₀ D₀) (max (n 1:ℝ) 2)
  have XX : X₀≤X := (le_max_left ..).trans (le_max_left ..)
  have XD : D₀≤X := (le_max_right ..).trans (le_max_left ..)
  have Xn : (n 1:ℝ)≤X := (le_max_left ..).trans (le_max_right ..)
  have X2 : 2≤X := (le_max_right ..).trans (le_max_right ..)
  let T := max (max 0 (log R)) (X-log d)
  have T0 : 0≤T := (le_max_left ..).trans (le_max_left ..)
  have TR : R≤exp T := ((exp_log (by linarith : 0<R)).symm).trans_le
    (exp_le_exp.mpr ((le_max_right ..).trans (le_max_left ..)))
  have TX : X-log d≤T := le_max_right ..
  have steps : 0≤∑' l, step q l := tsum_nonneg fun l => rpow_nonneg (by positivity) _
  refine ⟨exp (T+(∑' l, step q l)+1),TR.trans (exp_le_exp.mpr (by linarith)),?_⟩
  intro K hK a anchor _caps
  have aa := (exp_le_exp.mpr (show X≤log d+T by linarith)).trans (growth hm hd anchor T0)
  obtain ⟨j,t,ht,Y,i,hi,hXY,doubling,peak,terms,future⟩ :=
    normal_peak hK qp (by linarith : 1≤X) aa
  obtain ⟨⟨endvalues,scale⟩,err⟩ := hX₀ Y (XX.trans hXY)
  let δ := step q j
  let D := ⌈8*Y/δ⌉₊
  obtain ⟨δp,δ1,hcut,YD,Du,δlo,tiny⟩ := scale j doubling
  change 8*Y≤δ*(D:ℝ) at hcut
  change Y≤(D:ℝ) at YD
  have Yn : 0<Y := by linarith
  have oneD : n 1≤D := by exact_mod_cast (Xn.trans (hXY.trans YD))
  have n0 : 0<n 0 := by simpa using hgap 0
  obtain ⟨L,l2,lk,lD,up,cut⟩ := segment hm n0 K D hK oneD
  have iL : i<L := by
    by_contra! non
    have iD := (cut i hi).mpr non
    have pow := future i hi
    have id : term n a i (t+δ) = term n a i t * exp ((n i:ℝ)*δ) := by
      simp [term,mul_add,exp_add,mul_assoc]
    change term n a i (t+δ) ≤ _ at pow
    rw [id,peak,←exp_add,exp_le_exp] at pow
    have ineq := mul_le_mul_of_nonneg_right (show (D:ℝ)≤n i by exact_mod_cast iD.le) δp.le
    nlinarith only [pow,hcut,ineq,Yn]
  have Dl : (D:ℝ) ≤ A*Y*(log Y)^q := by
    exact Du.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left ..) Yn.le) (rpow_nonneg (log_nonneg (by linarith)) q))
  have L2 : (2:ℝ)≤L := by exact_mod_cast l2
  have LD : (L:ℝ)≤D := by exact_mod_cast lD
  have prev : L-1<L := by omega
  have ct := count D (XD.trans (hXY.trans YD)) (L-1) (by exact_mod_cast up _ prev)
  have Lcap : (L:ℝ) ≤ A*D/(log D)^p := by
    have cast : ((L-1:ℕ):ℝ)+1=L := by exact_mod_cast (show L-1+1=L by omega)
    rw [cast] at ct
    exact ct.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg _))
      (rpow_nonneg (log_nonneg (by linarith)) _))
  obtain ⟨loss,width⟩ := err D L YD Dl L2 LD Lcap
  have logp : 0<log Y := log_pos (by linarith)
  have factor : 0<(log Y)^q := rpow_pos_of_pos logp _
  have short : (L:ℝ)/D≤δ/2 := by
    calc
      _ ≤ ε/(log Y)^q := width
      _ ≤ (1/(2*C))/(log Y)^q := div_le_div_of_nonneg_right (min_le_right ..) factor.le
      _ = (1/(C*(log Y)^q))/2 := by ring
      _ ≤ _ := by gcongr
  have atT (l:ℕ) : ‖a l‖*(exp t)^(n l)=term n a l t := by simp [term,exp_nat_mul]
  obtain ⟨ρ,hρ,values⟩ := OMA.Sample516.local_estimate n hm a L D i l2 lD iL up (exp t) (exp Y)
    (exp_pos _) (exp_pos _) (by rw [atT,peak]) (fun l hl => (atT l).trans_le (terms l (hl.trans_le lk)))
  have ρp := (exp_pos t).trans_le hρ.1
  have ρu : ρ≤exp (t+δ/2) := hρ.2.trans (by
    rw [exp_add]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    linarith [add_one_le_exp (δ/2)])
  have radius : ρ≤exp (T+(∑' l, step q l)+1) := ρu.trans (exp_le_exp.mpr (by linarith [ht.2]))
  refine ⟨ρ,⟨TR.trans ((exp_le_exp.mpr ht.1).trans hρ.1),radius⟩,?_⟩
  intro z w hz hw
  have cmp (u : ℂ) (hu : ‖u‖=ρ) : ‖sectionSum n a K u-sectionSum n a L u‖≤1 :=
    tail hm a lk cut δp ρp ((log_le_iff_le_exp ρp).mpr ρu) hcut future tiny hu
  obtain ⟨nz,lo,_⟩ := values z hz
  obtain ⟨nw,_,upp⟩ := values w hw
  rw [log_exp] at lo upp
  have ew := (OMA.Value516.upper_error L2 LD).trans loss
  have eY := mul_le_mul_of_nonneg_right small Yn.le
  have gz := abs_le.mp ((abs_norm_sub_norm_le _ _).trans (cmp z hz))
  have gw := abs_le.mp ((abs_norm_sub_norm_le _ _).trans (cmp w hw))
  exact endvalues _ _ _ _ (norm_pos_iff.mpr nz) (norm_pos_iff.mpr nw) (by linarith) (by linarith)
    (by linarith) (by linarith) (norm_nonneg _)

end OMA.Assemble516

theorem OMA.solution : type_of% @Erdos516.erdos_516.variants.limsup_ratio_eq_one :=
  OMA.Window516.finish OMA.Assemble516.windows OMA.Window516.growth
