import OMAReductions.R_Erdos978_erdos_978_variants_sub_one_R1
import Mathlib

-- Step Erdos978.erdos_978.variants.sub_one.R1.H1: hypothesis H1 of reduction Erdos978.erdos_978.variants.sub_one.R1
-- Credit: @koolkao

/-!
# Small-prime sieve for `(k-1)`-th-power-free values on `(N, 2N]`

Original proof (Lane C, claude-code for koolkao). Fix `w` large. The residues `n mod ∏_{p ≤ w} p^(k-1)`
avoiding every `p^(k-1) ∣ f(n)` form a set of density at least `c > 0` (each local factor is positive by
the hypothesis; for `p` beyond the bad primes the local density is `≥ 1 - k/p²` because roots modulo
`p^(k-1)` reduce injectively to roots modulo `p`, by the Bezout identity `f u + f' v = D`). Primes
`p ∈ (w, N]` remove at most `k (N/p² + 1)` inputs each, in total `≤ 2kN/w + k π(N)`. Hence a proportion
`≥ c/4` of `(N, 2N]` survives for all large `N`.

The file also carries (unused here) the development of my #9300, whose helper lemmas it reuses.
-/

/-! Part 1: the algebraic bridge. For an irreducible `f ∈ ℤ[X]` we build the number field
`K = ℚ[X]/(f)`, the algebraic integer `θ = a·root` (`a` the leading coefficient), and for a prime
`p ∤ a·exponent θ` and a root `c` of `f` mod `p` the ideal `J p c = (p, θ - a c)` of norm `p`
(Kummer–Dedekind, Mathlib). Distinct pairs give coprime ideals. -/

noncomputable section
open Polynomial NumberField Ideal

namespace LaneC976

theorem absNorm_span_pair {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ}
    [hp : Fact p.Prime] (hpe : ¬ p ∣ RingOfIntegers.exponent θ) {c : ℤ}
    (hc : (p : ℤ) ∣ (minpoly ℤ θ).eval c) :
    absNorm (span {(p : 𝓞 K), θ - (c : 𝓞 K)}) = p := by
  classical
  set Q : ℤ[X] := X - C c with hQdef
  have hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    simp only [Q, Polynomial.map_sub, map_X, map_C, Multiset.mem_toFinset]
    rw [Polynomial.mem_normalizedFactors_iff (map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, IsRoot, eval_map, eval₂_hom, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hc
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpanPair hpe hQ
  have h1 : aeval θ Q = θ - (c : 𝓞 K) := by simp [Q]
  rw [absNorm_apply, Submodule.cardQuot_apply, ← h1]
  rw [← Nat.card_congr e.toEquiv]
  simp only [Q, Polynomial.map_sub, map_X, map_C]
  rw [Nat.card_congr (quotientSpanXSubCAlgEquiv _).toEquiv, Nat.card_zmod]

theorem one_mem_of_isCoprime {R : Type*} [CommRing R] {I : Ideal R} {x y : ℤ}
    (h : IsCoprime x y) (hx : (x : R) ∈ I) (hy : (y : R) ∈ I) : I = ⊤ := by
  obtain ⟨u, v, huv⟩ := h.map (Int.castRingHom R)
  rw [eq_top_iff_one, ← huv]
  exact add_mem (mul_mem_left _ _ (by simpa using hx)) (mul_mem_left _ _ (by simpa using hy))

/-- The ideals `(p, θ - a c)` for distinct pairs `(p, c)` with `c < p` are coprime. -/
theorem sup_span_pair_eq_top {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) (a : ℤ)
    {p q c c' : ℕ} (hp : p.Prime) (hq : q.Prime) (hc : c < p) (hc' : c' < q)
    (hpa : ¬ (p : ℤ) ∣ a) (hne : (p, c) ≠ (q, c')) :
    span {(p : 𝓞 K), θ - ((a * c : ℤ) : 𝓞 K)} ⊔ span {(q : 𝓞 K), θ - ((a * c' : ℤ) : 𝓞 K)}
      = ⊤ := by
  set I := span {(p : 𝓞 K), θ - ((a * c : ℤ) : 𝓞 K)} ⊔
    span {(q : 𝓞 K), θ - ((a * c' : ℤ) : 𝓞 K)}
  have hpI : ((p : ℤ) : 𝓞 K) ∈ I :=
    mem_sup_left (subset_span (by simp))
  have hqI : ((q : ℤ) : 𝓞 K) ∈ I :=
    mem_sup_right (subset_span (by simp))
  by_cases hpq : p = q
  · subst hpq
    have hcc : c ≠ c' := fun h ↦ hne (by rw [h])
    have h1 : θ - ((a * c : ℤ) : 𝓞 K) ∈ I := mem_sup_left (subset_span (by simp))
    have h2 : θ - ((a * c' : ℤ) : 𝓞 K) ∈ I := mem_sup_right (subset_span (by simp))
    have h3 : ((a * ((c : ℤ) - c') : ℤ) : 𝓞 K) ∈ I := by
      have := sub_mem h2 h1
      convert this using 1; push_cast; ring
    refine one_mem_of_isCoprime (x := a * ((c : ℤ) - c')) (y := p) ?_ h3 hpI
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    refine (IsCoprime.mul_left ?_ ?_)
    · exact ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hpa).symm
    · refine ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr ?_).symm
      intro hdvd
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by
        rw [abs_lt]; constructor <;> push_cast <;> omega)
      omega
  · refine one_mem_of_isCoprime (x := p) (y := q) ?_ hpI hqI
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)

theorem exponent_ne_zero {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
    (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) : RingOfIntegers.exponent θ ≠ 0 := by
  classical
  have hint : IsIntegral ℤ (θ : K) := RingOfIntegers.isIntegral_coe θ
  have hintQ : IsIntegral ℚ (θ : K) := hint.tower_top
  let B : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hintQ hθ
  have hgen : B.gen = (θ : K) := PowerBasis.ofAdjoinEqTop_gen hintQ hθ
  have hBint : IsIntegral ℤ B.gen := hgen ▸ hint
  obtain ⟨D, hD⟩ : ∃ D : ℤ, algebraMap ℤ ℚ D = Algebra.discr ℚ B.basis := by
    refine IsIntegrallyClosed.isIntegral_iff.mp (Algebra.discr_isIntegral ℚ fun i => ?_)
    rw [PowerBasis.coe_basis]; exact hBint.pow _
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hD.symm)
  have hmemD : (D : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]; intro b
    have h1 := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hBint (RingOfIntegers.isIntegral_coe b)
    rw [hgen, ← hD] at h1
    let φ : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
    have h2 : Algebra.adjoin ℤ {(θ : K)} = (Algebra.adjoin ℤ {θ}).map φ := by
      rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
    rw [h2, Subalgebra.mem_map] at h1
    obtain ⟨y, hy, hyeq⟩ := h1
    have : y = (D : 𝓞 K) * b := by
      apply RingOfIntegers.coe_injective
      change φ y = _
      rw [hyeq]
      simp [Algebra.smul_def]
    exact this ▸ hy
  have hmem : ((D.natAbs : ℕ) : 𝓞 K) ∈ conductor ℤ θ := by
    rcases Int.natAbs_eq D with h | h
    · have : ((D.natAbs : ℕ) : 𝓞 K) = (D : 𝓞 K) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hmemD
    · have : ((D.natAbs : ℕ) : 𝓞 K) = -(D : 𝓞 K) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact neg_mem hmemD
  rw [RingOfIntegers.exponent_eq_sInf]
  have hne : {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ}.Nonempty :=
    ⟨D.natAbs, Int.natAbs_pos.mpr hD0, hmem⟩
  exact (Nat.sInf_mem hne).1.ne'


section setup

variable (f : ℤ[X])

/-- `f` over `ℚ`. -/
abbrev fQ : ℚ[X] := f.map (Int.castRingHom ℚ)

/-- The number field `ℚ[X]/(f)`. -/
abbrev Kf := AdjoinRoot (fQ f)

theorem natDegree_fQ : (fQ f).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) f

variable {f} [hfi : Fact (Irreducible (fQ f))]

theorem f_ne_zero : f ≠ 0 := by
  intro h; apply hfi.out.ne_zero; simp [fQ, h]

theorem mk_eq_eval₂ (p : ℚ[X]) :
    AdjoinRoot.mk (fQ f) p = p.eval₂ (AdjoinRoot.of (fQ f)) (AdjoinRoot.root (fQ f)) := by
  induction p using Polynomial.induction_on with
  | C a => simp [AdjoinRoot.mk_C]
  | add p q hp hq => simp [hp, hq]
  | monomial n a h =>
    simp only [map_mul, map_pow, AdjoinRoot.mk_X, eval₂_mul, eval₂_X_pow, eval₂_C,
      AdjoinRoot.mk_C, eval₂_mul] at h ⊢

theorem aeval_root_f : aeval (AdjoinRoot.root (fQ f)) f = 0 := by
  rw [aeval_def, RingHom.ext_int (algebraMap ℤ (Kf f))
    ((AdjoinRoot.of (fQ f)).comp (Int.castRingHom ℚ)), ← eval₂_map]
  exact AdjoinRoot.eval₂_root (fQ f)

theorem isIntegral_theta :
    IsIntegral ℤ (f.leadingCoeff • AdjoinRoot.root (fQ f)) :=
  isIntegral_leadingCoeff_smul _ _ aeval_root_f

variable (f) in
/-- `θ = a · root`, an algebraic integer generating `K`. -/
def theta : 𝓞 (Kf f) := ⟨_, isIntegral_theta (f := f)⟩

theorem coe_theta : ((theta f : 𝓞 (Kf f)) : Kf f) =
    (f.leadingCoeff : Kf f) * AdjoinRoot.root (fQ f) := by
  change f.leadingCoeff • AdjoinRoot.root (fQ f) = _
  rw [Algebra.smul_def]; rfl

theorem adjoin_theta : Algebra.adjoin ℚ {((theta f : 𝓞 (Kf f)) : Kf f)} = ⊤ := by
  have ha : (f.leadingCoeff : ℚ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr f_ne_zero
  have h0 : AdjoinRoot.root (fQ f) ∈ Algebra.adjoin ℚ {((theta f : 𝓞 (Kf f)) : Kf f)} := by
    have : AdjoinRoot.root (fQ f) =
        algebraMap ℚ (Kf f) ((f.leadingCoeff : ℚ)⁻¹) * ((theta f : 𝓞 (Kf f)) : Kf f) := by
      rw [coe_theta, ← mul_assoc, ← map_intCast (algebraMap ℚ (Kf f)), ← map_mul,
        inv_mul_cancel₀ ha, map_one, one_mul]
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)
  rw [eq_top_iff]; intro x _
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have : AdjoinRoot.mk (fQ f) p = aeval (AdjoinRoot.root (fQ f)) p := by
      rw [mk_eq_eval₂, aeval_def, Subsingleton.elim (algebraMap ℚ (Kf f)) (AdjoinRoot.of (fQ f))]
    rw [this]
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr h0)) (aeval_mem_adjoin_singleton ℚ _)

theorem minpoly_theta : minpoly ℤ (theta f) = f.integralNormalization := by
  have hint : IsIntegral ℤ (theta f) := RingOfIntegers.isIntegral _
  have hm := minpoly.monic hint
  have hg : f.integralNormalization.Monic := monic_integralNormalization f_ne_zero
  have hroot : aeval (theta f) f.integralNormalization = 0 := by
    apply RingOfIntegers.coe_injective
    rw [← aeval_algebraMap_apply]
    simp only [map_zero]
    have := integralNormalization_aeval_eq_zero (aeval_root_f (f := f))
      (fun x hx => by simpa using hx)
    change aeval ((theta f : 𝓞 (Kf f)) : Kf f) _ = _
    rw [coe_theta]
    rwa [eq_intCast] at this
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hroot
  refine (eq_of_monic_of_dvd_of_natDegree_le hm hg hdvd ?_).symm
  rw [natDegree_integralNormalization]
  -- lower bound on the degree of the minimal polynomial: `m (a·root) = 0` forces `f ∣ m(aX)`
  set m := minpoly ℤ (theta f)
  have ha : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr f_ne_zero
  set q : ℚ[X] := (m.comp (C f.leadingCoeff * X)).map (Int.castRingHom ℚ) with hq
  have hmK : eval₂ (algebraMap ℤ (Kf f)) ((theta f : 𝓞 (Kf f)) : Kf f) m = 0 := by
    have h := minpoly.aeval ℤ (theta f)
    have h2 := congrArg (algebraMap (𝓞 (Kf f)) (Kf f)) h
    rw [← aeval_algebraMap_apply, map_zero] at h2
    rwa [aeval_def] at h2
  have hq0 : AdjoinRoot.mk (fQ f) q = 0 := by
    rw [mk_eq_eval₂, hq, eval₂_map, eval₂_comp]
    rw [coe_theta, RingHom.ext_int (algebraMap ℤ (Kf f))
      ((AdjoinRoot.of (fQ f)).comp (Int.castRingHom ℚ))] at hmK
    convert hmK using 2
    all_goals first
      | rfl
      | (simp only [eval₂_mul, eval₂_X]
         exact congrArg (· * AdjoinRoot.root (fQ f)) (map_intCast (eval₂RingHom _ _) _))
  rw [AdjoinRoot.mk_eq_zero] at hq0
  have hqdeg : q.natDegree = m.natDegree := by
    rw [hq, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_comp,
      natDegree_C_mul_X _ ha, mul_one]
  have hqne : q ≠ 0 := by
    intro h0
    have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
    rw [h0, natDegree_zero] at hqdeg
    omega
  have := natDegree_le_of_dvd hq0 hqne
  rw [natDegree_fQ, hqdeg] at this
  exact this

end setup

theorem exists_theta (f : ℤ[X]) (hfi : Irreducible (fQ f)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : 𝓞 K),
      minpoly ℤ θ = f.integralNormalization ∧ RingOfIntegers.exponent θ ≠ 0 := by
  have := Fact.mk hfi
  exact ⟨Kf f, inferInstance, inferInstance, theta f, minpoly_theta, exponent_ne_zero adjoin_theta⟩

end LaneC976

end

/-! Part 2: a Chebyshev–Mertens upper bound for families of pairwise coprime ideals of a
number field, from the ideal-counting asymptotic `#{I ≠ 0 : N I ≤ s} ~ κ s` (Mathlib). -/

noncomputable section
open Filter Topology Ideal NumberField Finset
open scoped nonZeroDivisors

namespace LaneC976

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The number of nonzero ideals of `𝓞 K` of norm at most `n`. -/
def cnt (n : ℕ) : ℕ :=
  #{I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset | I ≠ ⊥}

theorem cnt_eq_natCard (n : ℕ) :
    cnt K n = Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ I ∈ (Ideal (𝓞 K))⁰)
    (fun I ↦ absNorm I ≤ n))]
  have hfin : {I : Ideal (𝓞 K) | I ∈ (Ideal (𝓞 K))⁰ ∧ absNorm I ≤ n}.Finite :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  change cnt K n = Nat.card ({I | I ∈ (Ideal (𝓞 K))⁰ ∧ absNorm I ≤ n} : Set _)
  rw [Nat.card_eq_card_finite_toFinset hfin, cnt]
  congr 1
  ext I
  simp [mem_nonZeroDivisors_iff_ne_zero, and_comm]

theorem mem_cnt {n : ℕ} {I : Ideal (𝓞 K)} :
    I ∈ ({I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset | I ≠ ⊥} : Finset _) ↔
      I ≠ ⊥ ∧ absNorm I ≤ n := by
  simp [and_comm]

/-- Double counting. -/
theorem double_count {α : Type*} (ι : Finset α) (J : α → Ideal (𝓞 K)) (N : α → ℕ)
    (hN : ∀ i ∈ ι, absNorm (J i) = N i) (hN1 : ∀ i ∈ ι, N i ≠ 0)
    (hcop : ∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → J i ⊔ J j = ⊤) (n : ℕ) :
    ∑ i ∈ ι, Real.log (N i) * cnt K (n / N i) ≤ cnt K n * Real.log n := by
  classical
  set A : ℕ → Finset (Ideal (𝓞 K)) :=
    fun m ↦ {I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) m).toFinset | I ≠ ⊥} with hA
  have hcntA : ∀ m, cnt K m = #(A m) := fun m ↦ rfl
  -- step 1: injection `𝔟 ↦ J i * 𝔟`
  have step1 : ∀ i ∈ ι, (cnt K (n / N i) : ℝ) ≤ #{I ∈ A n | J i ∣ I} := by
    intro i hi
    rw [hcntA]
    have hJ0 : J i ≠ ⊥ := by
      intro h; apply hN1 i hi; rw [← hN i hi, h, absNorm_bot]
    exact_mod_cast Finset.card_le_card_of_injOn (fun I ↦ J i * I)
      (fun I hI ↦ by
        rw [Finset.mem_coe, mem_cnt] at hI
        rw [Finset.mem_coe, Finset.mem_filter, mem_cnt]
        refine ⟨⟨mul_ne_zero hJ0 hI.1, ?_⟩, dvd_mul_right _ _⟩
        rw [map_mul, hN i hi]
        calc N i * absNorm I ≤ N i * (n / N i) := Nat.mul_le_mul_left _ hI.2
          _ ≤ n := Nat.mul_div_le n (N i))
      (fun I _ I' _ h ↦ mul_left_cancel₀ hJ0 h)
  -- step 2: for each ideal, the norms of the `J i` dividing it multiply to at most its norm
  have step2 : ∀ I ∈ A n, ∑ i ∈ ι with J i ∣ I, Real.log (N i) ≤ Real.log n := by
    intro I hI
    rw [mem_cnt] at hI
    have hprod : (∏ i ∈ ι with J i ∣ I, J i) ∣ I := by
      refine Finset.prod_dvd_of_coprime ?_ (fun i hi ↦ (Finset.mem_filter.mp hi).2)
      intro i hi j hj hij
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      exact hcop i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
    have h1 := map_dvd absNorm hprod
    rw [map_prod] at h1
    have hI0 : absNorm I ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff]; exact hI.1
    have h2 : ∏ i ∈ ι with J i ∣ I, N i ≤ n := by
      calc ∏ i ∈ ι with J i ∣ I, N i = ∏ i ∈ ι with J i ∣ I, absNorm (J i) :=
            Finset.prod_congr rfl fun i hi ↦ (hN i (Finset.mem_filter.mp hi).1).symm
        _ ≤ absNorm I := Nat.le_of_dvd (Nat.pos_of_ne_zero hI0) h1
        _ ≤ n := hI.2
    have hpos : ∀ i ∈ ({i ∈ ι | J i ∣ I} : Finset α), (0 : ℝ) < N i := fun i hi ↦ by
      exact_mod_cast Nat.pos_of_ne_zero (hN1 i (Finset.mem_filter.mp hi).1)
    rw [← Real.log_prod (fun i hi ↦ (hpos i hi).ne')]
    apply Real.log_le_log (Finset.prod_pos hpos)
    exact_mod_cast h2
  calc ∑ i ∈ ι, Real.log (N i) * cnt K (n / N i)
      ≤ ∑ i ∈ ι, Real.log (N i) * #{I ∈ A n | J i ∣ I} := by
        refine Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (step1 i hi) ?_
        exact Real.log_natCast_nonneg _
    _ = ∑ I ∈ A n, ∑ i ∈ ι with J i ∣ I, Real.log (N i) := by
        simp_rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun I _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs <;> simp
    _ ≤ ∑ I ∈ A n, Real.log n := Finset.sum_le_sum step2
    _ = cnt K n * Real.log n := by rw [Finset.sum_const, nsmul_eq_mul, hcntA]

variable (K) in
theorem tendsto_cnt :
    Tendsto (fun n : ℕ ↦ (cnt K n : ℝ) / n) atTop (𝓝 (dedekindZeta_residue K)) := by
  have h := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  rw [← dedekindZeta_residue_def] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, cnt_eq_natCard]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ by simp)

variable (K) in
/-- Mertens-type upper bound `∑ log N(J)/N(J) ≤ (3/2) log n` for pairwise coprime ideals
of norm at most `n / M`. -/
theorem mertens_ideal : ∃ M : ℕ, 10 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ {α : Type} (ι : Finset α)
    (J : α → Ideal (𝓞 K)) (N : α → ℕ), (∀ i ∈ ι, absNorm (J i) = N i) →
    (∀ i ∈ ι, N i ≠ 0) → (∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → J i ⊔ J j = ⊤) →
    (∀ i ∈ ι, N i * M ≤ n) →
    ∑ i ∈ ι, Real.log (N i) / N i ≤ 3 / 2 * Real.log n := by
  set κ := dedekindZeta_residue K
  have hκ : 0 < κ := dedekindZeta_residue_pos K
  have hev := (tendsto_cnt K).eventually (Icc_mem_nhds (show 9 / 10 * κ < κ by linarith)
    (show κ < 11 / 10 * κ by linarith))
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hev
  refine ⟨max M0 10 + 1, by omega, fun n hn α ι J N hN hN1 hcop hle ↦ ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlow : ∀ m : ℕ, M0 ≤ m → 0 < m → 9 / 10 * κ * m ≤ cnt K m := by
    intro m hm hm0
    have := (hM0 m hm).1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    rwa [le_div_iff₀ hm'] at this
  have hup : (cnt K n : ℝ) ≤ 11 / 10 * κ * n := by
    have := (hM0 n (by omega)).2
    rwa [div_le_iff₀ hnpos] at this
  have hdc := double_count ι J N hN hN1 hcop n
  -- lower bound for each term
  have hterm : ∀ i ∈ ι, 81 / 100 * κ * n * (Real.log (N i) / N i) ≤
      Real.log (N i) * cnt K (n / N i) := by
    intro i hi
    have hNi : (0 : ℝ) < N i := by exact_mod_cast Nat.pos_of_ne_zero (hN1 i hi)
    have hm : max M0 10 + 1 ≤ n / N i :=
      (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (hN1 i hi))).mpr (by linarith [hle i hi])
    have h1 := hlow (n / N i) (by omega) (by omega)
    have h2 : (n : ℝ) / N i - 1 ≤ ((n / N i : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (hN1 i hi))
      rw [sub_le_iff_le_add, div_le_iff₀ hNi]
      exact_mod_cast (by nlinarith [this] : n ≤ (n / N i + 1) * N i)
    have h3 : (10 : ℝ) ≤ (n : ℝ) / N i := by
      have : ((10 : ℕ) : ℝ) ≤ ((n / N i : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have := Nat.cast_div_le (m := n) (n := N i) (α := ℝ)
      push_cast at *; linarith
    have hlog : 0 ≤ Real.log (N i) := Real.log_natCast_nonneg _
    have h4 : 81 / 100 * κ * n / N i ≤ cnt K (n / N i) := by
      calc 81 / 100 * κ * n / N i = 9 / 10 * κ * (9 / 10 * (n / N i)) := by ring
        _ ≤ 9 / 10 * κ * ((n : ℝ) / N i - 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ ≤ 9 / 10 * κ * ((n / N i : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ _ := h1
    calc 81 / 100 * κ * n * (Real.log (N i) / N i) = Real.log (N i) * (81 / 100 * κ * n / N i) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hlog
  have hsum : 81 / 100 * κ * n * ∑ i ∈ ι, Real.log (N i) / N i ≤ 11 / 10 * κ * n * Real.log n := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ i ∈ ι, Real.log (N i) * cnt K (n / N i) := Finset.sum_le_sum hterm
      _ ≤ cnt K n * Real.log n := hdc
      _ ≤ 11 / 10 * κ * n * Real.log n :=
          mul_le_mul_of_nonneg_right hup (Real.log_natCast_nonneg _)
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  have hc : 0 < 81 / 100 * κ * n := by positivity
  have : ∑ i ∈ ι, Real.log (N i) / N i ≤ (110 / 81) * Real.log n := by
    rw [← mul_le_mul_iff_of_pos_left hc]
    calc _ ≤ _ := hsum
      _ = 81 / 100 * κ * n * ((110 / 81) * Real.log n) := by ring
  linarith

end LaneC976

end

/-! Part 3: local counting. Bezout `f u + f' v = D`, clustering of the solutions of
`p^j ∣ f(k)`, and the bound on `#{k ≤ n : p^j ∣ f(k)}`. -/

noncomputable section
open Polynomial Finset

namespace LaneC976

/-- Bezout identity with a nonzero integer, from the resultant of `f` and `f'`. -/
theorem exists_bezout (f : ℤ[X]) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) :
    ∃ u v : ℤ[X], ∃ D : ℤ, D ≠ 0 ∧ f * u + derivative f * v = C D := by
  obtain ⟨u, v, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant f (derivative f) le_rfl le_rfl
    (Or.inl (by omega))
  refine ⟨u, v, _, ?_, h⟩
  have hinj := RingHom.injective_int (Int.castRingHom ℚ)
  intro h0
  have hsep : (f.map (Int.castRingHom ℚ)).Separable := hf.separable
  have hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (derivative (f.map (Int.castRingHom ℚ))) :=
    hsep
  have h1 := resultant_ne_zero _ _ hcop
  rw [derivative_map] at h1
  have e1 : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective hinj f
  have e2 : ((derivative f).map (Int.castRingHom ℚ)).natDegree = (derivative f).natDegree :=
    natDegree_map_eq_of_injective hinj _
  apply h1
  have := resultant_map_map f (derivative f) f.natDegree (derivative f).natDegree
    (Int.castRingHom ℚ)
  rw [h0, map_zero] at this
  rw [e1, e2]; exact this

/-- Clustering of solutions of `p^j ∣ f(x)` (Hensel-type, via the Bezout identity). -/
theorem cluster {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) {δ j : ℕ} (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D) (hj : δ + 1 ≤ j)
    {x y : ℤ} (hx : (p : ℤ) ^ j ∣ f.eval x) (hy : (p : ℤ) ^ j ∣ f.eval y)
    (hxy : (p : ℤ) ^ (δ + 1) ∣ y - x) : (p : ℤ) ^ (j - δ) ∣ y - x := by
  have hD : f.eval x * u.eval x + (derivative f).eval x * v.eval x = D := by
    have := congrArg (eval x) hB; simpa using this
  have hpd : ¬ (p : ℤ) ^ (δ + 1) ∣ (derivative f).eval x := by
    intro h; apply hδ; rw [← hD]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hj) hx) _)
      (dvd_mul_of_dvd_left h _)
  obtain ⟨w, hw⟩ := binomExpansion f x (y - x)
  set U := (derivative f).eval x + w * (y - x) with hUdef
  have hfy : f.eval y - f.eval x = (y - x) * U := by
    have : x + (y - x) = y := by ring
    rw [this] at hw; rw [hw, hUdef]; ring
  have hU : ¬ (p : ℤ) ^ (δ + 1) ∣ U := by
    intro h; apply hpd
    have : (derivative f).eval x = U - w * (y - x) := by rw [hUdef]; ring
    rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hxy _)
  have hdiv : (p : ℤ) ^ j ∣ (y - x) * U := hfy ▸ dvd_sub hy hx
  by_cases hyx : y - x = 0
  · rw [hyx]; exact dvd_zero _
  have hU0 : U ≠ 0 := by rintro h; exact hU (h ▸ dvd_zero _)
  haveI := Fact.mk hp
  have h1 := (padicValInt_dvd_iff (p := p) j ((y - x) * U)).mp hdiv
  rcases h1 with h1 | h1
  · exact absurd h1 (mul_ne_zero hyx hU0)
  rw [padicValInt.mul hyx hU0] at h1
  have h2 : padicValInt p U ≤ δ := by
    by_contra h2
    exact hU ((padicValInt_dvd_iff (p := p) (δ + 1) U).mpr (Or.inr (by omega)))
  exact (padicValInt_dvd_iff (p := p) (j - δ) (y - x)).mpr (Or.inr (by omega))

/-- A set of naturals `≤ n`, pairwise congruent mod `L`, has at most `n / L + 1` elements. -/
theorem card_le_of_modEq {S : Finset ℕ} {n L : ℕ} (hL : 0 < L) (hS : ∀ k ∈ S, k ≤ n)
    (h : ∀ k ∈ S, ∀ k' ∈ S, k ≡ k' [MOD L]) : #S ≤ n / L + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set k0 := S.min' hne
  have hk0 : k0 ∈ S := S.min'_mem hne
  have hdvd : ∀ k ∈ S, L ∣ k - k0 := fun k hk ↦
    (Nat.modEq_iff_dvd' (S.min'_le k hk)).mp (h k0 hk0 k hk)
  calc #S ≤ #(range (n / L + 1)) := by
        refine card_le_card_of_injOn (fun k ↦ (k - k0) / L) (fun k hk ↦ ?_) (fun k hk k' hk' e ↦ ?_)
        · simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right ((Nat.sub_le _ _).trans (hS k hk)))
        · have h1 := Nat.div_mul_cancel (hdvd k hk)
          have h2 := Nat.div_mul_cancel (hdvd k' hk')
          simp only at e
          have hle := S.min'_le k hk
          have hle' := S.min'_le k' hk'
          rw [e] at h1
          omega
    _ = n / L + 1 := card_range _

/-- The number of `k ≤ n` with `p^j ∣ f(k)`. -/
theorem card_pow_dvd_le {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) {δ j : ℕ} (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D) (hj : δ + 1 ≤ j)
    (n : ℕ) (R : Finset ℕ)
    (hR : ∀ k ∈ Icc 1 n, (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ) → k % p ^ (δ + 1) ∈ R) :
    #{k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} ≤ #R * (n / p ^ (j - δ) + 1) := by
  classical
  set S := {k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} with hSdef
  have hpos : 0 < p ^ (j - δ) := pow_pos hp.pos _
  calc #S ≤ (n / p ^ (j - δ) + 1) * #(S.image (· % p ^ (δ + 1))) := by
        refine card_le_mul_card_image S _ fun a _ ↦ card_le_of_modEq hpos ?_ ?_
        · intro k hk
          exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1).2
        · intro k hk k' hk'
          obtain ⟨hk1, hka⟩ := Finset.mem_filter.mp hk
          obtain ⟨hk1', hka'⟩ := Finset.mem_filter.mp hk'
          have hm : k ≡ k' [MOD p ^ (δ + 1)] := hka.trans hka'.symm
          rw [Nat.modEq_iff_dvd] at hm ⊢
          push_cast at hm ⊢
          exact cluster hB hp hδ hj (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk1').2 hm
    _ ≤ (n / p ^ (j - δ) + 1) * #R := by
        refine Nat.mul_le_mul_left _ (card_le_card fun a ha ↦ ?_)
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
        exact hR k hk1 hk2
    _ = #R * (n / p ^ (j - δ) + 1) := mul_comm _ _

/-- The sum over `k ≤ n` of the `p`-adic valuations of `f(k)`, as a sum over prime powers. -/
theorem sum_factorization_eq (f : ℤ[X]) (n p b : ℕ) (hp : p.Prime)
    (hf0 : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0) (hb : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs < p ^ b) :
    ∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p =
      ∑ j ∈ Ico 1 b, #{k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} := by
  classical
  rw [Finset.sum_congr rfl fun k hk ↦ Nat.factorization_eq_card_pow_dvd_of_lt hp
    (Int.natAbs_pos.mpr (hf0 k hk)) (hb k hk)]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  simp only [eq_iff_iff]
  rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
  push_cast; rfl

end LaneC976

end

/-! Part 4: elementary facts about `f` (no integer roots, size of `f(k)`), and `log n!`. -/

noncomputable section
open Polynomial Finset Real Filter

namespace LaneC976

theorem eval_ne_zero {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (k : ℤ) :
    f.eval k ≠ 0 := by
  intro h
  have hdvd : X - C k ∣ f := dvd_iff_isRoot.mpr h
  obtain ⟨g, hg⟩ := hdvd
  rcases hf.isUnit_or_isUnit hg with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at this; exact one_ne_zero this
  · have h0 : g ≠ 0 := by rintro rfl; simp at hg; exact hf.ne_zero hg
    have := natDegree_eq_zero_of_isUnit hu
    have h2 := congrArg natDegree hg
    rw [natDegree_mul (X_sub_C_ne_zero k) h0, natDegree_X_sub_C, this] at h2
    omega

/-- `|f(k)| ≤ S k^d` for `k ≥ 1`. -/
theorem natAbs_eval_le (f : ℤ[X]) : ∃ S : ℕ, 1 ≤ S ∧ ∀ k : ℕ, 1 ≤ k →
    (f.eval ((k : ℕ) : ℤ)).natAbs ≤ S * k ^ f.natDegree := by
  refine ⟨∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs + 1, by omega, fun k hk ↦ ?_⟩
  have h1 : (f.eval ((k : ℕ) : ℤ)).natAbs ≤ ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ i := by
    rw [eval_eq_sum_range]
    refine (Int.natAbs_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  refine h1.trans ?_
  calc ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ i
      ≤ ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs * k ^ f.natDegree :=
        Finset.sum_le_sum fun i hi ↦ Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = (∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs) * k ^ f.natDegree := by
        rw [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- `d log k - C ≤ log |f(k)|` for all `k ≥ 1`. -/
theorem log_abs_eval_ge {f : ℤ[X]} (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → f.natDegree * Real.log k - C ≤ Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
  set fR := f.map (Int.castRingHom ℝ)
  have hlead : fR.leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_map_of_injective (RingHom.injective_int _)]; rfl
  have hdeg : fR.natDegree = f.natDegree := natDegree_map_eq_of_injective (RingHom.injective_int _) _
  have ha : (f.leadingCoeff : ℝ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hf.ne_zero
  have hequiv := Polynomial.isEquivalent_atTop_lead fR
  rw [hlead, hdeg] at hequiv
  have hz : ∀ᶠ x : ℝ in atTop, (f.leadingCoeff : ℝ) * x ^ f.natDegree ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_ne_zero ha (pow_ne_zero _ hx.ne')
  have htend := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hequiv
  have hev : ∀ᶠ x : ℝ in atTop, 1 / 2 ≤ fR.eval x / (f.leadingCoeff * x ^ f.natDegree) := by
    have := htend.eventually (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    filter_upwards [this] with x hx
    simpa using hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 1))
  set k0 := ⌈x0⌉₊
  have hla : 1 ≤ |(f.leadingCoeff : ℝ)| := by
    have : (1 : ℝ) ≤ |f.leadingCoeff| := by exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hf.ne_zero)
    simpa using this
  refine ⟨f.natDegree * Real.log (k0 + 1) + Real.log 2, fun k hk ↦ ?_⟩
  have hfk : (1 : ℝ) ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (eval_ne_zero hf hd (k : ℤ))
  have hlogf : 0 ≤ Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := Real.log_nonneg hfk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hkk : (k : ℝ) < x0
  · have : Real.log k ≤ Real.log (k0 + 1) := by
      apply Real.log_le_log (by linarith)
      have := Nat.le_ceil x0; linarith
    have hd0 : (0 : ℝ) ≤ f.natDegree := by positivity
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num), mul_le_mul_of_nonneg_left this hd0]
  · push_neg at hkk
    obtain ⟨h1, -⟩ := hx0 k hkk
    have hpos : 0 < (k : ℝ) ^ f.natDegree := by positivity
    have heval : fR.eval (k : ℝ) = ((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ) := by
      simp [fR, eval_map]
    rw [heval] at h1
    have h2 : |(f.leadingCoeff : ℝ)| * (k : ℝ) ^ f.natDegree / 2 ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
      set F := ((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)
      set A := (f.leadingCoeff : ℝ) * (k : ℝ) ^ f.natDegree
      have hA : A ≠ 0 := mul_ne_zero ha hpos.ne'
      have e1 : |F| = |F / A| * |A| := by
        rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hA)]
      have e2 : 1 / 2 ≤ |F / A| := le_trans h1 (le_abs_self _)
      have e3 : |A| = |(f.leadingCoeff : ℝ)| * (k : ℝ) ^ f.natDegree := by
        rw [abs_mul, abs_of_pos hpos]
      rw [e1, ← e3]
      nlinarith [abs_nonneg A]
    have h4 : (k : ℝ) ^ f.natDegree / 2 ≤ |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
      refine le_trans ?_ h2
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    have h5 := Real.log_le_log (by positivity) h4
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h5
    have : 0 ≤ f.natDegree * Real.log (k0 + 1) := by
      have : (0 : ℝ) ≤ Real.log (k0 + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k0; linarith)
      positivity
    linarith

theorem log_factorial_ge (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hf] at h
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at this
  linarith

end LaneC976

end

/-! Part 5: `∑ log |f(k)|` as a sum over primes, and the bound for each prime. -/

noncomputable section
open Polynomial Finset

namespace LaneC976

theorem sum_log_eq (f : ℤ[X]) (n P : ℕ) (hf0 : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0)
    (hP : ∀ p, p.Prime → p ∣ (∏ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ)).natAbs → p ≤ P) :
    ∑ k ∈ Icc 1 n, Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| =
      ∑ p ∈ Nat.primesLE P,
        ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) * Real.log p := by
  classical
  set N := (∏ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ)).natAbs with hN
  have hN' : N = ∏ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs := by rw [hN]; exact map_prod Int.natAbsHom _ _
  have hne : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs ≠ 0 := fun k hk ↦ Int.natAbs_ne_zero.mpr (hf0 k hk)
  have h1 : ∑ k ∈ Icc 1 n, Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| = Real.log N := by
    rw [hN', Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Nat.cast_natAbs, Int.cast_abs]
    · intro k hk; exact_mod_cast hne k hk
  rw [h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hfac : ∀ p, N.factorization p = ∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p := by
    intro p
    rw [hN', Nat.factorization_prod hne, Finsupp.finsetSum_apply]
  rw [Finset.sum_subset (s₁ := N.factorization.support) (s₂ := Nat.primesLE P)]
  · refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [hfac]
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    rw [Nat.mem_primesLE]
    exact ⟨hP p hp' (Nat.dvd_of_mem_primeFactors hp), hp'⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]; simp

/-- Bound for the total `p`-adic valuation. -/
theorem ep_le {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) (δ : ℕ) (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D) (n H : ℕ)
    (hf0 : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0)
    (hH : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs ≤ H) (R : Finset ℕ)
    (hR : ∀ k ∈ Icc 1 n, ∀ j, δ + 1 ≤ j → (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ) → k % p ^ (δ + 1) ∈ R) :
    ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) ≤
      δ * n + #R * (n / (p - 1) + Nat.log p H) := by
  classical
  set b := Nat.log p H + 1
  have hb : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs < p ^ b :=
    fun k hk ↦ (hH k hk).trans_lt (Nat.lt_pow_succ_log_self hp.one_lt H)
  rw [sum_factorization_eq f n p b hp hf0 hb]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set g : ℕ → ℝ := fun j ↦ if j ≤ δ then (n : ℝ) else #R * (n * (p : ℝ) ^ δ * (1 / p) ^ j + 1)
  have hj : ∀ j ∈ Ico 1 b, (#{k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} : ℝ) ≤ g j := by
    intro j _
    simp only [g]
    split_ifs with hjd
    · have : #{k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} ≤ n := by
        calc _ ≤ #(Icc 1 n) := card_filter_le _ _
          _ = n := by simp
      exact_mod_cast this
    · push_neg at hjd
      have h1 := card_pow_dvd_le hB hp hδ hjd n R (fun k hk h ↦ hR k hk j hjd h)
      have h2 : ((n / p ^ (j - δ) : ℕ) : ℝ) ≤ n * (p : ℝ) ^ δ * (1 / p) ^ j := by
        refine (Nat.cast_div_le).trans (le_of_eq ?_)
        have hpow : (p : ℝ) ^ (j - δ) * (p : ℝ) ^ δ = (p : ℝ) ^ j := pow_sub_mul_pow _ hjd.le
        have hpj : (0 : ℝ) < (p : ℝ) ^ (j - δ) := by positivity
        rw [one_div, inv_pow, Nat.cast_pow, div_eq_iff hpj.ne']
        rw [mul_assoc, mul_assoc, ← hpow]
        field_simp
      calc (#{k ∈ Icc 1 n | (p : ℤ) ^ j ∣ f.eval ((k : ℕ) : ℤ)} : ℝ) ≤
            (#R * (n / p ^ (j - δ) + 1) : ℕ) := by exact_mod_cast h1
        _ ≤ #R * (n * (p : ℝ) ^ δ * (1 / p) ^ j + 1) := by
            push_cast
            exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  push_cast
  refine (Finset.sum_le_sum hj).trans ?_
  simp only [g]
  rw [Finset.sum_ite]
  have hA : #{j ∈ Ico 1 b | j ≤ δ} ≤ δ := by
    calc #{j ∈ Ico 1 b | j ≤ δ} ≤ #(Icc 1 δ) := card_le_card fun j hj ↦ by
          simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
      _ = δ := by simp
  have hB' : ({j ∈ Ico 1 b | ¬ j ≤ δ} : Finset ℕ) = Ico (δ + 1) b := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [hB', Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hgeom : ∑ j ∈ Ico (δ + 1) b, (1 / (p : ℝ)) ^ j ≤ (1 / p) ^ (δ + 1) / (1 - 1 / p) :=
    geom_sum_Ico_le_of_lt_one (by positivity) (by rw [div_lt_one hp0]; exact hp1)
  have hval : (n : ℝ) * p ^ δ * ((1 / p) ^ (δ + 1) / (1 - 1 / p)) = n / (p - 1) := by
    have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
    have e : (1 - 1 / (p : ℝ)) = (p - 1) / p := by field_simp
    rw [e, one_div_pow, pow_succ]
    field_simp
  have hcard : (#(Ico (δ + 1) b) : ℝ) ≤ Nat.log p H := by
    have : #(Ico (δ + 1) b) ≤ Nat.log p H := by simp [b]
    exact_mod_cast this
  have h1 : (#{j ∈ Ico 1 b | j ≤ δ} : ℝ) * n ≤ δ * n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (Nat.cast_nonneg _)
  have h2 : (n : ℝ) * p ^ δ * ∑ j ∈ Ico (δ + 1) b, (1 / (p : ℝ)) ^ j ≤ n / (p - 1) := by
    rw [← hval]; exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  have h3 : (0 : ℝ) ≤ #R := Nat.cast_nonneg _
  nlinarith

end LaneC976

end

/-! Part 6: the concrete Mertens bound for `ρ(p) = #{c < p : p ∣ f(c)}`, and small lemmas. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

/-- The number of roots of `f` modulo `p` in `[0, p)`. -/
def rho (f : ℤ[X]) (p : ℕ) : ℕ := #{c ∈ range p | (p : ℤ) ∣ f.eval ((c : ℕ) : ℤ)}

theorem rho_le {f : ℤ[X]} {p : ℕ} (hp : p.Prime) (hpa : ¬ (p : ℤ) ∣ f.leadingCoeff) :
    rho f p ≤ f.natDegree := by
  classical
  haveI := Fact.mk hp
  set g := f.map (Int.castRingHom (ZMod p)) with hgdef
  have hlc : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    rwa [Ne, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hg : g.natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero _ hlc
  have hg0 : g ≠ 0 := by
    intro h
    have : g.leadingCoeff = 0 := by rw [h, leadingCoeff_zero]
    rw [hgdef, leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc] at this
    exact hlc this
  calc rho f p ≤ #(g.roots.toFinset) := by
        refine card_le_card_of_injOn (fun c : ℕ ↦ (c : ZMod p)) (fun c hc ↦ ?_) (fun c hc c' hc' e ↦ ?_)
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hg0, IsRoot]
          simp only
          rw [show ((c : ℕ) : ZMod p) = ((c : ℤ) : ZMod p) by simp, hgdef, eval_intCast_map,
            eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hc.2
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc hc'
          simp only at e
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc'.1] at e
          exact e
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' g
    _ = f.natDegree := hg

theorem dvd_eval_mod {f : ℤ[X]} {p k : ℕ} (h : (p : ℤ) ∣ f.eval (k : ℤ)) :
    (p : ℤ) ∣ f.eval ((k % p : ℕ) : ℤ) := by
  have h1 := sub_dvd_eval_sub ((k % p : ℕ) : ℤ) (k : ℤ) f
  have h2 : (p : ℤ) ∣ ((k % p : ℕ) : ℤ) - k := by
    rw [Int.natCast_mod]
    have := (Int.mod_modEq (k : ℤ) p).dvd
    rw [← dvd_neg, neg_sub]; exact this
  have h3 := dvd_trans h2 h1
  have := dvd_add h3 h
  simpa using this

end LaneC976

end

/-! Part 7: the Mertens bound `∑_{p ≤ n good} ρ(p) log p / p ≤ (3/2) log n + C`. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

theorem mertens_rho {f : ℤ[X]} (hd : 1 ≤ f.natDegree) {K : Type} [Field K] [NumberField K]
    {θ : 𝓞 K} (hmin : minpoly ℤ θ = f.integralNormalization) (Bad : Finset ℕ)
    (hgood : ∀ p, p.Prime → p ∉ Bad →
      ¬ (p : ℤ) ∣ f.leadingCoeff ∧ ¬ p ∣ RingOfIntegers.exponent θ)
    {M : ℕ} (hM : ∀ n : ℕ, M ≤ n → ∀ {α : Type} (ι : Finset α)
      (J : α → Ideal (𝓞 K)) (N : α → ℕ), (∀ i ∈ ι, absNorm (J i) = N i) →
      (∀ i ∈ ι, N i ≠ 0) → (∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → J i ⊔ J j = ⊤) →
      (∀ i ∈ ι, N i * M ≤ n) →
      ∑ i ∈ ι, Real.log (N i) / N i ≤ 3 / 2 * Real.log n)
    (n : ℕ) (hn : M ≤ n) (hM1 : 1 ≤ M) :
    ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log p / p ≤
      3 / 2 * Real.log n + f.natDegree * M * Real.log 4 := by
  classical
  set a := f.leadingCoeff
  set ι : Finset (ℕ × ℕ) := (Nat.primesLE n ×ˢ range n).filter
    (fun x ↦ x.1 ∉ Bad ∧ x.1 * M ≤ n ∧ x.2 < x.1 ∧ (x.1 : ℤ) ∣ f.eval ((x.2 : ℕ) : ℤ)) with hι
  set J : ℕ × ℕ → Ideal (𝓞 K) :=
    fun x ↦ span {((x.1 : ℕ) : 𝓞 K), θ - ((a * (x.2 : ℤ) : ℤ) : 𝓞 K)} with hJ
  have hmem : ∀ x ∈ ι, x.1.Prime ∧ x.1 ∉ Bad ∧ x.1 * M ≤ n ∧ x.2 < x.1 ∧
      (x.1 : ℤ) ∣ f.eval ((x.2 : ℕ) : ℤ) := by
    intro x hx
    rw [hι, Finset.mem_filter, Finset.mem_product, Nat.primesLE, Nat.mem_primesBelow] at hx
    exact ⟨hx.1.1.2, hx.2⟩
  have hnorm : ∀ x ∈ ι, absNorm (J x) = x.1 := by
    intro x hx
    obtain ⟨hp, hbad, -, -, hdvd⟩ := hmem x hx
    haveI := Fact.mk hp
    refine absNorm_span_pair (hgood _ hp hbad).2 ?_
    rw [hmin]
    have := integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id ℤ) ((x.2 : ℕ) : ℤ)
    change f.integralNormalization.eval (a * (x.2 : ℤ)) =
      a ^ (f.natDegree - 1) * f.eval ((x.2 : ℕ) : ℤ) at this
    rw [this]
    exact dvd_mul_of_dvd_right hdvd _
  have hcop : ∀ x ∈ ι, ∀ y ∈ ι, x ≠ y → J x ⊔ J y = ⊤ := by
    intro x hx y hy hxy
    obtain ⟨hp, hbad, -, hc, -⟩ := hmem x hx
    obtain ⟨hq, -, -, hc', -⟩ := hmem y hy
    exact sup_span_pair_eq_top θ a hp hq hc hc' (hgood _ hp hbad).1 (by
      intro h; apply hxy; exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have h1 := hM n hn ι J (fun x ↦ x.1) hnorm (fun x hx ↦ (hmem x hx).1.ne_zero) hcop
    (fun x hx ↦ (hmem x hx).2.2.1)
  -- rewrite the sum over pairs as a sum over primes
  have h_eq : ∑ x ∈ ι, Real.log (x.1 : ℕ) / (x.1 : ℕ) =
      ∑ p ∈ Nat.primesLE n with p ∉ Bad ∧ p * M ≤ n, (rho f p : ℝ) * Real.log p / p := by
    rw [hι, Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hpn : p ≤ n := by
      rw [Nat.primesLE, Nat.mem_primesBelow] at hp; omega
    by_cases h : p ∉ Bad ∧ p * M ≤ n
    · rw [if_pos h, ← Finset.sum_filter]
      dsimp only
      rw [Finset.sum_const, nsmul_eq_mul, rho]
      have : ((range n).filter fun c ↦ p ∉ Bad ∧ p * M ≤ n ∧ c < p ∧
          (p : ℤ) ∣ f.eval ((c : ℕ) : ℤ)) = (range p).filter fun c ↦ (p : ℤ) ∣ f.eval ((c : ℕ) : ℤ) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨-, -, -, h3, h4⟩; exact ⟨h3, h4⟩
        · rintro ⟨h3, h4⟩; exact ⟨by omega, h.1, h.2, h3, h4⟩
      rw [this]; ring
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      rw [if_neg]; tauto
  -- the tail `p > n / M`
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htail : ∑ p ∈ Nat.primesLE n with p ∉ Bad ∧ ¬ p * M ≤ n, (rho f p : ℝ) * Real.log p / p ≤
      f.natDegree * M * Real.log 4 := by
    calc ∑ p ∈ Nat.primesLE n with p ∉ Bad ∧ ¬ p * M ≤ n, (rho f p : ℝ) * Real.log p / p
        ≤ ∑ p ∈ Nat.primesLE n with p ∉ Bad ∧ ¬ p * M ≤ n, f.natDegree * M / n * Real.log p := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
          obtain ⟨⟨-, hpp⟩, hbad, hlt⟩ := hp
          have hr : (rho f p : ℝ) ≤ f.natDegree := by
            exact_mod_cast rho_le hpp (hgood p hpp hbad).1
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hlt' : (n : ℝ) < p * M := by exact_mod_cast (not_le.mp hlt)
          have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg _
          have key : (f.natDegree * Real.log p) * n ≤ (f.natDegree * Real.log p) * (p * M) :=
            mul_le_mul_of_nonneg_left hlt'.le (by positivity)
          have k2 : (rho f p : ℝ) * Real.log p ≤ f.natDegree * Real.log p :=
            mul_le_mul_of_nonneg_right hr hlog
          rw [div_le_iff₀ hp0, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hn0]
          nlinarith [key, k2]
      _ ≤ ∑ p ∈ Nat.primesLE n, f.natDegree * M / n * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ ↦ by have := Real.log_natCast_nonneg p; positivity)
      _ = f.natDegree * M / n * Chebyshev.theta n := by
          rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum]
      _ ≤ f.natDegree * M / n * (Real.log 4 * n) :=
          mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hn0.le) (by positivity)
      _ = f.natDegree * M * Real.log 4 := by field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not ((Nat.primesLE n).filter (· ∉ Bad))
    (fun p ↦ p * M ≤ n) (fun p ↦ (rho f p : ℝ) * Real.log p / p)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  rw [← hsplit, ← h_eq]
  have h1' : ∑ x ∈ ι, Real.log (x.1 : ℕ) / (x.1 : ℕ) ≤ 3 / 2 * Real.log n := h1
  linarith

end LaneC976

end

/-! Part 8: assembly. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

theorem eventually_absorb (A B : ℝ) : ∀ᶠ n : ℕ in atTop,
    A * n + B * ((Real.sqrt n + 1) * (1 + Real.log n)) ≤ 7 / 40 * (n * Real.log n) := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (80 * |A| / 7 + 1))
  have hsq := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (320 * |B| / 7 + 1))
  filter_upwards [hlog, hsq] with n h1 h2
  simp only [Function.comp_apply] at h1 h2
  set L := Real.log n
  set s := Real.sqrt (n : ℝ)
  have hs2 : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) h1
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) h2
  have hLA : 80 * |A| / 7 ≤ L := by linarith [le_trans (le_max_right _ _) h1]
  have hsB : 320 * |B| / 7 ≤ s := by linarith [le_trans (le_max_right _ _) h2]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : A * n ≤ 7 / 80 * (n * L) := by
    have : A * n ≤ |A| * n := mul_le_mul_of_nonneg_right (le_abs_self A) hn0
    nlinarith [abs_nonneg A]
  have e2 : B * ((s + 1) * (1 + L)) ≤ 7 / 80 * (n * L) := by
    have h3 : (s + 1) * (1 + L) ≤ 4 * (s * L) := by nlinarith
    have h4 : B * ((s + 1) * (1 + L)) ≤ |B| * (4 * (s * L)) := by
      calc B * ((s + 1) * (1 + L)) ≤ |B| * ((s + 1) * (1 + L)) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
        _ ≤ |B| * (4 * (s * L)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
    have h5 : |B| * (4 * (s * L)) ≤ 7 / 80 * (n * L) := by
      rw [← hs2]
      have : 4 * |B| ≤ 7 / 80 * s := by linarith
      have hsL : 0 ≤ s * L := by positivity
      nlinarith
    linarith
  linarith

end LaneC976

end

/-! Part 9: per-prime bounds in the form used by the assembly. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC976

theorem natLog_mul_log_le {p H : ℕ} (hH : 1 ≤ H) :
    (Nat.log p H : ℝ) * Real.log p ≤ Real.log H := by
  have := Nat.pow_log_le_self p (by omega : H ≠ 0)
  have h2 : ((p ^ Nat.log p H : ℕ) : ℝ) ≤ H := by exact_mod_cast this
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp; exact Real.log_natCast_nonneg _
  have h3 := Real.log_le_log (by positivity) h2
  rwa [Nat.cast_pow, Real.log_pow] at h3

theorem ep_log_good {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D) {p : ℕ}
    (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) (n H : ℕ) (hH0 : 1 ≤ H)
    (hf0 : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0)
    (hH : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs ≤ H) :
    ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) * Real.log p ≤
      rho f p * (n * Real.log p / (p - 1) + Real.log H) := by
  have h := ep_le hB hp 0 (by simpa using hpD) n H hf0 hH
    ((range p).filter fun c ↦ (p : ℤ) ∣ f.eval ((c : ℕ) : ℤ)) (by
      intro k _ j hj hdvd
      simp only [zero_add, pow_one, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt _ hp.pos, dvd_eval_mod (dvd_trans (dvd_pow_self _ (by omega)) hdvd)⟩)
  change _ ≤ (0 : ℕ) * (n : ℝ) + (rho f p : ℝ) * (n / (p - 1) + Nat.log p H) at h
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  have hNat := natLog_mul_log_le (p := p) hH0
  have hr : (0 : ℝ) ≤ rho f p := Nat.cast_nonneg _
  simp only [Nat.cast_zero, zero_mul, zero_add] at h
  calc _ ≤ (rho f p : ℝ) * (n / (p - 1) + Nat.log p H) * Real.log p :=
        mul_le_mul_of_nonneg_right h hlogp
    _ = rho f p * (n * Real.log p / (p - 1) + Nat.log p H * Real.log p) := by ring
    _ ≤ rho f p * (n * Real.log p / (p - 1) + Real.log H) := by gcongr

theorem ep_log_bad {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D) (hD : D ≠ 0)
    {p : ℕ} (hp : p.Prime) (n H : ℕ) (hH0 : 1 ≤ H)
    (hf0 : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0)
    (hH : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs ≤ H) :
    ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) * Real.log p ≤
      (((padicValInt p D : ℕ) + (p : ℝ) ^ (padicValInt p D + 1)) * Real.log p +
        (p : ℝ) ^ (padicValInt p D + 1)) * (n + Real.log H) := by
  haveI := Fact.mk hp
  set δ := padicValInt p D
  have hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D := by
    rw [padicValInt_dvd_iff]; push_neg; exact ⟨hD, by omega⟩
  have h := ep_le hB hp δ hδ n H hf0 hH (range (p ^ (δ + 1)))
    (fun k _ _ _ _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos hp.pos _)))
  rw [card_range] at h
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  have hNat := natLog_mul_log_le (p := p) hH0
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdiv : (n : ℝ) / (p - 1) ≤ n := div_le_self hn0 (by linarith)
  have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (δ + 1) := by positivity
  have hlogH : 0 ≤ Real.log H := Real.log_natCast_nonneg _
  have h' : ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) ≤
      δ * n + (p : ℝ) ^ (δ + 1) * (n + Nat.log p H) := by
    refine h.trans ?_
    push_cast
    gcongr
  calc _ ≤ (δ * n + (p : ℝ) ^ (δ + 1) * (n + Nat.log p H)) * Real.log p :=
        mul_le_mul_of_nonneg_right h' hlogp
    _ = (δ + (p : ℝ) ^ (δ + 1)) * Real.log p * n +
          (p : ℝ) ^ (δ + 1) * (Nat.log p H * Real.log p) := by ring
    _ ≤ (δ + (p : ℝ) ^ (δ + 1)) * Real.log p * n + (p : ℝ) ^ (δ + 1) * Real.log H := by gcongr
    _ ≤ _ := by
        have : (0 : ℝ) ≤ (δ + (p : ℝ) ^ (δ + 1)) * Real.log p := by positivity
        nlinarith

end LaneC976

end

/-! Stepanov part 1: the derivative polynomials `Hp` with `g^u (g^N)^{(u)} = g^N Hp u`,
their degree bound, and `X^(b q)` behaving as a constant for derivatives in characteristic `q`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {F : Type*} [Field F]

/-- `Hp g c u` with `c = (N : F)`: `g^u · (g^N)^{(u)} = g^N · Hp g c u`. -/
def Hp (g : F[X]) (c : F) : ℕ → F[X]
  | 0 => 1
  | u + 1 => C (c - u) * derivative g * Hp g c u + g * derivative (Hp g c u)

theorem g_mul_derivative_pow (g : F[X]) (n : ℕ) :
    g * derivative (g ^ n) = C (n : F) * derivative g * g ^ n := by
  rcases n with _ | n
  · simp
  · rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

theorem Hp_identity (g : F[X]) (N u : ℕ) :
    g ^ u * derivative^[u] (g ^ N) = g ^ N * Hp g (N : F) u := by
  induction u with
  | zero => simp [Hp]
  | succ u ih =>
    have h1 := congrArg derivative ih
    rw [derivative_mul, derivative_mul] at h1
    have h2 : g * (derivative (g ^ u) * derivative^[u] (g ^ N) +
        g ^ u * derivative (derivative^[u] (g ^ N))) =
        g * (derivative (g ^ N) * Hp g (N : F) u + g ^ N * derivative (Hp g (N : F) u)) := by
      rw [h1]
    have e1 : g * derivative (g ^ u) * derivative^[u] (g ^ N) =
        C (u : F) * derivative g * (g ^ N * Hp g (N : F) u) := by
      rw [g_mul_derivative_pow, mul_assoc (C (u : F) * derivative g), ih]
    have e2 : g * derivative (g ^ N) = C (N : F) * derivative g * g ^ N := g_mul_derivative_pow g N
    rw [Function.iterate_succ_apply', pow_succ]
    simp only [Hp]
    rw [C_sub]
    linear_combination h2 - e1 + e2 * Hp g (N : F) u

theorem natDegree_Hp_le (g : F[X]) (c : F) {k : ℕ} (hk : 1 ≤ k) (hg : g.natDegree ≤ k) (u : ℕ) :
    (Hp g c u).natDegree ≤ u * (k - 1) := by
  induction u with
  | zero => simp [Hp]
  | succ u ih =>
    simp only [Hp]
    have hring : (u + 1) * (k - 1) = u * (k - 1) + (k - 1) := by ring
    have hd : (derivative g).natDegree ≤ k - 1 :=
      (natDegree_derivative_le g).trans (Nat.sub_le_sub_right hg 1)
    apply natDegree_add_le_of_degree_le
    · calc (C (c - u) * derivative g * Hp g c u).natDegree
          ≤ (C (c - u) * derivative g).natDegree + (Hp g c u).natDegree := natDegree_mul_le
        _ ≤ (k - 1) + u * (k - 1) := by
          gcongr
          exact natDegree_C_mul_le _ _ |>.trans hd
        _ = (u + 1) * (k - 1) := by rw [hring]; ring
    · by_cases h0 : (Hp g c u).natDegree = 0
      · rw [natDegree_eq_zero.mp h0 |>.choose_spec.symm, derivative_C, mul_zero, natDegree_zero]
        exact Nat.zero_le _
      · calc (g * derivative (Hp g c u)).natDegree
            ≤ g.natDegree + (derivative (Hp g c u)).natDegree := natDegree_mul_le
          _ ≤ k + ((Hp g c u).natDegree - 1) := by
            gcongr
            exact natDegree_derivative_le _
          _ ≤ (u + 1) * (k - 1) := by rw [hring]; omega

end LaneC978

end

/-! Stepanov part 2: the Leibniz identity for `g^m (A g^{js} X^{bq})^{(m)}` in characteristic `q`
and its evaluation at points with `g(r)^s = 1`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


theorem derivative_X_pow_mul_char (b : ℕ) (R : (ZMod q)[X]) :
    derivative (X ^ (b * q) * R) = X ^ (b * q) * derivative R := by
  rw [derivative_mul, derivative_X_pow]
  have : ((b * q : ℕ) : (ZMod q)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  rw [this, C_0, zero_mul, zero_mul, zero_add]

theorem iterate_derivative_X_pow_mul_char (b m : ℕ) (R : (ZMod q)[X]) :
    derivative^[m] (X ^ (b * q) * R) = X ^ (b * q) * derivative^[m] R := by
  induction m generalizing R with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X_pow_mul_char, ih]

/-- The polynomial that replaces `g^m (A g^N)^{(m)} / g^N`. -/
def Rterm (g : (ZMod q)[X]) (N m : ℕ) (A : (ZMod q)[X]) : (ZMod q)[X] :=
  ∑ t ∈ range m.succ, m.choose t • (derivative^[m - t] A * g ^ (m - t) * Hp g (N : (ZMod q)) t)

theorem leibniz_identity (g A : (ZMod q)[X]) (N m : ℕ) :
    g ^ m * derivative^[m] (A * g ^ N) = g ^ N * Rterm g N m A := by
  rw [iterate_derivative_mul, mul_sum, Rterm, mul_sum]
  refine sum_congr rfl fun t ht => ?_
  have htm : t ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ht)
  have hsplit : g ^ m = g ^ (m - t) * g ^ t := by rw [← pow_add, Nat.sub_add_cancel htm]
  have hH := Hp_identity g N t
  rw [mul_smul_comm, mul_smul_comm, hsplit]
  congr 1
  calc g ^ (m - t) * g ^ t * (derivative^[m - t] A * derivative^[t] (g ^ N))
      = derivative^[m - t] A * g ^ (m - t) * (g ^ t * derivative^[t] (g ^ N)) := by ring
    _ = derivative^[m - t] A * g ^ (m - t) * (g ^ N * Hp g (N : (ZMod q)) t) := by rw [hH]
    _ = g ^ N * (derivative^[m - t] A * g ^ (m - t) * Hp g (N : (ZMod q)) t) := by ring

/-- One summand of the auxiliary polynomial. -/
theorem summand_identity (g A : (ZMod q)[X]) (N b m : ℕ) :
    g ^ m * derivative^[m] (A * g ^ N * X ^ (b * q)) =
      X ^ (b * q) * g ^ N * Rterm g N m A := by
  rw [mul_comm (A * g ^ N), iterate_derivative_X_pow_mul_char, mul_left_comm,
    leibniz_identity, mul_assoc]

theorem eval_X_pow_mul_char (b : ℕ) (r : (ZMod q)) : (X ^ (b * q) : (ZMod q)[X]).eval r = r ^ b := by
  rw [eval_pow, eval_X, mul_comm, pow_mul, ZMod.pow_card]

/-- The auxiliary polynomial `P = ∑ A_{j,b} g^{j s} X^{b q}` over an index set. -/
def Paux {ι : Type*} (s : Finset ι) (g : (ZMod q)[X]) (N : ι → ℕ) (b : ι → ℕ) (A : ι → (ZMod q)[X]) : (ZMod q)[X] :=
  ∑ i ∈ s, A i * g ^ N i * X ^ (b i * q)

/-- The polynomial `Q_m = ∑ X^b Rterm`. -/
def Qaux {ι : Type*} (s : Finset ι) (g : (ZMod q)[X]) (N : ι → ℕ) (b : ι → ℕ) (m : ℕ)
    (A : ι → (ZMod q)[X]) : (ZMod q)[X] :=
  ∑ i ∈ s, X ^ b i * Rterm g (N i) m (A i)

theorem eval_aux {ι : Type*} (s : Finset ι) (g : (ZMod q)[X]) (S : ℕ) (j b : ι → ℕ) (m : ℕ)
    (A : ι → (ZMod q)[X]) (r : (ZMod q)) (hr : g.eval r ^ S = 1) :
    (g ^ m * derivative^[m] (Paux s g (fun i => j i * S) b A)).eval r =
      (Qaux s g (fun i => j i * S) b m A).eval r := by
  rw [Paux, iterate_derivative_sum, mul_sum, eval_finset_sum, Qaux, eval_finset_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [summand_identity, eval_mul, eval_mul, eval_X_pow_mul_char, eval_pow,
    show j i * S = S * j i from mul_comm _ _, pow_mul, hr, one_pow, mul_one, eval_mul, eval_pow,
    eval_X]

end LaneC978

end

/-! Stepanov part 3: linear algebra. The coefficients of the `Q_m` are linear in the
coefficients of the `A_i`; more unknowns than equations gives a nonzero solution. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

/-- The polynomial with coefficient vector `c i`. -/
def Alin (D : ℕ) (i : ι) : (ι → Fin D → (ZMod q)) →ₗ[(ZMod q)] (ZMod q)[X] :=
  ∑ t : Fin D, ((LinearMap.proj (R := (ZMod q)) t : (Fin D → (ZMod q)) →ₗ[(ZMod q)] (ZMod q)) ∘ₗ
    (LinearMap.proj (R := (ZMod q)) i : (ι → Fin D → (ZMod q)) →ₗ[(ZMod q)] (Fin D → (ZMod q)))).smulRight (X ^ (t : ℕ))

theorem Alin_apply (i : ι) (c : ι → Fin D → (ZMod q)) :
    Alin D i c = ∑ t : Fin D, c i t • (X ^ (t : ℕ) : (ZMod q)[X]) := by
  simp [Alin]

theorem coeff_Alin (i : ι) (c : ι → Fin D → (ZMod q)) (t : Fin D) :
    (Alin D i c).coeff t = c i t := by
  rw [Alin_apply, finsetSum_coeff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ ht'
    simp only [coeff_smul, coeff_X_pow, smul_eq_mul]
    rw [if_neg (fun h => ht' (Fin.ext h.symm))]
    simp
  · simp

theorem natDegree_Alin_lt (hD : 0 < D) (i : ι) (c : ι → Fin D → (ZMod q)) :
    (Alin D i c).natDegree < D := by
  rw [Alin_apply]
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := D - 1) fun t _ => ?_) (by omega)
  refine (natDegree_smul_le _ _).trans ?_
  rw [natDegree_X_pow]
  omega

theorem eq_zero_of_Alin_eq_zero (c : ι → Fin D → (ZMod q)) (h : ∀ i, Alin D i c = 0) : c = 0 := by
  funext i t
  have := coeff_Alin i c t
  rw [h i, coeff_zero] at this
  simp [← this]

/-- `Rterm` as a linear map. -/
def Rlin (g : (ZMod q)[X]) (N m : ℕ) : (ZMod q)[X] →ₗ[(ZMod q)] (ZMod q)[X] :=
  ∑ t ∈ range m.succ, m.choose t •
    (LinearMap.mulRight (ZMod q) (g ^ (m - t) * Hp g (N : (ZMod q)) t) ∘ₗ
      ((derivative : (ZMod q)[X] →ₗ[(ZMod q)] (ZMod q)[X]) ^ (m - t)))

theorem Rlin_apply (g : (ZMod q)[X]) (N m : ℕ) (A : (ZMod q)[X]) : Rlin g N m A = Rterm g N m A := by
  rw [Rlin, Rterm, LinearMap.sum_apply]
  refine sum_congr rfl fun t _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, Module.End.pow_apply,
    mul_assoc]

/-- `Q_m` as a linear function of the coefficient vector. -/
def Qlin (D : ℕ) (g : (ZMod q)[X]) (N b : ι → ℕ) (m : ℕ) : (ι → Fin D → (ZMod q)) →ₗ[(ZMod q)] (ZMod q)[X] :=
  ∑ i, LinearMap.mulLeft (ZMod q) (X ^ b i) ∘ₗ Rlin g (N i) m ∘ₗ Alin D i

theorem Qlin_apply (g : (ZMod q)[X]) (N b : ι → ℕ) (m : ℕ) (c : ι → Fin D → (ZMod q)) :
    Qlin D g N b m c = Qaux univ g N b m (fun i => Alin D i c) := by
  rw [Qlin, Qaux, LinearMap.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Rlin_apply]

/-- More unknowns than equations: a nonzero coefficient vector with all `Q_m = 0`. -/
theorem exists_aux (g : (ZMod q)[X]) (N b : ι → ℕ) (M E : ℕ)
    (hdeg : ∀ m < M, ∀ c : ι → Fin D → (ZMod q), (Qlin D g N b m c).natDegree < E)
    (hdim : M * E < Fintype.card ι * D) :
    ∃ c : ι → Fin D → (ZMod q), c ≠ 0 ∧ ∀ m < M, Qaux univ g N b m (fun i => Alin D i c) = 0 := by
  let Φ : (ι → Fin D → (ZMod q)) →ₗ[(ZMod q)] (Fin M → Fin E → (ZMod q)) :=
    LinearMap.pi fun m => LinearMap.pi fun e => lcoeff (ZMod q) (e : ℕ) ∘ₗ Qlin D g N b m
  have hfr : Module.finrank (ZMod q) (Fin M → Fin E → (ZMod q)) < Module.finrank (ZMod q) (ι → Fin D → (ZMod q)) := by
    simp only [Module.finrank_pi_fintype, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Module.finrank_self, mul_one]
    exact hdim
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hfr)
  refine ⟨c, hc0, fun m hm => ?_⟩
  rw [← Qlin_apply]
  have hz : ∀ e : Fin E, (Qlin D g N b m c).coeff e = 0 := fun e => by
    have hc' : Φ c = 0 := LinearMap.mem_ker.mp hc
    have h1 : Φ c ⟨m, hm⟩ e = 0 := by rw [hc']; rfl
    exact h1
  ext n
  rw [coeff_zero]
  by_cases hn : n < E
  · exact hz ⟨n, hn⟩
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg m hm c) (not_lt.mp hn))

end LaneC978

end

/-! Stepanov part 4: the bound `#{r : g(r)^s = 1} ≤ (1 - 1/(4ℓ)) q` for `ℓ s = q - 1`,
`deg g = k` coprime to `ℓ`, and `q` large. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


theorem natDegree_Rterm_le (g A : (ZMod q)[X]) {k D' : ℕ} (hk : 1 ≤ k) (hg : g.natDegree ≤ k)
    (hA : A.natDegree ≤ D') (N m : ℕ) : (Rterm g N m A).natDegree ≤ D' + m * k := by
  refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
  have htm : t ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ht)
  rw [nsmul_eq_mul]
  refine natDegree_mul_le.trans ?_
  rw [natDegree_natCast, zero_add]
  refine natDegree_mul_le.trans ?_
  refine (add_le_add natDegree_mul_le (natDegree_Hp_le g _ hk hg t)).trans ?_
  have h1 : (derivative^[m - t] A).natDegree ≤ D' :=
    (natDegree_iterate_derivative A _).trans (Nat.sub_le _ _ |>.trans hA)
  have h2 : (g ^ (m - t)).natDegree ≤ (m - t) * k := natDegree_pow_le_of_le _ hg
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le htm
  rw [Nat.add_sub_cancel_left] at h1 h2 ⊢
  have : u * k + t * (k - 1) ≤ (t + u) * k := by
    have : t * (k - 1) ≤ t * k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  omega

/-- If `c q = R` with `|R| < q` then `c = 0`. -/
theorem int_eq_zero_of_mul_lt {c R : ℤ} {Q : ℤ} (hQ : 0 < Q) (h : c * Q = R) (hR : |R| < Q) :
    c = 0 := by
  rw [abs_lt] at hR
  by_contra hc
  rcases lt_or_gt_of_ne hc with h' | h'
  · nlinarith
  · nlinarith

/-- Distinct exponents: `a + j s k + b q` determines `(j, b)` for `a < D`, `j < ℓ`. -/
theorem exps_inj {ℓ s k D a a' j j' b b' : ℕ} (hs : ℓ * s = q - 1) (hcop : Nat.Coprime k ℓ)
    (ha : a < D) (ha' : a' < D) (hj : j < ℓ) (hj' : j' < ℓ) (hqbig : ℓ * (D + k) < q)
    (h : a + j * s * k + b * q = a' + j' * s * k + b' * q) : j = j' ∧ b = b' := by
  have hq1 : 1 ≤ q := hq.out.one_lt.le
  have hsZ : (ℓ : ℤ) * s = q - 1 := by rw [← Nat.cast_mul, hs]; push_cast [Nat.cast_sub hq1]; ring
  have hZ : (a : ℤ) + j * s * k + b * q = a' + j' * s * k + b' * q := by exact_mod_cast h
  have key : (((j : ℤ) - j') * k + ℓ * (b - b')) * q = ℓ * (a' - a) + ((j : ℤ) - j') * k := by
    have e1 : (ℓ : ℤ) * (a + j * s * k + b * q) = ℓ * (a' + j' * s * k + b' * q) := by rw [hZ]
    have e2 : (ℓ : ℤ) * (j * s * k) = j * k * (q - 1) := by rw [← hsZ]; ring
    have e3 : (ℓ : ℤ) * (j' * s * k) = j' * k * (q - 1) := by rw [← hsZ]; ring
    linear_combination e1 - e2 + e3
  have hbound : |(ℓ : ℤ) * (a' - a) + ((j : ℤ) - j') * k| < q := by
    have hqZ : (ℓ : ℤ) * (D + k) < q := by exact_mod_cast hqbig
    rw [abs_lt]
    have : (a : ℤ) < D := by exact_mod_cast ha
    have : (a' : ℤ) < D := by exact_mod_cast ha'
    have : (j : ℤ) < ℓ := by exact_mod_cast hj
    have : (j' : ℤ) < ℓ := by exact_mod_cast hj'
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℤ) a, Nat.cast_nonneg (α := ℤ) a',
      Nat.cast_nonneg (α := ℤ) j, Nat.cast_nonneg (α := ℤ) j', Nat.cast_nonneg (α := ℤ) k,
      Nat.cast_nonneg (α := ℤ) ℓ]
  have hc := int_eq_zero_of_mul_lt (by exact_mod_cast hq.out.pos) key hbound
  have hdvd : (ℓ : ℤ) ∣ ((j : ℤ) - j') * k := ⟨b' - b, by linear_combination hc⟩
  have hcopZ : IsCoprime (ℓ : ℤ) k := Int.isCoprime_iff_gcd_eq_one.mpr (by
    rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.symm hcop)
  have hdj : (ℓ : ℤ) ∣ (j : ℤ) - j' := hcopZ.dvd_of_dvd_mul_right hdvd
  have hjj : j = j' := by
    obtain ⟨t, ht⟩ := hdj
    have : (j : ℤ) - j' < ℓ := by omega
    have : -(ℓ : ℤ) < (j : ℤ) - j' := by omega
    have hℓ : (0 : ℤ) < ℓ := by omega
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h' | h' | h'
      · have h3 : (ℓ : ℤ) * t ≤ ℓ * (-1) := mul_le_mul_of_nonneg_left (by omega) hℓ.le
        linarith
      · exact h'
      · have h3 : (ℓ : ℤ) * 1 ≤ ℓ * t := mul_le_mul_of_nonneg_left (by omega) hℓ.le
        linarith
    rw [ht0, mul_zero] at ht
    omega
  subst hjj
  refine ⟨rfl, ?_⟩
  have hℓ : (ℓ : ℤ) ≠ 0 := by
    have : 0 < ℓ := by omega
    exact_mod_cast this.ne'
  have : (ℓ : ℤ) * (b - b') = 0 := by linear_combination hc
  have := (mul_eq_zero.mp this).resolve_left hℓ
  omega

end LaneC978

end

/-! Stepanov part 5: the bound itself. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


theorem final_arith {ℓ s k T D : ℕ} (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) (hs : ℓ * s = q - 1)
    (hqD : 2 * ℓ * D < q) (hT : 2 * k * T ≤ (D - 1) + (ℓ - 1) * s * k + k * q) :
    4 * ℓ * T ≤ (4 * ℓ - 1) * q := by
  have hq1 : 1 ≤ q := hq.out.one_lt.le
  have hD1 : D - 1 ≤ D := Nat.sub_le _ _
  have hTZ : (2 * k * T : ℤ) ≤ D + ((ℓ : ℤ) - 1) * s * k + k * q := by
    have : ((ℓ - 1 : ℕ) : ℤ) = ℓ - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ ℓ)]; ring
    have h' : ((2 * k * T : ℕ) : ℤ) ≤ (((D - 1) + (ℓ - 1) * s * k + k * q : ℕ) : ℤ) := by
      exact_mod_cast hT
    push_cast [Nat.cast_sub (by omega : 1 ≤ ℓ)] at h'
    have : ((D - 1 : ℕ) : ℤ) ≤ D := by exact_mod_cast hD1
    linarith
  have hsZ : (ℓ : ℤ) * s = q - 1 := by
    rw [← Nat.cast_mul, hs]; push_cast [Nat.cast_sub hq1]; ring
  have hqDZ : (2 * ℓ * D : ℤ) < q := by exact_mod_cast hqD
  have hkq : (q : ℤ) ≤ k * q := by
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg (α := ℤ) q]
  have h4 : (2 * ℓ : ℤ) * (2 * k * T) ≤ 2 * ℓ * (D + ((ℓ : ℤ) - 1) * s * k + k * q) :=
    mul_le_mul_of_nonneg_left hTZ (by positivity)
  have h5 : (2 * ℓ : ℤ) * (((ℓ : ℤ) - 1) * s * k) = 2 * ((ℓ : ℤ) - 1) * k * (q - 1) := by
    rw [← hsZ]; ring
  have hℓZ : (2 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have goalZ : (k : ℤ) * (4 * ℓ * T) ≤ k * ((4 * ℓ - 1) * q) := by
    nlinarith [Nat.cast_nonneg (α := ℤ) q, Nat.cast_nonneg (α := ℤ) T]
  have goalZ' : (4 * ℓ * T : ℤ) ≤ (4 * ℓ - 1) * q := le_of_mul_le_mul_left goalZ hkZ
  have h41 : ((4 * ℓ - 1 : ℕ) : ℤ) = 4 * ℓ - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * ℓ)]; ring
  have : ((4 * ℓ * T : ℕ) : ℤ) ≤ ((4 * ℓ - 1 : ℕ) : ℤ) * (q : ℤ) := by
    rw [h41]; push_cast; exact goalZ'
  exact_mod_cast this

end LaneC978

end

/-! Stepanov part 6: assembly of the bound `4ℓ #{r : g(r)^s = 1} ≤ (4ℓ - 1) q`. -/

noncomputable section
open Polynomial Finset
open scoped Function

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


theorem prod_X_sub_C_pow_dvd (P : (ZMod q)[X]) (S : Finset (ZMod q)) (M : ℕ)
    (h : ∀ r ∈ S, (X - C r) ^ M ∣ P) : (∏ r ∈ S, (X - C r) ^ M) ∣ P := by
  refine Finset.prod_dvd_of_coprime ?_ h
  intro a _ b _ hab
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow

theorem natDegree_prod_X_sub_C_pow (S : Finset (ZMod q)) (M : ℕ) :
    (∏ r ∈ S, (X - C r) ^ M).natDegree = M * #S := by
  rw [natDegree_prod _ _ (fun r _ => pow_ne_zero _ (X_sub_C_ne_zero r))]
  simp [natDegree_pow, natDegree_X_sub_C, mul_comm]

theorem stepanov {ℓ s k : ℕ} (hℓ : 2 ≤ ℓ) (hs : ℓ * s = q - 1) (g : (ZMod q)[X]) (hk : 1 ≤ k)
    (hgk : g.natDegree = k) (hcop : Nat.Coprime k ℓ)
    (hqbig : 2 * ℓ * (3 * k ^ 3 + 1 + k) < q) :
    4 * ℓ * #{r : (ZMod q) | g.eval r ^ s = 1} ≤ (4 * ℓ - 1) * q := by
  classical
  set D := 3 * k ^ 3 + 1 with hD
  set M := 2 * k with hM
  set E := k + D + M * k with hE
  have hDpos : 0 < D := by omega
  have hq1 : 1 ≤ q := hq.out.one_lt.le
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, mul_zero] at hs; have := hq.out.two_le; omega
    · exact h
  let ι := Fin ℓ × Fin (k + 1)
  let j : ι → ℕ := fun i => (i.1 : ℕ)
  let b : ι → ℕ := fun i => (i.2 : ℕ)
  let N : ι → ℕ := fun i => j i * s
  have hg0 : g ≠ 0 := by rintro rfl; simp at hgk; omega
  have hdeg : ∀ m < M, ∀ c : ι → Fin D → (ZMod q), (Qlin D g N b m c).natDegree < E := by
    intro m hm c
    rw [Qlin_apply, Qaux]
    refine lt_of_le_of_lt
      (natDegree_sum_le_of_forall_le _ _ (n := k + (D - 1) + m * k) fun i _ => ?_) ?_
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_X_pow]
      have h1 := natDegree_Rterm_le g (Alin D i c) hk hgk.le
        (Nat.le_sub_one_of_lt (natDegree_Alin_lt hDpos i c)) (N i) m
      have hb : b i ≤ k := Nat.lt_succ_iff.mp i.2.2
      omega
    · have : m * k < M * k := Nat.mul_lt_mul_of_pos_right hm (by omega)
      omega
  have hdim : M * E < Fintype.card ι * D := by
    have hcard : Fintype.card ι = ℓ * (k + 1) := by simp [ι]
    rw [hcard]
    have hk3 : k ^ 2 ≤ k ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
    have h1 : M * E + 1 ≤ 2 * (k + 1) * D := by
      simp only [hM, hE, hD]; ring_nf; nlinarith
    have h2 : 2 * (k + 1) * D ≤ ℓ * (k + 1) * D := by gcongr
    omega
  obtain ⟨c, hc0, hQ⟩ := exists_aux g N b M E hdeg hdim
  set A : ι → (ZMod q)[X] := fun i => Alin D i c with hA
  have hAdeg : ∀ i, (A i).natDegree < D := fun i => natDegree_Alin_lt hDpos i c
  obtain ⟨i0, hi0⟩ : ∃ i0, A i0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hc0 (eq_zero_of_Alin_eq_zero c hcon)
  set term : ι → (ZMod q)[X] := fun i => A i * g ^ N i * X ^ (b i * q) with hterm
  have hP : Paux univ g N b A = ∑ i, term i := rfl
  have hterm0 : ∀ i, term i ≠ 0 ↔ A i ≠ 0 := by
    intro i
    simp only [term, ne_eq, mul_eq_zero, pow_eq_zero_iff', hg0, X_ne_zero, false_and, or_false]
  have hdegterm : ∀ i, A i ≠ 0 →
      (term i).natDegree = (A i).natDegree + j i * s * k + b i * q := by
    intro i hi
    simp only [term]
    rw [natDegree_mul (mul_ne_zero hi (pow_ne_zero _ hg0)) (pow_ne_zero _ X_ne_zero),
      natDegree_mul hi (pow_ne_zero _ hg0), natDegree_pow, natDegree_X_pow, hgk]
  have hqbig' : ℓ * (D + k) < q := by
    have : ℓ * (D + k) ≤ 2 * ℓ * (D + k) := by nlinarith
    omega
  have hdisj : Set.Pairwise {i | i ∈ (univ : Finset ι) ∧ term i ≠ 0}
      (Ne on natDegree ∘ term) := by
    rintro i ⟨-, hi⟩ i' ⟨-, hi'⟩ hii' heq
    rw [hterm0] at hi hi'
    simp only [Function.comp_apply] at heq
    rw [hdegterm i hi, hdegterm i' hi'] at heq
    obtain ⟨h1, h2⟩ := exps_inj (D := D) hs hcop (hAdeg i) (hAdeg i') i.1.2 i'.1.2 hqbig' heq
    exact hii' (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hdisj' : Set.Pairwise {i | i ∈ (univ : Finset ι) ∧ term i ≠ 0}
      (Ne on degree ∘ term) := by
    intro i hi i' hi' hii' heq
    apply hdisj hi hi' hii'
    simp only [Function.comp_apply] at heq ⊢
    rw [degree_eq_natDegree hi.2, degree_eq_natDegree hi'.2] at heq
    exact_mod_cast heq
  have hPne : Paux univ g N b A ≠ 0 := by
    intro h0
    have hdg := degree_sum_eq_of_disjoint term univ hdisj'
    rw [← hP, h0, degree_zero] at hdg
    have hle : degree (term i0) ≤ univ.sup fun i => degree (term i) :=
      Finset.le_sup (f := fun i => degree (term i)) (mem_univ i0)
    rw [← hdg, le_bot_iff, degree_eq_bot] at hle
    exact ((hterm0 i0).mpr hi0) hle
  have hPdeg : (Paux univ g N b A).natDegree ≤ (D - 1) + (ℓ - 1) * s * k + k * q := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    by_cases hi : A i = 0
    · simp [term, hi]
    · rw [hdegterm i hi]
      have h1 : (A i).natDegree ≤ D - 1 := Nat.le_sub_one_of_lt (hAdeg i)
      have h2 : j i ≤ ℓ - 1 := Nat.le_sub_one_of_lt i.1.2
      have h3 : b i ≤ k := Nat.lt_succ_iff.mp i.2.2
      have h4 : j i * s * k ≤ (ℓ - 1) * s * k := by gcongr
      have h5 : b i * q ≤ k * q := by gcongr
      omega
  -- every point of the set is a root of multiplicity ≥ M
  have hroot : ∀ r : (ZMod q), g.eval r ^ s = 1 → (X - C r) ^ M ∣ Paux univ g N b A := by
    intro r hr
    have hgr : g.eval r ≠ 0 := by
      intro h0; rw [h0, zero_pow hspos.ne'] at hr; exact zero_ne_one hr
    have hder : ∀ m ≤ M - 1, (derivative^[m] (Paux univ g N b A)).IsRoot r := by
      intro m hm
      have hmM : m < M := by omega
      have he := eval_aux univ g s j b m A r hr
      rw [show (fun i => j i * s) = N from rfl, hQ m hmM, eval_zero, eval_mul, eval_pow] at he
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hgr)
    have hnzd : ∀ m ≤ M - 1, m ≠ 0 → (m : (ZMod q)) ∈ nonZeroDivisors (ZMod q) := by
      intro m hm hm0
      apply mem_nonZeroDivisors_of_ne_zero
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      have : M < q := by nlinarith
      omega
    have hmult := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
      hPne hder hnzd
    exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd _ r)
  have hprod := prod_X_sub_C_pow_dvd _ (univ.filter fun r : (ZMod q) => g.eval r ^ s = 1) M
    (fun r hr => hroot r (mem_filter.mp hr).2)
  have hle := natDegree_le_of_dvd hprod hPne
  rw [natDegree_prod_X_sub_C_pow] at hle
  have hqD : 2 * ℓ * D < q := lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) hqbig
  exact final_arith hk hℓ hs hqD (by rw [hM] at hle; linarith)

end LaneC978

end

/-! Lemma 3, part a: elementary facts on `ρ(m) = #{r < m : m ∣ f(r)}` — reduction of roots,
submultiplicativity over coprime moduli, uniform bounds at bad prime powers, smooth moduli. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

theorem dvd_eval_mod {f : ℤ[X]} {m d r : ℕ} (hd : d ∣ m) (hr : (m : ℤ) ∣ f.eval (r : ℤ)) :
    (d : ℤ) ∣ f.eval ((r % d : ℕ) : ℤ) := by
  have h1 := sub_dvd_eval_sub ((r % d : ℕ) : ℤ) (r : ℤ) f
  have h2 : (d : ℤ) ∣ ((r % d : ℕ) : ℤ) - r := by
    have := (Nat.mod_modEq r d)
    have h3 := (Nat.modEq_iff_dvd.mp this)
    rw [← dvd_neg, neg_sub]; exact h3
  have h4 : (d : ℤ) ∣ f.eval (r : ℤ) := (Int.natCast_dvd_natCast.mpr hd).trans hr
  have := dvd_add (h2.trans h1) h4
  simpa using this

theorem rho_le_self (f : ℤ[X]) (m : ℕ) : rho f m ≤ m := by
  rw [rho]; exact (card_filter_le _ _).trans (by simp)

theorem rho_one (f : ℤ[X]) : rho f 1 = 1 := by
  rw [rho, range_one, filter_singleton, if_pos (by simp), card_singleton]

theorem rho_mul_le (f : ℤ[X]) {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (h : Nat.Coprime u v) :
    rho f (u * v) ≤ rho f u * rho f v := by
  classical
  rw [rho, rho, rho, ← card_product]
  refine card_le_card_of_injOn (fun r => (r % u, r % v)) ?_ ?_
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq]
    exact ⟨⟨Nat.mod_lt _ hu, dvd_eval_mod (dvd_mul_right u v) (by exact_mod_cast hr.2)⟩,
      ⟨Nat.mod_lt _ hv, dvd_eval_mod (dvd_mul_left v u) (by exact_mod_cast hr.2)⟩⟩
  · intro r hr r' hr' heq
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
    simp only [Prod.mk.injEq] at heq
    have : r ≡ r' [MOD u * v] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨heq.1, heq.2⟩
    exact Nat.ModEq.eq_of_lt_of_lt this hr.1 hr'.1

/-- Uniform bound at prime powers from the Bezout identity `f u + f' v = D`. -/
theorem rho_prime_pow_le {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p δ : ℕ} (hp : p.Prime) (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D) (j : ℕ) :
    rho f (p ^ j) ≤ p ^ (2 * δ + 1) := by
  classical
  have hp0 : 0 < p := hp.pos
  by_cases hj : j ≤ δ
  · calc rho f (p ^ j) ≤ p ^ j := rho_le_self f _
      _ ≤ p ^ (2 * δ + 1) := Nat.pow_le_pow_right hp0 (by omega)
  rw [not_le] at hj
  set P := p ^ (j - δ) with hP
  have hPpos : 0 < P := pow_pos hp0 _
  have hsplit : p ^ j = p ^ δ * P := by rw [hP, ← pow_add]; congr 1; omega
  calc rho f (p ^ j) ≤ #(range (p ^ (δ + 1)) ×ˢ range (p ^ δ)) := by
        rw [rho]
        refine card_le_card_of_injOn (fun r => (r % p ^ (δ + 1), r / P)) ?_ ?_
        · intro r hr
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
          simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
          refine ⟨Nat.mod_lt _ (pow_pos hp0 _), ?_⟩
          rw [Nat.div_lt_iff_lt_mul hPpos, ← hsplit]; exact hr.1
        · intro r hr r' hr' heq
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
          simp only [Prod.mk.injEq] at heq
          have h1 : ((p ^ (δ + 1) : ℕ) : ℤ) ∣ (r' : ℤ) - r :=
            Nat.modEq_iff_dvd.mp heq.1
          have h2 := cluster hB hp hδ (show δ + 1 ≤ j by omega) (x := (r : ℤ)) (y := (r' : ℤ))
            (by exact_mod_cast hr.2) (by exact_mod_cast hr'.2) (by exact_mod_cast h1)
          have h3 : r ≡ r' [MOD P] := Nat.modEq_iff_dvd.mpr (by rw [hP]; exact_mod_cast h2)
          rw [← Nat.div_add_mod r P, ← Nat.div_add_mod r' P, heq.2, h3]
    _ = p ^ (2 * δ + 1) := by
        rw [card_product, card_range, card_range, ← pow_add]; congr 1; omega

/-- Bound for moduli all of whose prime factors lie in a finite set `B` of primes. -/
theorem rho_smooth_le (f : ℤ[X]) (B : Finset ℕ) (Cb : ℕ → ℕ) (hC1 : ∀ p, 1 ≤ Cb p)
    (hC : ∀ p ∈ B, ∀ j, rho f (p ^ j) ≤ Cb p) :
    ∀ w : ℕ, 0 < w → (∀ p ∈ w.primeFactors, p ∈ B) → rho f w ≤ ∏ p ∈ B, Cb p := by
  have key : ∀ w : ℕ, 0 < w → (∀ p ∈ w.primeFactors, p ∈ B) →
      rho f w ≤ ∏ p ∈ w.primeFactors, Cb p := by
    intro w
    induction w using Nat.recOnPosPrimePosCoprime with
    | prime_pow p n hp hn =>
      intro _ hB
      have hpn : (p ^ n).primeFactors = {p} := Nat.primeFactors_prime_pow hn.ne' hp
      rw [hpn, prod_singleton]
      exact hC p (hB p (by rw [hpn]; simp)) n
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | one => intro _ _; rw [rho_one]; simp
    | coprime a b ha hb hab iha ihb =>
      intro _ hB
      rw [Nat.Coprime.primeFactors_mul hab] at hB ⊢
      rw [prod_union (Nat.Coprime.disjoint_primeFactors hab)]
      calc rho f (a * b) ≤ rho f a * rho f b := rho_mul_le f (by omega) (by omega) hab
        _ ≤ (∏ p ∈ a.primeFactors, Cb p) * ∏ p ∈ b.primeFactors, Cb p := by
          gcongr
          · exact iha (by omega) (fun p hp => hB p (mem_union_left _ hp))
          · exact ihb (by omega) (fun p hp => hB p (mem_union_right _ hp))
  intro w hw hB
  refine (key w hw hB).trans ?_
  exact prod_le_prod_of_subset_of_one_le' (fun p hp => hB p hp) (fun p _ _ => hC1 p)

end LaneC978

end

/-! Lemma 3, part b: for a modulus `m` all of whose prime factors are good, the roots of `f`
modulo `m` inject into the ideals of norm `m` of the ring of integers. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal `(p, θ - a c)`. -/
def Jp (θ : 𝓞 K) (a : ℤ) (p c : ℕ) : Ideal (𝓞 K) :=
  span {(p : 𝓞 K), θ - ((a * (c : ℤ) : ℤ) : 𝓞 K)}

theorem absNorm_Jp {f : ℤ[X]} (hd : 1 ≤ f.natDegree) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = f.integralNormalization) {p c : ℕ} (hp : p.Prime)
    (hpe : ¬ p ∣ RingOfIntegers.exponent θ) (hc : (p : ℤ) ∣ f.eval (c : ℤ)) :
    absNorm (Jp θ f.leadingCoeff p c) = p := by
  haveI := Fact.mk hp
  refine absNorm_span_pair hpe ?_
  rw [hmin]
  have := integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id ℤ) (c : ℤ)
  change f.integralNormalization.eval (f.leadingCoeff * (c : ℤ)) =
    f.leadingCoeff ^ (f.natDegree - 1) * f.eval (c : ℤ) at this
  rw [this]
  exact dvd_mul_of_dvd_right hc _

theorem isMaximal_of_absNorm_prime {I : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime)
    (hI : absNorm I = p) : I.IsMaximal := by
  have hirr : Irreducible (absNorm I) := by rw [hI]; exact Nat.prime_iff.mp hp |>.irreducible
  have hprime := isPrime_of_irreducible_absNorm hirr
  have hne : I ≠ ⊥ := by
    rintro rfl; rw [absNorm_bot] at hI; exact hp.ne_zero hI.symm
  exact hprime.isMaximal hne

/-- The ideal attached to a root `r` modulo `m`. -/
def Phi (θ : 𝓞 K) (a : ℤ) (m r : ℕ) : Ideal (𝓞 K) :=
  ∏ p ∈ m.primeFactors, Jp θ a p (r % p) ^ (m.factorization p)

theorem prod_primeFactors_pow (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m := by
  have := Nat.prod_factorization_pow_eq_self hm
  rw [Finsupp.prod, Nat.support_factorization] at this
  exact this

theorem rho_good_le {f : ℤ[X]} (hd : 1 ≤ f.natDegree) {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = f.integralNormalization) {u v : ℤ[X]} {D : ℤ}
    (hB : f * u + derivative f * v = C D) (m : ℕ) (hm : 0 < m)
    (hgood : ∀ p ∈ m.primeFactors, ¬ (p : ℤ) ∣ f.leadingCoeff ∧
      ¬ p ∣ RingOfIntegers.exponent θ ∧ ¬ (p : ℤ) ∣ D) :
    rho f m ≤ #{I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) m).toFinset | absNorm I = m} := by
  classical
  set a := f.leadingCoeff
  have hroot : ∀ r : ℕ, (m : ℤ) ∣ f.eval (r : ℤ) → ∀ p ∈ m.primeFactors,
      (p : ℤ) ∣ f.eval ((r % p : ℕ) : ℤ) := fun r hr p hp =>
    dvd_eval_mod (Nat.dvd_of_mem_primeFactors hp) hr
  have hnorm : ∀ r : ℕ, (m : ℤ) ∣ f.eval (r : ℤ) → ∀ p ∈ m.primeFactors,
      absNorm (Jp θ a p (r % p)) = p := fun r hr p hp =>
    absNorm_Jp hd hmin (Nat.prime_of_mem_primeFactors hp) (hgood p hp).2.1 (hroot r hr p hp)
  rw [rho]
  refine card_le_card_of_injOn (Phi θ a m) ?_ ?_
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
    have hN : absNorm (Phi θ a m r) = m := by
      rw [Phi, map_prod]
      simp_rw [map_pow]
      refine (prod_congr rfl fun p hp => ?_).trans (prod_primeFactors_pow m hm.ne')
      rw [hnorm r (by exact_mod_cast hr.2) p hp]
    simp only [coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨hN.le, hN⟩
  · intro r hr r' hr' heq
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
    have hr2 : (m : ℤ) ∣ f.eval (r : ℤ) := by exact_mod_cast hr.2
    have hr2' : (m : ℤ) ∣ f.eval (r' : ℤ) := by exact_mod_cast hr'.2
    -- residues agree modulo every prime factor
    have hres : ∀ p ∈ m.primeFactors, r % p = r' % p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hv : m.factorization p ≠ 0 :=
        (Nat.support_factorization m ▸ hp : p ∈ m.factorization.support) |> Finsupp.mem_support_iff.mp
      have hmax := isMaximal_of_absNorm_prime hpp (hnorm r hr2 p hp)
      have hle : Phi θ a m r' ≤ Jp θ a p (r % p) := by
        rw [← heq]
        refine (le_of_dvd (dvd_prod_of_mem _ hp)).trans ?_
        exact pow_le_self hv
      obtain ⟨p', hp', hle'⟩ := (hmax.isPrime.prod_le).mp hle
      have hle'' := hmax.isPrime.le_of_pow_le hle'
      have hmax' := isMaximal_of_absNorm_prime (Nat.prime_of_mem_primeFactors hp')
        (hnorm r' hr2' p' hp')
      have heqJ : Jp θ a p' (r' % p') = Jp θ a p (r % p) :=
        hmax'.eq_of_le hmax.ne_top hle''
      by_contra hne
      have hpair : (p', r' % p') ≠ (p, r % p) := by
        intro h; apply hne; rw [(Prod.mk.inj h).2.symm, (Prod.mk.inj h).1]
      have htop := sup_span_pair_eq_top θ a (Nat.prime_of_mem_primeFactors hp') hpp
        (Nat.mod_lt _ (Nat.prime_of_mem_primeFactors hp').pos) (Nat.mod_lt _ hpp.pos)
        (hgood p' hp').1 hpair
      change Jp θ a p' (r' % p') ⊔ Jp θ a p (r % p) = ⊤ at htop
      rw [heqJ, sup_idem] at htop
      exact hmax.ne_top htop
    -- hence `m ∣ r' - r`
    have hdvd : ∀ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℤ) ∣ (r' : ℤ) - r := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hv : 1 ≤ m.factorization p := Nat.pos_of_ne_zero
        ((Nat.support_factorization m ▸ hp : p ∈ m.factorization.support) |> Finsupp.mem_support_iff.mp)
      have hpow : ((p ^ m.factorization p : ℕ) : ℤ) ∣ (m : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd m p)
      have h1 : ((p : ℕ) : ℤ) ^ (0 + 1) ∣ (r' : ℤ) - r := by
        rw [zero_add, pow_one]; exact Nat.modEq_iff_dvd.mp (hres p hp)
      have hpow' : ((p : ℕ) : ℤ) ^ m.factorization p ∣ (m : ℤ) := by
        push_cast at hpow; exact hpow
      have h2 := cluster hB hpp (δ := 0) (by rw [zero_add, pow_one]; exact (hgood p hp).2.2)
        (show 0 + 1 ≤ m.factorization p by omega) (hpow'.trans hr2) (hpow'.trans hr2') h1
      rw [Nat.sub_zero] at h2
      exact_mod_cast h2
    have hall : (m : ℤ) ∣ (r' : ℤ) - r := by
      have := Finset.prod_dvd_of_coprime (t := m.primeFactors)
        (s := fun p => ((p ^ m.factorization p : ℕ) : ℤ)) ?_ hdvd
      · rwa [← Nat.cast_prod, prod_primeFactors_pow m hm.ne'] at this
      · intro p hp q hq hpq
        simp only [Function.onFun]
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.modEq_iff_dvd.mpr hall) hr.1 hr'.1

end LaneC978

end

/-! Lemma 3, part c: `∑_{m ≤ x} ρ(m) ≤ C x` for irreducible `f`. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

/-- `n ↦ 1/n` as a multiplicative map. -/
def finv : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

theorem sum_inv_smooth_le (P : ℕ) (U : Finset ℕ) (hU : ∀ u ∈ U, u ∈ P.smoothNumbers) :
    ∑ u ∈ U, (u : ℝ)⁻¹ ≤ ∏ p ∈ P.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖finv p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hlt P
  change ∑ u ∈ U, finv u ≤ ∏ p ∈ P.primesBelow, (1 - finv p)⁻¹
  rw [← Finset.sum_subtype_of_mem (fun k => finv k) hU]
  exact sum_le_hasSum _ (fun i _ => by change (0 : ℝ) ≤ ((i : ℕ) : ℝ)⁻¹; positivity) hS

variable {K : Type*} [Field K] [NumberField K]

/-- Ideals of norm exactly `n`. -/
abbrev nI (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  #{I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset | absNorm I = n}

theorem sum_nI_eq_cnt (y : ℕ) : ∑ w ∈ Icc 1 y, nI K w = cnt K y := by
  classical
  rw [cnt, card_eq_sum_card_fiberwise (f := fun I => absNorm I) (t := Icc 1 y)]
  · refine sum_congr rfl fun w hw => ?_
    rw [mem_Icc] at hw
    apply congrArg Finset.card
    ext I
    simp only [mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩; refine ⟨⟨h ▸ hw.2, ?_⟩, h⟩
      rintro rfl; rw [absNorm_bot] at h; omega
    · rintro ⟨-, h⟩; exact ⟨h.le, h⟩
  · intro I hI
    simp only [coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
    simp only [coe_Icc, Set.mem_Icc]
    refine ⟨?_, hI.1⟩
    exact Nat.pos_of_ne_zero (fun h => hI.2 (absNorm_eq_zero_iff.mp h))

theorem cnt_mono {a b : ℕ} (h : a ≤ b) : cnt K a ≤ cnt K b := by
  rw [cnt, cnt]
  refine card_le_card fun I hI => ?_
  simp only [mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI ⊢
  exact ⟨hI.1.trans h, hI.2⟩

theorem cnt_zero : cnt K 0 = 0 := by
  rw [cnt, card_eq_zero, filter_eq_empty_iff]
  intro I hI
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, nonpos_iff_eq_zero] at hI
  exact fun h => h (absNorm_eq_zero_iff.mp hI)

variable (K) in
theorem cnt_le_linear : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ y : ℕ, (cnt K y : ℝ) ≤ C0 * y := by
  set κ := dedekindZeta_residue K
  have hev := (tendsto_cnt K).eventually (Iio_mem_nhds (show κ < κ + 1 by linarith))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  have hκ : 0 < κ := dedekindZeta_residue_pos K
  refine ⟨(κ + 1) * (N0 + 1), by positivity, fun y => ?_⟩
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [cnt_zero]
  have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
  by_cases hyN : N0 ≤ y
  · have h1 := hN0 y hyN
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  · push_neg at hyN
    have hNpos : 0 < max N0 1 := by omega
    have h1 := hN0 (max N0 1) (le_max_left _ _)
    rw [div_lt_iff₀ (by exact_mod_cast hNpos)] at h1
    have h2 : (cnt K y : ℝ) ≤ cnt K (max N0 1) := by exact_mod_cast cnt_mono (by omega)
    have h3 : ((max N0 1 : ℕ) : ℝ) ≤ N0 + 1 := by
      have : max N0 1 ≤ N0 + 1 := by omega
      exact_mod_cast this
    have h4 : (κ + 1) * ((max N0 1 : ℕ) : ℝ) ≤ (κ + 1) * (N0 + 1) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (κ + 1) * (N0 + 1) ≤ (κ + 1) * (N0 + 1) * y :=
      le_mul_of_one_le_right (by positivity) hy'
    linarith

end LaneC978

end

/-! Lemma 3, part d: `∑_{m ≤ x} ρ(m) ≤ C x` for `f` irreducible over `ℚ`. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

/-- Prime factors of a product of prime powers over a set `S` of primes lie in `S`. -/
theorem primeFactors_prod_pow_subset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) :
    ∀ q ∈ (∏ p ∈ S, p ^ e p).primeFactors, q ∈ S := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hdvd := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨p, hp, hqd⟩ := (Nat.Prime.prime hqp).dvd_finset_prod_iff _ |>.mp hdvd
  have := (Nat.prime_dvd_prime_iff_eq hqp (hS p hp)).mp (hqp.dvd_of_dvd_pow hqd)
  rw [this]; exact hp

theorem coprime_prod_pow (S T : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hST : Disjoint S T) (e : ℕ → ℕ) :
    Nat.Coprime (∏ p ∈ S, p ^ e p) (∏ p ∈ T, p ^ e p) := by
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  refine Nat.Coprime.pow _ _ ((Nat.coprime_primes (hS p hp) (hT q hq)).mpr ?_)
  rintro rfl; exact Finset.disjoint_left.mp hST hp hq

theorem prod_pow_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) :
    0 < ∏ p ∈ S, p ^ e p :=
  prod_pos fun p hp => pow_pos (hS p hp).pos _

theorem sum_rho_le (f : ℤ[X]) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, (∑ m ∈ Icc 1 x, (rho f m : ℝ)) ≤ C * x := by
  classical
  obtain ⟨K, _, _, θ, hmin, hexp⟩ := exists_theta f hf
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout f hf hd
  set a := f.leadingCoeff with ha
  have hf0 : f ≠ 0 := by rintro rfl; simp at hd
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set Bnum := a.natAbs * RingOfIntegers.exponent θ * D.natAbs with hBnum
  have hBnum0 : Bnum ≠ 0 := by
    simp only [hBnum, ne_eq, mul_eq_zero, Int.natAbs_eq_zero, not_or]
    exact ⟨⟨ha0, hexp⟩, hD0⟩
  set B := Bnum.primeFactors with hBdef
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- good primes
  have hgood : ∀ p, p.Prime → p ∉ B → ¬ (p : ℤ) ∣ a ∧
      ¬ p ∣ RingOfIntegers.exponent θ ∧ ¬ (p : ℤ) ∣ D := by
    intro p hp hpB
    have hmem : ∀ d, d ∣ Bnum → p ∣ d → False := fun d hdB hpd =>
      hpB (Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdB, hBnum0⟩)
    refine ⟨fun h => hmem a.natAbs ?_ (Int.natCast_dvd.mp h), fun h => hmem _ ?_ h,
      fun h => hmem D.natAbs ?_ (Int.natCast_dvd.mp h)⟩
    · exact Dvd.intro _ (by rw [hBnum, mul_assoc])
    · exact (Dvd.intro_left _ rfl :
        RingOfIntegers.exponent θ ∣ a.natAbs * RingOfIntegers.exponent θ).trans (Dvd.intro _ rfl)
    · exact Dvd.intro_left (a.natAbs * RingOfIntegers.exponent θ) rfl
  -- bad prime powers
  set Cb : ℕ → ℕ := fun p => max 1 (p ^ (2 * D.natAbs.factorization p + 1)) with hCb
  have hC : ∀ p ∈ B, ∀ j, rho f (p ^ j) ≤ Cb p := by
    intro p hp j
    have hpp := hBp p hp
    have hδ : ¬ (p : ℤ) ^ (D.natAbs.factorization p + 1) ∣ D := by
      intro h
      apply Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hD0) hpp
      have : ((p ^ (D.natAbs.factorization p + 1) : ℕ) : ℤ) ∣ D := by push_cast; exact h
      exact Int.natCast_dvd.mp this
    exact (rho_prime_pow_le hB hpp hδ j).trans (le_max_right _ _)
  set CB := ∏ p ∈ B, Cb p with hCB
  -- the split m = u w
  set uP : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors with p ∈ B, p ^ m.factorization p with huP
  set wP : ℕ → ℕ := fun m => ∏ p ∈ m.primeFactors with p ∉ B, p ^ m.factorization p with hwP
  have hpf : ∀ m : ℕ, ∀ p ∈ m.primeFactors, p.Prime := fun m p hp => Nat.prime_of_mem_primeFactors hp
  have hsplit : ∀ m, 0 < m → uP m * wP m = m := by
    intro m hm
    simp only [huP, hwP]
    rw [prod_filter_mul_prod_filter_not]
    exact prod_primeFactors_pow m hm.ne'
  have hupos : ∀ m, 0 < uP m := fun m =>
    prod_pow_pos _ (fun p hp => hpf m p (mem_filter.mp hp).1) _
  have hwpos : ∀ m, 0 < wP m := fun m =>
    prod_pow_pos _ (fun p hp => hpf m p (mem_filter.mp hp).1) _
  have hcop : ∀ m, Nat.Coprime (uP m) (wP m) := fun m =>
    coprime_prod_pow _ _ (fun p hp => hpf m p (mem_filter.mp hp).1)
      (fun p hp => hpf m p (mem_filter.mp hp).1) (disjoint_filter_filter_not _ _ _) _
  have huB : ∀ m, ∀ q ∈ (uP m).primeFactors, q ∈ B := fun m q hq =>
    (mem_filter.mp (primeFactors_prod_pow_subset _ (fun p hp => hpf m p (mem_filter.mp hp).1) _
      q hq)).2
  have hwG : ∀ m, ∀ q ∈ (wP m).primeFactors, q ∉ B := fun m q hq =>
    (mem_filter.mp (primeFactors_prod_pow_subset _ (fun p hp => hpf m p (mem_filter.mp hp).1) _
      q hq)).2
  -- pointwise bound
  have hpt : ∀ m, 0 < m → rho f m ≤ CB * nI K (wP m) := by
    intro m hm
    have he : rho f m = rho f (uP m * wP m) := by rw [hsplit m hm]
    rw [he]
    refine (rho_mul_le f (hupos m) (hwpos m) (hcop m)).trans ?_
    gcongr
    · exact rho_smooth_le f B Cb (fun p => le_max_left _ _) hC _ (hupos m) (huB m)
    · exact rho_good_le hd hmin hB _ (hwpos m) (fun p hp => hgood p
        (Nat.prime_of_mem_primeFactors hp) (hwG m p hp))
  obtain ⟨C0, hC0, hcnt⟩ := cnt_le_linear K
  set P := Bnum + 1
  set CU := ∏ p ∈ P.primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ with hCU
  have hCU0 : 0 ≤ CU := by
    refine prod_nonneg fun p hp => inv_nonneg.mpr ?_
    have hp2 : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp2
    linarith
  refine ⟨CB * C0 * CU, by positivity, fun x => ?_⟩
  set U := (Icc 1 x).filter (fun w => ∀ q ∈ w.primeFactors, q ∈ B) with hU
  have hUs : ∀ w ∈ U, w ∈ P.smoothNumbers := by
    intro w hw
    rw [hU, mem_filter, mem_Icc] at hw
    refine Nat.mem_smoothNumbers_of_primeFactors_subset (by omega) fun q hq => ?_
    rw [mem_range]
    have := Nat.le_of_mem_primeFactors (hw.2 q hq)
    omega
  -- the sum over m injects into pairs (u, w)
  have hinj : Set.InjOn (fun m => (uP m, wP m)) (Icc 1 x : Set ℕ) := by
    intro m hm m' hm' h
    simp only [coe_Icc, Set.mem_Icc, Prod.mk.injEq] at hm hm' h
    rw [← hsplit m (by omega), ← hsplit m' (by omega), h.1, h.2]
  have hsub : (Icc 1 x).image (fun m => (uP m, wP m)) ⊆
      (U ×ˢ Icc 1 x).filter (fun pr => pr.1 * pr.2 ≤ x) := by
    intro pr hpr
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hpr
    rw [mem_Icc] at hm
    have hs := hsplit m (by omega)
    simp only [mem_filter, mem_product, hU, mem_Icc]
    have hu1 := hupos m
    have hw1 := hwpos m
    have hule : uP m ≤ x := by
      have := Nat.le_of_dvd (by omega) (Dvd.intro _ hs); omega
    have hwle : wP m ≤ x := by
      have := Nat.le_of_dvd (by omega) (Dvd.intro_left _ hs); omega
    exact ⟨⟨⟨⟨by omega, hule⟩, huB m⟩, by omega, hwle⟩, by rw [hs]; exact hm.2⟩
  calc (∑ m ∈ Icc 1 x, (rho f m : ℝ))
      ≤ ∑ m ∈ Icc 1 x, (CB * nI K (wP m) : ℝ) := by
        refine sum_le_sum fun m hm => ?_
        exact_mod_cast hpt m (by rw [mem_Icc] at hm; omega)
    _ = CB * ∑ pr ∈ (Icc 1 x).image (fun m => (uP m, wP m)), (nI K pr.2 : ℝ) := by
        rw [sum_image hinj, mul_sum]
    _ ≤ CB * ∑ pr ∈ (U ×ˢ Icc 1 x).filter (fun pr => pr.1 * pr.2 ≤ x), (nI K pr.2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)) (by positivity)
    _ = CB * ∑ w ∈ U, ∑ y ∈ Icc 1 (x / w), (nI K y : ℝ) := by
        congr 1
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun w hw => ?_
        rw [← sum_filter]
        have hw1 : 1 ≤ w := (mem_Icc.mp (mem_filter.mp hw).1).1
        congr 1
        ext y
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩
        · rintro ⟨h1, h2⟩
          have := (Nat.le_div_iff_mul_le (by omega)).mp h2
          refine ⟨⟨h1, ?_⟩, by linarith⟩
          nlinarith
    _ = CB * ∑ w ∈ U, (cnt K (x / w) : ℝ) := by
        congr 1
        refine sum_congr rfl fun w _ => ?_
        rw [← sum_nI_eq_cnt]; push_cast; rfl
    _ ≤ CB * ∑ w ∈ U, C0 * x * (w : ℝ)⁻¹ := by
        gcongr with w hw
        refine (hcnt _).trans ?_
        rw [mul_assoc]
        gcongr
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = CB * C0 * x * ∑ w ∈ U, (w : ℝ)⁻¹ := by rw [← mul_sum]; ring
    _ ≤ CB * C0 * x * CU := by
        gcongr
        exact sum_inv_smooth_le P U hUs
    _ = CB * C0 * CU * x := by ring

end LaneC978

end

/-! Counting integers in residue classes: `#{n < N : n mod W ∈ T} ≤ #T (N/W + 1)`, and the
Chinese remainder combination of a root condition mod `m` with conditions mod primes `q`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

theorem count_mod_le (N W : ℕ) (hW : 0 < W) (T : Finset ℕ) :
    #{n ∈ range N | n % W ∈ T} ≤ #T * (N / W + 1) := by
  classical
  have hfib := card_eq_sum_card_fiberwise (s := (range N).filter fun n => n % W ∈ T)
    (f := fun n => n % W) (t := T) (fun n hn => (mem_filter.mp hn).2)
  rw [hfib, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun t _ => ?_
  refine (card_le_card_of_injOn (fun n => n / W) (t := range (N / W + 1)) ?_ ?_).trans (by simp)
  · intro n hn
    simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hn
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.1.le)
  · intro n hn n' hn' h
    simp only [coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hn hn'
    rw [← Nat.div_add_mod n W, ← Nat.div_add_mod n' W]
    simp only at h
    rw [h, hn.2, hn'.2]

/-- The set of residues mod `m * ∏ S` meeting all the conditions. -/
def resSet (f : ℤ[X]) (m : ℕ) (S : Finset ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  (range (m * ∏ q ∈ S, q)).filter fun x => (m : ℤ) ∣ f.eval ((x % m : ℕ) : ℤ) ∧
    ∀ q ∈ S, x % q ∈ A q

theorem card_resSet_le (f : ℤ[X]) (m : ℕ) (hm : 0 < m) (A : ℕ → Finset ℕ) :
    ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → (∀ q ∈ S, Nat.Coprime m q) →
      #(resSet f m S A) ≤ rho f m * ∏ q ∈ S, #(A q) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    rw [resSet, rho, prod_empty, prod_empty, mul_one, mul_one]
    refine card_le_card_of_injOn id (fun x hx => ?_) (fun x _ y _ h => h)
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx ⊢
    rw [Nat.mod_eq_of_lt hx.1] at hx
    exact ⟨hx.1, hx.2.1⟩
  | insert q S hqS ih =>
    intro hP hC
    have hq := hP q (mem_insert_self q S)
    have hW : 0 < m * ∏ q ∈ S, q :=
      Nat.mul_pos hm (prod_pos fun r hr => (hP r (mem_insert_of_mem hr)).pos)
    have hcop : Nat.Coprime (m * ∏ q ∈ S, q) q := by
      refine Nat.Coprime.mul_left (hC q (mem_insert_self q S)) ?_
      refine Nat.Coprime.prod_left fun r hr => ?_
      refine (Nat.coprime_primes (hP r (mem_insert_of_mem hr)) hq).mpr ?_
      rintro rfl; exact hqS hr
    have hdvdm : m ∣ m * ∏ q ∈ S, q := dvd_mul_right _ _
    calc #(resSet f m (insert q S) A)
        ≤ #(resSet f m S A ×ˢ A q) := by
          rw [resSet, prod_insert hqS]
          refine card_le_card_of_injOn (fun x => (x % (m * ∏ q ∈ S, q), x % q)) ?_ ?_
          · intro x hx
            simp only [coe_filter, mem_range, Set.mem_ofPred_eq, forall_mem_insert] at hx
            simp only [coe_product, Set.mem_prod, resSet, coe_filter, mem_range,
              Set.mem_ofPred_eq]
            refine ⟨⟨Nat.mod_lt _ hW, ?_, fun r hr => ?_⟩, hx.2.2.1⟩
            · rw [Nat.mod_mod_of_dvd _ hdvdm]; exact hx.2.1
            · rw [Nat.mod_mod_of_dvd _ (dvd_mul_of_dvd_right (dvd_prod_of_mem _ hr) _)]
              exact hx.2.2.2 r hr
          · intro x hx y hy h
            simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
            simp only [Prod.mk.injEq] at h
            have : x ≡ y [MOD (m * ∏ q ∈ S, q) * q] :=
              (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h.1, h.2⟩
            have he : m * (q * ∏ q ∈ S, q) = (m * ∏ q ∈ S, q) * q := by ring
            exact Nat.ModEq.eq_of_lt_of_lt this (he ▸ hx.1) (he ▸ hy.1)
    _ = #(resSet f m S A) * #(A q) := card_product _ _
    _ ≤ rho f m * (∏ q ∈ S, #(A q)) * #(A q) := by
          gcongr
          exact ih (fun r hr => hP r (mem_insert_of_mem hr))
            (fun r hr => hC r (mem_insert_of_mem hr))
    _ = rho f m * ∏ q ∈ insert q S, #(A q) := by rw [prod_insert hqS]; ring

/-- Count of `n < N` with `m ∣ f(n)` and `n mod q ∈ A q` for all `q ∈ S`. -/
theorem count_crt_le (f : ℤ[X]) (N m : ℕ) (hm : 0 < m) (A : ℕ → Finset ℕ) (S : Finset ℕ)
    (hP : ∀ q ∈ S, q.Prime) (hC : ∀ q ∈ S, Nat.Coprime m q) :
    #{n ∈ range N | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧ ∀ q ∈ S, n % q ∈ A q} ≤
      rho f m * (∏ q ∈ S, #(A q)) * (N / (m * ∏ q ∈ S, q) + 1) := by
  classical
  have hW : 0 < m * ∏ q ∈ S, q := Nat.mul_pos hm (prod_pos fun r hr => (hP r hr).pos)
  refine le_trans ?_ ((count_mod_le N _ hW (resSet f m S A)).trans
    (Nat.mul_le_mul_right _ (card_resSet_le f m hm A S hP hC)))
  refine card_le_card fun n hn => ?_
  simp only [mem_filter, mem_range] at hn ⊢
  refine ⟨hn.1, ?_⟩
  simp only [resSet, mem_filter, mem_range]
  refine ⟨Nat.mod_lt _ hW, ?_, fun q hq => ?_⟩
  · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)]
    have := dvd_eval_mod (dvd_refl m) hn.2.1
    exact this
  · rw [Nat.mod_mod_of_dvd _ (dvd_mul_of_dvd_right (dvd_prod_of_mem _ hq) _)]
    exact hn.2.2 q hq

end LaneC978

end

/-! The local power-residue bound: for `q ≡ 1 (mod ℓ)` large and `q ∤ m`, at most a fraction
`1 - 1/(4ℓ)` of the residues `r mod q` have `f(r)/m` an `ℓ`-th power residue. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

/-- Residues `r < q` with `(f(r)/m)^((q-1)/ℓ) = 1` in `ZMod q`. -/
def Aset (f : ℤ[X]) (m q ℓ : ℕ) : Finset ℕ :=
  (range q).filter fun r =>
    (((f.eval (r : ℤ) : ℤ) : ZMod q) * ((m : ZMod q))⁻¹) ^ ((q - 1) / ℓ) = 1

theorem card_Aset_le (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) (hfk : f.natDegree = k) {m q ℓ : ℕ}
    (hq : q.Prime) (hℓ : 2 ≤ ℓ) (hℓq : ℓ ∣ q - 1) (hcop : Nat.Coprime k ℓ)
    (hqa : ¬ (q : ℤ) ∣ f.leadingCoeff) (hqm : ¬ q ∣ m)
    (hqbig : 2 * ℓ * (3 * k ^ 3 + 1 + k) < q) :
    4 * ℓ * #(Aset f m q ℓ) ≤ (4 * ℓ - 1) * q := by
  classical
  haveI := Fact.mk hq
  set s := (q - 1) / ℓ with hs
  have hsℓ : ℓ * s = q - 1 := Nat.mul_div_cancel' hℓq
  have hm0 : (m : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqm
  set g : (ZMod q)[X] := C ((m : ZMod q)⁻¹) * f.map (Int.castRingHom (ZMod q)) with hg
  have hlc : (Int.castRingHom (ZMod q)) f.leadingCoeff ≠ 0 := by
    rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqa
  have hgk : g.natDegree = k := by
    rw [hg, natDegree_C_mul (inv_ne_zero hm0), natDegree_map_of_leadingCoeff_ne_zero _ hlc, hfk]
  have hst := stepanov hℓ hsℓ g hk hgk hcop hqbig
  have hcard : #(Aset f m q ℓ) = #{r : ZMod q | g.eval r ^ s = 1} := by
    refine card_nbij (fun r => (r : ZMod q)) ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, Aset, mem_range, Set.mem_ofPred_eq] at hr
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      rw [hg, eval_mul, eval_C, show ((r : ℕ) : ZMod q) = (((r : ℕ) : ℤ) : ZMod q) by push_cast; rfl,
        eval_intCast_map, eq_intCast, mul_comm]
      exact hr.2
    · intro r hr r' hr' h
      simp only [coe_filter, Aset, mem_range, Set.mem_ofPred_eq] at hr hr'
      have := congrArg ZMod.val h
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hr'.1] at this
      exact this
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
      simp only [coe_filter, Aset, mem_range, Set.mem_ofPred_eq]
      refine ⟨ZMod.val_lt x, ?_⟩
      have := hx
      rw [hg, eval_mul, eval_C, ← ZMod.natCast_zmod_val x,
        show ((x.val : ℕ) : ZMod q) = (((x.val : ℕ) : ℤ) : ZMod q) by push_cast; rfl,
        eval_intCast_map, eq_intCast, mul_comm] at this
      exact this
  rw [hcard]
  exact hst

/-- Exceptional values land in `Aset`. -/
theorem mem_Aset (f : ℤ[X]) {k m q ℓ p n : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q)
    (hqm : ¬ q ∣ m) (hℓq : ℓ ∣ q - 1) (hℓk : ℓ ∣ k - 1) (hℓ : 0 < ℓ)
    (hfn : f.eval (n : ℤ) = (m : ℤ) * (p : ℤ) ^ (k - 1)) :
    n % q ∈ Aset f m q ℓ := by
  haveI := Fact.mk hq
  simp only [Aset, mem_filter, mem_range]
  refine ⟨Nat.mod_lt _ hq.pos, ?_⟩
  have hm0 : (m : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqm
  have hp0 : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hcast : (((f.eval ((n % q : ℕ) : ℤ)) : ℤ) : ZMod q) = ((f.eval (n : ℤ) : ℤ) : ZMod q) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 := sub_dvd_eval_sub ((n % q : ℕ) : ℤ) (n : ℤ) f
    have h2 : (q : ℤ) ∣ ((n % q : ℕ) : ℤ) - n := by
      have h3 := Nat.modEq_iff_dvd.mp (Nat.mod_modEq n q)
      rw [← dvd_neg, neg_sub]; exact h3
    rw [dvd_sub_comm]; exact h2.trans h1
  rw [hcast, hfn]
  push_cast
  rw [mul_comm (m : ZMod q), mul_assoc, mul_inv_cancel₀ hm0, mul_one]
  obtain ⟨t, ht⟩ := hℓk
  have he : (ℓ * t) * ((q - 1) / ℓ) = t * (q - 1) := by
    rw [mul_comm ℓ t, mul_assoc, Nat.mul_div_cancel' hℓq]
  rw [ht, ← pow_mul, he, pow_mul, ZMod.pow_card_sub_one_eq_one (pow_ne_zero _ hp0)]

end LaneC978

end

/-! Few `n < N` have many prime factors from a fixed finite set `Q` of primes dividing `f(n)`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- Number of primes of `Q` dividing `f(n)`. -/
def omQ (f : ℤ[X]) (Q : Finset ℕ) (n : ℕ) : ℕ := #{q ∈ Q | ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}

theorem count_all_dvd_le (f : ℤ[X]) (N : ℕ) (E : Finset ℕ) (hE : ∀ q ∈ E, q.Prime)
    (hlc : ∀ q ∈ E, ¬ (q : ℤ) ∣ f.leadingCoeff) :
    (#{n ∈ range N | ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ) ≤
      (f.natDegree : ℝ) ^ #E * (N / ∏ q ∈ E, (q : ℝ) + 1) := by
  classical
  set A : ℕ → Finset ℕ := fun q => (range q).filter fun r => (q : ℤ) ∣ f.eval ((r : ℕ) : ℤ)
  have h := count_crt_le f N 1 one_pos A E hE (fun q _ => Nat.coprime_one_left q)
  have hsub : ((range N).filter fun n => ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)) ⊆
      (range N).filter fun n => ((1 : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧ ∀ q ∈ E, n % q ∈ A q := by
    intro n hn
    simp only [mem_filter, mem_range] at hn ⊢
    refine ⟨hn.1, by simp, fun q hq => ?_⟩
    simp only [A, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ (hE q hq).pos, dvd_eval_mod (dvd_refl q) (hn.2 q hq)⟩
  have h1 := (card_le_card hsub).trans h
  rw [rho_one, one_mul, one_mul] at h1
  have hA : ∀ q ∈ E, #(A q) ≤ f.natDegree := fun q hq => rho_le (hE q hq) (hlc q hq)
  have hprodA : (∏ q ∈ E, #(A q) : ℝ) ≤ (f.natDegree : ℝ) ^ #E := by
    rw [← prod_const]
    exact_mod_cast prod_le_prod' fun q hq => hA q hq
  have hdiv : ((N / ∏ q ∈ E, q : ℕ) : ℝ) ≤ N / ∏ q ∈ E, (q : ℝ) := by
    rw [← Nat.cast_prod]; exact Nat.cast_div_le
  calc (#{n ∈ range N | ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ)
      ≤ ((∏ q ∈ E, #(A q)) * (N / ∏ q ∈ E, q + 1) : ℕ) := by exact_mod_cast h1
    _ ≤ (f.natDegree : ℝ) ^ #E * (N / ∏ q ∈ E, (q : ℝ) + 1) := by
      push_cast
      gcongr

theorem sum_two_pow_omQ (f : ℤ[X]) (N : ℕ) (Q : Finset ℕ) :
    ∑ n ∈ range N, (2 : ℝ) ^ omQ f Q n =
      ∑ E ∈ Q.powerset, (#{n ∈ range N | ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ) := by
  classical
  have h1 : ∀ n, (2 : ℝ) ^ omQ f Q n =
      ∑ E ∈ Q.powerset, if ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ) then 1 else 0 := by
    intro n
    rw [sum_boole, omQ]
    have : (Q.filter fun q => ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)).powerset =
        Q.powerset.filter fun E => ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ) := by
      ext E
      simp only [mem_powerset, mem_filter, subset_iff]
      constructor
      · intro h; exact ⟨fun q hq => (h hq).1, fun q hq => (h hq).2⟩
      · intro h q hq; exact ⟨h.1 hq, h.2 q hq⟩
    rw [← this, card_powerset]
    push_cast; ring
  simp_rw [h1]
  rw [sum_comm]
  refine sum_congr rfl fun E _ => ?_
  rw [sum_boole]

theorem card_many_le (f : ℤ[X]) (N R : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hlc : ∀ q ∈ Q, ¬ (q : ℤ) ∣ f.leadingCoeff) (hQ2 : ∀ q ∈ Q, 1 ≤ q) :
    (2 : ℝ) ^ R * #{n ∈ range N | R ≤ omQ f Q n} ≤
      N * ∏ q ∈ Q, (1 + f.natDegree / (q : ℝ)) + (1 + f.natDegree) ^ #Q := by
  classical
  have hM : (2 : ℝ) ^ R * #{n ∈ range N | R ≤ omQ f Q n} ≤ ∑ n ∈ range N, (2 : ℝ) ^ omQ f Q n := by
    calc (2 : ℝ) ^ R * #{n ∈ range N | R ≤ omQ f Q n}
        = ∑ n ∈ (range N).filter (fun n => R ≤ omQ f Q n), (2 : ℝ) ^ R := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ (range N).filter (fun n => R ≤ omQ f Q n), (2 : ℝ) ^ omQ f Q n :=
          sum_le_sum fun n hn => pow_le_pow_right₀ (by norm_num) (mem_filter.mp hn).2
      _ ≤ ∑ n ∈ range N, (2 : ℝ) ^ omQ f Q n :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  refine hM.trans ?_
  rw [sum_two_pow_omQ]
  calc ∑ E ∈ Q.powerset, (#{n ∈ range N | ∀ q ∈ E, ((q : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ)
      ≤ ∑ E ∈ Q.powerset, ((f.natDegree : ℝ) ^ #E * (N / ∏ q ∈ E, (q : ℝ) + 1)) := by
        refine sum_le_sum fun E hE => ?_
        have hEQ := mem_powerset.mp hE
        exact count_all_dvd_le f N E (fun q hq => hQ q (hEQ hq)) (fun q hq => hlc q (hEQ hq))
    _ = N * ∑ E ∈ Q.powerset, ∏ q ∈ E, ((f.natDegree : ℝ) / q) +
          ∑ E ∈ Q.powerset, ∏ q ∈ E, (f.natDegree : ℝ) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun E _ => ?_
        rw [prod_const, prod_div_distrib, prod_const]
        ring
    _ = N * ∏ q ∈ Q, (1 + f.natDegree / (q : ℝ)) + (1 + f.natDegree) ^ #Q := by
        rw [prod_one_add, ← prod_const, prod_one_add]

theorem prod_one_add_le_exp (Q : Finset ℕ) (z : ℕ) (hQ : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ z) (k : ℝ)
    (hk : 0 ≤ k) : ∏ q ∈ Q, (1 + k / (q : ℝ)) ≤ Real.exp (k * (1 + Real.log z)) := by
  have h1 : ∏ q ∈ Q, (1 + k / (q : ℝ)) ≤ ∏ q ∈ Q, Real.exp (k / q) :=
    prod_le_prod (fun q _ => by positivity) (fun q _ => by linarith [Real.add_one_le_exp (k / q)])
  rw [← Real.exp_sum] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have h2 : ∑ q ∈ Q, k / (q : ℝ) ≤ ∑ i ∈ range z, k / ((i + 1 : ℕ) : ℝ) := by
    have : ∑ q ∈ Q, k / (q : ℝ) = ∑ i ∈ Q.image (fun q => q - 1), k / ((i + 1 : ℕ) : ℝ) := by
      rw [sum_image]
      · refine sum_congr rfl fun q hq => ?_
        congr 2; have := (hQ q hq).1; push_cast [Nat.sub_add_cancel this]; ring
      · intro a ha b hb h
        have := (hQ a ha).1; have := (hQ b hb).1
        simp only at h; omega
    rw [this]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro i hi
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hi
    have := hQ q hq
    rw [mem_range]; omega
  have h3 : ∑ i ∈ range z, k / ((i + 1 : ℕ) : ℝ) = k * (harmonic z : ℝ) := by
    rw [harmonic, Rat.cast_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [h3] at h2
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log z) hk

end LaneC978

end

/-! The bound on one dyadic level `b^z ≤ N/m < b^(z+1)` of cofactors `m`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- Cofactors of level `z`. -/
def Lev (N b z M : ℕ) : Finset ℕ := (Icc 1 M).filter fun m => Nat.log b (N / m) = z

theorem lev_props {N b z M m : ℕ} (hb : 1 < b) (hz : 1 ≤ z) (hm : m ∈ Lev N b z M) :
    1 ≤ m ∧ m ≤ N / b ^ z ∧ N < m * b ^ (z + 1) := by
  simp only [Lev, mem_filter, mem_Icc] at hm
  obtain ⟨⟨h1, -⟩, h2⟩ := hm
  have hNm : N / m ≠ 0 := by
    intro h0; rw [h0, Nat.log_zero_right] at h2; omega
  have hpow := Nat.pow_log_le_self b hNm
  rw [h2] at hpow
  have hlt := Nat.lt_pow_succ_log_self hb (N / m)
  rw [h2] at hlt
  refine ⟨h1, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le (pow_pos (by omega) _)]
    have := (Nat.le_div_iff_mul_le (by omega)).mp hpow
    linarith
  · have h3 : N < (N / m + 1) * m := by
      have := Nat.lt_div_mul_add (a := N) (show 0 < m by omega)
      linarith
    calc N < (N / m + 1) * m := h3
      _ ≤ b ^ (z + 1) * m := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
      _ = m * b ^ (z + 1) := mul_comm _ _

/-- The number of `ρ`-weighted cofactors of level `z`. -/
theorem lev_sums (f : ℤ[X]) {N b z M : ℕ} (hb : 1 < b) (hz : 1 ≤ z) {Cρ : ℝ}
    (hCρ : ∀ x : ℕ, (∑ m ∈ Icc 1 x, (rho f m : ℝ)) ≤ Cρ * x) :
    (∑ m ∈ Lev N b z M, (rho f m : ℝ) / m) ≤ Cρ * b ∧
      (∑ m ∈ Lev N b z M, (rho f m : ℝ)) ≤ Cρ * (N / b ^ z : ℕ) := by
  have hsub : Lev N b z M ⊆ Icc 1 (N / b ^ z) := by
    intro m hm
    have := lev_props hb hz hm
    rw [mem_Icc]; exact ⟨this.1, this.2.1⟩
  have hS : (∑ m ∈ Lev N b z M, (rho f m : ℝ)) ≤ Cρ * (N / b ^ z : ℕ) :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans (hCρ _)
  refine ⟨?_, hS⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : Lev N b z M = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro m hm
      have := lev_props hb hz hm
      have : N / b ^ z = 0 := by rw [hN]; simp
      omega
    rw [this, sum_empty]
    have : (0 : ℝ) ≤ Cρ := by
      have := hCρ 1; simp [rho_one] at this; linarith
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbr : (1 : ℝ) < b := by exact_mod_cast hb
  have h1 : ∀ m ∈ Lev N b z M, (rho f m : ℝ) / m ≤ (rho f m : ℝ) * (b ^ (z + 1) / N) := by
    intro m hm
    have hp := lev_props hb hz hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hp.1
    have hlt : (N : ℝ) < m * b ^ (z + 1) := by exact_mod_cast hp.2.2
    rw [div_eq_mul_inv]
    gcongr
    rw [inv_le_comm₀ hm0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
    linarith
  calc (∑ m ∈ Lev N b z M, (rho f m : ℝ) / m)
      ≤ ∑ m ∈ Lev N b z M, (rho f m : ℝ) * (b ^ (z + 1) / N) := sum_le_sum h1
    _ = (∑ m ∈ Lev N b z M, (rho f m : ℝ)) * (b ^ (z + 1) / N) := by rw [sum_mul]
    _ ≤ Cρ * (N / b ^ z : ℕ) * (b ^ (z + 1) / N) := by gcongr
    _ ≤ Cρ * ((N : ℝ) / b ^ z) * (b ^ (z + 1) / N) := by
        have hC : 0 ≤ Cρ := by
          have := hCρ 1; simp [rho_one] at this; linarith
        gcongr
        exact Nat.cast_div_le.trans (by push_cast; rfl)
    _ = Cρ * b := by
        field_simp
        ring

end LaneC978

end

/-! The count of one level, after removing the inputs with many small prime divisors. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- Number of primes of `Q` dividing `m`. -/
def omQm (Q : Finset ℕ) (m : ℕ) : ℕ := #{q ∈ Q | q ∣ m}

/-- Inputs `n < N` whose cofactor `m` has level `z`, few primes of `Q`, and all the
power-residue conditions. -/
def Tset (f : ℤ[X]) (N : ℕ) (Q : Finset ℕ) (ℓ m : ℕ) : Finset ℕ :=
  (range N).filter fun n => (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ) ∧
    ∀ q ∈ Q.filter (fun q => ¬ q ∣ m), n % q ∈ Aset f m q ℓ

theorem card_Tset_le (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) (hfk : f.natDegree = k) {N ℓ z m R : ℕ}
    (hℓ : 2 ≤ ℓ) (hcop : Nat.Coprime k ℓ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ ℓ ∣ q - 1 ∧ ¬ (q : ℤ) ∣ f.leadingCoeff ∧
      2 * ℓ * (3 * k ^ 3 + 1 + k) < q)
    (hm : 0 < m) (hmR : omQm Q m < R) :
    (#(Tset f N Q ℓ m) : ℝ) ≤
      rho f m * ((1 - 1 / (4 * ℓ : ℝ)) ^ (#Q - R) * N / m + 4 ^ z) := by
  set S := Q.filter (fun q => ¬ q ∣ m) with hS
  have hSP : ∀ q ∈ S, q.Prime := fun q hq => (hQ q (mem_filter.mp hq).1).1
  have hSC : ∀ q ∈ S, Nat.Coprime m q := fun q hq =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hSP q hq)).mpr (mem_filter.mp hq).2)
  have h1 := count_crt_le f N m hm (fun q => Aset f m q ℓ) S hSP hSC
  set θ : ℝ := 1 - 1 / (4 * ℓ : ℝ) with hθ
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_one (by positivity)]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; have : 0 ≤ 1 / (4 * ℓ : ℝ) := by positivity
                         linarith
  have hA : ∀ q ∈ S, (#(Aset f m q ℓ) : ℝ) ≤ θ * q := by
    intro q hq
    obtain ⟨hqp, -, hℓq, hqa, hqbig⟩ := hQ q (mem_filter.mp hq).1
    have := card_Aset_le f hk hfk hqp hℓ hℓq hcop hqa (mem_filter.mp hq).2 hqbig
    have h4 : (4 * ℓ : ℝ) * #(Aset f m q ℓ) ≤ (4 * ℓ - 1) * q := by
      have h41 : ((4 * ℓ - 1 : ℕ) : ℝ) = 4 * ℓ - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * ℓ)]; ring
      rw [← h41]; exact_mod_cast this
    have h4l : (0 : ℝ) < 4 * ℓ := by positivity
    have he : θ * q = (4 * ℓ - 1) * q / (4 * ℓ) := by rw [hθ]; field_simp
    rw [he, le_div_iff₀ h4l]
    linarith
  have hprodA : (∏ q ∈ S, (#(Aset f m q ℓ) : ℝ)) ≤ θ ^ #S * ∏ q ∈ S, (q : ℝ) := by
    calc (∏ q ∈ S, (#(Aset f m q ℓ) : ℝ)) ≤ ∏ q ∈ S, (θ * q) :=
          prod_le_prod (fun _ _ => Nat.cast_nonneg _) hA
      _ = θ ^ #S * ∏ q ∈ S, (q : ℝ) := by rw [prod_mul_distrib, prod_const]
  have hprodS : (∏ q ∈ S, (q : ℝ)) ≤ 4 ^ z := by
    have hsub : S ⊆ (range (z + 1)).filter Nat.Prime := by
      intro q hq
      obtain ⟨hqp, hqz, -⟩ := hQ q (mem_filter.mp hq).1
      rw [mem_filter, mem_range]; exact ⟨by omega, hqp⟩
    have : (∏ q ∈ S, q) ≤ primorial z := by
      rw [primorial]
      exact prod_le_prod_of_subset_of_one_le' hsub (fun p hp _ => (mem_filter.mp hp).2.one_lt.le)
    have h4 := this.trans (primorial_le_four_pow z)
    have h5 : ((∏ q ∈ S, q : ℕ) : ℝ) ≤ ((4 ^ z : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5; exact h5
  have hprodA' : (∏ q ∈ S, (#(Aset f m q ℓ) : ℝ)) ≤ ∏ q ∈ S, (q : ℝ) := by
    refine hprodA.trans ?_
    calc θ ^ #S * ∏ q ∈ S, (q : ℝ) ≤ 1 * ∏ q ∈ S, (q : ℝ) := by
          gcongr; exact pow_le_one₀ hθ0 hθ1
      _ = _ := one_mul _
  have hcardS : #Q - R ≤ #S := by
    have e1 : #(Q.filter (fun q => q ∣ m)) + #S = #Q := by
      rw [hS]; exact card_filter_add_card_filter_not (fun q => q ∣ m)
    have e2 : omQm Q m = #(Q.filter (fun q => q ∣ m)) := rfl
    omega
  have hθpow : θ ^ #S ≤ θ ^ (#Q - R) := pow_le_pow_of_le_one hθ0 hθ1 hcardS
  have hS0 : (0 : ℝ) < ∏ q ∈ S, (q : ℝ) := prod_pos fun q hq => by exact_mod_cast (hSP q hq).pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : ((N / (m * ∏ q ∈ S, q) : ℕ) : ℝ) ≤ N / (m * ∏ q ∈ S, (q : ℝ)) := by
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := m * ∏ q ∈ S, q)
    push_cast at this; exact this
  have h1' : #(Tset f N Q ℓ m) ≤
      rho f m * (∏ q ∈ S, #(Aset f m q ℓ)) * (N / (m * ∏ q ∈ S, q) + 1) := h1
  set Ap : ℕ := ∏ q ∈ S, #(Aset f m q ℓ) with hAp
  set Sp : ℕ := ∏ q ∈ S, q with hSp
  have hApr : (Ap : ℝ) = ∏ q ∈ S, (#(Aset f m q ℓ) : ℝ) := by rw [hAp, Nat.cast_prod]
  have hSpr : (Sp : ℝ) = ∏ q ∈ S, (q : ℝ) := by rw [hSp, Nat.cast_prod]
  rw [← hApr] at hprodA hprodA'
  rw [← hSpr] at hprodA hprodA' hprodS hS0
  have hdiv' : ((N / (m * Sp) : ℕ) : ℝ) ≤ N / (m * (Sp : ℝ)) := by
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := m * Sp)
    rw [Nat.cast_mul] at this; exact this
  have hmS : (0 : ℝ) < m * Sp := mul_pos hm0 hS0
  calc (#(Tset f N Q ℓ m) : ℝ)
      ≤ ((rho f m * Ap * (N / (m * Sp) + 1) : ℕ) : ℝ) := Nat.cast_le.mpr h1'
    _ = (rho f m : ℝ) * Ap * (((N / (m * Sp) : ℕ) : ℝ) + 1) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ (rho f m : ℝ) * Ap * (N / (m * (Sp : ℝ)) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hdiv'])
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = rho f m * (Ap * N / (m * Sp) + Ap) := by ring
    _ ≤ rho f m * (θ ^ #S * Sp * N / (m * Sp) + 4 ^ z) := by
        gcongr
        exact hprodA'.trans hprodS
    _ = rho f m * (θ ^ #S * N / m + 4 ^ z) := by
        congr 2
        field_simp
    _ ≤ rho f m * (θ ^ (#Q - R) * N / m + 4 ^ z) := by gcongr

end LaneC978

end

/-! Summing the level bound over the cofactors of one level. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

theorem level_total (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) (hfk : f.natDegree = k) {N ℓ z M R b : ℕ}
    (hℓ : 2 ≤ ℓ) (hcop : Nat.Coprime k ℓ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ ℓ ∣ q - 1 ∧ ¬ (q : ℤ) ∣ f.leadingCoeff ∧
      2 * ℓ * (3 * k ^ 3 + 1 + k) < q)
    (hb : 1 < b) (hz : 1 ≤ z) {Cρ : ℝ}
    (hCρ : ∀ x : ℕ, (∑ m ∈ Icc 1 x, (rho f m : ℝ)) ≤ Cρ * x) :
    (∑ m ∈ (Lev N b z M).filter (fun m => omQm Q m < R), (#(Tset f N Q ℓ m) : ℝ)) ≤
      Cρ * b * N * (1 - 1 / (4 * ℓ : ℝ)) ^ (#Q - R) + Cρ * (N / b ^ z : ℕ) * 4 ^ z := by
  set θ : ℝ := 1 - 1 / (4 * ℓ : ℝ) with hθ
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_one (by positivity)]; linarith
  have hsums := lev_sums f (N := N) (z := z) (M := M) hb hz hCρ
  have hsub : (Lev N b z M).filter (fun m => omQm Q m < R) ⊆ Lev N b z M := filter_subset _ _
  calc (∑ m ∈ (Lev N b z M).filter (fun m => omQm Q m < R), (#(Tset f N Q ℓ m) : ℝ))
      ≤ ∑ m ∈ (Lev N b z M).filter (fun m => omQm Q m < R),
          (rho f m * (θ ^ (#Q - R) * N / m + 4 ^ z) : ℝ) := by
        refine sum_le_sum fun m hm => ?_
        have hmL := (mem_filter.mp hm)
        have hp := lev_props hb hz hmL.1
        exact card_Tset_le f hk hfk hℓ hcop Q hQ (by omega) hmL.2
    _ ≤ ∑ m ∈ Lev N b z M, (rho f m * (θ ^ (#Q - R) * N / m + 4 ^ z) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = θ ^ (#Q - R) * N * (∑ m ∈ Lev N b z M, (rho f m : ℝ) / m) +
          4 ^ z * ∑ m ∈ Lev N b z M, (rho f m : ℝ) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun m _ => ?_
        ring
    _ ≤ θ ^ (#Q - R) * N * (Cρ * b) + 4 ^ z * (Cρ * (N / b ^ z : ℕ)) := by
        gcongr
        · exact hsums.1
        · exact hsums.2
    _ = Cρ * b * N * θ ^ (#Q - R) + Cρ * (N / b ^ z : ℕ) * 4 ^ z := by ring

end LaneC978

end

/-! Primes `≡ 1 (mod ℓ)` are not too sparse: for every `A`, eventually more than `A log x` primes
`p ≡ 1 (mod ℓ)` divide `∏_{k ≤ x} Φ_ℓ(k)`. Elementary, via the Nagell-type valuation budget. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem cyc_prime_dvd {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (k : ℕ)
    (h : (p : ℤ) ∣ (cyclotomic ℓ ℤ).eval (k : ℤ)) : p = ℓ ∨ p % ℓ = 1 := by
  haveI := Fact.mk hp
  by_cases hpl : p = ℓ
  · exact Or.inl hpl
  right
  have hroot : IsRoot (cyclotomic ℓ (ZMod p)) (k : ZMod p) := by
    rw [IsRoot.def, ← map_cyclotomic_int ℓ (ZMod p), show ((k : ℕ) : ZMod p) = ((k : ℤ) : ZMod p)
      by push_cast; rfl, eval_intCast_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  have hne : NeZero (ℓ : ZMod p) := by
    refine ⟨?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hd)
  have hprim := (isRoot_cyclotomic_iff.mp hroot)
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hprim
    have := hprim.pow_eq_one
    rw [zero_pow hℓ.ne_zero] at this
    exact zero_ne_one this
  have hdiv : orderOf (k : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hk0
  rw [← hprim.eq_orderOf] at hdiv
  have h1 : p % ℓ = 1 % ℓ := by
    have := (Nat.modEq_iff_dvd' hp.one_lt.le).mpr hdiv
    exact this.symm
  rw [h1, Nat.mod_eq_of_lt hℓ.one_lt]

end LaneC978

end

/-! The budget argument for `Φ_ℓ`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem eventually_dominate (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∀ᶠ x : ℕ in atTop, K * (x + Real.log x ^ 2 + Real.log x + 1) < c * x * Real.log x := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (8 * K / c), eventually_ge_atTop 1] with x hx hx1
  have hx1r : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1r
  have hl1 : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hsq : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_rpow_div (x := x) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hsq2 : Real.log x ^ 2 ≤ 4 * x := by
    have h := pow_le_pow_left₀ hl0 hsq 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h; linarith
  have h7 : K * (x + Real.log x ^ 2 + Real.log x + 1) ≤ K * (7 * x) := by
    apply mul_le_mul_of_nonneg_left _ hK; linarith
  have h8 : K * (7 * x) < c * x * Real.log x := by
    have : 8 * K < c * Real.log x := by rw [div_lt_iff₀ hc] at hx; linarith
    nlinarith
  linarith

set_option maxHeartbeats 2000000 in
theorem many_one_mod {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : 3 ≤ ℓ) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ x : ℕ in atTop,
      A * Real.log x < #((Nat.primesLE (S * x ^ (ℓ - 1))).filter fun p => p % ℓ = 1) := by
  classical
  set F : ℤ[X] := cyclotomic ℓ ℤ with hF
  have hFirr : Irreducible F := cyclotomic.irreducible hℓ.pos
  have hFQ : Irreducible (F.map (Int.castRingHom ℚ)) := by
    rw [hF, map_cyclotomic_int]; exact cyclotomic.irreducible_rat hℓ.pos
  have hdeg : F.natDegree = ℓ - 1 := by
    rw [hF, natDegree_cyclotomic, Nat.totient_prime hℓ]
  have hd2 : 2 ≤ F.natDegree := by omega
  have hlc : F.leadingCoeff = 1 := (cyclotomic.monic ℓ ℤ).leadingCoeff
  obtain ⟨S, hS1, hS⟩ := natAbs_eval_le F
  obtain ⟨C1, hC1⟩ := log_abs_eval_ge hFirr hd2
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout F hFQ (by omega)
  refine ⟨S, hS1, fun A hA => ?_⟩
  set d := ℓ - 1 with hd
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  set Bad : Finset ℕ := (ℓ * D.natAbs).primeFactors with hBad
  have hBad0 : ℓ * D.natAbs ≠ 0 := mul_ne_zero hℓ.ne_zero (Int.natAbs_ne_zero.mpr hD0)
  set Bterm : ℕ → ℝ := fun p => (((padicValInt p D : ℕ) + (p : ℝ) ^ (padicValInt p D + 1)) *
    Real.log p + (p : ℝ) ^ (padicValInt p D + 1)) with hBterm
  have hBterm0 : ∀ p, 0 ≤ Bterm p := fun p => by
    have := Real.log_natCast_nonneg p; positivity
  set CB : ℝ := ∑ p ∈ Bad, Bterm p with hCB
  have hCB0 : 0 ≤ CB := sum_nonneg fun p _ => hBterm0 p
  -- the threshold `T`
  set T : ℕ := ⌈256 * A ^ 2⌉₊ + 3 with hT
  have hT3 : (3 : ℝ) ≤ T := by rw [hT]; push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈256 * A ^ 2⌉₊
                               linarith
  have hTA : 8 * A * (Real.log T / T) ≤ 1 := by
    have hT0 : (0 : ℝ) < T := by linarith
    have hlogT : Real.log T ≤ 2 * Real.sqrt T := by
      have := Real.log_le_rpow_div (x := T) hT0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [← Real.sqrt_eq_rpow] at this; linarith
    have hsT : 16 * A ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by positivity) hT0.le]
      have : 256 * A ^ 2 ≤ T := by
        rw [hT]; push_cast; have := Nat.le_ceil (256 * A ^ 2); linarith
      nlinarith
    have hsqT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
    have hsq0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
    rw [mul_div_assoc', div_le_one hT0]
    calc 8 * A * Real.log T ≤ 8 * A * (2 * Real.sqrt T) := by gcongr
      _ = 16 * A * Real.sqrt T := by ring
      _ ≤ Real.sqrt T * Real.sqrt T := by gcongr
      _ = T := hsqT
  -- constants in the final inequality
  have hlS : 0 ≤ Real.log S := Real.log_natCast_nonneg _
  set c : ℝ := (ℓ - 1 : ℝ) / 4 with hc
  have hℓr : (3 : ℝ) ≤ ℓ := by exact_mod_cast h3
  have hc0 : 0 < c := by rw [hc]; linarith
  set K : ℝ := ((ℓ : ℝ) - 1) * T * (1 + Real.log S + d) + d + |C1| + CB * (1 + Real.log S + d) +
    ((ℓ : ℝ) - 1) * A * (Real.log S + d) + 1 with hK
  have hK0 : 0 ≤ K := by
    have := abs_nonneg C1
    have : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
    positivity
  filter_upwards [eventually_dominate c K hc0 hK0, eventually_ge_atTop 1] with x hdom hx1
  by_contra hcon
  push_neg at hcon
  set H := S * x ^ d with hH
  have hx1r : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1r
  have hH0 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have hlogH : Real.log H = Real.log S + d * Real.log x := by
    rw [hH, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
  have hf0 : ∀ k ∈ Icc 1 x, F.eval ((k : ℕ) : ℤ) ≠ 0 := fun k _ => eval_ne_zero hFirr hd2 _
  have hHk : ∀ k ∈ Icc 1 x, (F.eval ((k : ℕ) : ℤ)).natAbs ≤ H := by
    intro k hk
    rw [mem_Icc] at hk
    refine (hS k hk.1).trans ?_
    rw [hdeg, hH]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk.2 _)
  -- lower bound
  have hlow : (d : ℝ) * (x * Real.log x - x) - C1 * x ≤
      ∑ k ∈ Icc 1 x, Real.log |((F.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
    have h1 : ∑ k ∈ Icc 1 x, ((d : ℝ) * Real.log k - C1) ≤
        ∑ k ∈ Icc 1 x, Real.log |((F.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| :=
      sum_le_sum fun k hk => by
        have := hC1 k (mem_Icc.mp hk).1; rw [hdeg] at this; exact this
    have h2 : ∑ k ∈ Icc 1 x, Real.log k = Real.log x.factorial := by
      rw [← Real.log_prod (fun k hk => by
        have := (mem_Icc.mp hk).1; positivity)]
      congr 1
      rw [← Nat.cast_prod, show Icc 1 x = Ico 1 (x + 1) from rfl, Finset.prod_Ico_id_eq_factorial]
    have h3 := log_factorial_ge x
    rw [sum_sub_distrib, ← mul_sum, h2, sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    simp only [add_tsub_cancel_right] at h1
    have : (d : ℝ) * (x * Real.log x - x) ≤ d * Real.log x.factorial :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  -- upper bound through the prime factorization
  have hP : ∀ p, p.Prime → p ∣ (∏ k ∈ Icc 1 x, F.eval ((k : ℕ) : ℤ)).natAbs → p ≤ H := by
    intro p hp hdvd
    rw [show (∏ k ∈ Icc 1 x, F.eval ((k : ℕ) : ℤ)).natAbs =
      ∏ k ∈ Icc 1 x, (F.eval ((k : ℕ) : ℤ)).natAbs from map_prod Int.natAbsHom _ _] at hdvd
    obtain ⟨k, hk, hpk⟩ := (Nat.Prime.prime hp).dvd_finset_prod_iff _ |>.mp hdvd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (hf0 k hk))) hpk).trans
      (hHk k hk)
  have heq := sum_log_eq F x H hf0 hP
  set e : ℕ → ℝ := fun p => ((∑ k ∈ Icc 1 x, (F.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ)
    * Real.log p with he
  -- each prime
  have hzero : ∀ p ∈ Nat.primesLE H, p ∉ Bad → p % ℓ ≠ 1 → e p = 0 := by
    intro p hp hpB hpl
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have : ∑ k ∈ Icc 1 x, (F.eval ((k : ℕ) : ℤ)).natAbs.factorization p = 0 := by
      refine sum_eq_zero fun k _ => ?_
      refine Nat.factorization_eq_zero_of_not_dvd fun hd' => ?_
      have hdz : (p : ℤ) ∣ F.eval ((k : ℕ) : ℤ) := Int.natCast_dvd.mpr hd'
      rcases cyc_prime_dvd hℓ hpp k hdz with h | h
      · exact hpB (Nat.mem_primeFactors.mpr ⟨hpp, by rw [h]; exact dvd_mul_right _ _, hBad0⟩)
      · exact hpl h
    simp only [he, this, Nat.cast_zero, zero_mul]
  have hgood : ∀ p ∈ Nat.primesLE H, p ∉ Bad →
      e p ≤ (ℓ - 1 : ℝ) * (x * Real.log p / (p - 1) + Real.log H) := by
    intro p hp hpB
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hpD : ¬ (p : ℤ) ∣ D := fun hd' => hpB (Nat.mem_primeFactors.mpr ⟨hpp,
      dvd_mul_of_dvd_right (Int.natCast_dvd.mp hd') _, hBad0⟩)
    have h1 := ep_log_good hB hpp hpD x H hH0 hf0 hHk
    have hr : (rho F p : ℝ) ≤ ℓ - 1 := by
      have := rho_le hpp (by rw [hlc]; exact_mod_cast hpp.not_dvd_one)
      rw [hdeg] at this
      have h' : ((ℓ - 1 : ℕ) : ℝ) = ℓ - 1 := by push_cast [Nat.cast_sub hℓ.one_lt.le]; ring
      rw [← h']; exact_mod_cast this
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hnn : 0 ≤ x * Real.log p / (p - 1) + Real.log H := by
      have := Real.log_natCast_nonneg p; have := Real.log_natCast_nonneg H
      have : (0 : ℝ) < p - 1 := by linarith
      positivity
    exact h1.trans (mul_le_mul_of_nonneg_right hr hnn)
  have hbad : ∀ p ∈ Bad, e p ≤ Bterm p * (x + Real.log H) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ep_log_bad hB hD0 hpp x H hH0 hf0 hHk
  -- split the sum
  set G := (Nat.primesLE H).filter fun p => p ∉ Bad ∧ p % ℓ = 1 with hG
  have hsplit : ∑ p ∈ Nat.primesLE H, e p ≤
      ∑ p ∈ G, (ℓ - 1 : ℝ) * (x * Real.log p / (p - 1) + Real.log H) +
        CB * (x + Real.log H) := by
    rw [← sum_filter_add_sum_filter_not (Nat.primesLE H) (fun p => p ∈ Bad)]
    have hB1 : ∑ p ∈ (Nat.primesLE H).filter (fun p => p ∈ Bad), e p ≤ CB * (x + Real.log H) := by
      calc ∑ p ∈ (Nat.primesLE H).filter (fun p => p ∈ Bad), e p
          ≤ ∑ p ∈ (Nat.primesLE H).filter (fun p => p ∈ Bad), Bterm p * (x + Real.log H) :=
            sum_le_sum fun p hp => hbad p (mem_filter.mp hp).2
        _ ≤ ∑ p ∈ Bad, Bterm p * (x + Real.log H) := by
            refine sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.mp hp).2) ?_
            intro p _ _
            have := Real.log_natCast_nonneg H
            have := hBterm0 p
            positivity
        _ = CB * (x + Real.log H) := by rw [hCB, sum_mul]
    have hB2 : ∑ p ∈ (Nat.primesLE H).filter (fun p => p ∉ Bad), e p ≤
        ∑ p ∈ G, (ℓ - 1 : ℝ) * (x * Real.log p / (p - 1) + Real.log H) := by
      rw [← sum_filter_add_sum_filter_not ((Nat.primesLE H).filter (fun p => p ∉ Bad))
        (fun p => p % ℓ = 1)]
      have hz : ∑ p ∈ ((Nat.primesLE H).filter (fun p => p ∉ Bad)).filter (fun p => ¬ p % ℓ = 1),
          e p = 0 := by
        refine sum_eq_zero fun p hp => ?_
        simp only [mem_filter] at hp
        exact hzero p hp.1.1 hp.1.2 hp.2
      rw [hz, add_zero, filter_filter]
      exact sum_le_sum fun p hp => hgood p (mem_filter.mp hp).1 (mem_filter.mp hp).2.1
    linarith
  -- the sum over `G`
  have hGsub : G ⊆ (Nat.primesLE H).filter fun p => p % ℓ = 1 := by
    intro p hp; simp only [hG, mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
  have hM : (#G : ℝ) ≤ A * Real.log x := by
    have := card_le_card hGsub; exact (by exact_mod_cast this : (#G : ℝ) ≤ _).trans hcon
  have hGsum : ∑ p ∈ G, (x * Real.log p / (p - 1) + Real.log H) ≤
      T * (x + Real.log H) + #G * (2 * x * (Real.log T / T) + Real.log H) := by
    rw [← sum_filter_add_sum_filter_not G (fun p => p ≤ T)]
    have hlo : ∑ p ∈ G.filter (fun p => p ≤ T), (x * Real.log p / (p - 1) + Real.log H) ≤
        T * (x + Real.log H) := by
      calc ∑ p ∈ G.filter (fun p => p ≤ T), (x * Real.log p / (p - 1) + Real.log H)
          ≤ ∑ p ∈ G.filter (fun p => p ≤ T), (x + Real.log H) := by
            refine sum_le_sum fun p hp => ?_
            have hpp : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
            have h1 : Real.log p ≤ p - 1 := Real.log_le_sub_one_of_pos (by linarith)
            have : x * Real.log p / (p - 1) ≤ x := by
              rw [div_le_iff₀ (by linarith)]; nlinarith
            linarith
        _ = #(G.filter (fun p => p ≤ T)) * (x + Real.log H) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ T * (x + Real.log H) := by
            have hcard : #(G.filter (fun p => p ≤ T)) ≤ T := by
              refine (card_le_card (s := G.filter (fun p => p ≤ T)) (t := Icc 1 T) ?_).trans
                (by simp)
              intro p hp
              simp only [mem_filter, mem_Icc] at hp ⊢
              have hpp : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp hp.1).1).2
              exact ⟨hpp.one_lt.le, hp.2⟩
            have := Real.log_natCast_nonneg H
            gcongr
    have hhi : ∑ p ∈ G.filter (fun p => ¬ p ≤ T), (x * Real.log p / (p - 1) + Real.log H) ≤
        #G * (2 * x * (Real.log T / T) + Real.log H) := by
      calc ∑ p ∈ G.filter (fun p => ¬ p ≤ T), (x * Real.log p / (p - 1) + Real.log H)
          ≤ ∑ p ∈ G.filter (fun p => ¬ p ≤ T), (2 * x * (Real.log T / T) + Real.log H) := by
            refine sum_le_sum fun p hp => ?_
            have hpT : (T : ℝ) ≤ p := by
              have := (mem_filter.mp hp).2; exact_mod_cast (not_le.mp this).le
            have hp3 : (3 : ℝ) ≤ p := hT3.trans hpT
            have he1 : Real.exp 1 ≤ (T : ℝ) := by
              have := Real.exp_one_lt_d9; linarith
            have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he1)
              (Set.mem_Ici.mpr (he1.trans hpT)) hpT
            simp only at hanti
            have h1 : Real.log p / (p - 1) ≤ 2 * (Real.log p / p) := by
              have hlp := Real.log_natCast_nonneg p
              calc Real.log p / (p - 1) ≤ Real.log p / (p / 2) :=
                    div_le_div_of_nonneg_left hlp (by linarith) (by linarith)
                _ = 2 * (Real.log p / p) := by field_simp
            have h2 : x * Real.log p / (p - 1) ≤ 2 * x * (Real.log T / T) := by
              rw [mul_div_assoc]
              calc x * (Real.log p / (p - 1)) ≤ x * (2 * (Real.log p / p)) := by gcongr
                _ ≤ x * (2 * (Real.log T / T)) := by gcongr
                _ = 2 * x * (Real.log T / T) := by ring
            linarith
        _ = #(G.filter (fun p => ¬ p ≤ T)) * (2 * x * (Real.log T / T) + Real.log H) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ #G * (2 * x * (Real.log T / T) + Real.log H) := by
            have : 0 ≤ 2 * x * (Real.log T / T) + Real.log H := by
              have := Real.log_natCast_nonneg H; have := Real.log_natCast_nonneg T
              positivity
            gcongr
            exact filter_subset _ _
    linarith
  -- combine
  have hmain : (d : ℝ) * (x * Real.log x - x) - C1 * x ≤
      (ℓ - 1 : ℝ) * (T * (x + Real.log H) + A * Real.log x * (2 * x * (Real.log T / T) +
        Real.log H)) + CB * (x + Real.log H) := by
    have h1 := (hlow.trans heq.le).trans hsplit
    have h2 : ∑ p ∈ G, (ℓ - 1 : ℝ) * (x * Real.log p / (p - 1) + Real.log H) ≤
        (ℓ - 1 : ℝ) * (T * (x + Real.log H) + A * Real.log x * (2 * x * (Real.log T / T) +
          Real.log H)) := by
      rw [← mul_sum]
      have hℓ1 : (0 : ℝ) ≤ ℓ - 1 := by linarith
      apply mul_le_mul_of_nonneg_left _ hℓ1
      refine hGsum.trans ?_
      have : 0 ≤ 2 * x * (Real.log T / T) + Real.log H := by
        have := Real.log_natCast_nonneg H; have := Real.log_natCast_nonneg T
        positivity
      nlinarith
    linarith
  have hdℓ : (d : ℝ) = ℓ - 1 := by rw [hd]; push_cast [Nat.cast_sub hℓ.one_lt.le]; ring
  rw [hlogH, hdℓ] at hmain
  -- `2 (ℓ-1) A (log T / T) x log x ≤ (ℓ-1)/4 x log x`
  have hkey : (ℓ - 1 : ℝ) * (A * Real.log x * (2 * x * (Real.log T / T))) ≤
      c * x * Real.log x := by
    rw [hc]
    have hℓ1 : (0 : ℝ) ≤ ℓ - 1 := by linarith
    have : A * (2 * (Real.log T / T)) ≤ 1 / 4 := by linarith
    have hxl : 0 ≤ x * Real.log x := by positivity
    calc (ℓ - 1 : ℝ) * (A * Real.log x * (2 * x * (Real.log T / T)))
        = (ℓ - 1) * (A * (2 * (Real.log T / T))) * (x * Real.log x) := by ring
      _ ≤ (ℓ - 1) * (1 / 4) * (x * Real.log x) := by gcongr
      _ = (ℓ - 1) / 4 * x * Real.log x := by ring
  have hK' : K * (x + Real.log x ^ 2 + Real.log x + 1) < c * x * Real.log x := hdom
  set L := Real.log x with hL
  set Ls := Real.log S with hLs
  have hℓ1 : (0 : ℝ) ≤ ℓ - 1 := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set a1 : ℝ := (ℓ - 1) * T + CB + (ℓ - 1) + C1 with ha1
  set a2 : ℝ := (ℓ - 1) * A * (ℓ - 1) with ha2
  set a3 : ℝ := (ℓ - 1) * T * (ℓ - 1) + (ℓ - 1) * A * Ls + CB * (ℓ - 1) with ha3
  set a4 : ℝ := (ℓ - 1) * T * Ls + CB * Ls with ha4
  have hdK : (d : ℝ) = ℓ - 1 := hdℓ
  have h1 : a1 ≤ K := by
    have := le_abs_self C1
    have : (ℓ - 1 : ℝ) * T ≤ (ℓ - 1 : ℝ) * T * (1 + Ls + d) := by
      have : (1 : ℝ) ≤ 1 + Ls + d := by have := Nat.cast_nonneg (α := ℝ) d; have : 0 ≤ Ls := Real.log_natCast_nonneg S; linarith
      exact le_mul_of_one_le_right (by positivity) this
    have : CB ≤ CB * (1 + Ls + d) := by
      have : (1 : ℝ) ≤ 1 + Ls + d := by have := Nat.cast_nonneg (α := ℝ) d; have : 0 ≤ Ls := Real.log_natCast_nonneg S; linarith
      exact le_mul_of_one_le_right hCB0 this
    have : 0 ≤ (ℓ - 1 : ℝ) * A * (Ls + d) := by
      have := Nat.cast_nonneg (α := ℝ) d; positivity
    rw [ha1, hK]
    linarith [hdK]
  have h2 : a2 ≤ K := by
    have : (ℓ - 1 : ℝ) * A * (ℓ - 1) ≤ (ℓ - 1) * A * (Ls + d) := by
      rw [hdK]; have : 0 ≤ (ℓ - 1 : ℝ) * A := by positivity
      have : 0 ≤ Ls := Real.log_natCast_nonneg S
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have : 0 ≤ (ℓ - 1 : ℝ) * T * (1 + Ls + d) := by
      have := Nat.cast_nonneg (α := ℝ) d; positivity
    have : 0 ≤ CB * (1 + Ls + d) := by have := Nat.cast_nonneg (α := ℝ) d; positivity
    have := abs_nonneg C1
    have := Nat.cast_nonneg (α := ℝ) d
    rw [ha2, hK]; linarith
  have h3 : a3 ≤ K := by
    have e1 : (ℓ - 1 : ℝ) * T * (ℓ - 1) + CB * (ℓ - 1) ≤
        (ℓ - 1) * T * (1 + Ls + d) + CB * (1 + Ls + d) := by
      rw [hdK]
      have h' : (ℓ - 1 : ℝ) ≤ 1 + Ls + (ℓ - 1) := by
        have : 0 ≤ Ls := Real.log_natCast_nonneg S; linarith
      exact add_le_add (mul_le_mul_of_nonneg_left h' (by positivity))
        (mul_le_mul_of_nonneg_left h' hCB0)
    have e2 : (ℓ - 1 : ℝ) * A * Ls ≤ (ℓ - 1) * A * (Ls + d) := by
      have := Nat.cast_nonneg (α := ℝ) d
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := abs_nonneg C1
    have := Nat.cast_nonneg (α := ℝ) d
    rw [ha3, hK]; linarith
  have h4 : a4 ≤ K := by
    have e1 : (ℓ - 1 : ℝ) * T * Ls + CB * Ls ≤ (ℓ - 1) * T * (1 + Ls + d) + CB * (1 + Ls + d) := by
      have h' : Ls ≤ 1 + Ls + d := by have := Nat.cast_nonneg (α := ℝ) d; linarith
      exact add_le_add (mul_le_mul_of_nonneg_left h' (by positivity))
        (mul_le_mul_of_nonneg_left h' hCB0)
    have : 0 ≤ (ℓ - 1 : ℝ) * A * (Ls + d) := by
      have := Nat.cast_nonneg (α := ℝ) d; positivity
    have := abs_nonneg C1
    have := Nat.cast_nonneg (α := ℝ) d
    rw [ha4, hK]; linarith
  have hxr : (0 : ℝ) ≤ x := by linarith
  have hR : a1 * x + a2 * L ^ 2 + a3 * L + a4 ≤ K * (x + L ^ 2 + L + 1) := by
    have : a1 * x ≤ K * x := mul_le_mul_of_nonneg_right h1 hxr
    have : a2 * L ^ 2 ≤ K * L ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    have : a3 * L ≤ K * L := mul_le_mul_of_nonneg_right h3 hlx
    rw [show K * (x + L ^ 2 + L + 1) = K * x + K * L ^ 2 + K * L + K by ring]
    linarith
  have hexp : (ℓ - 1 : ℝ) * (T * (x + (Ls + (ℓ - 1) * L)) + A * L * (2 * x * (Real.log T / T) +
        (Ls + (ℓ - 1) * L))) + CB * (x + (Ls + (ℓ - 1) * L)) =
      (ℓ - 1 : ℝ) * (A * L * (2 * x * (Real.log T / T))) +
        (a1 * x + a2 * L ^ 2 + a3 * L + a4) - (ℓ - 1) * x - C1 * x := by
    rw [ha1, ha2, ha3, ha4]; ring
  rw [hexp] at hmain
  have hxl : 0 ≤ x * L := by positivity
  have hcx : c * x * L = ((ℓ : ℝ) - 1) / 4 * (x * L) := by rw [hc]; ring
  have hfin0 : 0 ≤ ((ℓ : ℝ) - 1) * (x * L) := mul_nonneg hℓ1 hxl
  have hmain' : ((ℓ : ℝ) - 1) * (x * L) ≤ (ℓ - 1 : ℝ) * (A * L * (2 * x * (Real.log T / T))) +
      (a1 * x + a2 * L ^ 2 + a3 * L + a4) := by linarith
  have hpos : 0 < ((ℓ : ℝ) - 1) * (x * L) ∨ ((ℓ : ℝ) - 1) * (x * L) = 0 := by
    rcases hfin0.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  linarith

end LaneC978

end

/-! For every `c`, eventually `c · log₂ z ≤ #{q ≤ z prime : q > q0, q ≡ 1 (mod ℓ)}`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

/-- The sieving primes up to `z`. -/
def Qz (ℓ q0 z : ℕ) : Finset ℕ := (Icc 1 z).filter fun q => q.Prime ∧ q0 < q ∧ q % ℓ = 1

theorem Qz_card_ge_sub (ℓ q0 z : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z ∧ p % ℓ = 1) :
    #P ≤ #(Qz ℓ q0 z) + q0 := by
  classical
  have h1 : P ⊆ Qz ℓ q0 z ∪ Icc 1 q0 := by
    intro p hp
    obtain ⟨hpp, hpz, hpl⟩ := hP p hp
    rw [mem_union, Qz, mem_filter, mem_Icc, mem_Icc]
    by_cases h : q0 < p
    · exact Or.inl ⟨⟨hpp.one_lt.le, hpz⟩, hpp, h, hpl⟩
    · exact Or.inr ⟨hpp.one_lt.le, by omega⟩
  calc #P ≤ #(Qz ℓ q0 z ∪ Icc 1 q0) := card_le_card h1
    _ ≤ #(Qz ℓ q0 z) + #(Icc 1 q0) := card_union_le _ _
    _ = #(Qz ℓ q0 z) + q0 := by simp

theorem HQ_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : 3 ≤ ℓ) (q0 c : ℕ) :
    ∀ᶠ z : ℕ in atTop, c * Nat.log 2 z ≤ #(Qz ℓ q0 z) := by
  obtain ⟨S, hS1, hmany⟩ := many_one_mod hℓ h3
  set d := ℓ - 1 with hd
  set A : ℝ := (2 * c * (d + 1) + q0 + 1) / Real.log 2 with hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hmany A hA0)
  -- choose `z` with `w = log₂ z / (d+1)` large
  have hev : ∀ᶠ z : ℕ in atTop, (d + 1) * (X0 + S + 1) ≤ Nat.log 2 z := by
    filter_upwards [eventually_ge_atTop (2 ^ ((d + 1) * (X0 + S + 1)))] with z hz
    exact Nat.le_log_of_pow_le (by norm_num) hz
  filter_upwards [hev] with z hz
  set j := Nat.log 2 z with hj
  set w := j / (d + 1) with hw
  have hw1 : X0 + S + 1 ≤ w := by rw [hw]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  set x := 2 ^ w with hx
  have hxX : X0 ≤ x := le_trans (show X0 ≤ w by omega) (Nat.lt_two_pow_self (n := w)).le
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hSx : S ≤ 2 ^ w := le_trans (show S ≤ w by omega) (Nat.lt_two_pow_self (n := w)).le
  have hj0 : 0 < j := by
    by_contra h0
    have hj00 : j = 0 := by omega
    rw [hw, hj00, Nat.zero_div] at hw1
    omega
  have hz0 : z ≠ 0 := fun h => by rw [hj, h, Nat.log_zero_right] at hj0; omega
  have hHz : S * x ^ d ≤ z := by
    calc S * x ^ d ≤ 2 ^ w * (2 ^ w) ^ d := Nat.mul_le_mul_right _ hSx
      _ = 2 ^ ((d + 1) * w) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by rw [hw]; exact Nat.mul_div_le j (d + 1))
      _ ≤ z := Nat.pow_log_le_self 2 hz0
  have hcnt := hX0 x hxX
  set P := (Nat.primesLE (S * x ^ d)).filter fun p => p % ℓ = 1 with hP
  have hPsub : ∀ p ∈ P, p.Prime ∧ p ≤ z ∧ p % ℓ = 1 := by
    intro p hp
    rw [hP, mem_filter, Nat.mem_primesLE] at hp
    exact ⟨hp.1.2, hp.1.1.trans hHz, hp.2⟩
  have hle := Qz_card_ge_sub ℓ q0 z P hPsub
  have hlogx : Real.log x = w * Real.log 2 := by
    rw [hx, Nat.cast_pow, Real.log_pow]; push_cast; ring
  rw [hlogx] at hcnt
  have hjw : j < (d + 1) * (w + 1) := by
    rw [hw]
    have := Nat.lt_div_mul_add (a := j) (show 0 < d + 1 by omega)
    linarith
  have hgoal : ((c * j : ℕ) : ℝ) + q0 ≤ A * (w * Real.log 2) := by
    have hAw : A * (w * Real.log 2) = (2 * c * (d + 1) + q0 + 1) * w := by
      rw [hA]; field_simp
    rw [hAw]
    have hj' : (j : ℝ) ≤ (d + 1) * (w + 1) := by exact_mod_cast hjw.le
    have hw1' : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    push_cast
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
    have : (c : ℝ) * j ≤ c * ((d + 1) * (w + 1)) := mul_le_mul_of_nonneg_left hj' hc0
    have h1 : (c : ℝ) * (d + 1) ≤ c * (d + 1) * w := le_mul_of_one_le_right (by positivity) hw1'
    have h2 : (q0 : ℝ) ≤ q0 * w := le_mul_of_one_le_right hq0 hw1'
    have h3 : (0 : ℝ) ≤ w := by linarith
    linarith
  have hfin : ((c * j : ℕ) : ℝ) + q0 < (#(Qz ℓ q0 z) : ℝ) + q0 := by
    have : (#P : ℝ) ≤ #(Qz ℓ q0 z) + q0 := by exact_mod_cast hle
    linarith
  have : ((c * j : ℕ) : ℝ) < #(Qz ℓ q0 z) := by linarith
  exact_mod_cast this.le

end LaneC978

end

/-! The case `ℓ = 2`: odd primes, from Chebyshev's lower bound. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

theorem eventually_sqrt_dominate (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ z : ℕ in atTop, K * (Real.log z ^ 2 + Real.log z + Real.log (z + 1)) + 1 < z * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Tendsto (fun z : ℕ => Real.sqrt z) atTop atTop :=
    (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  filter_upwards [hs.eventually_gt_atTop ((40 * K + 1) / Real.log 2), eventually_ge_atTop 1]
    with z hz hz1
  have hz1r : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hsq0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg _
  have hsq1 : 1 ≤ Real.sqrt z := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hzz : (z : ℝ) = Real.sqrt z * Real.sqrt z := (Real.mul_self_sqrt (by linarith)).symm
  have hl4 : Real.log z ≤ 4 * (z : ℝ) ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div (x := z) (by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show (z : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * (z : ℝ) ^ ((1 : ℝ) / 4) by ring]
  have hq : (z : ℝ) ^ ((1 : ℝ) / 4) * (z : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt z := by
    rw [← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]; norm_num
  have hq0 : 0 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hq1 : (z : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt z := by
    have : 1 ≤ (z : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hz1r (by norm_num)
    nlinarith
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg hz1r
  have hlsq : Real.log z ^ 2 ≤ 16 * Real.sqrt z := by
    have := pow_le_pow_left₀ hl0 hl4 2
    nlinarith
  have hl1 : Real.log z ≤ 4 * Real.sqrt z := by linarith
  have hlz1 : Real.log (z + 1) ≤ Real.log z + 1 := by
    have h2 : Real.log (z + 1) ≤ Real.log (2 * z) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hsum : Real.log z ^ 2 + Real.log z + Real.log (z + 1) ≤ 40 * Real.sqrt z := by linarith
  have hkey : (40 * K + 1) < Real.sqrt z * Real.log 2 := by
    rwa [div_lt_iff₀ hl2] at hz
  calc K * (Real.log z ^ 2 + Real.log z + Real.log (z + 1)) + 1 ≤ K * (40 * Real.sqrt z) + 1 := by
        gcongr
    _ ≤ (40 * K + 1) * Real.sqrt z := by nlinarith
    _ < Real.sqrt z * Real.log 2 * Real.sqrt z := by
        exact mul_lt_mul_of_pos_right hkey (by linarith)
    _ = Real.log 2 * (Real.sqrt z * Real.sqrt z) := by ring
    _ = z * Real.log 2 := by rw [← hzz]; ring

theorem HQ_two (q0 c : ℕ) : ∀ᶠ z : ℕ in atTop, c * Nat.log 2 z ≤ #(Qz 2 q0 z) := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := c / Real.log 2 + q0 + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_sqrt_dominate K hK0, eventually_ge_atTop 2] with z hz hz2
  have hz2r : (2 : ℝ) ≤ z := by exact_mod_cast hz2
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  -- primes up to `z` other than `2`
  set P := (Nat.primesLE z).filter fun p => p % 2 = 1 with hP
  have hPsub : ∀ p ∈ P, p.Prime ∧ p ≤ z ∧ p % 2 = 1 := by
    intro p hp; rw [hP, mem_filter, Nat.mem_primesLE] at hp; exact ⟨hp.1.2, hp.1.1, hp.2⟩
  have hle := Qz_card_ge_sub 2 q0 z P hPsub
  have hPcard : #(Nat.primesLE z) ≤ #P + 1 := by
    have : Nat.primesLE z ⊆ P ∪ {2} := by
      intro p hp
      rw [mem_union, mem_singleton, hP, mem_filter]
      have hpp := (Nat.mem_primesLE.mp hp).2
      rcases hpp.eq_two_or_odd with h | h
      · exact Or.inr h
      · exact Or.inl ⟨hp, h⟩
    exact (card_le_card this).trans ((card_union_le _ _).trans (by simp))
  have hpi := Chebyshev.pi_ge z
  rw [← Nat.primesLE_card_eq_primeCounting] at hpi
  have hlog2 : (Nat.log 2 z : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    have h := Nat.pow_log_le_self 2 (show z ≠ 0 by omega)
    have h' : ((2 ^ Nat.log 2 z : ℕ) : ℝ) ≤ z := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
  -- `c log₂ z + q0 + 1 ≤ π z`
  have hmain : (c : ℝ) * Nat.log 2 z + q0 + 1 < #(Nat.primesLE z) := by
    refine lt_of_lt_of_le ?_ hpi
    rw [lt_div_iff₀ hlz]
    have h1 : (c : ℝ) * Nat.log 2 z ≤ c / Real.log 2 * Real.log z := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
    have hlz1 : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
    have h2 : ((c : ℝ) * Nat.log 2 z + q0 + 1) * Real.log z + Real.log (z + 1) ≤
        K * (Real.log z ^ 2 + Real.log z + Real.log (z + 1)) := by
      have hc2 : 0 ≤ (c : ℝ) / Real.log 2 := by positivity
      have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
      have e1 : ((c : ℝ) * Nat.log 2 z + q0 + 1) * Real.log z ≤
          c / Real.log 2 * Real.log z ^ 2 + (q0 + 1) * Real.log z := by
        have := mul_le_mul_of_nonneg_right h1 hlz.le
        nlinarith
      have e2 : c / Real.log 2 * Real.log z ^ 2 ≤ K * Real.log z ^ 2 :=
        mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (by positivity)
      have e3 : ((q0 : ℝ) + 1) * Real.log z ≤ K * Real.log z :=
        mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hlz.le
      have e4 : Real.log (z + 1) ≤ K * Real.log (z + 1) := by
        have : (1 : ℝ) ≤ K := by rw [hK]; linarith
        exact le_mul_of_one_le_left hlz1 this
      nlinarith
    linarith
  have : (c * Nat.log 2 z : ℝ) < #(Qz 2 q0 z) + 1 := by
    have h1 : ((#(Nat.primesLE z) : ℕ) : ℝ) ≤ #P + 1 := by exact_mod_cast hPcard
    have h2 : ((#P : ℕ) : ℝ) ≤ #(Qz 2 q0 z) + q0 := by exact_mod_cast hle
    linarith
  have : c * Nat.log 2 z < #(Qz 2 q0 z) + 1 := by exact_mod_cast this
  omega

end LaneC978

end

/-! The covering of the exceptional set: small `n`, cofactors of low level (few large primes),
inputs with many small prime factors, and the sieved sets. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- `Qz` (duplicated here so this file does not depend on the prime-counting part). -/
def Qs (ℓ q0 z : ℕ) : Finset ℕ := (Icc 1 z).filter fun q => q.Prime ∧ q0 < q ∧ q % ℓ = 1

open Classical in
/-- The exceptional set below `N`. -/
def Exc (f : ℤ[X]) (N : ℕ) : Finset ℕ :=
  (range N).filter fun n => ∃ p, p.Prime ∧ N < p ∧ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval ((n : ℕ) : ℤ)

/-- Inputs with a prime divisor `p ∈ (N, M]` of `f(n)`. -/
def CaseA (f : ℤ[X]) (N M : ℕ) : Finset ℕ :=
  ((Ioc N M).filter Nat.Prime).biUnion fun p =>
    (range N).filter fun n => (p : ℤ) ∣ f.eval ((n : ℕ) : ℤ)

def B1 (f : ℤ[X]) (N : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (range N).filter fun n => #Q / 2 ≤ omQ f Q n

def Tb (f : ℤ[X]) (N b z M ℓ : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  ((Lev N b z M).filter fun m => omQm Q m < #Q / 2).biUnion fun m => Tset f N Q ℓ m

theorem exc_cover (f : ℤ[X]) {k ℓ q0 b z1 S n0 N : ℕ} (hfk : f.natDegree = k) (hk : 2 ≤ k)
    (hℓk : ℓ ∣ k - 1) (hℓ : 2 ≤ ℓ) (hb : 1 < b) (hz1 : 1 ≤ z1) (hn01 : 1 ≤ n0)
    (hS : ∀ n : ℕ, 1 ≤ n → (f.eval ((n : ℕ) : ℤ)).natAbs ≤ S * n ^ k)
    (hn0 : ∀ n : ℕ, n0 ≤ n → 1 ≤ f.eval ((n : ℕ) : ℤ)) :
    Exc f N ⊆ range n0 ∪ CaseA f N (S * b ^ z1 * N) ∪
      (Icc z1 (Nat.log b N)).biUnion fun z =>
        B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z) := by
  classical
  intro n hn
  simp only [Exc, mem_filter, mem_range] at hn
  obtain ⟨hnN, p, hp, hNp, hpdvd⟩ := hn
  rw [hfk] at hpdvd
  by_cases hsmall : n < n0
  · exact mem_union_left _ (mem_union_left _ (mem_range.mpr hsmall))
  push_neg at hsmall
  have hfpos := hn0 n hsmall
  set fn := (f.eval ((n : ℕ) : ℤ)).toNat with hfn
  have hfnZ : (fn : ℤ) = f.eval ((n : ℕ) : ℤ) := Int.toNat_of_nonneg (by linarith)
  have hpdvdN : p ^ (k - 1) ∣ fn := by
    have : ((p ^ (k - 1) : ℕ) : ℤ) ∣ (fn : ℤ) := by push_cast; rw [hfnZ]; exact hpdvd
    exact_mod_cast this
  set m := fn / p ^ (k - 1) with hm
  have hmeq : fn = m * p ^ (k - 1) := (Nat.div_mul_cancel hpdvdN).symm
  have hfn1 : 1 ≤ fn := by
    have : (1 : ℤ) ≤ fn := by rw [hfnZ]; exact hfpos
    exact_mod_cast this
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hmeq; omega
    · exact h
  have hn1 : 1 ≤ n := le_trans hn01 hsmall
  have hfnle : fn ≤ S * n ^ k := by
    have := hS n hn1
    rwa [show (f.eval ((n : ℕ) : ℤ)).natAbs = fn by rw [hfn]; omega] at this
  have hN1 : 1 ≤ N := by omega
  have hpk : N ^ (k - 1) ≤ p ^ (k - 1) := Nat.pow_le_pow_left hNp.le _
  have hfnN : fn ≤ S * N ^ k := hfnle.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnN.le _))
  have hNk : N ^ k = N * N ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hmS : m ≤ S * N := by
    have h1 : m * N ^ (k - 1) ≤ S * N * N ^ (k - 1) := by
      calc m * N ^ (k - 1) ≤ m * p ^ (k - 1) := Nat.mul_le_mul_left _ hpk
        _ = fn := hmeq.symm
        _ ≤ S * N ^ k := hfnN
        _ = S * N * N ^ (k - 1) := by rw [hNk]; ring
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos (by omega) _)
  have hmdvd : (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ) := by
    rw [← hfnZ]; exact_mod_cast Dvd.intro _ hmeq.symm
  have hfnZ' : f.eval ((n : ℕ) : ℤ) = (m : ℤ) * (p : ℤ) ^ (k - 1) := by
    rw [← hfnZ, hmeq]; push_cast; ring
  set z := Nat.log b (N / m) with hz
  by_cases hzlo : z < z1
  · -- few levels: a large prime in `(N, S b^z1 N]`
    refine mem_union_left _ (mem_union_right _ ?_)
    have hlt : N / m < b ^ z1 := Nat.lt_pow_of_log_lt hb hzlo
    have hNm : N < m * b ^ z1 := by
      have h3 : N < (N / m + 1) * m := by
        have := Nat.lt_div_mul_add (a := N) (show 0 < m by omega); linarith
      calc N < (N / m + 1) * m := h3
        _ ≤ b ^ z1 * m := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
        _ = m * b ^ z1 := mul_comm _ _
    have hpM : p ≤ S * b ^ z1 * N := by
      by_contra hcon
      push_neg at hcon
      have hk1 : 1 ≤ k - 1 := by omega
      have hpow : S * b ^ z1 * N * N ^ (k - 2) < p ^ (k - 1) := by
        have : p ^ (k - 1) = p * p ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
        rw [this]
        exact Nat.mul_lt_mul_of_lt_of_le hcon (Nat.pow_le_pow_left hNp.le _) (pow_pos (by omega) _)
      have hNk' : N ^ k = N * N * N ^ (k - 2) := by
        rw [mul_assoc, ← pow_succ', ← pow_succ']; congr 1; omega
      have : S * N ^ k < fn := by
        calc S * N ^ k = S * N * N * N ^ (k - 2) := by rw [hNk']; ring
          _ ≤ S * (m * b ^ z1) * N * N ^ (k - 2) := by gcongr
          _ = m * (S * b ^ z1 * N * N ^ (k - 2)) := by ring
          _ < m * p ^ (k - 1) := Nat.mul_lt_mul_of_pos_left hpow (by omega)
          _ = fn := hmeq.symm
      omega
    simp only [CaseA, mem_biUnion, mem_filter, mem_Ioc, mem_range]
    refine ⟨p, ⟨⟨hNp, hpM⟩, hp⟩, hnN, ?_⟩
    exact (dvd_pow_self (p : ℤ) (by omega : k - 1 ≠ 0)).trans hpdvd
  push_neg at hzlo
  have hzhi : z ≤ Nat.log b N := Nat.log_mono_right (Nat.div_le_self _ _)
  refine mem_union_right _ (mem_biUnion.mpr ⟨z, mem_Icc.mpr ⟨hzlo, hzhi⟩, ?_⟩)
  set Q := Qs ℓ q0 z with hQ
  by_cases hmany : #Q / 2 ≤ omQ f Q n
  · exact mem_union_left _ (by simp only [B1, mem_filter, mem_range]; exact ⟨hnN, hmany⟩)
  push_neg at hmany
  refine mem_union_right _ ?_
  have hom : omQm Q m ≤ omQ f Q n := by
    refine card_le_card fun q hq => ?_
    simp only [mem_filter] at hq ⊢
    exact ⟨hq.1, (Int.natCast_dvd_natCast.mpr hq.2).trans hmdvd⟩
  simp only [Tb, mem_biUnion, mem_filter]
  refine ⟨m, ⟨?_, by omega⟩, ?_⟩
  · simp only [Lev, mem_filter, mem_Icc]; exact ⟨⟨hm1, hmS⟩, rfl⟩
  · simp only [Tset, mem_filter, mem_range]
    refine ⟨hnN, hmdvd, fun q hq => ?_⟩
    simp only [hQ, Qs, mem_filter, mem_Icc] at hq
    obtain ⟨⟨⟨-, hqz⟩, hqp, -, hql⟩, hqm⟩ := hq
    have hzN : z < N := lt_of_le_of_lt hzhi (Nat.log_lt_self b (by omega))
    have hpq : p ≠ q := by omega
    have hℓq : ℓ ∣ q - 1 := by
      have h1 : 1 ≡ q [MOD ℓ] := by
        rw [Nat.ModEq, hql, Nat.mod_eq_of_lt (by omega)]
      exact (Nat.modEq_iff_dvd' hqp.one_lt.le).mp h1
    exact mem_Aset f hqp hp hpq hqm hℓq hℓk (by omega) hfnZ'

end LaneC978

end

/-! The bound for one level `z` in terms of `1/z²`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

theorem two_pow_log_gt (z : ℕ) : (z : ℝ) / 2 < (2 : ℝ) ^ Nat.log 2 z := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z
  have h' : (z : ℝ) < (2 : ℝ) ^ (Nat.log 2 z + 1) := by exact_mod_cast h
  rw [pow_succ] at h'; linarith

theorem level_bound (f : ℤ[X]) {k ℓ q0 z c' N b : ℕ} (hk : 1 ≤ k) (hfk : f.natDegree = k)
    (hℓ : 2 ≤ ℓ) (hcop : Nat.Coprime k ℓ) (hq0 : 2 * ℓ * (3 * k ^ 3 + 1 + k) < q0)
    (hq0a : f.leadingCoeff.natAbs ≤ q0) (hz : 2 ≤ z) (hc' : k + 2 ≤ c')
    (hθ : (1 - 1 / (4 * ℓ : ℝ)) ^ c' ≤ 1 / 4) (hb : 16 ≤ b)
    (hQ : 2 * c' * Nat.log 2 z ≤ #(Qs ℓ q0 z)) {Cρ : ℝ} (hCρ0 : 0 ≤ Cρ)
    (hCρ : ∀ x : ℕ, (∑ m ∈ Icc 1 x, (rho f m : ℝ)) ≤ Cρ * x) (M : ℕ) :
    (#(B1 f N (Qs ℓ q0 z)) : ℝ) +
        ∑ m ∈ (Lev N b z M).filter (fun m => omQm (Qs ℓ q0 z) m < #(Qs ℓ q0 z) / 2),
          (#(Tset f N (Qs ℓ q0 z) ℓ m) : ℝ) ≤
      N * (Real.exp k * 2 ^ c' + 4 * Cρ * b + Cρ) / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z := by
  set Q := Qs ℓ q0 z with hQdef
  set R := #Q / 2 with hR
  set j := Nat.log 2 z with hj
  have hzr : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hP2 := two_pow_log_gt z
  rw [← hj] at hP2
  have hQprops : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ ℓ ∣ q - 1 ∧ ¬ (q : ℤ) ∣ f.leadingCoeff ∧
      2 * ℓ * (3 * k ^ 3 + 1 + k) < q := by
    intro q hq
    simp only [hQdef, Qs, mem_filter, mem_Icc] at hq
    obtain ⟨⟨-, hqz⟩, hqp, hq0q, hql⟩ := hq
    refine ⟨hqp, hqz, ?_, ?_, by omega⟩
    · have h1 : 1 ≡ q [MOD ℓ] := by rw [Nat.ModEq, hql, Nat.mod_eq_of_lt (by omega)]
      exact (Nat.modEq_iff_dvd' hqp.one_lt.le).mp h1
    · intro hdvd
      have ha0 : f.leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr (fun h => by rw [h, natDegree_zero] at hfk; omega)
      have h1 := Int.natCast_dvd.mp hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) h1
      omega
  have hQcard : #Q ≤ z := by
    calc #Q ≤ #(Icc 1 z) := card_le_card (filter_subset _ _)
      _ = z := by simp
  -- the `B1` part
  have hB1 := card_many_le f N R Q (fun q hq => (hQprops q hq).1) (fun q hq => (hQprops q hq).2.2.2.1)
    (fun q hq => (hQprops q hq).1.one_lt.le)
  have hexp := prod_one_add_le_exp Q z (fun q hq => ⟨(hQprops q hq).1.one_lt.le, (hQprops q hq).2.1⟩)
    (f.natDegree : ℝ) (Nat.cast_nonneg _)
  have hQ' : 2 * (c' * j) ≤ #Q := by rw [← mul_assoc]; exact hQ
  have hRj : c' * j ≤ R := by rw [hR]; omega
  have h2R : ((z : ℝ) / 2) ^ c' ≤ (2 : ℝ) ^ R := by
    calc ((z : ℝ) / 2) ^ c' ≤ ((2 : ℝ) ^ j) ^ c' := pow_le_pow_left₀ (by positivity) hP2.le _
      _ = (2 : ℝ) ^ (c' * j) := by rw [← pow_mul, mul_comm]
      _ ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) hRj
  have hexpk : Real.exp (f.natDegree * (1 + Real.log z)) = Real.exp k * (z : ℝ) ^ k := by
    rw [hfk, mul_add, mul_one, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]
  have hB1' : (#(B1 f N Q) : ℝ) ≤ N * (Real.exp k * 2 ^ c') / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z := by
    have h2Rpos : (0 : ℝ) < 2 ^ R := by positivity
    have hcard : (#(B1 f N Q) : ℝ) ≤ (N * (Real.exp k * (z : ℝ) ^ k) + (1 + k) ^ #Q) / 2 ^ R := by
      rw [le_div_iff₀ h2Rpos, mul_comm]
      refine hB1.trans ?_
      rw [hfk] at hexp ⊢
      rw [← hexpk, hfk]
      gcongr
    refine hcard.trans ?_
    rw [add_div]
    gcongr ?_ + ?_
    · -- `N e^k z^k / 2^R ≤ N e^k 2^c' / z^2`
      rw [div_le_div_iff₀ h2Rpos (by positivity)]
      have hzc : (z : ℝ) ^ k * (z : ℝ) ^ 2 ≤ (z : ℝ) ^ c' := by
        rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) hc'
      have h3 : (z : ℝ) ^ c' = 2 ^ c' * ((z : ℝ) / 2) ^ c' := by
        rw [div_pow, mul_div_cancel₀ _ (by positivity)]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have he : 0 ≤ Real.exp k := (Real.exp_pos _).le
      calc (N : ℝ) * (Real.exp k * (z : ℝ) ^ k) * (z : ℝ) ^ 2
          = N * Real.exp k * ((z : ℝ) ^ k * (z : ℝ) ^ 2) := by ring
        _ ≤ N * Real.exp k * (2 ^ c' * ((z : ℝ) / 2) ^ c') := by rw [← h3]; gcongr
        _ ≤ N * Real.exp k * (2 ^ c' * 2 ^ R) := by gcongr
        _ = N * (Real.exp k * 2 ^ c') * 2 ^ R := by ring
    · -- `(1+k)^#Q / 2^R ≤ (1+k)^z`
      calc ((1 : ℝ) + k) ^ #Q / 2 ^ R ≤ ((1 : ℝ) + k) ^ #Q := div_le_self (by positivity)
            (one_le_pow₀ (by norm_num))
        _ ≤ ((1 : ℝ) + k) ^ z := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) hQcard
  -- the sieved part
  have hlt := level_total f hk hfk hℓ hcop Q hQprops (N := N) (M := M) (R := R) (b := b)
    (by omega) (by omega) hCρ
  set θ : ℝ := 1 - 1 / (4 * ℓ : ℝ) with hθdef
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hθ0 : 0 ≤ θ := by rw [hθdef, sub_nonneg, div_le_one (by positivity)]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθdef]; have : 0 ≤ 1 / (4 * ℓ : ℝ) := by positivity
                         linarith
  have hθpow : θ ^ (#Q - R) ≤ 4 / (z : ℝ) ^ 2 := by
    have hjR : c' * j ≤ #Q - R := by rw [hR]; omega
    calc θ ^ (#Q - R) ≤ θ ^ (c' * j) := pow_le_pow_of_le_one hθ0 hθ1 hjR
      _ = (θ ^ c') ^ j := by rw [pow_mul]
      _ ≤ (1 / 4 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) hθ _
      _ = 1 / ((2 : ℝ) ^ j) ^ 2 := by rw [one_div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
      _ ≤ 1 / ((z : ℝ) / 2) ^ 2 := by
          gcongr
      _ = 4 / (z : ℝ) ^ 2 := by field_simp; ring
  have hb4 : ((N / b ^ z : ℕ) : ℝ) * 4 ^ z ≤ N / (z : ℝ) ^ 2 := by
    have hbr : (16 : ℝ) ≤ b := by exact_mod_cast hb
    have h1 : ((N / b ^ z : ℕ) : ℝ) ≤ N / (b : ℝ) ^ z := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := b ^ z); push_cast at this; exact this
    have h2 : (b : ℝ) ^ z ≥ (4 : ℝ) ^ z * (4 : ℝ) ^ z := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by linarith) _
    have h3 : (z : ℝ) ^ 2 ≤ (4 : ℝ) ^ z := by
      have : (z : ℝ) ≤ 2 ^ z := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (z : ℝ) ^ 2 ≤ ((2 : ℝ) ^ z) ^ 2 := pow_le_pow_left₀ (by positivity) this _
        _ = (4 : ℝ) ^ z := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h4pos : (0 : ℝ) < 4 ^ z := by positivity
    calc ((N / b ^ z : ℕ) : ℝ) * 4 ^ z ≤ N / (b : ℝ) ^ z * 4 ^ z := by gcongr
      _ ≤ N / ((4 : ℝ) ^ z * (4 : ℝ) ^ z) * 4 ^ z := by gcongr
      _ = N / (4 : ℝ) ^ z := by field_simp
      _ ≤ N / (z : ℝ) ^ 2 := by gcongr
  have hTs : (∑ m ∈ (Lev N b z M).filter (fun m => omQm Q m < R), (#(Tset f N Q ℓ m) : ℝ)) ≤
      N * (4 * Cρ * b + Cρ) / (z : ℝ) ^ 2 := by
    refine hlt.trans ?_
    have hbr : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    calc Cρ * b * N * θ ^ (#Q - R) + Cρ * ((N / b ^ z : ℕ) : ℝ) * 4 ^ z
        ≤ Cρ * b * N * (4 / (z : ℝ) ^ 2) + Cρ * (N / (z : ℝ) ^ 2) := by
          have e1 : Cρ * b * N * θ ^ (#Q - R) ≤ Cρ * b * N * (4 / (z : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hθpow (by positivity)
          have e2 : Cρ * ((N / b ^ z : ℕ) : ℝ) * 4 ^ z ≤ Cρ * (N / (z : ℝ) ^ 2) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb4 hCρ0
          linarith
      _ = N * (4 * Cρ * b + Cρ) / (z : ℝ) ^ 2 := by ring
  calc (#(B1 f N Q) : ℝ) + ∑ m ∈ (Lev N b z M).filter (fun m => omQm Q m < R),
        (#(Tset f N Q ℓ m) : ℝ)
      ≤ (N * (Real.exp k * 2 ^ c') / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z) +
          N * (4 * Cρ * b + Cρ) / (z : ℝ) ^ 2 := add_le_add hB1' hTs
    _ = N * (Real.exp k * 2 ^ c' + 4 * Cρ * b + Cρ) / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z := by ring

end LaneC978

end

/-! The large-prime estimate: for every `ε > 0`, eventually `#Exc(N) ≤ ε N`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem sum_inv_sq_le (a : ℕ) (ha : 1 ≤ a) :
    ∀ Z : ℕ, a ≤ Z → ∑ z ∈ Icc a Z, (1 : ℝ) / (z : ℝ) ^ 2 ≤ 2 / a - 1 / Z := by
  intro Z hZ
  induction Z, hZ using Nat.le_induction with
  | base =>
    rw [Icc_self, sum_singleton]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  | succ Z hZ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast (le_trans ha hZ)
    have h : (1 : ℝ) / ((Z + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / Z - 1 / (Z + 1 : ℕ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem sum_inv_sq_le' (a Z : ℕ) (ha : 1 ≤ a) :
    ∑ z ∈ Icc a Z, (1 : ℝ) / (z : ℝ) ^ 2 ≤ 2 / a := by
  by_cases h : a ≤ Z
  · have := sum_inv_sq_le a ha Z h
    have : (0 : ℝ) ≤ 1 / Z := by positivity
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty]; positivity

/-- `k π(T N) ≤ (ε/4) N` eventually. -/
theorem pi_small (k T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (k : ℝ) * Nat.primeCounting (T * N) ≤ ε / 4 * N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  filter_upwards [hlog.eventually_ge_atTop (16 * k * Real.log 4 * T / ε + 1),
    hsq.eventually_ge_atTop (8 * k * Real.sqrt T / ε + 1), eventually_ge_atTop 2] with N h1 h2 hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set x : ℝ := (T : ℝ) * N with hx
  have hx1 : 1 < x := by rw [hx]; nlinarith
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  rw [show ⌊x⌋₊ = T * N by rw [hx]; exact_mod_cast Nat.floor_natCast (T * N)] at hpi
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlx : Real.log N / 2 ≤ Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (by linarith), hx, Real.log_mul (by positivity) (by positivity)]
    have := Real.log_nonneg hTr; linarith
  have hlxpos : 0 < Real.log (Real.sqrt x) := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hsqx : Real.sqrt x = Real.sqrt T * Real.sqrt N := by
    rw [hx, Real.sqrt_mul (by positivity)]
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hsqN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have t1 : (k : ℝ) * (Real.log 4 * x / Real.log (Real.sqrt x)) ≤ ε / 8 * N := by
    rw [mul_div_assoc', div_le_iff₀ hlxpos]
    have : 16 * k * Real.log 4 * T / ε ≤ Real.log N := by linarith
    rw [div_le_iff₀ hε] at this
    rw [hx]
    have hNn : (0 : ℝ) ≤ N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlx (show (0 : ℝ) ≤ ε / 8 * N by positivity)]
  have t2 : (k : ℝ) * Real.sqrt x ≤ ε / 8 * N := by
    rw [hsqx]
    have : 8 * k * Real.sqrt T / ε ≤ Real.sqrt N := by linarith
    rw [div_le_iff₀ hε] at this
    calc (k : ℝ) * (Real.sqrt T * Real.sqrt N) = (k * Real.sqrt T) * Real.sqrt N := by ring
      _ ≤ (ε / 8 * Real.sqrt N) * Real.sqrt N :=
          mul_le_mul_of_nonneg_right (by linarith) hsqN0.le
      _ = ε / 8 * N := by rw [mul_assoc, hsqN]
  calc (k : ℝ) * Nat.primeCounting (T * N) ≤ k * (Real.log 4 * x / Real.log (Real.sqrt x) +
        Real.sqrt x) := mul_le_mul_of_nonneg_left hpi hk0
    _ = k * (Real.log 4 * x / Real.log (Real.sqrt x)) + k * Real.sqrt x := by ring
    _ ≤ ε / 8 * N + ε / 8 * N := add_le_add t1 t2
    _ = ε / 4 * N := by ring

/-- The polynomially many levels contribute `o(N)`. -/
theorem top_small (k L : ℕ) (hk : 1 ≤ k) (hL : 1 + k ≤ 2 ^ L) (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : 16 / ε ^ 2 ≤ N) :
    ((Nat.log (2 ^ (8 * L)) N + 1 : ℕ) : ℝ) * ((1 + k : ℝ)) ^ Nat.log (2 ^ (8 * L)) N ≤ ε / 4 * N := by
  set Z := Nat.log (2 ^ (8 * L)) N with hZ
  set Y : ℝ := (1 + k : ℝ) ^ Z with hY
  have hk1 : (2 : ℝ) ≤ 1 + k := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                   linarith
  have hY1 : 1 ≤ Y := one_le_pow₀ (by linarith)
  have hZY : ((Z + 1 : ℕ) : ℝ) ≤ Y := by
    have h1 : ((Z + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Z := by
      have := Nat.lt_two_pow_self (n := Z)
      exact_mod_cast this
    exact h1.trans (pow_le_pow_left₀ (by norm_num) hk1 _)
  have hY8 : Y ^ 8 ≤ N := by
    have hpow : ((1 + k) ^ 8) ^ Z ≤ (2 ^ (8 * L)) ^ Z := by
      apply Nat.pow_le_pow_left
      calc (1 + k) ^ 8 ≤ (2 ^ L) ^ 8 := Nat.pow_le_pow_left hL _
        _ = 2 ^ (8 * L) := by rw [← pow_mul, mul_comm]
    have hN0 : N ≠ 0 := by
      intro h; rw [h] at hN; simp at hN
      have : 0 < 16 / ε ^ 2 := by positivity
      linarith
    have h2 := Nat.pow_log_le_self (2 ^ (8 * L)) hN0
    rw [← hZ] at h2
    have h3 : ((1 + k) ^ 8) ^ Z ≤ N := hpow.trans h2
    rw [hY, ← pow_mul, mul_comm, pow_mul]
    exact_mod_cast h3
  have hY2 : ((Z + 1 : ℕ) : ℝ) * Y ≤ Y ^ 2 := by rw [sq]; gcongr
  refine hY2.trans ?_
  by_cases hcase : 4 / ε ≤ Y ^ 6
  · calc Y ^ 2 = Y ^ 8 / Y ^ 6 := by field_simp
      _ ≤ N / (4 / ε) := by gcongr
      _ = ε / 4 * N := by field_simp
  · push_neg at hcase
    have h1 : Y ^ 2 ≤ Y ^ 6 := pow_le_pow_right₀ hY1 (by norm_num)
    have h2 : 4 / ε ≤ ε / 4 * N := by
      rw [div_le_iff₀ hε]
      have : 16 / ε ^ 2 * ε ^ 2 = 16 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg ε)]
    linarith

end LaneC978

end

/-! The final assembly: the large-prime estimate of Hooley for `(k-1)`-th powers. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem eventually_eval_pos (f : ℤ[X]) (hd : 0 < f.natDegree) (hlc : 0 < f.leadingCoeff) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → 1 ≤ f.eval ((n : ℕ) : ℤ) := by
  set fR := f.map (Int.castRingHom ℝ)
  have hdeg : fR.natDegree = f.natDegree := natDegree_map_eq_of_injective (RingHom.injective_int _) _
  have hlcR : fR.leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff_map_of_injective (RingHom.injective_int _)]; rfl
  have ht := tendsto_atTop_of_leadingCoeff_nonneg fR
    (natDegree_pos_iff_degree_pos.mp (hdeg ▸ hd)) (by rw [hlcR]; exact_mod_cast hlc.le)
  have ht' := ht.comp tendsto_natCast_atTop_atTop
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (ht'.eventually_ge_atTop 1)
  refine ⟨max n0 1, le_max_right _ _, fun n hn => ?_⟩
  have h := hn0 n (le_trans (le_max_left _ _) hn)
  simp only [Function.comp_apply] at h
  have e := eval_intCast_map (Int.castRingHom ℝ) f (n : ℤ)
  simp only [Int.cast_natCast, eq_intCast] at e
  rw [e] at h
  exact_mod_cast h

set_option maxHeartbeats 4000000 in
theorem H2_finset (f : ℤ[X]) (hi : Irreducible f) (hd : 2 < f.natDegree)
    (hlc : 0 < f.leadingCoeff) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (#(Exc f N) : ℝ) ≤ ε * N := by
  classical
  set k := f.natDegree with hk
  have hk1 : 1 ≤ k := by omega
  set ℓ := (k - 1).minFac with hℓdef
  have hℓp : ℓ.Prime := Nat.minFac_prime (by omega)
  have hℓk : ℓ ∣ k - 1 := Nat.minFac_dvd _
  have hℓ2 : 2 ≤ ℓ := hℓp.two_le
  have hcop : Nat.Coprime k ℓ := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓp]
    intro h
    have h1 : ℓ ∣ k - (k - 1) := Nat.dvd_sub h hℓk
    rw [show k - (k - 1) = 1 by omega] at h1
    exact hℓp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hfQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive (by omega))).mp hi
  obtain ⟨Cρ, hCρ0, hCρ⟩ := sum_rho_le f hfQ hk1
  obtain ⟨S, hS1, hS⟩ := natAbs_eval_le f
  obtain ⟨n0, hn01, hn0⟩ := eventually_eval_pos f (by omega) hlc
  set a := f.leadingCoeff.natAbs with ha
  set q0 := 2 * ℓ * (3 * k ^ 3 + 1 + k) + a + 1 with hq0
  -- `θ^{c'} ≤ 1/4`
  set θ : ℝ := 1 - 1 / (4 * ℓ : ℝ) with hθ
  have hℓr : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  have hθ0 : 0 ≤ θ := by rw [hθ, sub_nonneg, div_le_one (by positivity)]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; have : 0 < 1 / (4 * ℓ : ℝ) := by positivity
                         linarith
  obtain ⟨cθ, hcθ⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 4 by norm_num) hθ1
  set c' := max (k + 2) cθ with hc'
  have hθc : θ ^ c' ≤ 1 / 4 :=
    (pow_le_pow_of_le_one hθ0 hθ1.le (le_max_right _ _)).trans hcθ.le
  -- the prime-count hypothesis
  have HQ : ∀ᶠ z : ℕ in atTop, 2 * c' * Nat.log 2 z ≤ #(Qs ℓ q0 z) := by
    by_cases h2 : ℓ = 2
    · have := HQ_two q0 (2 * c')
      rw [h2]; exact this
    · exact HQ_odd hℓp (by omega) q0 (2 * c')
  obtain ⟨zc, hzc⟩ := eventually_atTop.mp HQ
  -- the base `b`
  set L := k + 1 with hL
  have hLk : 1 + k ≤ 2 ^ L := by
    have := Nat.lt_two_pow_self (n := L); omega
  set b := 2 ^ (8 * L) with hb
  have hb16 : 16 ≤ b := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (8 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : 1 < b := by omega
  set K0 : ℝ := Real.exp k * 2 ^ c' + 4 * Cρ * b + Cρ with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set z1 := max (max zc 2) (⌈8 * K0 / ε⌉₊ + 1) with hz1
  have hz12 : 2 ≤ z1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hz1c : zc ≤ z1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hz1r : (8 * K0 / ε) ≤ z1 := by
    have h1 : (⌈8 * K0 / ε⌉₊ : ℝ) + 1 ≤ z1 := by exact_mod_cast le_max_right (max zc 2) _
    have := Nat.le_ceil (8 * K0 / ε); linarith
  have hz1pos : (0 : ℝ) < z1 := by have : (2 : ℝ) ≤ z1 := by exact_mod_cast hz12
                                   linarith
  have hK0z : 2 * K0 / z1 ≤ ε / 4 := by
    rw [div_le_iff₀ hz1pos]
    rw [div_le_iff₀ hε] at hz1r
    nlinarith
  set T := S * b ^ z1 with hT
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  filter_upwards [pi_small k T hT1 ε hε, eventually_ge_atTop (⌈16 / ε ^ 2⌉₊ + n0 * ⌈4 / ε⌉₊ + a + 1)]
    with N hpiN hNbig
  have hN1 : 1 ≤ N := by omega
  have hNa : a < N := by omega
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- covering
  have hcov := exc_cover f (k := k) (ℓ := ℓ) (q0 := q0) (b := b) (z1 := z1) (S := S) (n0 := n0)
    (N := N) rfl (by omega) hℓk hℓ2 hb1 (by omega) hn01 hS hn0
  have hcard := card_le_card hcov
  -- the three parts
  have hA : (#(CaseA f N (S * b ^ z1 * N)) : ℝ) ≤ k * Nat.primeCounting (T * N) := by
    have h1 : #(CaseA f N (S * b ^ z1 * N)) ≤
        ∑ p ∈ (Ioc N (S * b ^ z1 * N)).filter Nat.Prime,
          #((range N).filter fun n => (p : ℤ) ∣ f.eval ((n : ℕ) : ℤ)) := card_biUnion_le
    have h2 : ∀ p ∈ (Ioc N (S * b ^ z1 * N)).filter Nat.Prime,
        #((range N).filter fun n => (p : ℤ) ∣ f.eval ((n : ℕ) : ℤ)) ≤ k := by
      intro p hp
      simp only [mem_filter, mem_Ioc] at hp
      have hpa : ¬ (p : ℤ) ∣ f.leadingCoeff := by
        intro hdvd
        have ha0 : f.leadingCoeff ≠ 0 := hlc.ne'
        have := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) (Int.natCast_dvd.mp hdvd)
        omega
      refine le_trans ?_ (rho_le hp.2 hpa)
      rw [rho]
      refine card_le_card fun n hn => ?_
      simp only [mem_filter, mem_range] at hn ⊢
      exact ⟨by omega, hn.2⟩
    have h3 : ((Ioc N (S * b ^ z1 * N)).filter Nat.Prime) ⊆ Nat.primesLE (T * N) := by
      intro p hp
      simp only [mem_filter, mem_Ioc] at hp
      rw [Nat.mem_primesLE]; exact ⟨by rw [hT]; exact hp.1.2, hp.2⟩
    have h4 : #(CaseA f N (S * b ^ z1 * N)) ≤ k * Nat.primeCounting (T * N) := by
      refine h1.trans ?_
      refine (sum_le_sum h2).trans ?_
      rw [sum_const, smul_eq_mul, mul_comm, ← Nat.primesLE_card_eq_primeCounting]
      exact Nat.mul_le_mul_left _ (card_le_card h3)
    exact_mod_cast h4
  have hlev : ∀ z ∈ Icc z1 (Nat.log b N),
      (#(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) : ℝ) ≤
        N * K0 / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z := by
    intro z hz
    rw [mem_Icc] at hz
    have hu := card_union_le (B1 f N (Qs ℓ q0 z)) (Tb f N b z (S * N) ℓ (Qs ℓ q0 z))
    have hT' : #(Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) ≤
        ∑ m ∈ (Lev N b z (S * N)).filter (fun m => omQm (Qs ℓ q0 z) m < #(Qs ℓ q0 z) / 2),
          #(Tset f N (Qs ℓ q0 z) ℓ m) := card_biUnion_le
    have hlb := level_bound f (N := N) (b := b) hk1 rfl hℓ2 hcop (by omega) (by omega)
      (le_trans hz12 hz.1) (le_max_left _ _) hθc hb16 (hzc z (le_trans hz1c hz.1)) hCρ0 hCρ (S * N)
    have : (#(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) : ℝ) ≤
        (#(B1 f N (Qs ℓ q0 z)) : ℝ) +
          ∑ m ∈ (Lev N b z (S * N)).filter (fun m => omQm (Qs ℓ q0 z) m < #(Qs ℓ q0 z) / 2),
            (#(Tset f N (Qs ℓ q0 z) ℓ m) : ℝ) := by
      have := hu.trans (Nat.add_le_add_left hT' _)
      exact_mod_cast this
    refine this.trans (hlb.trans (le_of_eq ?_))
    rw [hK0]
  -- summing the levels
  set Zm := Nat.log b N with hZm
  have hsum : (∑ z ∈ Icc z1 Zm, (#(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) : ℝ)) ≤
      N * K0 * (2 / z1) + ((Zm + 1 : ℕ) : ℝ) * (1 + k : ℝ) ^ Zm := by
    calc (∑ z ∈ Icc z1 Zm, (#(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) : ℝ))
        ≤ ∑ z ∈ Icc z1 Zm, (N * K0 / (z : ℝ) ^ 2 + (1 + k : ℝ) ^ z) := sum_le_sum hlev
      _ = N * K0 * ∑ z ∈ Icc z1 Zm, (1 : ℝ) / (z : ℝ) ^ 2 + ∑ z ∈ Icc z1 Zm, (1 + k : ℝ) ^ z := by
          rw [sum_add_distrib, mul_sum]
          congr 1
          refine sum_congr rfl fun z _ => ?_
          ring
      _ ≤ N * K0 * (2 / z1) + ((Zm + 1 : ℕ) : ℝ) * (1 + k : ℝ) ^ Zm := by
          gcongr
          · exact sum_inv_sq_le' z1 Zm (by omega)
          · calc ∑ z ∈ Icc z1 Zm, (1 + k : ℝ) ^ z ≤ ∑ z ∈ Icc z1 Zm, (1 + k : ℝ) ^ Zm := by
                  refine sum_le_sum fun z hz => ?_
                  exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
                    (mem_Icc.mp hz).2
              _ = #(Icc z1 Zm) * (1 + k : ℝ) ^ Zm := by rw [sum_const, nsmul_eq_mul]
              _ ≤ ((Zm + 1 : ℕ) : ℝ) * (1 + k : ℝ) ^ Zm :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast (show #(Icc z1 Zm) ≤ Zm + 1 by
                    rw [Nat.card_Icc]; omega)) (by positivity)
  -- the small inputs
  have hsmall : (n0 : ℝ) ≤ ε / 4 * N := by
    have h1 : (n0 : ℝ) * ⌈4 / ε⌉₊ ≤ N := by
      have : n0 * ⌈4 / ε⌉₊ ≤ N := by omega
      exact_mod_cast this
    have h2 : 4 / ε ≤ (⌈4 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
    have h3 : (n0 : ℝ) * (4 / ε) ≤ N := le_trans (mul_le_mul_of_nonneg_left h2 hn0r) h1
    rw [mul_div_assoc', div_le_iff₀ hε] at h3
    linarith
  have htop := top_small k L hk1 hLk ε hε N (by
    have := Nat.le_ceil (16 / ε ^ 2)
    have h' : ((⌈16 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (show ⌈16 / ε ^ 2⌉₊ ≤ N by omega)
    linarith)
  rw [← hb, ← hZm] at htop
  -- combine
  have hc1 := hcard.trans (card_union_le _ _)
  have hc2 : #(range n0 ∪ CaseA f N (S * b ^ z1 * N)) ≤ n0 + #(CaseA f N (S * b ^ z1 * N)) := by
    have := card_union_le (range n0) (CaseA f N (S * b ^ z1 * N))
    rwa [card_range] at this
  have hc3 : #((Icc z1 Zm).biUnion fun z =>
      B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) ≤
      ∑ z ∈ Icc z1 Zm, #(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) := card_biUnion_le
  have htot : (#(Exc f N) : ℝ) ≤ n0 + #(CaseA f N (S * b ^ z1 * N)) +
      ∑ z ∈ Icc z1 Zm, (#(B1 f N (Qs ℓ q0 z) ∪ Tb f N b z (S * N) ℓ (Qs ℓ q0 z)) : ℝ) := by
    have h := hc1.trans (Nat.add_le_add hc2 hc3)
    exact_mod_cast h
  have hNK : N * K0 * (2 / z1) ≤ ε / 4 * N := by
    have : K0 * (2 / z1) ≤ ε / 4 := by rw [mul_div_assoc', mul_comm]; exact hK0z
    nlinarith
  linarith

end LaneC978

end

/-! The step `Erdos978.erdos_978.parts.i.R1.H2`, in the reduction's own form. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem H2_main : ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
    (∀ e : ℕ, f.natDegree ≠ 2^e) → 0 < f.leadingCoeff →
    ∀ ε > (0:ℝ), ∀ᶠ N : ℕ in atTop,
      {n : ℕ | ∃ p : ℕ, p.Prime ∧ N < p ∧ (p:ℤ)^(f.natDegree-1) ∣ f.eval (n:ℤ)}.partialDensity
        Set.univ N < ε := by
  intro f hi hd _ hlc ε hε
  filter_upwards [H2_finset f hi hd hlc (ε / 2) (by linarith), eventually_ge_atTop 1] with N hN hN1
  have h1 : (Set.univ ∩ Set.Iio N).ncard = N := by simp
  have h2 : (({n : ℕ | ∃ p : ℕ, p.Prime ∧ N < p ∧ (p:ℤ)^(f.natDegree-1) ∣ f.eval (n:ℤ)} ∩
      Set.univ) ∩ Set.Iio N).ncard = #(Exc f N) := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext n
    simp only [Exc, Set.inter_univ, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio,
      coe_filter, mem_range]
    tauto
  unfold Set.partialDensity
  rw [h1, h2]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [div_lt_iff₀ hNr]
  have : 0 < ε * N := mul_pos hε hNr
  linarith

end LaneC978

end

/-! Tools for the small-prime sieve: CRT lower bound, counts in `(N, 2N]`, good prime powers. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- At a good prime `p ∤ D`, roots modulo `p^j` reduce injectively to roots modulo `p`. -/
theorem rho_pow_le_rho {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) {j : ℕ} (hj : 1 ≤ j) :
    rho f (p ^ j) ≤ rho f p := by
  classical
  rw [rho, rho]
  refine card_le_card_of_injOn (fun r => r % p) ?_ ?_
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr ⊢
    have hpj : p ∣ p ^ j := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hj)
    exact ⟨Nat.mod_lt _ hp.pos, dvd_eval_mod hpj (by exact_mod_cast hr.2)⟩
  · intro r hr r' hr' h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
    simp only at h
    have h1 : ((p : ℕ) : ℤ) ^ (0 + 1) ∣ (r' : ℤ) - r := by
      rw [zero_add, pow_one]; exact Nat.modEq_iff_dvd.mp h
    have h2 := cluster hB hp (δ := 0) (by rw [zero_add, pow_one]; exact hpD) (show 0 + 1 ≤ j by omega)
      (x := (r : ℤ)) (y := (r' : ℤ)) (by exact_mod_cast hr.2) (by exact_mod_cast hr'.2) h1
    rw [Nat.sub_zero] at h2
    have h3 : r ≡ r' [MOD p ^ j] := Nat.modEq_iff_dvd.mpr (by exact_mod_cast h2)
    exact Nat.ModEq.eq_of_lt_of_lt h3 hr.1 hr'.1

/-- Lower bound for the Chinese remainder combination of residue conditions. -/
theorem card_res_ge (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ p ∈ P, B p ⊆ range (p ^ j)) :
    ∏ p ∈ P, #(B p) ≤
      #((range (∏ p ∈ P, p ^ j)).filter fun x => ∀ p ∈ P, x % p ^ j ∈ B p) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact card_pos.mpr ⟨0, by simp⟩
  | insert q S hqS ih =>
    have hq := hP q (mem_insert_self q S)
    have hS : ∀ p ∈ S, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have ih' := ih hS (fun p hp => hB p (mem_insert_of_mem hp))
    set W := ∏ p ∈ S, p ^ j with hW
    have hW0 : 0 < W := prod_pos fun p hp => pow_pos (hS p hp).pos _
    have hcop : Nat.Coprime W (q ^ j) := by
      refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.pow _ _ ?_
      refine (Nat.coprime_primes (hS p hp) hq).mpr ?_
      rintro rfl; exact hqS hp
    set T := (range W).filter fun x => ∀ p ∈ S, x % p ^ j ∈ B p with hT
    rw [prod_insert hqS, prod_insert hqS, mul_comm (#(B q))]
    calc (∏ x ∈ S, #(B x)) * #(B q) ≤ #T * #(B q) := Nat.mul_le_mul_right _ ih'
      _ = #(T ×ˢ B q) := (card_product _ _).symm
      _ ≤ #((range (q ^ j * W)).filter fun x => ∀ p ∈ insert q S, x % p ^ j ∈ B p) := by
        refine card_le_card_of_injOn (s := T ×ˢ B q)
          (t := (range (q ^ j * W)).filter fun x => ∀ p ∈ insert q S, x % p ^ j ∈ B p)
          (fun xy => (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ)) ?_ ?_
        · intro xy hxy
          simp only [coe_product, Set.mem_prod, hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hxy
          have hcr := (Nat.chineseRemainder hcop xy.1 xy.2).2
          have hlt := Nat.chineseRemainder_lt_mul hcop xy.1 xy.2 hW0.ne' (pow_pos hq.pos _).ne'
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq, forall_mem_insert]
          refine ⟨by rw [mul_comm]; exact hlt, ?_, fun p hp => ?_⟩
          · have h1 : (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ) % q ^ j = xy.2 % q ^ j := hcr.2
            rw [h1, Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy.2))]
            exact hxy.2
          · have h1 : (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ) % W = xy.1 % W := hcr.1
            have hdvd : p ^ j ∣ W := dvd_prod_of_mem _ hp
            rw [← Nat.mod_mod_of_dvd _ hdvd, h1, Nat.mod_mod_of_dvd _ hdvd]
            exact hxy.1.2 p hp
        · intro xy hxy xy' hxy' h
          simp only [coe_product, Set.mem_prod, hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hxy hxy'
          have hcr := (Nat.chineseRemainder hcop xy.1 xy.2).2
          have hcr' := (Nat.chineseRemainder hcop xy'.1 xy'.2).2
          simp only at h
          rw [h] at hcr
          have e1 : xy.1 % W = xy'.1 % W := hcr.1.symm.trans hcr'.1
          have e2 : xy.2 % q ^ j = xy'.2 % q ^ j := hcr.2.symm.trans hcr'.2
          rw [Nat.mod_eq_of_lt hxy.1.1, Nat.mod_eq_of_lt hxy'.1.1] at e1
          rw [Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy.2)),
            Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy'.2))] at e2
          exact Prod.ext e1 e2

/-- Lower bound for residue classes in `(N, 2N]`. -/
theorem count_Ioc_ge (N W : ℕ) (hW : 0 < W) (T : Finset ℕ) (hT : T ⊆ range W) :
    #T * (N / W) ≤ #((Ioc N (2 * N)).filter fun n => n % W ∈ T) := by
  classical
  set r := (N + 1) % W with hr
  rw [← card_range (N / W), ← card_product]
  refine card_le_card_of_injOn
    (fun ti => N + 1 + (ti.1 + W - r) % W + W * ti.2) ?_ ?_
  · intro ti hti
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio] at hti
    have ht := mem_range.mp (hT hti.1)
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    have hrW : r < W := Nat.mod_lt _ hW
    have hmod : (ti.1 + W - r) % W < W := Nat.mod_lt _ hW
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have : W * ti.2 + W ≤ N := by
        have := Nat.div_mul_le_self N W
        nlinarith [hti.2]
      omega
    · -- the residue is `ti.1`
      have e1 : (N + 1 + (ti.1 + W - r) % W + W * ti.2) % W =
          ((N + 1) % W + (ti.1 + W - r) % W) % W := by
        rw [Nat.add_mul_mod_self_left, Nat.add_mod, Nat.add_mod ((N + 1) % W), Nat.mod_mod,
          Nat.mod_mod, Nat.mod_mod]
      rw [e1, ← hr, Nat.add_mod_mod, show r + (ti.1 + W - r) = ti.1 + W by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt ht]
      exact hti.1
  · intro ti hti ti' hti' h
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio] at hti hti'
    simp only at h
    have hmod : (ti.1 + W - r) % W < W := Nat.mod_lt _ hW
    have hmod' : (ti'.1 + W - r) % W < W := Nat.mod_lt _ hW
    have h1 : (ti.1 + W - r) % W + W * ti.2 = (ti'.1 + W - r) % W + W * ti'.2 := by omega
    have h2 : ti.2 = ti'.2 := by
      have := congrArg (· / W) h1
      rwa [Nat.add_mul_div_left _ _ hW, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hmod,
        Nat.div_eq_of_lt hmod', zero_add, zero_add] at this
    have h3 : (ti.1 + W - r) % W = (ti'.1 + W - r) % W := by rw [h2] at h1; omega
    have ht := mem_range.mp (hT hti.1)
    have ht' := mem_range.mp (hT hti'.1)
    have hrW : r < W := Nat.mod_lt _ hW
    have h4 : ti.1 = ti'.1 := by
      have e : (ti.1 + W - r) % W + r ≡ (ti'.1 + W - r) % W + r [MOD W] := by rw [h3]
      have e1 : (ti.1 + W - r) % W + r ≡ ti.1 [MOD W] := by
        calc (ti.1 + W - r) % W + r ≡ (ti.1 + W - r) + r [MOD W] :=
              Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          _ = ti.1 + W := by omega
          _ ≡ ti.1 [MOD W] := Nat.add_modEq_right
      have e2 : (ti'.1 + W - r) % W + r ≡ ti'.1 [MOD W] := by
        calc (ti'.1 + W - r) % W + r ≡ (ti'.1 + W - r) + r [MOD W] :=
              Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          _ = ti'.1 + W := by omega
          _ ≡ ti'.1 [MOD W] := Nat.add_modEq_right
      exact Nat.ModEq.eq_of_lt_of_lt (e1.symm.trans (e.trans e2)) ht ht'
    exact Prod.ext h4 h2

/-- Upper bound for residue classes in `(N, 2N]`. -/
theorem count_Ioc_le (N P : ℕ) (hP : 0 < P) (R : Finset ℕ) :
    #((Ioc N (2 * N)).filter fun n => n % P ∈ R) ≤ #R * (N / P + 1) := by
  classical
  rw [← card_range (N / P + 1), ← card_product]
  refine card_le_card_of_injOn (fun n => (n % P, (n - (N + 1)) / P)) ?_ ?_
  · intro n hn
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hn
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio]
    refine ⟨hn.2, ?_⟩
    have : (n - (N + 1)) / P ≤ N / P := Nat.div_le_div_right (by omega)
    omega
  · intro n hn n' hn' h
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hn hn'
    simp only [Prod.mk.injEq] at h
    have hu : n - (N + 1) ≡ n' - (N + 1) [MOD P] := by
      have h' : (n - (N + 1)) + (N + 1) ≡ (n' - (N + 1)) + (N + 1) [MOD P] := by
        rw [Nat.sub_add_cancel hn.1.1, Nat.sub_add_cancel hn'.1.1]; exact h.1
      exact Nat.ModEq.add_right_cancel' _ h'
    have hq : n - (N + 1) = n' - (N + 1) := by
      rw [← Nat.div_add_mod (n - (N + 1)) P, ← Nat.div_add_mod (n' - (N + 1)) P, h.2]
      rw [show (n - (N + 1)) % P = (n' - (N + 1)) % P from hu]
    omega

end LaneC978

end

/-! The step `Erdos978.erdos_978.variants.sub_one.R1.H1`: the small-prime sieve on `(N, 2N]`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem prod_one_sub_ge {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hx0 := h0 a (mem_insert_self a s)
    have hx1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have hp0 : 0 ≤ ∏ i ∈ s, (1 - x i) :=
      prod_nonneg fun i hi => by have := h1 i (mem_insert_of_mem hi); linarith
    nlinarith [mul_le_mul_of_nonneg_left ih' (show 0 ≤ 1 - x a by linarith)]

theorem dvd_of_mod {f : ℤ[X]} {P n : ℕ} (h : (P : ℤ) ∣ f.eval ((n : ℕ) : ℤ)) :
    (P : ℤ) ∣ f.eval ((n % P : ℕ) : ℤ) := dvd_eval_mod (dvd_refl P) h

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem sub_one_H1 : ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
    (∀ p : ℕ, p.Prime → ∃ a : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (a : ℤ)) →
    ∃ A : ℕ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      N ≤ A * ((Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ N → ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)).card := by
  intro f hi hd hadm
  set k := f.natDegree with hk
  set j := k - 1 with hj
  have hj1 : 1 ≤ j := by omega
  have hfQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive (by omega))).mp hi
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout f hfQ (by omega)
  have hlc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hi.ne_zero
  set p1 := 4 * k + D.natAbs + f.leadingCoeff.natAbs + 1 with hp1
  -- roots at good prime powers
  have hgood : ∀ p, p.Prime → p1 < p → rho f (p ^ j) ≤ k := by
    intro p hp hpp1
    have hpD : ¬ (p : ℤ) ∣ D := by
      intro h; have := Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) (Int.natCast_dvd.mp h); omega
    have hpa : ¬ (p : ℤ) ∣ f.leadingCoeff := by
      intro h; have := Nat.le_of_dvd (Int.natAbs_pos.mpr hlc0) (Int.natCast_dvd.mp h); omega
    exact (rho_pow_le_rho hB hp hpD hj1).trans (rho_le hp hpa)
  -- allowed residues mod `p^j`
  set Bs : ℕ → Finset ℕ := fun p => (range (p ^ j)).filter fun s =>
    ¬ (((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) with hBs
  have hBsub : ∀ p, Bs p ⊆ range (p ^ j) := fun p => filter_subset _ _
  have hBcard : ∀ p, #(Bs p) + rho f (p ^ j) = p ^ j := by
    intro p
    rw [hBs, rho, add_comm, card_filter_add_card_filter_not, card_range]
  have hBpos : ∀ p, p.Prime → 1 ≤ #(Bs p) := by
    intro p hp
    obtain ⟨a, ha⟩ := hadm p hp
    refine card_pos.mpr ⟨a % p ^ j, ?_⟩
    rw [hBs, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (pow_pos hp.pos _), fun h => ha ?_⟩
    have h1 : ((p ^ j : ℕ) : ℤ) ∣ f.eval ((a % p ^ j : ℕ) : ℤ) := h
    have h2 := sub_dvd_eval_sub (a : ℤ) ((a % p ^ j : ℕ) : ℤ) f
    have h3 : ((p ^ j : ℕ) : ℤ) ∣ (a : ℤ) - ((a % p ^ j : ℕ) : ℤ) :=
      (Nat.modEq_iff_dvd.mp (Nat.mod_modEq a (p ^ j)))
    have := dvd_add (h3.trans h2) h1
    simp only [sub_add_cancel] at this
    push_cast at this; exact this
  -- the constant `c`
  set P1 := Nat.primesLE p1 with hP1
  set c : ℝ := (1 / 2) * ∏ p ∈ P1, (1 / (p : ℝ) ^ j) with hc
  have hc0 : 0 < c := by
    rw [hc]; refine mul_pos (by norm_num) (prod_pos fun p hp => ?_)
    have := (Nat.mem_primesLE.mp hp).2.pos; positivity
  set w := p1 + ⌈32 * k / c⌉₊ with hw
  set P := Nat.primesLE w with hP
  set W := ∏ p ∈ P, p ^ j with hW
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hW0 : 0 < W := prod_pos fun p hp => pow_pos (hPp p hp).pos _
  set G := (range W).filter fun x => ∀ p ∈ P, x % p ^ j ∈ Bs p with hG
  have hGcard := card_res_ge P hPp j Bs (fun p _ => hBsub p)
  -- density of `G`
  have hdens : c * W ≤ (#G : ℝ) := by
    have hsplit : P = P.filter (fun p => p ≤ p1) ∪ P.filter (fun p => ¬ p ≤ p1) :=
      (filter_union_filter_not_eq _ _).symm
    have hdisj := disjoint_filter_filter_not P P (fun p => p ≤ p1)
    have hratio : ∀ p ∈ P, (#(Bs p) : ℝ) = (p : ℝ) ^ j * (#(Bs p) / (p : ℝ) ^ j) := by
      intro p hp
      have : (0 : ℝ) < (p : ℝ) ^ j := by have := (hPp p hp).pos; positivity
      rw [mul_div_assoc', mul_div_cancel_left₀ _ this.ne']
    have hprod : (∏ p ∈ P, (#(Bs p) : ℝ)) = W * ∏ p ∈ P, (#(Bs p) / (p : ℝ) ^ j) := by
      rw [prod_congr rfl hratio, prod_mul_distrib, hW]; push_cast; rfl
    have hlow1 : ∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) ≥
        ∏ p ∈ P1, (1 / (p : ℝ) ^ j) := by
      have hsub : P.filter (fun p => p ≤ p1) ⊆ P1 := by
        intro p hp; rw [mem_filter, hP, Nat.mem_primesLE] at hp
        rw [hP1, Nat.mem_primesLE]; exact ⟨hp.2, hp.1.2⟩
      have heq : P.filter (fun p => p ≤ p1) = P1 := by
        refine Subset.antisymm hsub fun p hp => ?_
        rw [hP1, Nat.mem_primesLE] at hp
        rw [mem_filter, hP, Nat.mem_primesLE]; exact ⟨⟨by omega, hp.2⟩, hp.1⟩
      calc ∏ p ∈ P1, (1 / (p : ℝ) ^ j) = ∏ p ∈ P.filter (fun p => p ≤ p1), (1 / (p : ℝ) ^ j) := by
            rw [heq]
        _ ≤ ∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) := by
            refine prod_le_prod (fun p _ => by positivity) fun p hp => ?_
            have := hBpos p (hPp p (mem_filter.mp hp).1)
            gcongr
            exact_mod_cast this
    have hlow2 : ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) ≥ 1 / 2 := by
      have hge : ∀ p ∈ P.filter (fun p => ¬ p ≤ p1),
          1 - k / (p : ℝ) ^ 2 ≤ (#(Bs p) / (p : ℝ) ^ j) := by
        intro p hp
        have hpp := hPp p (mem_filter.mp hp).1
        have hpbig : p1 < p := by have := (mem_filter.mp hp).2; omega
        have hr := hgood p hpp hpbig
        have hb := hBcard p
        have hpj : (0 : ℝ) < (p : ℝ) ^ j := by have := hpp.pos; positivity
        have hp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
          (by omega)
        have hbr : (#(Bs p) : ℝ) = (p : ℝ) ^ j - rho f (p ^ j) := by
          have : ((#(Bs p) + rho f (p ^ j) : ℕ) : ℝ) = ((p ^ j : ℕ) : ℝ) := by rw [hb]
          push_cast at this; linarith
        rw [hbr, sub_div, div_self hpj.ne']
        have h1 : (rho f (p ^ j) : ℝ) / (p : ℝ) ^ j ≤ k / (p : ℝ) ^ 2 := by
          have hr' : (rho f (p ^ j) : ℝ) ≤ k := by exact_mod_cast hr
          calc (rho f (p ^ j) : ℝ) / (p : ℝ) ^ j ≤ k / (p : ℝ) ^ j := by gcongr
            _ ≤ k / (p : ℝ) ^ 2 := by
                apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by have := hpp.pos; positivity) hp2
        linarith
      have hsum : ∑ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2 := by
        have hsub : P.filter (fun p => ¬ p ≤ p1) ⊆ Icc (p1 + 1) w := by
          intro p hp
          rw [mem_filter, hP, Nat.mem_primesLE] at hp
          rw [mem_Icc]; exact ⟨by omega, hp.1.1⟩
        calc ∑ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2
            ≤ ∑ p ∈ Icc (p1 + 1) w, (k : ℝ) / (p : ℝ) ^ 2 :=
              sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = k * ∑ p ∈ Icc (p1 + 1) w, (1 : ℝ) / (p : ℝ) ^ 2 := by
              rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
          _ ≤ k * (2 / ((p1 + 1 : ℕ) : ℝ)) := by
              gcongr; exact sum_inv_sq_le' (p1 + 1) w (by omega)
          _ ≤ 1 / 2 := by
              have hp1r : (4 * k + 1 : ℝ) ≤ ((p1 + 1 : ℕ) : ℝ) := by
                have : 4 * k + 1 ≤ p1 + 1 := by omega
                exact_mod_cast this
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      have hx1 : ∀ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
        intro p hp
        have hpp := hPp p (mem_filter.mp hp).1
        have hpbig : p1 < p := by have := (mem_filter.mp hp).2; omega
        have hpr : (4 * k : ℝ) ≤ p := by exact_mod_cast (show 4 * k ≤ p by omega)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        rw [div_le_one (by positivity)]
        nlinarith
      have := prod_one_sub_ge (P.filter (fun p => ¬ p ≤ p1)) (fun p => (k : ℝ) / (p : ℝ) ^ 2)
        (fun _ _ => by positivity) hx1
      have hmono : ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (1 - (k : ℝ) / (p : ℝ) ^ 2) ≤
          ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) :=
        prod_le_prod (fun p hp => by have := hx1 p hp; linarith) hge
      linarith
    have hpos1 : 0 ≤ ∏ p ∈ P1, (1 / (p : ℝ) ^ j) := prod_nonneg fun p _ => by positivity
    have hGr : (∏ p ∈ P, (#(Bs p) : ℝ)) ≤ (#G : ℝ) := by exact_mod_cast hGcard
    rw [hprod, hsplit, prod_union hdisj] at hGr
    rw [hc]
    have hW0r : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have : (1 / 2) * ∏ p ∈ P1, (1 / (p : ℝ) ^ j) ≤
        (∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j)) *
          ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) := by
      rw [mul_comm]
      exact mul_le_mul hlow1 hlow2 (by norm_num) (le_trans hpos1 hlow1)
    nlinarith [mul_le_mul_of_nonneg_left this hW0r]
  -- the count
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (pi_small k 1 le_rfl c hc0)
  set A := ⌈4 / c⌉₊ + 1 with hA
  refine ⟨A, by omega, max N1 (max (4 * W) (w + 1)), fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNW : 4 * W ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNw : w + 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set Good := (Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
    ∀ p : ℕ, p.Prime → p ≤ N → ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ) with hGood
  set Cand := (Ioc N (2 * N)).filter fun n => n % W ∈ G with hCand
  set Bad := ((Ioc w N).filter Nat.Prime).biUnion fun p =>
    (Ioc N (2 * N)).filter fun n => n % p ^ j ∈ (range (p ^ j)).filter
      fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ) with hBad
  have hsub : Cand \ Bad ⊆ Good := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnC, hnB⟩ := hn
    rw [hCand, mem_filter] at hnC
    rw [hGood, mem_filter]
    refine ⟨hnC.1, fun p hp hpN hdvd => ?_⟩
    have hdvd' : ((p ^ j : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ) := by push_cast; exact hdvd
    by_cases hpw : p ≤ w
    · have hpP : p ∈ P := by rw [hP, Nat.mem_primesLE]; exact ⟨hpw, hp⟩
      have hG' := (mem_filter.mp hnC.2).2 p hpP
      rw [Nat.mod_mod_of_dvd _ (dvd_prod_of_mem _ hpP)] at hG'
      rw [hBs, mem_filter] at hG'
      exact hG'.2 (dvd_of_mod hdvd')
    · apply hnB
      rw [hBad, mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · rw [mem_filter, mem_Ioc]; exact ⟨⟨by omega, hpN⟩, hp⟩
      · rw [mem_filter]
        refine ⟨hnC.1, ?_⟩
        rw [mem_filter, mem_range]
        exact ⟨Nat.mod_lt _ (pow_pos hp.pos _), dvd_of_mod hdvd'⟩
  have hcount : (#Cand : ℝ) ≤ #Good + #Bad := by
    have h1 := card_le_card_sdiff_add_card (s := Cand) (t := Bad)
    have h2 := card_le_card hsub
    have : #Cand ≤ #Good + #Bad := by omega
    exact_mod_cast this
  have hCand_ge : #G * (N / W) ≤ #Cand := count_Ioc_ge N W hW0 G (filter_subset _ _)
  have hBad_le : (#Bad : ℝ) ≤ k * N * (2 / ((w + 1 : ℕ) : ℝ)) + k * Nat.primeCounting (1 * N) := by
    have h1 : #Bad ≤ ∑ p ∈ (Ioc w N).filter Nat.Prime, #((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) :=
      card_biUnion_le
    have h2 : ∀ p ∈ (Ioc w N).filter Nat.Prime, (#((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ) ≤
        k * (N / (p : ℝ) ^ 2 + 1) := by
      intro p hp
      rw [mem_filter, mem_Ioc] at hp
      have hpp := hp.2
      have hc1 := count_Ioc_le N (p ^ j) (pow_pos hpp.pos _)
        ((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ))
      have hrho : #((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) ≤ k := by
        have := hgood p hpp (by omega)
        rw [rho] at this
        exact this
      have hp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
        (by omega)
      have hp20 : (0 : ℝ) < (p : ℝ) ^ 2 := by have := hpp.pos; positivity
      have hdiv : ((N / p ^ j : ℕ) : ℝ) ≤ N / (p : ℝ) ^ 2 := by
        refine (Nat.cast_div_le).trans ?_
        push_cast
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp20 hp2
      calc (#((Ioc N (2 * N)).filter fun n =>
            n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ)
          ≤ ((#((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) *
              (N / p ^ j + 1) : ℕ) : ℝ) := by exact_mod_cast hc1
        _ ≤ k * (N / (p : ℝ) ^ 2 + 1) := by
            push_cast
            gcongr
            exact_mod_cast hrho
    have h3 : ∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1) ≤
        k * N * (2 / ((w + 1 : ℕ) : ℝ)) + k * Nat.primeCounting (1 * N) := by
      have e : ∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1) =
          k * N * ∑ p ∈ (Ioc w N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 +
            k * #((Ioc w N).filter Nat.Prime) := by
        rw [show (∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1)) =
            ∑ p ∈ (Ioc w N).filter Nat.Prime, ((k : ℝ) * N * (1 / (p : ℝ) ^ 2) + k) from
          sum_congr rfl (fun p _ => by ring), sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
        ring
      rw [e]
      have hs1 : ∑ p ∈ (Ioc w N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / ((w + 1 : ℕ) : ℝ) := by
        refine le_trans ?_ (sum_inv_sq_le' (w + 1) N (by omega))
        refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
        rw [mem_filter, mem_Ioc] at hp; rw [mem_Icc]; omega
      have hs2 : #((Ioc w N).filter Nat.Prime) ≤ Nat.primeCounting (1 * N) := by
        rw [one_mul, ← Nat.primesLE_card_eq_primeCounting]
        refine card_le_card fun p hp => ?_
        rw [mem_filter, mem_Ioc] at hp; rw [Nat.mem_primesLE]; exact ⟨hp.1.2, hp.2⟩
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hs2r : (#((Ioc w N).filter Nat.Prime) : ℝ) ≤ Nat.primeCounting (1 * N) := by
        exact_mod_cast hs2
      have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hk0 hN0)
      have := mul_le_mul_of_nonneg_left hs2r hk0
      linarith
    have h1' : (#Bad : ℝ) ≤ ∑ p ∈ (Ioc w N).filter Nat.Prime, (#((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans ((sum_le_sum h2).trans h3)
  -- final arithmetic
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hNWr : (4 * W : ℝ) ≤ N := by exact_mod_cast hNW
  have hdivlow : (N : ℝ) / W - 1 ≤ ((N / W : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) hW0
    have h' : (N : ℝ) < ((N / W : ℕ) : ℝ) * W + W := by exact_mod_cast h
    rw [div_sub_one hWr.ne', div_le_iff₀ hWr]; linarith
  have hCr : c * N - c * W ≤ (#Cand : ℝ) := by
    have h1 : ((#G * (N / W) : ℕ) : ℝ) ≤ #Cand := by exact_mod_cast hCand_ge
    push_cast at h1
    have h2 : c * W * ((N : ℝ) / W - 1) ≤ (#G : ℝ) * ((N / W : ℕ) : ℝ) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) / W - 1 := by
        rw [sub_nonneg, le_div_iff₀ hWr]; linarith
      calc c * W * ((N : ℝ) / W - 1) ≤ (#G : ℝ) * ((N : ℝ) / W - 1) :=
            mul_le_mul_of_nonneg_right hdens hN0
        _ ≤ (#G : ℝ) * ((N / W : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hdivlow (Nat.cast_nonneg _)
    have h3 : c * W * ((N : ℝ) / W - 1) = c * N - c * W := by field_simp
    linarith
  have hpi := hN1 N hNN1
  have hwr : 32 * k / c ≤ ((w + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (32 * k / c)
    have h' : ((⌈32 * k / c⌉₊ : ℕ) : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show ⌈32 * k / c⌉₊ ≤ w + 1 by omega)
    linarith
  have hw1 : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  have hkw : (k : ℝ) * (2 / ((w + 1 : ℕ) : ℝ)) ≤ c / 16 := by
    rw [mul_div_assoc', div_le_iff₀ hw1]
    rw [div_le_iff₀ hc0] at hwr
    nlinarith
  have hBadr : (#Bad : ℝ) ≤ c / 16 * N + c / 4 * N := by
    have := mul_le_mul_of_nonneg_right hkw (show (0 : ℝ) ≤ N by positivity)
    linarith [hBad_le]
  have hGoodr : c / 4 * N ≤ (#Good : ℝ) := by
    have hcW : c * W ≤ c / 4 * N := by nlinarith
    linarith
  have hAr : 4 / c ≤ (A : ℝ) := by
    have := Nat.le_ceil (4 / c); rw [hA]; push_cast; linarith
  have : (N : ℝ) ≤ A * #Good := by
    calc (N : ℝ) = 4 / c * (c / 4 * N) := by field_simp
      _ ≤ A * #Good := by
          apply mul_le_mul hAr hGoodr (by positivity) (by positivity)
  exact_mod_cast this

end LaneC978

end

theorem OMA.solution : OMA.R_Erdos978_erdos_978_variants_sub_one_R1.H1 := LaneC978.sub_one_H1
