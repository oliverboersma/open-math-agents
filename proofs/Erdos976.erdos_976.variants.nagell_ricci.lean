import FormalConjectures.ErdosProblems.«976»

/-!
# Erdős Problem 976, variant of Nagell and Ricci: `F_f(n) ≫ n log n`

Original proof (Lane C, claude-code for koolkao). Chebyshev-type argument:
* Kummer–Dedekind (Mathlib) gives, for good primes `p` and roots `c` of `f` mod `p`, pairwise
  coprime ideals `(p, θ - a c)` of norm `p` in `K = ℚ[X]/(f)`;
* the ideal-counting asymptotic (Mathlib) gives `∑_{p ≤ n} ρ(p) log p / p ≤ (3/2) log n + O(1)`;
* root clustering mod `p^j` (Bezout with the resultant of `f, f′`) bounds the valuations;
* comparing with `∑_{k ≤ n} log |f(k)| ≥ d n log n - O(n)` forces `θ(F_f(n)) ≫ n log n`.
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

/-! Part 10: the main estimate. -/

noncomputable section
open Polynomial Finset Filter NumberField

namespace LaneC976

theorem log_le_mul_log {S p : ℕ} (hS : 1 ≤ S) (hp : 2 ≤ p) :
    Real.log S ≤ Real.log S / Real.log 2 * Real.log p := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlS : 0 ≤ Real.log S := Real.log_natCast_nonneg _
  have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  exact mul_le_mul_of_nonneg_left hlp hlS

set_option maxHeartbeats 1600000 in
theorem main_bound (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ P : ℕ,
      (∀ p, p.Prime → p ∣ (∏ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ)).natAbs → p ≤ P) →
      c * (n * Real.log n) ≤ P := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  have ha0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hfQ : Irreducible (fQ f) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive (by omega))).mp hf
  obtain ⟨K, _, _, θ, hmin, hE⟩ := exists_theta f hfQ
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout f hfQ (by omega)
  obtain ⟨M, hM10, hMert⟩ := mertens_ideal K
  obtain ⟨S, hS1, hS⟩ := natAbs_eval_le f
  obtain ⟨C1, hC1⟩ := log_abs_eval_ge hf hd
  set d := f.natDegree with hd_def
  set a := f.leadingCoeff with ha_def
  set E := RingOfIntegers.exponent θ with hE_def
  set Bad : Finset ℕ := (a * (E : ℤ) * D).natAbs.primeFactors with hBad
  have hBad0 : (a * (E : ℤ) * D).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero ha0 (by exact_mod_cast hE)) hD0
  have hgood : ∀ p, p.Prime → p ∉ Bad → ¬ (p : ℤ) ∣ a ∧ ¬ p ∣ E ∧ ¬ (p : ℤ) ∣ D := by
    intro p hp hpB
    have hnd : ¬ p ∣ (a * (E : ℤ) * D).natAbs := fun h ↦
      hpB (Nat.mem_primeFactors.mpr ⟨hp, h, hBad0⟩)
    rw [← Int.natCast_dvd] at hnd
    refine ⟨fun h ↦ hnd ?_, fun h ↦ hnd ?_, fun h ↦ hnd ?_⟩
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast h) _) _
    · exact dvd_mul_of_dvd_right h _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlS : 0 ≤ Real.log S := Real.log_natCast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- constants
  set Bterm : ℕ → ℝ := fun p ↦ (((padicValInt p D : ℕ) + (p : ℝ) ^ (padicValInt p D + 1)) *
    Real.log p + (p : ℝ) ^ (padicValInt p D + 1)) with hBterm
  have hBterm0 : ∀ p, 0 ≤ Bterm p := fun p ↦ by
    have := Real.log_natCast_nonneg p; positivity
  set CB : ℝ := ∑ p ∈ Bad, Bterm p with hCB
  have hCB0 : 0 ≤ CB := Finset.sum_nonneg fun p _ ↦ hBterm0 p
  set Λ : ℝ := Real.log S + d with hΛ
  set Cl1 : ℝ := Real.log S / Real.log 2 + d with hCl1
  set Cl2 : ℝ := Real.log S / Real.log 2 + 2 * d with hCl2
  have hCl1nn : 0 ≤ Cl1 := by positivity
  set C' : ℝ := d * (1 + Cl1) * Real.log 4 + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set A : ℝ := CB + 11 / 10 * d * M * Real.log 4 + 11 * d + d * Cl2 * Real.log 4 + d + C1
  set Bc : ℝ := CB * Λ + d * Λ
  refine ⟨7 / 40 / C', by positivity, ?_⟩
  filter_upwards [eventually_absorb A Bc, eventually_ge_atTop (M + Bad.sup id + 1)]
    with n habs hn P hP
  have hn1 : 1 ≤ n := by omega
  have hnM : M ≤ n := by omega
  have hBadle : ∀ p ∈ Bad, p ≤ n := fun p hp ↦ by
    have := Finset.le_sup (f := id) hp; simp only [id] at this; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  set H : ℕ := S * n ^ d with hHdef
  have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hf0' : ∀ k ∈ Icc 1 n, f.eval ((k : ℕ) : ℤ) ≠ 0 := fun k _ ↦ eval_ne_zero hf hd _
  have hH : ∀ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs ≤ H := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact (hS k hk1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkn _))
  have hlogH : Real.log H = Real.log S + d * Real.log n := by
    rw [hHdef, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
  have hlogH0 : 0 ≤ Real.log H := Real.log_natCast_nonneg _
  have hlogHΛ : Real.log H ≤ Λ * (1 + Real.log n) := by
    rw [hlogH, hΛ]; nlinarith
  set e : ℕ → ℝ := fun p ↦
    ((∑ k ∈ Icc 1 n, (f.eval ((k : ℕ) : ℤ)).natAbs.factorization p : ℕ) : ℝ) with he
  have he0 : ∀ p, 0 ≤ e p := fun p ↦ Nat.cast_nonneg _
  have helog0 : ∀ p, 0 ≤ e p * Real.log p := fun p ↦
    mul_nonneg (he0 p) (Real.log_natCast_nonneg _)
  -- (1) the identity
  have hsum := sum_log_eq f n P hf0' hP
  -- (2) lower bound
  have hlow : d * (n * Real.log n - n) - C1 * n ≤
      ∑ k ∈ Icc 1 n, Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| := by
    have h1 : ∑ k ∈ Icc 1 n, (d * Real.log k - C1) ≤
        ∑ k ∈ Icc 1 n, Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| :=
      Finset.sum_le_sum fun k hk ↦ hC1 k (Finset.mem_Icc.mp hk).1
    have h2 : ∑ k ∈ Icc 1 n, (d * Real.log k - C1) = d * Real.log n.factorial - C1 * n := by
      have hIcc : Icc 1 n = Ico 1 (n + 1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      have hfac : ∑ k ∈ Icc 1 n, Real.log (k : ℝ) = Real.log n.factorial := by
        rw [← Real.log_prod (fun k hk ↦ by
          have := (Finset.mem_Icc.mp hk).1; positivity), ← Nat.cast_prod, hIcc,
          Finset.prod_Ico_id_eq_factorial]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hfac, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul]
      simp only [add_tsub_cancel_right]
      ring
    have h3 := mul_le_mul_of_nonneg_left (log_factorial_ge n) hd0
    linarith
  -- (3) split at `n`
  have hsplitP : ∑ p ∈ Nat.primesLE P, e p * Real.log p ≤
      ∑ p ∈ Nat.primesLE n, e p * Real.log p +
        ∑ p ∈ Nat.primesLE P with ¬ p ≤ n, e p * Real.log p := by
    rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE P) (· ≤ n)]
    gcongr
    intro p hp
    rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    rw [Nat.primesLE, Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  -- (4) primes `p ≤ n`: bad and good
  have hsplitn := Finset.sum_filter_add_sum_filter_not (Nat.primesLE n) (· ∉ Bad)
    (fun p ↦ e p * Real.log p)
  have hbadpart : ∑ p ∈ Nat.primesLE n with ¬ p ∉ Bad, e p * Real.log p ≤
      CB * (n + Real.log H) := by
    calc ∑ p ∈ Nat.primesLE n with ¬ p ∉ Bad, e p * Real.log p
        ≤ ∑ p ∈ Nat.primesLE n with ¬ p ∉ Bad, Bterm p * (n + Real.log H) := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
          exact ep_log_bad hB hD0 hp.1.2 n H hH1 hf0' hH
      _ ≤ ∑ p ∈ Bad, Bterm p * (n + Real.log H) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_filter] at hp
            exact not_not.mp hp.2
          · intro p _ _; exact mul_nonneg (hBterm0 p) (by positivity)
      _ = CB * (n + Real.log H) := by rw [hCB, Finset.sum_mul]
  have hgoodpart : ∑ p ∈ Nat.primesLE n with p ∉ Bad, e p * Real.log p ≤
      ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * (n * Real.log p / (p - 1)) +
      ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log H := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    have := ep_log_good hB hp.1.2 (hgood p hp.1.2 hp.2).2.2 n H hH1 hf0' hH
    rw [mul_add] at this
    exact this
  -- (4a)
  have hmert := mertens_rho (by omega : 1 ≤ f.natDegree) hmin Bad
    (fun p hp hpB ↦ ⟨(hgood p hp hpB).1, (hgood p hp hpB).2.1⟩) hMert n hnM (by omega)
  have h4a : ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * (n * Real.log p / (p - 1)) ≤
      11 / 10 * n * (3 / 2 * Real.log n + d * M * Real.log 4) + 11 * d * n := by
    have hterm : ∀ p ∈ ({p ∈ Nat.primesLE n | p ∉ Bad} : Finset ℕ),
        (rho f p : ℝ) * (n * Real.log p / (p - 1)) ≤
        11 / 10 * n * ((rho f p : ℝ) * Real.log p / p) + (if p < 11 then (d : ℝ) * n else (0 : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
      have hpp := hp.1.2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
      have hr : (rho f p : ℝ) ≤ d := by exact_mod_cast rho_le hpp (hgood p hpp hp.2).1
      have hr0 : (0 : ℝ) ≤ rho f p := Nat.cast_nonneg _
      have hp1 : (0 : ℝ) < p - 1 := by linarith
      split_ifs with h11
      · -- small primes: `log p ≤ p - 1`
        have hlp' : Real.log p ≤ p - 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by linarith); linarith
        have : (rho f p : ℝ) * (n * Real.log p / (p - 1)) ≤ d * n := by
          rw [mul_div_assoc]
          have hq : Real.log p / (p - 1) ≤ 1 := by rw [div_le_one hp1]; exact hlp'
          have hq0 : 0 ≤ Real.log p / (p - 1) := div_nonneg hlp hp1.le
          calc (rho f p : ℝ) * (n * (Real.log p / (p - 1))) ≤ d * (n * 1) := by
                apply mul_le_mul hr _ (by positivity) hd0
                exact mul_le_mul_of_nonneg_left hq (by linarith)
            _ = d * n := by ring
        have : 0 ≤ 11 / 10 * n * ((rho f p : ℝ) * Real.log p / p) := by positivity
        linarith
      · push_neg at h11
        have hp11 : (11 : ℝ) ≤ p := by exact_mod_cast h11
        have hp0 : (0 : ℝ) < p := by linarith
        rw [add_zero]
        have hX : 0 ≤ (rho f p : ℝ) * n * Real.log p := by positivity
        have key : (rho f p : ℝ) * (n * Real.log p / (p - 1)) =
            ((rho f p : ℝ) * n * Real.log p) / (p - 1) := by ring
        have key2 : 11 / 10 * n * ((rho f p : ℝ) * Real.log p / p) * (p - 1) =
            ((rho f p : ℝ) * n * Real.log p) * (11 / 10 * (p - 1) / p) := by
          field_simp
        rw [key, div_le_iff₀ hp1, key2]
        have h : (1 : ℝ) ≤ 11 / 10 * ((p : ℝ) - 1) / p := by rw [le_div_iff₀ hp0]; linarith
        exact le_mul_of_one_le_right hX h
    calc _ ≤ ∑ p ∈ Nat.primesLE n with p ∉ Bad,
          (11 / 10 * n * ((rho f p : ℝ) * Real.log p / p) + (if p < 11 then (d : ℝ) * n else (0 : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = 11 / 10 * n * ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log p / p +
          ∑ p ∈ Nat.primesLE n with p ∉ Bad, (if p < 11 then (d : ℝ) * n else (0 : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 11 / 10 * n * (3 / 2 * Real.log n + d * M * Real.log 4) + 11 * d * n := by
          gcongr
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have : #(({p ∈ Nat.primesLE n | p ∉ Bad} : Finset ℕ).filter (· < 11)) ≤ 11 := by
            calc _ ≤ #(range 11) := card_le_card fun p hp ↦ by
                  rw [Finset.mem_filter] at hp; exact Finset.mem_range.mpr hp.2
              _ = 11 := card_range _
          have h' : (#(({p ∈ Nat.primesLE n | p ∉ Bad} : Finset ℕ).filter (· < 11)) : ℝ) ≤ 11 := by
            exact_mod_cast this
          have hdn : (0 : ℝ) ≤ (d : ℝ) * n := by positivity
          have := mul_le_mul_of_nonneg_right h' hdn
          linarith
  -- (4b)
  have h4b : ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log H ≤
      d * ((Real.sqrt n + 1) * Real.log H + Cl2 * (Real.log 4 * n)) := by
    have hstep : ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log H ≤
        ∑ p ∈ Nat.primesLE n, d * Real.log H := by
      calc _ ≤ ∑ p ∈ Nat.primesLE n with p ∉ Bad, d * Real.log H := by
            refine Finset.sum_le_sum fun p hp ↦ ?_
            rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
            have hr : (rho f p : ℝ) ≤ d := by exact_mod_cast rho_le hp.1.2 (hgood p hp.1.2 hp.2).1
            exact mul_le_mul_of_nonneg_right hr hlogH0
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ ↦ mul_nonneg hd0 hlogH0)
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hd0
    rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p ↦ p * p < n)]
    gcongr ?_ + ?_
    · rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hlogH0
      have hc : #({p ∈ Nat.primesLE n | p * p < n}) ≤ Nat.sqrt n + 1 := by
        calc _ ≤ #(range (Nat.sqrt n + 1)) := card_le_card fun p hp ↦ by
              rw [Finset.mem_filter] at hp
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt.mpr hp.2.le))
          _ = _ := card_range _
      calc (#({p ∈ Nat.primesLE n | p * p < n}) : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
            exact_mod_cast hc
        _ ≤ Real.sqrt n + 1 := by gcongr; exact Real.nat_sqrt_le_real_sqrt
    · calc ∑ p ∈ Nat.primesLE n with ¬ p * p < n, Real.log H
          ≤ ∑ p ∈ Nat.primesLE n with ¬ p * p < n, Cl2 * Real.log p := by
            refine Finset.sum_le_sum fun p hp ↦ ?_
            rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
            have hpp := hp.1.2
            have hnp : (n : ℝ) ≤ p * p := by exact_mod_cast not_lt.mp hp.2
            have h1 : Real.log n ≤ 2 * Real.log p := by
              have := Real.log_le_log (by positivity) hnp
              rw [Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hpp.ne_zero)]
                at this
              linarith
            have h2 := log_le_mul_log hS1 hpp.two_le
            rw [hlogH, hCl2]
            nlinarith
        _ ≤ ∑ p ∈ Nat.primesLE n, Cl2 * Real.log p :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun p _ _ ↦ by have := Real.log_natCast_nonneg p; positivity)
        _ = Cl2 * Chebyshev.theta n := by rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum]
        _ ≤ Cl2 * (Real.log 4 * n) :=
            mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n))
              (by positivity)
  -- (5) primes `p > n`
  have h5 : ∑ p ∈ Nat.primesLE P with ¬ p ≤ n, e p * Real.log p ≤
      d * (1 + Cl1) * Real.log 4 * P := by
    calc ∑ p ∈ Nat.primesLE P with ¬ p ≤ n, e p * Real.log p
        ≤ ∑ p ∈ Nat.primesLE P with ¬ p ≤ n, d * (1 + Cl1) * Real.log p := by
          refine Finset.sum_le_sum fun p hp ↦ ?_
          rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
          have hpp := hp.1.2
          have hpB : p ∉ Bad := fun h ↦ hp.2 (hBadle p h)
          have h1 := ep_log_good hB hpp (hgood p hpp hpB).2.2 n H hH1 hf0' hH
          have hr : (rho f p : ℝ) ≤ d := by exact_mod_cast rho_le hpp (hgood p hpp hpB).1
          have hr0 : (0 : ℝ) ≤ rho f p := Nat.cast_nonneg _
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
          have hnp : (n : ℝ) + 1 ≤ p := by exact_mod_cast (not_le.mp hp.2)
          have hp1 : (0 : ℝ) < p - 1 := by linarith
          have hq : n * Real.log p / (p - 1) ≤ Real.log p := by
            rw [div_le_iff₀ hp1]; nlinarith
          have hlH : Real.log H ≤ Cl1 * Real.log p := by
            have h2 := log_le_mul_log hS1 hpp.two_le
            have h3 : Real.log n ≤ Real.log p := Real.log_le_log (by positivity) (by linarith)
            rw [hlogH, hCl1]; nlinarith
          calc e p * Real.log p ≤ rho f p * (n * Real.log p / (p - 1) + Real.log H) := h1
            _ ≤ d * (Real.log p + Cl1 * Real.log p) := by
                apply mul_le_mul hr (by linarith) (by positivity) hd0
            _ = d * (1 + Cl1) * Real.log p := by ring
      _ ≤ ∑ p ∈ Nat.primesLE P, d * (1 + Cl1) * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ ↦ by have := Real.log_natCast_nonneg p; positivity)
      _ = d * (1 + Cl1) * Chebyshev.theta P := by
          rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum]
      _ ≤ d * (1 + Cl1) * (Real.log 4 * P) :=
          mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg P))
            (by positivity)
      _ = d * (1 + Cl1) * Real.log 4 * P := by ring
  -- (6) combine
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hΛ0 : 0 ≤ Λ := by positivity
  have hX : Real.log H ≤ Λ * ((Real.sqrt n + 1) * (1 + Real.log n)) := by
    calc Real.log H ≤ Λ * (1 + Real.log n) := hlogHΛ
      _ ≤ Λ * ((Real.sqrt n + 1) * (1 + Real.log n)) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0; nlinarith
  have hY : (Real.sqrt n + 1) * Real.log H ≤ Λ * ((Real.sqrt n + 1) * (1 + Real.log n)) := by
    calc (Real.sqrt n + 1) * Real.log H ≤ (Real.sqrt n + 1) * (Λ * (1 + Real.log n)) :=
          mul_le_mul_of_nonneg_left hlogHΛ (by positivity)
      _ = _ := by ring
  have hCBX := mul_le_mul_of_nonneg_left hX hCB0
  have hdY := mul_le_mul_of_nonneg_left hY hd0
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hnl : 0 ≤ (n : ℝ) * Real.log n := by positivity
  have hdX : 7 / 20 * (n * Real.log n) ≤ (d - 33 / 20) * (n * Real.log n) :=
    mul_le_mul_of_nonneg_right (by linarith) hnl
  have hsplitn' : ∑ p ∈ Nat.primesLE n, e p * Real.log p =
      ∑ p ∈ Nat.primesLE n with p ∉ Bad, e p * Real.log p +
        ∑ p ∈ Nat.primesLE n with ¬ p ∉ Bad, e p * Real.log p := hsplitn.symm
  have hmain : 7 / 20 * (n * Real.log n) ≤
      (CB + 11 / 10 * d * M * Real.log 4 + 11 * d + d * Cl2 * Real.log 4 + d + C1) * n +
        (CB * Λ + d * Λ) * ((Real.sqrt n + 1) * (1 + Real.log n)) +
        d * (1 + Cl1) * Real.log 4 * P := by
    have e1 : ∑ k ∈ Icc 1 n, Real.log |((f.eval ((k : ℕ) : ℤ) : ℤ) : ℝ)| =
        ∑ p ∈ Nat.primesLE P, e p * Real.log p := hsum
    linarith
  have hfin : 7 / 40 * (n * Real.log n) ≤ C' * P := by
    have := habs
    simp only [A, Bc] at this
    nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hC'0]
  linarith

end LaneC976

end

open Filter Asymptotics in
theorem OMA.solution : type_of% @Erdos976.erdos_976.variants.nagell_ricci := by
  intro f hf hd
  obtain ⟨c, hc, hev⟩ := LaneC976.main_bound f hf hd
  refine IsBigO.of_bound (1 / c) ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hN0 : (∏ k ∈ Finset.Icc 1 n, f.eval ((k : ℕ) : ℤ)).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    exact fun k _ ↦ LaneC976.eval_ne_zero hf hd _
  have hP := hn (Erdos976.F f n) (fun p hp hdvd ↦ Nat.le_maxPrimeFac hN0 hp hdvd)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _),
    one_div, ← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]
  exact hP
