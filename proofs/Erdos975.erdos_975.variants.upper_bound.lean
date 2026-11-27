import FormalConjectures.ErdosProblems.«975»

/-!
# Erdős Problem 975, upper bound: `∑_{n ≤ x} τ(f(n)) ≪ x log x`

Original proof (Lane C, claude-code for koolkao), following the decomposition idea of Erdős (1952)
without a sieve:
* for `N = f(n)` write `N = a b`, `a` the product of the smallest prime factors with `a ≤ x`,
  `q` the next prime; `τ(N) ≤ τ(a) 2^{Ω(b)}` and `τ(a) ≤ 2 #{m ∣ a : m² ≥ a}`;
* `∑ ρ(m)/m` over smooth `m` is bounded by Rankin's trick and an Euler product, using
  `∏_{p<y} (1 + ρ(p)/p) ≪ log y`, proved with ideals of norm `p` (Kummer–Dedekind, Mathlib)
  and Mathlib's ideal-counting asymptotic;
* the root counts `ρ(p^k)` are bounded via the Bezout identity `f u + f′ v = Res(f, f′)`.
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

/-! Q1: elementary bounds for the divisor function. -/

noncomputable section
open Finset

namespace LaneC976

theorem card_divisors_mul_le (a b : ℕ) : #(a * b).divisors ≤ #a.divisors * #b.divisors := by
  rw [Nat.divisors_mul]; exact Finset.card_mul_le

theorem card_divisors_eq_prod {n : ℕ} (hn : n ≠ 0) :
    #n.divisors = n.factorization.prod fun _ k ↦ k + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hn]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  simp only
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-- If all prime factors of `b` are `≥ q`, then `τ(b) ≤ 2^s` with `q^s ≤ b`. -/
theorem card_divisors_le_two_pow {b q : ℕ} (hb : b ≠ 0)
    (hpf : ∀ p ∈ b.primeFactors, q ≤ p) :
    ∃ s : ℕ, #b.divisors ≤ 2 ^ s ∧ q ^ s ≤ b := by
  refine ⟨b.factorization.sum fun _ k ↦ k, ?_, ?_⟩
  · rw [card_divisors_eq_prod hb, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun p _ ↦ Nat.lt_two_pow_self
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hb]
    rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun p hp ↦ Nat.pow_le_pow_left (hpf p hp) _

/-- Pairing `m ↔ a / m`: at least half of the divisors of `a` satisfy `a ≤ m²`. -/
theorem card_divisors_le_two_mul (a : ℕ) (ha : a ≠ 0) :
    #a.divisors ≤ 2 * #{m ∈ a.divisors | a ≤ m * m} := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := a.divisors)
    (fun m ↦ a ≤ m * m)
  have hinj : #{m ∈ a.divisors | ¬ a ≤ m * m} ≤ #{m ∈ a.divisors | a ≤ m * m} := by
    refine card_le_card_of_injOn (fun m ↦ a / m) (fun m hm ↦ ?_) (fun m hm m' hm' e ↦ ?_)
    · rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hm
      rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      obtain ⟨⟨hdvd, -⟩, hlt⟩ := hm
      push_neg at hlt
      refine ⟨⟨Nat.div_dvd_of_dvd hdvd, ha⟩, ?_⟩
      obtain ⟨c, rfl⟩ := hdvd
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
      simp only
      rw [Nat.mul_div_cancel_left c hm0]
      nlinarith
    · rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hm hm'
      simp only at e
      have h1 := Nat.div_mul_cancel hm.1.1
      have h2 := Nat.div_mul_cancel hm'.1.1
      rw [e] at h1
      have hpos : 0 < a / m' := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hm'.1.1)
        (Nat.pos_of_ne_zero (by rintro rfl; simp at hm'))
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  omega

/-- The divisor bound `τ(n) ≤ C n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M : ℝ := 1 / (ε * Real.log 2) + 1 with hM
  have hM1 : 1 ≤ M := by have : 0 ≤ 1 / (ε * Real.log 2) := by positivity
                         linarith
  set P0 : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨M ^ P0, by positivity, fun n hn ↦ ?_⟩
  -- per-prime estimate
  have hloc : ∀ p : ℕ, p.Prime → ∀ e : ℕ,
      ((e : ℝ) + 1) ≤ (if p < P0 then M else 1) * ((p : ℝ) ^ e) ^ ε := by
    intro p hp e
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h2e : (2 : ℝ) ^ ((e : ℝ) * ε) ≤ ((p : ℝ) ^ e) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      exact Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    split_ifs with hlt
    · have h1 : 1 + (e : ℝ) * ε * Real.log 2 ≤ (2 : ℝ) ^ ((e : ℝ) * ε) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        have := Real.add_one_le_exp (Real.log 2 * ((e : ℝ) * ε)); linarith
      have h3 : (e : ℝ) + 1 ≤ M * (2 : ℝ) ^ ((e : ℝ) * ε) := by
        have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) * ε) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        have : (e : ℝ) ≤ ((2 : ℝ) ^ ((e : ℝ) * ε) - 1) / (ε * Real.log 2) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        calc (e : ℝ) + 1 ≤ ((2 : ℝ) ^ ((e : ℝ) * ε) - 1) / (ε * Real.log 2) + 1 := by linarith
          _ ≤ (2 : ℝ) ^ ((e : ℝ) * ε) / (ε * Real.log 2) + (2 : ℝ) ^ ((e : ℝ) * ε) := by
              gcongr; linarith
          _ = M * (2 : ℝ) ^ ((e : ℝ) * ε) := by rw [hM]; ring
      exact h3.trans (mul_le_mul_of_nonneg_left h2e (by linarith))
    · push_neg at hlt
      have hpε : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have h1 : (2 : ℝ) ^ (1 / ε) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hlt)
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
      have h4 : ((p : ℝ) ^ e) ^ ε = ((p : ℝ) ^ ε) ^ e := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm,
          Real.rpow_mul (by linarith), Real.rpow_natCast]
      rw [one_mul, h4]
      calc (e : ℝ) + 1 ≤ 2 ^ e := by exact_mod_cast Nat.lt_two_pow_self
        _ ≤ ((p : ℝ) ^ ε) ^ e := pow_le_pow_left₀ (by norm_num) hpε e
  have hτ : (#n.divisors : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [card_divisors_eq_prod hn, Finsupp.prod]; push_cast; rfl
  have hn' : ((n : ℝ)) ^ ε = ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p)) ^ ε := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.cast_prod, Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    push_cast; rfl
  rw [hτ, hn']
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < P0 then M else 1) *
          (((p : ℝ) ^ n.factorization p)) ^ ε) :=
        Finset.prod_le_prod (fun _ _ ↦ by positivity)
          (fun p hp ↦ hloc p (Nat.prime_of_mem_primeFactors hp) _)
    _ = (∏ p ∈ n.primeFactors, (if p < P0 then M else 1)) *
          ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p)) ^ ε := Finset.prod_mul_distrib
    _ ≤ M ^ P0 * ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p)) ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ ↦ by positivity)
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply pow_le_pow_right₀ hM1
        calc #({p ∈ n.primeFactors | p < P0} : Finset ℕ) ≤ #(range P0) :=
              card_le_card fun p hp ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          _ = P0 := card_range _

end LaneC976

end

/-! Q2: the root-counting function `ρ(m)`: counting, submultiplicativity, prime powers. -/

noncomputable section
open Polynomial Finset

namespace LaneC976

theorem rho_le_self (f : ℤ[X]) (m : ℕ) : rho f m ≤ m := by
  unfold rho; exact (card_filter_le _ _).trans (by simp)

/-- `#{n ≤ X : m ∣ f(n)} ≤ ρ(m) (X / m + 1)`. -/
theorem count_dvd_le (f : ℤ[X]) {m : ℕ} (hm : 0 < m) (X : ℕ) :
    #{n ∈ range (X + 1) | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} ≤ rho f m * (X / m + 1) := by
  classical
  set S := {n ∈ range (X + 1) | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ)}
  calc #S ≤ (X / m + 1) * #(S.image (· % m)) := by
        refine card_le_mul_card_image S _ fun a _ ↦ card_le_of_modEq hm ?_ ?_
        · intro k hk
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
          rw [Finset.mem_range] at this; omega
        · intro k hk k' hk'
          exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hk').2.symm
    _ ≤ (X / m + 1) * rho f m := by
        refine Nat.mul_le_mul_left _ (card_le_card fun a ha ↦ ?_)
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        rw [Finset.mem_filter] at hk ⊢
        exact ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), dvd_eval_mod hk.2⟩
    _ = rho f m * (X / m + 1) := mul_comm _ _

theorem rho_mul_le (f : ℤ[X]) {m₁ m₂ : ℕ} (h : m₁.Coprime m₂) (h1 : 0 < m₁) (h2 : 0 < m₂) :
    rho f (m₁ * m₂) ≤ rho f m₁ * rho f m₂ := by
  classical
  unfold rho
  rw [← card_product]
  refine card_le_card_of_injOn (fun c ↦ (c % m₁, c % m₂)) (fun c hc ↦ ?_) (fun c hc c' hc' e ↦ ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hc
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ h1, dvd_eval_mod ?_⟩, ⟨Nat.mod_lt _ h2, dvd_eval_mod ?_⟩⟩
    · exact dvd_trans (by exact_mod_cast Dvd.intro m₂ rfl) hc.2
    · exact dvd_trans (by exact_mod_cast Dvd.intro_left m₁ rfl) hc.2
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc hc'
    simp only [Prod.mk.injEq] at e
    have := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨e.1, e.2⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc'.1] at this

theorem rho_le_prod (f : ℤ[X]) (m : ℕ) (hm : m ≠ 0) :
    rho f m ≤ ∏ p ∈ m.primeFactors, rho f (p ^ m.factorization p) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton,
      hp.factorization_pow, Finsupp.single_eq_same]
  | zero => exact absurd rfl hm
  | one => simp [rho]
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    refine (rho_mul_le f hab (by omega) (by omega)).trans ?_
    rw [Nat.Coprime.primeFactors_mul hab, Finset.prod_union hab.disjoint_primeFactors]
    have e1 : ∀ p ∈ a.primeFactors, (a * b).factorization p = a.factorization p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hb' : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun h ↦
        hpp.one_lt.ne' (Nat.eq_one_of_dvd_one (by
          rw [← Nat.Coprime.gcd_eq_one hab]; exact Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h))
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, hb', add_zero]
    have e2 : ∀ p ∈ b.primeFactors, (a * b).factorization p = b.factorization p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have ha' : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun h ↦
        hpp.one_lt.ne' (Nat.eq_one_of_dvd_one (by
          rw [← Nat.Coprime.gcd_eq_one hab]; exact Nat.dvd_gcd h (Nat.dvd_of_mem_primeFactors hp)))
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, ha', zero_add]
    exact Nat.mul_le_mul
      ((iha ha0).trans (le_of_eq (Finset.prod_congr rfl fun p hp ↦ by rw [e1 p hp])))
      ((ihb hb0).trans (le_of_eq (Finset.prod_congr rfl fun p hp ↦ by rw [e2 p hp])))

/-- Good primes: `ρ(p^k) ≤ ρ(p)`. -/
theorem rho_pow_le_good {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) {k : ℕ} (hk : 1 ≤ k) :
    rho f (p ^ k) ≤ rho f p := by
  classical
  unfold rho
  refine card_le_card_of_injOn (fun c ↦ c % p) (fun c hc ↦ ?_) (fun c hc c' hc' e ↦ ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hc
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hp.pos, dvd_eval_mod (dvd_trans ?_ hc.2)⟩
    exact_mod_cast dvd_pow_self p (by omega)
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc hc'
    simp only at e
    have hxy : ((p : ℤ) ^ (0 + 1)) ∣ (c' : ℤ) - c := by
      rw [zero_add, pow_one]
      exact (Nat.modEq_iff_dvd.mp e)
    have h := cluster hB hp (δ := 0) (by simpa using hpD) (by omega)
      (by exact_mod_cast hc.2) (by exact_mod_cast hc'.2) hxy
    rw [Nat.sub_zero] at h
    have h2 : ((p ^ k : ℕ) : ℤ) ∣ (c' : ℤ) - c := by exact_mod_cast h
    have := (Nat.modEq_iff_dvd.mpr h2)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc'.1] at this

/-- All primes: `ρ(p^k) ≤ p^(2δ+1)`, `δ = v_p(D)`. -/
theorem rho_pow_le_bad {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    (hD : D ≠ 0) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    rho f (p ^ k) ≤ p ^ (2 * padicValInt p D + 1) := by
  classical
  haveI := Fact.mk hp
  set δ := padicValInt p D
  have hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D := by
    rw [padicValInt_dvd_iff]; push_neg; exact ⟨hD, by omega⟩
  by_cases hk : k ≤ δ
  · calc rho f (p ^ k) ≤ p ^ k := rho_le_self f _
      _ ≤ p ^ (2 * δ + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  push_neg at hk
  set S := ({c ∈ range (p ^ k) | ((p ^ k : ℕ) : ℤ) ∣ f.eval ((c : ℕ) : ℤ)} : Finset ℕ)
  have hpos : 0 < p ^ (k - δ) := pow_pos hp.pos _
  have h1 : #S ≤ ((p ^ k - 1) / p ^ (k - δ) + 1) * #(S.image (· % p ^ (δ + 1))) := by
    refine card_le_mul_card_image S _ fun a _ ↦ card_le_of_modEq hpos ?_ ?_
    · intro c hc
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
      rw [Finset.mem_range] at this; omega
    · intro c hc c' hc'
      obtain ⟨hc1, hca⟩ := Finset.mem_filter.mp hc
      obtain ⟨hc1', hca'⟩ := Finset.mem_filter.mp hc'
      have hm : c ≡ c' [MOD p ^ (δ + 1)] := hca.trans hca'.symm
      rw [Nat.modEq_iff_dvd] at hm ⊢
      push_cast at hm ⊢
      have e1 := (Finset.mem_filter.mp hc1).2
      have e2 := (Finset.mem_filter.mp hc1').2
      push_cast at e1 e2
      exact cluster hB hp hδ (by omega) e1 e2 hm
  have h2 : #(S.image (· % p ^ (δ + 1))) ≤ p ^ (δ + 1) := by
    calc _ ≤ #(range (p ^ (δ + 1))) := card_le_card fun a ha ↦ by
          obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
          exact Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos hp.pos _))
      _ = _ := card_range _
  have h3 : (p ^ k - 1) / p ^ (k - δ) + 1 ≤ p ^ δ := by
    have : (p ^ k - 1) / p ^ (k - δ) < p ^ δ := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show δ + (k - δ) = k by omega]
      have := Nat.one_le_pow k p hp.pos
      omega
    omega
  calc rho f (p ^ k) = #S := rfl
    _ ≤ p ^ δ * p ^ (δ + 1) := h1.trans (Nat.mul_le_mul h3 h2)
    _ = p ^ (2 * δ + 1) := by rw [← pow_add]; congr 1; omega

end LaneC976

end

/-! Q3: Rankin's trick with a finite Euler product over smooth numbers. -/

noncomputable section
open Finset

namespace LaneC976

theorem rankin_euler {r : ℕ → ℝ} (r0 : ∀ p, 0 ≤ r p) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (y : ℕ) (g : ℕ → ℝ) (hg0 : ∀ m, 0 ≤ g m) (hg : ∀ m, m ≠ 0 → g m ≤ ∏ p ∈ m.primeFactors, r p)
    (S : Finset ℕ) (hS : ∀ m ∈ S, m ∈ y.smoothNumbers) (w : ℝ) (hw : 0 < w)
    (hSw : ∀ m ∈ S, w ≤ m) :
    ∑ m ∈ S, g m / m ≤ w ^ (-δ) * ∏ p ∈ Nat.primesBelow y,
      (1 + r p * (p : ℝ) ^ (δ - 1) / (1 - (p : ℝ) ^ (δ - 1))) := by
  classical
  set F : ℕ → ℝ := fun m ↦ (∏ p ∈ m.primeFactors, r p) * (m : ℝ) ^ (δ - 1) with hF
  have F0 : ∀ m, 0 ≤ F m := fun m ↦ mul_nonneg (Finset.prod_nonneg fun p _ ↦ r0 p) (by positivity)
  have hF1 : F 1 = 1 := by simp [hF]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    simp only [hF]
    rw [Nat.Coprime.primeFactors_mul hmn, Finset.prod_union hmn.disjoint_primeFactors,
      Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    ring
  have hpow : ∀ {p : ℕ}, p.Prime → ∀ n : ℕ,
      F (p ^ (n + 1)) = r p * ((p : ℝ) ^ (δ - 1)) ^ (n + 1) := by
    intro p hp n
    simp only [hF]
    rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero n) hp, Finset.prod_singleton, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    simp only [mul_comm]
  have ht : ∀ {p : ℕ}, p.Prime → 0 ≤ (p : ℝ) ^ (δ - 1) ∧ (p : ℝ) ^ (δ - 1) < 1 := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact ⟨by positivity, Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)⟩
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖F (p ^ n)‖) := by
    intro p hp
    obtain ⟨t0, t1⟩ := ht hp
    have hg' : Summable (fun n : ℕ ↦ (r p + 1) * ((p : ℝ) ^ (δ - 1)) ^ n) :=
      (summable_geometric_of_lt_one t0 t1).mul_left _
    refine hg'.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    rw [Real.norm_of_nonneg (F0 _)]
    rcases n with _ | n
    · simp [hF1]; linarith [r0 p]
    · rw [hpow hp]
      have : 0 ≤ ((p : ℝ) ^ (δ - 1)) ^ (n + 1) := by positivity
      nlinarith
  obtain ⟨-, hHS⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hF1 hmul hsum y
  have h1 : ∑ m ∈ S, F m ≤ ∏ p ∈ Nat.primesBelow y, ∑' n : ℕ, F (p ^ n) := by
    rw [← Finset.sum_subtype_of_mem F hS]
    exact sum_le_hasSum _ (fun i _ ↦ F0 i) hHS
  have h2 : ∀ p ∈ Nat.primesBelow y, ∑' n : ℕ, F (p ^ n) =
      1 + r p * (p : ℝ) ^ (δ - 1) / (1 - (p : ℝ) ^ (δ - 1)) := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    obtain ⟨t0, t1⟩ := ht hpp
    have hs : Summable (fun n : ℕ ↦ F (p ^ n)) := (hsum hpp).of_norm
    have hshift : ∀ n : ℕ, F (p ^ (n + 1)) = (r p * (p : ℝ) ^ (δ - 1)) * ((p : ℝ) ^ (δ - 1)) ^ n := by
      intro n; rw [hpow hpp, pow_succ]; ring
    rw [hs.tsum_eq_zero_add, pow_zero, hF1]
    simp_rw [hshift]
    rw [tsum_mul_left, tsum_geometric_of_lt_one t0 t1]
    field_simp
  have h3 : ∀ m ∈ S, g m / m ≤ w ^ (-δ) * F m := by
    intro m hm
    have hm0 : m ≠ 0 := (Nat.mem_smoothNumbers.mp (hS m hm)).1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hwm := hSw m hm
    have hP := hg m hm0
    have hPn : 0 ≤ ∏ p ∈ m.primeFactors, r p := Finset.prod_nonneg fun p _ ↦ r0 p
    have hk : 1 ≤ ((m : ℝ) / w) ^ δ := Real.one_le_rpow (by rw [le_div_iff₀ hw]; linarith) hδ0
    have e : w ^ (-δ) * (m : ℝ) ^ (δ - 1) = ((m : ℝ) / w) ^ δ / m := by
      rw [Real.div_rpow hmpos.le hw.le, Real.rpow_neg hw.le, Real.rpow_sub_one hmpos.ne']
      field_simp
    calc g m / m ≤ (∏ p ∈ m.primeFactors, r p) / m := div_le_div_of_nonneg_right hP hmpos.le
      _ ≤ (∏ p ∈ m.primeFactors, r p) * (((m : ℝ) / w) ^ δ / m) := by
          rw [div_eq_mul_one_div]
          apply mul_le_mul_of_nonneg_left _ hPn
          exact div_le_div_of_nonneg_right hk hmpos.le
      _ = w ^ (-δ) * F m := by rw [hF, ← e]; ring
  calc ∑ m ∈ S, g m / m ≤ ∑ m ∈ S, w ^ (-δ) * F m := Finset.sum_le_sum h3
    _ = w ^ (-δ) * ∑ m ∈ S, F m := by rw [Finset.mul_sum]
    _ ≤ w ^ (-δ) * ∏ p ∈ Nat.primesBelow y, ∑' n : ℕ, F (p ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [Finset.prod_congr rfl h2]

end LaneC976

end

/-! Q4: `∏ (1 + N(J)^{-s}) ≤ C / (s - 1)` for pairwise coprime ideals of prime norm. -/

noncomputable section
open Filter Topology Ideal NumberField Finset

namespace LaneC976

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- A linear bound on the ideal count. -/
theorem cnt_le_linear : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, (cnt K m : ℝ) ≤ C * (m + 1) := by
  have h := (tendsto_cnt K).eventually (gt_mem_nhds (lt_add_one (dedekindZeta_residue K)))
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  set B : ℝ := ∑ m ∈ range (M + 1), (cnt K m : ℝ)
  have hres := dedekindZeta_residue_pos K
  refine ⟨B + dedekindZeta_residue K + 1, by positivity, fun m ↦ ?_⟩
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ m + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  by_cases hmM : m ≤ M
  · have : (cnt K m : ℝ) ≤ B :=
      Finset.single_le_sum (f := fun m ↦ (cnt K m : ℝ)) (fun _ _ ↦ Nat.cast_nonneg _)
        (Finset.mem_range.mpr (by omega))
    nlinarith
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have := hM m (by omega)
    rw [div_lt_iff₀ hm0] at this
    nlinarith

/-- Prime-norm ideals are maximal. -/
theorem isMaximal_of_absNorm_prime {J : Ideal (𝓞 K)} (h : (absNorm J).Prime) : J.IsMaximal := by
  have hP : J.IsPrime := isPrime_of_irreducible_absNorm (Nat.prime_iff.mp h |>.irreducible)
  have hne : J ≠ ⊥ := by
    rintro rfl; rw [absNorm_bot] at h; exact Nat.not_prime_zero h
  exact hP.isMaximal hne

/-- Products over distinct subsets of pairwise coprime prime-norm ideals are distinct. -/
theorem prod_injOn {α : Type*} (ι : Finset α) (J : α → Ideal (𝓞 K))
    (hp : ∀ i ∈ ι, (absNorm (J i)).Prime) (hcop : ∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → J i ⊔ J j = ⊤) :
    Set.InjOn (fun S : Finset α ↦ ∏ i ∈ S, J i) (ι.powerset : Set (Finset α)) := by
  classical
  -- `i ∈ S ↔ ∏_S J ≤ J i` for `S ⊆ ι`
  have key : ∀ S ⊆ ι, ∀ i ∈ ι, (∏ j ∈ S, J j ≤ J i ↔ i ∈ S) := by
    intro S hS i hi
    constructor
    · intro hle
      have hprime : (J i).IsPrime := (isMaximal_of_absNorm_prime (hp i hi)).isPrime
      obtain ⟨j, hj, hji⟩ := (Ideal.IsPrime.prod_le hprime).mp hle
      by_contra hiS
      have hij : j ≠ i := fun h ↦ hiS (h ▸ hj)
      have := hcop j (hS hj) i hi hij
      rw [sup_eq_right.mpr hji] at this
      exact (isMaximal_of_absNorm_prime (hp i hi)).ne_top this
    · intro hiS
      exact Ideal.prod_le_inf.trans (Finset.inf_le hiS)
  intro S hS S' hS' e
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hS hS'
  ext i
  constructor
  · intro hi
    have := (key S hS i (hS hi)).mpr hi
    simp only at e
    rw [e] at this
    exact (key S' hS' i (hS hi)).mp this
  · intro hi
    have := (key S' hS' i (hS' hi)).mpr hi
    simp only at e
    rw [← e] at this
    exact (key S hS i (hS' hi)).mp this

theorem one_sub_two_rpow_ge {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    (s - 1) * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (1 - s) := by
  set t := (s - 1) * Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have : s - 1 ≤ 1 := by linarith
    calc t ≤ 1 * Real.log 2 := mul_le_mul_of_nonneg_right this hl2.le
      _ ≤ 1 := by linarith
  have h2 : (2 : ℝ) ^ (1 - s) = Real.exp (-t) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; simp only [t]; ring
  have h3 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp t])
  rw [h2]
  have : 1 / (1 + t) ≤ 1 - t / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

variable (K) in
/-- Dyadic bound for partial Dedekind zeta sums. -/
theorem zeta_partial_le : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 → ∀ Z : ℕ,
    ∑ I ∈ ({I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) Z).toFinset | I ≠ ⊥} : Finset _),
      (absNorm I : ℝ) ^ (-s) ≤ C / (s - 1) := by
  classical
  obtain ⟨C0, hC0, hcnt⟩ := cnt_le_linear K
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨6 * C0 / Real.log 2, by positivity, fun s hs hs2 Z ↦ ?_⟩
  set A := ({I ∈ (finite_setOfPred_absNorm_le (S := 𝓞 K) Z).toFinset | I ≠ ⊥} : Finset _)
  set key : Ideal (𝓞 K) → ℕ := fun I ↦ Nat.log 2 (absNorm I)
  have hmaps : ∀ I ∈ A, key I ∈ range (Nat.log 2 Z + 1) := by
    intro I hI
    rw [mem_cnt] at hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hI.2))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hq0 : 0 < (2 : ℝ) ^ (1 - s) := by positivity
  have hq1 : (2 : ℝ) ^ (1 - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hfib : ∀ j ∈ range (Nat.log 2 Z + 1),
      ∑ I ∈ A with key I = j, (absNorm I : ℝ) ^ (-s) ≤ 3 * C0 * ((2 : ℝ) ^ (1 - s)) ^ j := by
    intro j _
    calc ∑ I ∈ A with key I = j, (absNorm I : ℝ) ^ (-s)
        ≤ ∑ I ∈ A with key I = j, ((2 : ℝ) ^ j) ^ (-s) := by
          refine Finset.sum_le_sum fun I hI ↦ ?_
          rw [Finset.mem_filter, mem_cnt] at hI
          have hN0 : absNorm I ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact hI.1.1
          have h1 : 2 ^ j ≤ absNorm I := hI.2 ▸ Nat.pow_log_le_self 2 hN0
          apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast h1) (by linarith)
      _ = #({I ∈ A | key I = j} : Finset _) * ((2 : ℝ) ^ j) ^ (-s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C0 * ((2 ^ (j + 1) : ℕ) + 1)) * ((2 : ℝ) ^ j) ^ (-s) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          refine le_trans ?_ (hcnt (2 ^ (j + 1)))
          exact_mod_cast Finset.card_le_card fun I hI ↦ by
            rw [Finset.mem_filter, mem_cnt] at hI
            rw [mem_cnt]
            refine ⟨hI.1.1, ?_⟩
            have hN0 : absNorm I ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact hI.1.1
            have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (absNorm I)
            simp only [key] at hI
            rw [hI.2] at this; exact this.le
      _ ≤ 3 * C0 * ((2 : ℝ) ^ (1 - s)) ^ j := by
          have e1 : ((2 : ℝ) ^ j) ^ (-s) * (2 : ℝ) ^ j = ((2 : ℝ) ^ (1 - s)) ^ j := by
            have h1 : ((2 : ℝ) ^ j) ^ (-s) = ((2 : ℝ) ^ (-s)) ^ j := by
              rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
                ← Real.rpow_mul (by norm_num), mul_comm]
            have h2 : (2 : ℝ) ^ (-s) * 2 = (2 : ℝ) ^ (1 - s) := by
              rw [show (1 - s) = -s + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
            rw [h1, ← mul_pow, h2]
          have e2 : (((2 ^ (j + 1) : ℕ) : ℝ) + 1) ≤ 3 * (2 : ℝ) ^ j := by
            push_cast; rw [pow_succ]
            have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
            linarith
          have hpos : 0 ≤ ((2 : ℝ) ^ j) ^ (-s) := by positivity
          calc C0 * (((2 ^ (j + 1) : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ j) ^ (-s)
              ≤ C0 * (3 * (2 : ℝ) ^ j) * ((2 : ℝ) ^ j) ^ (-s) := by gcongr
            _ = 3 * C0 * (((2 : ℝ) ^ j) ^ (-s) * (2 : ℝ) ^ j) := by ring
            _ = _ := by rw [e1]
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := Nat.log 2 Z + 1) hq0.le hq1
  rw [Finset.range_eq_Ico]
  have hden := one_sub_two_rpow_ge hs hs2
  have hpos : 0 < 1 - (2 : ℝ) ^ (1 - s) := by linarith
  calc 3 * C0 * ∑ j ∈ Ico 0 (Nat.log 2 Z + 1), ((2 : ℝ) ^ (1 - s)) ^ j
      ≤ 3 * C0 * (((2 : ℝ) ^ (1 - s)) ^ 0 / (1 - (2 : ℝ) ^ (1 - s))) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 3 * C0 / (1 - (2 : ℝ) ^ (1 - s)) := by rw [pow_zero]; ring
    _ ≤ 3 * C0 / ((s - 1) * Real.log 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by nlinarith) hden
    _ = 6 * C0 / Real.log 2 / (s - 1) := by
        have : (s - 1) ≠ 0 := by linarith
        field_simp
        ring

variable (K) in
theorem prod_one_add_le : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 → ∀ {α : Type}
    (ι : Finset α) (J : α → Ideal (𝓞 K)), (∀ i ∈ ι, (absNorm (J i)).Prime) →
    (∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → J i ⊔ J j = ⊤) →
    ∏ i ∈ ι, (1 + (absNorm (J i) : ℝ) ^ (-s)) ≤ C / (s - 1) := by
  classical
  obtain ⟨C, hC, hZ⟩ := zeta_partial_le K
  refine ⟨C, hC, fun s hs hs2 α ι J hp hcop ↦ ?_⟩
  set Z := ∏ i ∈ ι, absNorm (J i)
  rw [Finset.prod_one_add]
  have h1 : ∀ S ∈ ι.powerset, ∏ i ∈ S, (absNorm (J i) : ℝ) ^ (-s) =
      (absNorm (∏ i ∈ S, J i) : ℝ) ^ (-s) := by
    intro S _
    rw [map_prod, Nat.cast_prod, Real.finsetProd_rpow _ _ (fun i _ ↦ Nat.cast_nonneg _)]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_image (f := fun I ↦ (absNorm I : ℝ) ^ (-s))
    (prod_injOn ι J hp hcop)]
  refine le_trans ?_ (hZ s hs hs2 Z)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
    rw [Finset.mem_powerset] at hS
    rw [mem_cnt]
    have hne : ∀ i ∈ ι, absNorm (J i) ≠ 0 := fun i hi ↦ (hp i hi).ne_zero
    refine ⟨?_, ?_⟩
    · intro h0
      have := congrArg absNorm h0
      rw [map_prod, absNorm_bot, Finset.prod_eq_zero_iff] at this
      obtain ⟨i, hi, h⟩ := this
      exact hne i (hS hi) h
    · rw [map_prod]
      exact Finset.prod_le_prod_of_subset_of_one_le' hS fun i hi _ ↦
        Nat.one_le_iff_ne_zero.mpr (hne i hi)
  · intro I _ _; positivity

end LaneC976

end

/-! Q5: `∏_{p < y good} (1 + ρ(p)/p) ≪ log y`, and Rankin's bound for `∑ ρ(m)/m` over smooth `m`. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

/-- `1 + 1/p ≤ (1 + p^{-s}) exp(σ log p / p)`, `s = 1 + σ`. -/
theorem one_add_inv_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 + 1 / (p : ℝ) ≤ (1 + (p : ℝ) ^ (-(1 + σ))) * Real.exp (σ * Real.log p / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  have e1 : (p : ℝ) ^ (-(1 + σ)) = 1 / p * Real.exp (-(σ * Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0, show Real.log p * -(1 + σ) = -Real.log p + -(σ * Real.log p) by
      ring, Real.exp_add, Real.exp_neg (Real.log p), Real.exp_log hp0, one_div]
  have h1 : 1 - σ * Real.log p ≤ Real.exp (-(σ * Real.log p)) := by
    have := Real.add_one_le_exp (-(σ * Real.log p)); linarith
  have hb : 0 ≤ σ * Real.log p / p := by positivity
  have h2 := Real.add_one_le_exp (σ * Real.log p / p)
  rw [e1]
  have hq : 0 ≤ 1 / (p : ℝ) * Real.exp (-(σ * Real.log p)) := by positivity
  -- 1 + 1/p ≤ 1 + (1/p) e^{-u} + u/p ≤ (1 + (1/p) e^{-u}) (1 + u/p)
  have h3 : 1 + 1 / (p : ℝ) ≤ 1 + 1 / p * Real.exp (-(σ * Real.log p)) + σ * Real.log p / p := by
    have : 1 / (p : ℝ) * (1 - σ * Real.log p) ≤ 1 / p * Real.exp (-(σ * Real.log p)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e2 : 1 / (p : ℝ) * (1 - σ * Real.log p) = 1 / p - σ * Real.log p / p := by ring
    linarith
  calc 1 + 1 / (p : ℝ) ≤ 1 + 1 / p * Real.exp (-(σ * Real.log p)) + σ * Real.log p / p := h3
    _ ≤ (1 + 1 / p * Real.exp (-(σ * Real.log p))) * (1 + σ * Real.log p / p) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem two_rpow_le : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 5 := by
  have hx : 0 ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by positivity
  have h4 : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ (4 : ℕ) = 1 / 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ (4 : ℕ) ≤ (3 / 5 : ℝ) ^ (4 : ℕ) := by
    rw [h4]; norm_num
  exact (pow_le_pow_iff_left₀ hx (by norm_num) (by norm_num)).mp this

theorem exp_sub_one_le (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have h := Real.add_one_le_exp (-u)
  have hpos := Real.exp_pos u
  have : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- Per-prime factor bound for good primes. -/
theorem good_factor_le {p : ℕ} (hp : p.Prime) {ρ δ κ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4) (hκ : δ * Real.log p ≤ κ) :
    1 + ρ * (p : ℝ) ^ (δ - 1) / (1 - (p : ℝ) ^ (δ - 1)) ≤
      (1 + ρ / p) * Real.exp (ρ * δ * Real.exp κ * Real.log p / p +
        5 / 2 * ρ * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  set t := (p : ℝ) ^ (δ - 1)
  have ht0 : 0 ≤ t := by positivity
  have htle : t ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h34 : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 5 := by
    have : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    exact this.trans two_rpow_le
  have ht1 : t ≤ 3 / 5 := htle.trans h34
  have hpd : (p : ℝ) ^ δ ≤ Real.exp κ := by
    rw [Real.rpow_def_of_pos hp0]; exact Real.exp_le_exp.mpr (by linarith)
  have hpd1 : (p : ℝ) ^ δ - 1 ≤ δ * Real.log p * Real.exp κ := by
    have := exp_sub_one_le (δ * Real.log p)
    rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p)]
    have h3 : Real.exp (δ * Real.log p) ≤ Real.exp κ := Real.exp_le_exp.mpr hκ
    have h4 : 0 ≤ δ * Real.log p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have htdef : t = (p : ℝ) ^ δ / p := by
    simp only [t]; rw [Real.rpow_sub_one hp0.ne']
  have ht2 : t * t ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc t * t ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) * (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
          mul_le_mul htle htle ht0 (by positivity)
      _ = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hp0]; norm_num
  -- t / (1 - t) ≤ t + (5/2) t²
  have hfrac : t / (1 - t) ≤ t + 5 / 2 * (t * t) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg (mul_nonneg ht0 ht0) (by linarith : (0:ℝ) ≤ 3 / 5 - t)]
  have hA : ρ * t ≤ ρ / p + ρ * δ * Real.exp κ * Real.log p / p := by
    rw [htdef]
    have : (p : ℝ) ^ δ ≤ 1 + δ * Real.log p * Real.exp κ := by linarith
    calc ρ * ((p : ℝ) ^ δ / p) = ρ * (p : ℝ) ^ δ / p := by ring
      _ ≤ ρ * (1 + δ * Real.log p * Real.exp κ) / p := by gcongr
      _ = _ := by ring
  set B := ρ * δ * Real.exp κ * Real.log p / p + 5 / 2 * ρ * (p : ℝ) ^ (-(3 / 2 : ℝ))
  have hB0 : 0 ≤ B := by positivity
  have h1 : 1 + ρ * t / (1 - t) ≤ 1 + ρ / p + B := by
    have : ρ * t / (1 - t) = ρ * (t / (1 - t)) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hfrac hρ0
    have h5 := mul_le_mul_of_nonneg_left ht2 hρ0
    simp only [B]; nlinarith
  have h2 : 1 + ρ / p + B ≤ (1 + ρ / p) * Real.exp B := by
    have := Real.add_one_le_exp B
    have hq : 0 ≤ ρ / p := by positivity
    nlinarith
  linarith

section concrete

variable {f : ℤ[X]} (hd : 1 ≤ f.natDegree) {K : Type} [Field K] [NumberField K] {θ : 𝓞 K}
  (hmin : minpoly ℤ θ = f.integralNormalization) (Bad : Finset ℕ)
  (hgood : ∀ p, p.Prime → p ∉ Bad →
    ¬ (p : ℤ) ∣ f.leadingCoeff ∧ ¬ p ∣ RingOfIntegers.exponent θ)
include hd hmin hgood

/-- The ideals `(p, θ - a c)`: norms and coprimality. -/
theorem pair_props (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ∉ Bad) (Y : ℕ) :
    let ι := ((P ×ˢ range Y).filter fun x : ℕ × ℕ ↦
      x.2 < x.1 ∧ (x.1 : ℤ) ∣ f.eval ((x.2 : ℕ) : ℤ))
    let J : ℕ × ℕ → Ideal (𝓞 K) :=
      fun x ↦ span {((x.1 : ℕ) : 𝓞 K), θ - ((f.leadingCoeff * (x.2 : ℤ) : ℤ) : 𝓞 K)}
    (∀ x ∈ ι, absNorm (J x) = x.1) ∧ (∀ x ∈ ι, ∀ y ∈ ι, x ≠ y → J x ⊔ J y = ⊤) := by
  intro ι J
  have hmem : ∀ x ∈ ι, x.1.Prime ∧ x.1 ∉ Bad ∧ x.2 < x.1 ∧
      (x.1 : ℤ) ∣ f.eval ((x.2 : ℕ) : ℤ) := by
    intro x hx
    simp only [ι, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨(hP _ hx.1.1).1, (hP _ hx.1.1).2, hx.2⟩
  refine ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_⟩
  · obtain ⟨hp, hbad, -, hdvd⟩ := hmem x hx
    haveI := Fact.mk hp
    refine absNorm_span_pair (hgood _ hp hbad).2 ?_
    rw [hmin]
    have := integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id ℤ) ((x.2 : ℕ) : ℤ)
    change f.integralNormalization.eval (f.leadingCoeff * (x.2 : ℤ)) =
      f.leadingCoeff ^ (f.natDegree - 1) * f.eval ((x.2 : ℕ) : ℤ) at this
    rw [this]
    exact dvd_mul_of_dvd_right hdvd _
  · obtain ⟨hp, hbad, hc, -⟩ := hmem x hx
    obtain ⟨hq, -, hc', -⟩ := hmem y hy
    exact sup_span_pair_eq_top θ f.leadingCoeff hp hq hc hc' (hgood _ hp hbad).1 (by
      intro h; apply hxy; exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Chebyshev bound for `ρ`, valid for all `n`. -/
theorem cheb_rho : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log p / p ≤
      3 / 2 * Real.log n + C := by
  obtain ⟨M, hM10, hMert⟩ := mertens_ideal K
  set C0 : ℝ := ∑ p ∈ Nat.primesLE M, f.natDegree * Real.log p / p
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg fun p _ ↦ by
    have := Real.log_natCast_nonneg p; positivity
  refine ⟨f.natDegree * M * Real.log 4 + C0, by positivity, fun n ↦ ?_⟩
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg _
  by_cases hn : M ≤ n
  · have := mertens_rho hd hmin Bad (fun p hp hpB ↦ hgood p hp hpB) hMert n hn (by omega)
    linarith
  · push_neg at hn
    have h1 : ∑ p ∈ Nat.primesLE n with p ∉ Bad, (rho f p : ℝ) * Real.log p / p ≤ C0 := by
      calc _ ≤ ∑ p ∈ Nat.primesLE n with p ∉ Bad, f.natDegree * Real.log p / p := by
            refine Finset.sum_le_sum fun p hp ↦ ?_
            rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
            have hr : (rho f p : ℝ) ≤ f.natDegree := by
              exact_mod_cast rho_le hp.1.2 (hgood p hp.1.2 hp.2).1
            have := Real.log_natCast_nonneg p
            have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.2.pos
            gcongr
        _ ≤ C0 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
              rw [Nat.primesLE, Nat.mem_primesBelow]; exact ⟨by omega, hp.1.2⟩
            · intro p _ _; have := Real.log_natCast_nonneg p; positivity
    have : 0 ≤ f.natDegree * M * Real.log 4 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
    linarith

theorem prod_rho_le : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y →
    ∏ p ∈ Nat.primesBelow y with p ∉ Bad, (1 + (rho f p : ℝ) / p) ≤ C * Real.log y := by
  classical
  obtain ⟨Cc, hCc0, hCc⟩ := cheb_rho hd hmin Bad hgood
  obtain ⟨C4, hC4, hprod⟩ := prod_one_add_le K
  refine ⟨C4 * Real.exp (3 / 2 + Cc), by positivity, fun y hy ↦ ?_⟩
  set P := (Nat.primesBelow y).filter (· ∉ Bad)
  have hP : ∀ p ∈ P, p.Prime ∧ p ∉ Bad := fun p hp ↦ by
    rw [Finset.mem_filter, Nat.mem_primesBelow] at hp; exact ⟨hp.1.2, hp.2⟩
  obtain ⟨hnorm, hcop⟩ := pair_props hd hmin Bad hgood (K := K) P hP y
  set ι := ((P ×ˢ range y).filter fun x : ℕ × ℕ ↦
      x.2 < x.1 ∧ (x.1 : ℤ) ∣ f.eval ((x.2 : ℕ) : ℤ))
  set J : ℕ × ℕ → Ideal (𝓞 K) :=
      fun x ↦ span {((x.1 : ℕ) : 𝓞 K), θ - ((f.leadingCoeff * (x.2 : ℤ) : ℤ) : 𝓞 K)}
  have hly : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  set σ := 1 / Real.log y with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by rw [hσ, div_le_one (by linarith)]; exact hly
  -- regroup a product over pairs as a product over primes
  have hgroup : ∀ g : ℕ → ℝ, ∏ x ∈ ι, g x.1 = ∏ p ∈ P, g p ^ rho f p := by
    intro g
    rw [Finset.prod_filter, Finset.prod_product]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hpy : p < y := by
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp; exact hp.1.1
    rw [← Finset.prod_filter]
    dsimp only
    rw [Finset.prod_const, rho]
    congr 1
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
  have hgroupS : ∀ g : ℕ → ℝ, ∑ x ∈ ι, g x.1 = ∑ p ∈ P, rho f p * g p := by
    intro g
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hpy : p < y := by
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp; exact hp.1.1
    rw [← Finset.sum_filter]
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul, rho]
    congr 1
    norm_cast
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
  -- step 1: Bernoulli
  have h1 : ∏ p ∈ P, (1 + (rho f p : ℝ) / p) ≤ ∏ x ∈ ι, (1 + 1 / (x.1 : ℝ)) := by
    rw [hgroup (fun p ↦ 1 + 1 / (p : ℝ))]
    refine Finset.prod_le_prod (fun p _ ↦ by positivity) fun p _ ↦ ?_
    have h0 : (0 : ℝ) ≤ 1 / p := by positivity
    have := one_add_mul_le_pow (a := 1 / (p : ℝ)) (by linarith) (rho f p)
    calc 1 + (rho f p : ℝ) / p = 1 + (rho f p : ℝ) * (1 / p) := by ring
      _ ≤ _ := this
  -- step 2: compare with `p^{-s}`
  have h2 : ∏ x ∈ ι, (1 + 1 / (x.1 : ℝ)) ≤
      (∏ x ∈ ι, (1 + (x.1 : ℝ) ^ (-(1 + σ)))) * ∏ x ∈ ι, Real.exp (σ * Real.log x.1 / x.1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun x _ ↦ by positivity) fun x hx ↦ ?_
    have hp : x.1.Prime := by
      have := (Finset.mem_filter.mp hx).1
      exact (hP _ (Finset.mem_product.mp this).1).1
    exact one_add_inv_le hp hσ0.le
  -- step 3: the ideal product
  have h3 : ∏ x ∈ ι, (1 + (x.1 : ℝ) ^ (-(1 + σ))) ≤ C4 * Real.log y := by
    have := hprod (1 + σ) (by linarith) (by linarith) ι J
      (fun x hx ↦ by rw [hnorm x hx]; have := (Finset.mem_filter.mp hx).1
                     exact (hP _ (Finset.mem_product.mp this).1).1) hcop
    rw [Finset.prod_congr rfl fun x hx ↦ by rw [hnorm x hx]] at this
    calc _ ≤ C4 / (1 + σ - 1) := this
      _ = C4 * Real.log y := by rw [add_sub_cancel_left, hσ, div_div_eq_mul_div, div_one]
  -- step 4: the exponential factor
  have h4 : ∏ x ∈ ι, Real.exp (σ * Real.log x.1 / x.1) ≤ Real.exp (3 / 2 + Cc) := by
    rw [← Real.exp_sum, hgroupS (fun p ↦ σ * Real.log p / p)]
    apply Real.exp_le_exp.mpr
    have hsub : ∑ p ∈ P, (rho f p : ℝ) * (σ * Real.log p / p) =
        σ * ∑ p ∈ P, (rho f p : ℝ) * Real.log p / p := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ ↦ by ring
    rw [hsub]
    have hPle : ∑ p ∈ P, (rho f p : ℝ) * Real.log p / p ≤ 3 / 2 * Real.log y + Cc := by
      refine le_trans ?_ (hCc y)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
        rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow]
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
      · intro p _ _; have := Real.log_natCast_nonneg p; positivity
    calc σ * ∑ p ∈ P, (rho f p : ℝ) * Real.log p / p ≤ σ * (3 / 2 * Real.log y + Cc) :=
          mul_le_mul_of_nonneg_left hPle hσ0.le
      _ = 3 / 2 + σ * Cc := by rw [hσ]; field_simp
      _ ≤ 3 / 2 + Cc := by nlinarith
  calc ∏ p ∈ P, (1 + (rho f p : ℝ) / p) ≤ ∏ x ∈ ι, (1 + 1 / (x.1 : ℝ)) := h1
    _ ≤ _ := h2
    _ ≤ (C4 * Real.log y) * Real.exp (3 / 2 + Cc) :=
        mul_le_mul h3 h4 (Finset.prod_nonneg fun _ _ ↦ by positivity) (by positivity)
    _ = C4 * Real.exp (3 / 2 + Cc) * Real.log y := by ring

theorem rankin_rho {u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D) (hD0 : D ≠ 0)
    (hgoodD : ∀ p, p.Prime → p ∉ Bad → ¬ (p : ℤ) ∣ D) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∀ y : ℕ, 3 ≤ y → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → δ * Real.log y ≤ κ →
      ∀ w : ℝ, 0 < w → ∀ S : Finset ℕ, (∀ m ∈ S, m ∈ y.smoothNumbers) → (∀ m ∈ S, w ≤ m) →
      ∑ m ∈ S, (rho f m : ℝ) / m ≤ K1 * w ^ (-δ) * Real.log y := by
  classical
  obtain ⟨Cρ, hCρ, hprodρ⟩ := prod_rho_le hd hmin Bad hgood
  obtain ⟨Cc, hCc0, hCc⟩ := cheb_rho hd hmin Bad hgood
  set r : ℕ → ℝ := fun p ↦ if p ∈ Bad then (p : ℝ) ^ (2 * padicValInt p D + 1) else rho f p
    with hr
  have r0 : ∀ p, 0 ≤ r p := fun p ↦ by simp only [hr]; split_ifs <;> positivity
  set CB : ℝ := ∏ p ∈ Bad, (1 + 3 / 2 * r p)
  have hCB : 1 ≤ CB := Finset.one_le_prod fun p _ ↦ by have := r0 p; linarith
  have hsumm : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set Zs : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹
  have hZs : 0 ≤ Zs := tsum_nonneg fun n ↦ by positivity
  set E : ℝ := Real.exp κ * (3 / 2 * κ + Cc) + 5 / 2 * f.natDegree * Zs with hEdef
  refine ⟨CB * Cρ * Real.exp E, by positivity, fun y hy δ hδ0 hδ hδκ w hw S hS hSw ↦ ?_⟩
  have hly : 0 ≤ Real.log y := Real.log_natCast_nonneg _
  have hg : ∀ m, m ≠ 0 → (rho f m : ℝ) ≤ ∏ p ∈ m.primeFactors, r p := by
    intro m hm
    have h1 : (rho f m : ℝ) ≤ ∏ p ∈ m.primeFactors, (rho f (p ^ m.factorization p) : ℝ) := by
      exact_mod_cast rho_le_prod f m hm
    refine h1.trans (Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _) fun p hp ↦ ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    simp only [hr]
    split_ifs with hbad
    · exact_mod_cast rho_pow_le_bad hB hD0 hpp _
    · have hk : 1 ≤ m.factorization p :=
        (Nat.Prime.factorization_pos_of_dvd hpp hm (Nat.dvd_of_mem_primeFactors hp))
      exact_mod_cast rho_pow_le_good hB hpp (hgoodD p hpp hbad) hk
  have hR := rankin_euler r0 hδ0 hδ y (fun m ↦ (rho f m : ℝ)) (fun _ ↦ Nat.cast_nonneg _) hg S hS
    w hw hSw
  refine hR.trans ?_
  -- bound the Euler product
  set fac : ℕ → ℝ := fun p ↦ 1 + r p * (p : ℝ) ^ (δ - 1) / (1 - (p : ℝ) ^ (δ - 1)) with hfac
  have hfac1 : ∀ p, p.Prime → 1 ≤ fac p ∧ fac p ≤ 1 + 3 / 2 * r p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    set t := (p : ℝ) ^ (δ - 1)
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 3 / 5 := by
      have htle : t ≤ (p : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      have h3 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 5 := two_rpow_le
      linarith
    have hq : t / (1 - t) ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hq0 : 0 ≤ t / (1 - t) := div_nonneg ht0 (by linarith)
    have e : r p * t / (1 - t) = r p * (t / (1 - t)) := by ring
    simp only [hfac]
    rw [e]
    constructor
    · have := mul_nonneg (r0 p) hq0; linarith
    · have := mul_le_mul_of_nonneg_left hq (r0 p); linarith
  rw [← Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow y) (· ∈ Bad)]
  have hbadprod : ∏ p ∈ Nat.primesBelow y with p ∈ Bad, fac p ≤ CB := by
    calc _ ≤ ∏ p ∈ Nat.primesBelow y with p ∈ Bad, (1 + 3 / 2 * r p) :=
          Finset.prod_le_prod (fun p hp ↦ by
            have := (hfac1 p (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2).1; linarith)
            fun p hp ↦ (hfac1 p (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2).2
      _ ≤ CB := Finset.prod_le_prod_of_subset_of_one_le (fun p hp ↦ (Finset.mem_filter.mp hp).2)
            (fun p _ ↦ by have := r0 p; linarith) fun p _ _ ↦ by have := r0 p; linarith
  have hgoodprod : ∏ p ∈ Nat.primesBelow y with ¬ p ∈ Bad, fac p ≤
      Cρ * Real.log y * Real.exp E := by
    have hstep : ∀ p ∈ ({p ∈ Nat.primesBelow y | ¬ p ∈ Bad} : Finset ℕ), fac p ≤ (1 + (rho f p : ℝ) / p) *
        Real.exp (rho f p * δ * Real.exp κ * Real.log p / p +
          5 / 2 * rho f p * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      have hpp := hp.1.2
      have hrp : r p = rho f p := by simp only [hr]; rw [if_neg hp.2]
      simp only [hfac]; rw [hrp]
      refine good_factor_le hpp (Nat.cast_nonneg _) hδ0 hδ ?_
      have : Real.log p ≤ Real.log y :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hp.1.1.le)
      nlinarith
    refine (Finset.prod_le_prod (fun p hp ↦ by
      have := (hfac1 p (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2).1; linarith)
      hstep).trans ?_
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    have hP := hprodρ y hy
    have hexp : ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
        ((rho f p : ℝ) * δ * Real.exp κ * Real.log p / p +
          5 / 2 * rho f p * (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤ E := by
      rw [Finset.sum_add_distrib]
      have e1 : ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
          (rho f p : ℝ) * δ * Real.exp κ * Real.log p / p =
          δ * Real.exp κ * ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
            (rho f p : ℝ) * Real.log p / p := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ ↦ by ring
      have hcheb : ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad, (rho f p : ℝ) * Real.log p / p ≤
          3 / 2 * Real.log y + Cc := by
        refine le_trans ?_ (hCc y)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
          rw [Finset.mem_filter, Nat.primesLE, Nat.mem_primesBelow]
          exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
        · intro p _ _; have := Real.log_natCast_nonneg p; positivity
      have e2 : ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
          5 / 2 * (rho f p : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 5 / 2 * f.natDegree * Zs := by
        calc _ ≤ ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
              5 / 2 * (f.natDegree : ℝ) * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
              refine Finset.sum_le_sum fun p hp ↦ ?_
              rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
              have hrd : (rho f p : ℝ) ≤ f.natDegree := by
                exact_mod_cast rho_le hp.1.2 (hgood p hp.1.2 hp.2).1
              rw [Real.rpow_neg (Nat.cast_nonneg _)]
              gcongr
          _ = 5 / 2 * f.natDegree * ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
                ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [Finset.mul_sum]
          _ ≤ 5 / 2 * f.natDegree * Zs := by
              gcongr
              exact hsumm.sum_le_tsum _ (fun n _ ↦ by positivity)
      rw [e1]
      have h3 : δ * Real.exp κ * ∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
          (rho f p : ℝ) * Real.log p / p ≤ Real.exp κ * (3 / 2 * κ + Cc) := by
        calc _ ≤ δ * Real.exp κ * (3 / 2 * Real.log y + Cc) :=
              mul_le_mul_of_nonneg_left hcheb (by positivity)
          _ = Real.exp κ * (3 / 2 * (δ * Real.log y) + δ * Cc) := by ring
          _ ≤ Real.exp κ * (3 / 2 * κ + Cc) := by
              gcongr
              · nlinarith
      rw [hEdef]
      linarith
    calc (∏ p ∈ Nat.primesBelow y with ¬ p ∈ Bad, (1 + (rho f p : ℝ) / p)) *
          Real.exp (∑ p ∈ Nat.primesBelow y with ¬ p ∈ Bad,
            ((rho f p : ℝ) * δ * Real.exp κ * Real.log p / p +
              5 / 2 * rho f p * (p : ℝ) ^ (-(3 / 2 : ℝ))))
        ≤ (Cρ * Real.log y) * Real.exp E :=
          mul_le_mul hP (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity)
      _ = _ := rfl
  have hgp0 : 0 ≤ ∏ p ∈ Nat.primesBelow y with ¬ p ∈ Bad, fac p :=
    Finset.prod_nonneg fun p hp ↦ by
      have := (hfac1 p (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2).1; linarith
  calc w ^ (-δ) * ((∏ p ∈ Nat.primesBelow y with p ∈ Bad, fac p) *
        ∏ p ∈ Nat.primesBelow y with ¬ p ∈ Bad, fac p)
      ≤ w ^ (-δ) * (CB * (Cρ * Real.log y * Real.exp E)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hbadprod hgoodprod hgp0 (by positivity)
    _ = CB * Cρ * Real.exp E * w ^ (-δ) * Real.log y := by ring

end concrete

end LaneC976

end

/-! Q6: Erdős's decomposition `N = a b` (smallest prime factors in `a ≤ X`) and the pointwise
bound for `τ(N)`. -/

noncomputable section
open Finset

namespace LaneC976

theorem primeFactors_listProd_subset {l : List ℕ} (hl : ∀ x ∈ l, x.Prime) {p : ℕ}
    (hp : p ∈ l.prod.primeFactors) : p ∈ l := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨x, hx, hpx⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.mp hpp)).mp
    (Nat.dvd_of_mem_primeFactors hp)
  rwa [(Nat.prime_dvd_prime_iff_eq hpp (hl x hx)).mp hpx]

theorem decomp (N X : ℕ) (hN : N ≠ 0) (hX : 1 ≤ X) (hNX : X < N) :
    ∃ a b q : ℕ, q.Prime ∧ a * b = N ∧ a ≤ X ∧ X < a * q ∧
      (∀ p ∈ a.primeFactors, p ≤ q) ∧ (∀ p ∈ b.primeFactors, q ≤ p) := by
  classical
  set L := N.primeFactorsList with hL
  have hprod : L.prod = N := Nat.prod_primeFactorsList hN
  have hsorted : L.Pairwise (· ≤ ·) := (Nat.primeFactorsList_sorted N).pairwise
  have hprime : ∀ x ∈ L, x.Prime := fun x hx ↦ Nat.prime_of_mem_primeFactorsList hx
  set P : ℕ → Prop := fun i ↦ (L.take i).prod ≤ X
  set j := Nat.findGreatest P L.length with hj
  have hPj : P j := Nat.findGreatest_spec (P := P) (Nat.zero_le _) (by simp [P]; exact hX)
  have hjle : j ≤ L.length := Nat.findGreatest_le _
  have hjlt : j < L.length := by
    rcases lt_or_eq_of_le hjle with h | h
    · exact h
    · exfalso; simp only [P] at hPj; rw [h, List.take_length, hprod] at hPj; omega
  set q := L[j]
  have hqmem : q ∈ L := List.getElem_mem hjlt
  refine ⟨(L.take j).prod, (L.drop j).prod, q, hprime q hqmem, ?_, hPj, ?_, ?_, ?_⟩
  · rw [List.prod_take_mul_prod_drop, hprod]
  · have h1 : ¬ P (j + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) (by omega)
    simp only [P, not_le] at h1
    rwa [List.prod_take_succ L j hjlt] at h1
  · intro p hp
    have hpt := primeFactors_listProd_subset (fun x hx ↦ hprime x (List.mem_of_mem_take hx)) hp
    have hs := hsorted
    rw [← List.take_append_drop j L] at hs
    have := (List.pairwise_append.mp hs).2.2 p hpt q (by
      rw [List.drop_eq_getElem_cons hjlt]; exact List.mem_cons.mpr (Or.inl rfl))
    exact this
  · intro p hp
    have hpd := primeFactors_listProd_subset (fun x hx ↦ hprime x (List.mem_of_mem_drop hx)) hp
    have hs : (L.drop j).Pairwise (· ≤ ·) := hsorted.sublist (List.drop_sublist _ _)
    rw [List.drop_eq_getElem_cons hjlt] at hs hpd
    rcases List.mem_cons.mp hpd with h | h
    · exact h ▸ le_refl _
    · exact (List.pairwise_cons.mp hs).1 p h

/-- The smoothness bound `⌊X^{1/r}⌋ + 1`. -/
def yr (X r : ℕ) : ℕ := ⌊(X : ℝ) ^ ((1 : ℝ) / r)⌋₊ + 1

def TB (X r : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun m ↦ X < m ^ 4 ∧ m ∈ (yr X r).smoothNumbers

def TC (X Y0 : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun m ↦ X < m * Y0 ∧ m ∈ (Y0 + 1).smoothNumbers

def Rset (X Y0 : ℕ) : Finset ℕ := (Icc 2 X).filter fun r ↦ Y0 < ⌊(X : ℝ) ^ ((1 : ℝ) / r)⌋₊

/-- the number of `m ∈ T` dividing `N` -/
def dcount (T : Finset ℕ) (N : ℕ) : ℕ := #{m ∈ T | m ∣ N}

theorem le_floor_rpow {q r X : ℕ} (hr : 1 ≤ r) (h : q ^ r ≤ X) :
    q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / r)⌋₊ := by
  apply Nat.le_floor
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : ((q : ℝ) ^ r) ≤ X := by exact_mod_cast h
  calc (q : ℝ) = ((q : ℝ) ^ (r : ℝ)) ^ ((1 : ℝ) / r) := by
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hr'.ne', Real.rpow_one]
    _ ≤ (X : ℝ) ^ ((1 : ℝ) / r) := by
        apply Real.rpow_le_rpow (by positivity) (by rw [Real.rpow_natCast]; exact h1)
          (by positivity)

theorem tau_pointwise (N X D' Y0 : ℕ) (hN : N ≠ 0) (hX : 1 ≤ X) (hNX : N ≤ X ^ D') :
    (#N.divisors : ℝ) ≤ 4 ^ D' * dcount (Icc 1 X) N +
      ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) * dcount (TB X r) N +
      #N.divisors * dcount (TC X Y0) N := by
  classical
  have hA0 : (0 : ℝ) ≤ 4 ^ D' * dcount (Icc 1 X) N := by positivity
  have hB0 : (0 : ℝ) ≤ ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) * dcount (TB X r) N :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hC0 : (0 : ℝ) ≤ #N.divisors * dcount (TC X Y0) N := by positivity
  -- divisors of a divisor `a ≤ X` of `N` are counted by `dcount (Icc 1 X) N`
  have hsubA : ∀ a, a ∣ N → a ≤ X → #a.divisors ≤ dcount (Icc 1 X) N := by
    intro a ha haX
    unfold dcount
    refine card_le_card fun m hm ↦ ?_
    rw [Nat.mem_divisors] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    exact ⟨⟨hm0, (Nat.le_of_dvd (Nat.pos_of_ne_zero hm.2) hm.1).trans haX⟩, hm.1.trans ha⟩
  by_cases hNle : N ≤ X
  · have := hsubA N dvd_rfl hNle
    have h4 : (1 : ℝ) ≤ 4 ^ D' := one_le_pow₀ (by norm_num)
    have : (#N.divisors : ℝ) ≤ dcount (Icc 1 X) N := by exact_mod_cast this
    nlinarith
  push_neg at hNle
  obtain ⟨a, b, q, hq, hab, haX, hXaq, hpa, hpb⟩ := decomp N X hN hX hNle
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hN hab.symm
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hN hab.symm
  have hq2 := hq.two_le
  obtain ⟨s, hτb, hqs⟩ := card_divisors_le_two_pow hb0 hpb
  have hbN : b ≤ N := hab ▸ Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hτN : (#N.divisors : ℝ) ≤ #a.divisors * 2 ^ s := by
    have := card_divisors_mul_le a b
    rw [hab] at this
    have h2 : #a.divisors * #b.divisors ≤ #a.divisors * 2 ^ s := Nat.mul_le_mul_left _ hτb
    exact_mod_cast this.trans h2
  by_cases hA : X < q * q
  · -- case A
    have hs : s < 2 * D' := by
      have : q ^ s < q ^ (2 * D') := by
        calc q ^ s ≤ N := hqs.trans hbN
          _ ≤ X ^ D' := hNX
          _ < (q * q) ^ D' := Nat.pow_lt_pow_left hA (by
              rcases Nat.eq_zero_or_pos D' with h | h
              · subst h; simp at hNX; omega
              · omega)
          _ = q ^ (2 * D') := by rw [← pow_two, ← pow_mul]
      exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
    have h2s : (2 : ℝ) ^ s ≤ 4 ^ D' := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (2 * D') := pow_le_pow_right₀ (by norm_num) hs.le
        _ = 4 ^ D' := by rw [pow_mul]; norm_num
    have hτa : (#a.divisors : ℝ) ≤ dcount (Icc 1 X) N := by
      exact_mod_cast hsubA a (hab ▸ dvd_mul_right a b) haX
    have : (#N.divisors : ℝ) ≤ 4 ^ D' * dcount (Icc 1 X) N := by
      calc _ ≤ (#a.divisors : ℝ) * 2 ^ s := hτN
        _ ≤ dcount (Icc 1 X) N * 4 ^ D' :=
            mul_le_mul hτa h2s (by positivity) (by positivity)
        _ = _ := by ring
    linarith
  push_neg at hA
  by_cases hC : q ≤ Y0
  · -- case C
    have : 1 ≤ dcount (TC X Y0) N := by
      unfold dcount
      apply Finset.card_pos.mpr
      refine ⟨a, ?_⟩
      rw [Finset.mem_filter, TC, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨Nat.pos_of_ne_zero ha0, haX⟩, ?_, ?_⟩, hab ▸ dvd_mul_right a b⟩
      · calc X < a * q := hXaq
          _ ≤ a * Y0 := Nat.mul_le_mul_left _ hC
      · rw [Nat.mem_smoothNumbers']
        intro p hp hpa'
        have := hpa p (Nat.mem_primeFactors.mpr ⟨hp, hpa', ha0⟩)
        omega
    have h1 : (1 : ℝ) ≤ dcount (TC X Y0) N := by exact_mod_cast this
    have : (#N.divisors : ℝ) ≤ #N.divisors * dcount (TC X Y0) N := by
      have := Nat.cast_nonneg (α := ℝ) (#N.divisors); nlinarith
    linarith
  push_neg at hC
  -- case B
  set r := Nat.log q X
  have hqr : q ^ r ≤ X := Nat.pow_log_le_self q (by omega)
  have hXr : X < q ^ (r + 1) := Nat.lt_pow_succ_log_self hq.one_lt X
  have hr2 : 2 ≤ r := by
    have : q ^ 2 ≤ X := by rw [pow_two]; exact hA
    exact Nat.le_log_of_pow_le hq.one_lt this
  have hrX : r ≤ X := (Nat.log_le_self q X)
  have hqF : q ≤ ⌊(X : ℝ) ^ ((1 : ℝ) / r)⌋₊ := le_floor_rpow (by omega) hqr
  have hrR : r ∈ Rset X Y0 := by
    rw [Rset, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hr2, hrX⟩, by omega⟩
  have hs : s < (r + 1) * D' := by
    have : q ^ s < q ^ ((r + 1) * D') := by
      calc q ^ s ≤ N := hqs.trans hbN
        _ ≤ X ^ D' := hNX
        _ < (q ^ (r + 1)) ^ D' := Nat.pow_lt_pow_left hXr (by
              rcases Nat.eq_zero_or_pos D' with h | h
              · subst h; simp at hNX; omega
              · omega)
        _ = q ^ ((r + 1) * D') := by rw [← pow_mul]
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
  have hτa : #a.divisors ≤ 2 * dcount (TB X r) N := by
    refine (card_divisors_le_two_mul a ha0).trans (Nat.mul_le_mul_left _ ?_)
    unfold dcount
    refine card_le_card fun m hm ↦ ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hm
    obtain ⟨⟨hma, -⟩, ham⟩ := hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hma; exact ha0 hma
    rw [Finset.mem_filter, TB, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.pos_of_ne_zero hm0, (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hma).trans haX⟩,
      ?_, ?_⟩, hma.trans (hab ▸ dvd_mul_right a b)⟩
    · -- `X < m^4`: `a² > X` since `a q > X` and `q² ≤ X`
      have h1 : X * X < (a * q) * (a * q) := Nat.mul_lt_mul'' hXaq hXaq
      have h2 : X < a * a := by
        by_contra h
        push_neg at h
        have : (a * q) * (a * q) ≤ X * X := by
          calc (a * q) * (a * q) = (a * a) * (q * q) := by ring
            _ ≤ X * X := Nat.mul_le_mul h hA
        omega
      calc X < a * a := h2
        _ ≤ (m * m) * (m * m) := Nat.mul_le_mul ham ham
        _ = m ^ 4 := by ring
    · rw [Nat.mem_smoothNumbers']
      intro p hp hpm
      have := hpa p (Nat.mem_primeFactors.mpr ⟨hp, hpm.trans hma, ha0⟩)
      unfold yr; omega
  have : (#N.divisors : ℝ) ≤ (2 : ℝ) ^ ((r + 1) * D' + 1) * dcount (TB X r) N := by
    calc _ ≤ (#a.divisors : ℝ) * 2 ^ s := hτN
      _ ≤ (2 * dcount (TB X r) N : ℕ) * (2 : ℝ) ^ ((r + 1) * D') :=
          mul_le_mul (by exact_mod_cast hτa) (pow_le_pow_right₀ (by norm_num) hs.le)
            (by positivity) (by positivity)
      _ = _ := by push_cast; rw [pow_succ]; ring
  have hsingle := Finset.single_le_sum (f := fun r ↦ (2 : ℝ) ^ ((r + 1) * D' + 1) *
    dcount (TB X r) N) (fun _ _ ↦ by positivity) hrR
  linarith

end LaneC976

end

/-! Q7: summing the pointwise bound over `n`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC976

/-- Swapping the sums: `∑_n #{m ∈ T : m ∣ f(n)} ≤ 2X ∑_{m ∈ T} ρ(m)/m`. -/
theorem sum_dcount_le (f : ℤ[X]) (X : ℕ) (S : Finset ℕ) (hS : S ⊆ range (X + 1))
    (T : Finset ℕ) (hT : T ⊆ Icc 1 X) :
    ∑ n ∈ S, (dcount T (f.eval ((n : ℕ) : ℤ)).natAbs : ℝ) ≤
      2 * X * ∑ m ∈ T, (rho f m : ℝ) / m := by
  classical
  have h1 : ∑ n ∈ S, (dcount T (f.eval ((n : ℕ) : ℤ)).natAbs : ℝ) =
      ∑ m ∈ T, (#{n ∈ S | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ) := by
    simp only [dcount, Finset.card_filter, Nat.cast_sum, Int.natCast_dvd]
    rw [Finset.sum_comm]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hT hm)).1
  have hmX : m ≤ X := (Finset.mem_Icc.mp (hT hm)).2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have h2 : #{n ∈ S | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} ≤ rho f m * (X / m + 1) := by
    refine le_trans (card_le_card fun n hn ↦ ?_) (count_dvd_le f hm1 X)
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hS hn.1, hn.2⟩
  have h3 : ((X / m + 1 : ℕ) : ℝ) ≤ 2 * X / m := by
    have : (X / m : ℕ) ≤ (X : ℝ) / m := Nat.cast_div_le
    have h4 : (1 : ℝ) ≤ X / m := by
      rw [le_div_iff₀ hm0]; exact_mod_cast (show 1 * m ≤ X by omega)
    push_cast; linarith [show (2 : ℝ) * X / m = X / m + X / m by ring]
  calc (#{n ∈ S | (m : ℤ) ∣ f.eval ((n : ℕ) : ℤ)} : ℝ) ≤ (rho f m * (X / m + 1) : ℕ) := by
        exact_mod_cast h2
    _ = (rho f m : ℝ) * ((X / m + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (rho f m : ℝ) * (2 * X / m) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = 2 * X * ((rho f m : ℝ) / m) := by ring

section terms

variable {f : ℤ[X]} {K1 κ : ℝ}

/-- The `B_r` term. -/
theorem termB (hK : ∀ y : ℕ, 3 ≤ y → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → δ * Real.log y ≤ κ →
      ∀ w : ℝ, 0 < w → ∀ S : Finset ℕ, (∀ m ∈ S, m ∈ y.smoothNumbers) → (∀ m ∈ S, w ≤ m) →
      ∑ m ∈ S, (rho f m : ℝ) / m ≤ K1 * w ^ (-δ) * Real.log y)
    (hκ : 0 < κ) (hK1 : 0 ≤ K1) {Y0 X r : ℕ} (hY0 : Real.exp (4 * κ) ≤ Y0) (hY3 : 3 ≤ Y0)
    (hX : 1 ≤ X) (hr : r ∈ Rset X Y0) :
    ∑ m ∈ TB X r, (rho f m : ℝ) / m ≤ K1 * Real.exp (-(κ * r / 8)) * Real.log (X + 1) := by
  rw [Rset, Finset.mem_filter, Finset.mem_Icc] at hr
  obtain ⟨⟨hr2, hrX⟩, hF⟩ := hr
  set F := ⌊(X : ℝ) ^ ((1 : ℝ) / r)⌋₊
  set y := yr X r
  have hy : y = F + 1 := rfl
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hXr : (X : ℝ) ^ ((1 : ℝ) / r) ≤ X := by
    calc (X : ℝ) ^ ((1 : ℝ) / r) ≤ (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX)
            (by rw [div_le_one hr0]; exact_mod_cast (show 1 ≤ r by omega))
      _ = X := Real.rpow_one _
  have hFle : (F : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / r) := Nat.floor_le (by positivity)
  have hF2 : (2 : ℝ) ≤ F := by exact_mod_cast (show 2 ≤ F by omega)
  have hy3 : 3 ≤ y := by omega
  have hyR : (y : ℝ) = F + 1 := by rw [hy]; push_cast; ring
  have hlogy_pos : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogy4 : 4 * κ ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    calc Real.exp (4 * κ) ≤ Y0 := hY0
      _ ≤ y := by exact_mod_cast (show Y0 ≤ y by omega)
  set δ := κ / Real.log y
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 4 := by rw [div_le_iff₀ hlogy_pos]; linarith
  have hδκ : δ * Real.log y ≤ κ := by rw [div_mul_cancel₀ _ hlogy_pos.ne']
  set w := (X : ℝ) ^ ((1 : ℝ) / 4)
  have hw : 0 < w := by positivity
  have hS : ∀ m ∈ TB X r, m ∈ y.smoothNumbers := fun m hm ↦ (Finset.mem_filter.mp hm).2.2
  have hSw : ∀ m ∈ TB X r, w ≤ m := by
    intro m hm
    have h4 : (X : ℝ) < (m : ℝ) ^ 4 := by exact_mod_cast (Finset.mem_filter.mp hm).2.1
    calc w ≤ ((m : ℝ) ^ 4) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) h4.le (by norm_num)
      _ = m := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have h := hK y hy3 δ hδ0 hδ hδκ w hw (TB X r) hS hSw
  refine h.trans ?_
  -- `w^{-δ} ≤ exp(-κ r / 8)` and `log y ≤ log (X + 1)`
  have hlogy : Real.log y ≤ 2 * Real.log X / r := by
    have h1 : (y : ℝ) ≤ 2 * (X : ℝ) ^ ((1 : ℝ) / r) := by rw [hyR]; linarith
    have h2 : Real.log y ≤ Real.log 2 + Real.log X / r := by
      calc Real.log y ≤ Real.log (2 * (X : ℝ) ^ ((1 : ℝ) / r)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log 2 + Real.log X / r := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hXpos]; ring
    have h3 : Real.log 2 ≤ Real.log X / r := by
      have : (2 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / r) := hF2.trans hFle
      have := Real.log_le_log (by norm_num) this
      rwa [Real.log_rpow hXpos, one_div_mul_eq_div] at this
    have : 2 * Real.log X / r = Real.log X / r + Real.log X / r := by ring
    linarith
  have hw' : w ^ (-δ) ≤ Real.exp (-(κ * r / 8)) := by
    rw [Real.rpow_def_of_pos hw, Real.log_rpow hXpos]
    apply Real.exp_le_exp.mpr
    have hlX : 0 ≤ Real.log X := Real.log_natCast_nonneg _
    -- `(1/4) log X · δ ≥ κ r / 8`
    have : κ * r / 8 ≤ 1 / 4 * Real.log X * δ := by
      have e : 1 / 4 * Real.log X * δ = κ * (Real.log X / (4 * Real.log y)) := by
        simp only [δ]; field_simp
      rw [e, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hκ.le
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hlogy (show (0 : ℝ) ≤ r / 8 * 4 by positivity)
      have e2 : r / 8 * 4 * (2 * Real.log X / r) = Real.log X := by field_simp; ring
      rw [e2] at this
      nlinarith
    nlinarith
  have hly : Real.log y ≤ Real.log (X + 1) := by
    apply Real.log_le_log (by positivity)
    rw [hyR]; linarith
  have hlogy0 : 0 ≤ Real.log y := hlogy_pos.le
  calc K1 * w ^ (-δ) * Real.log y ≤ K1 * Real.exp (-(κ * r / 8)) * Real.log y := by
        gcongr
    _ ≤ K1 * Real.exp (-(κ * r / 8)) * Real.log (X + 1) := by gcongr

end terms

end LaneC976

end

/-! Q8: the main estimate `∑_{n ≤ X} τ(f(n)) ≪ X log X` for irreducible `f` of degree `≥ 1`. -/

noncomputable section
open Polynomial Finset Filter NumberField

namespace LaneC976

/-- The geometric sum over `r`. -/
theorem sum_weights_le (D' : ℕ) (hD : 1 ≤ D') (R : Finset ℕ) :
    ∑ r ∈ R, (2 : ℝ) ^ ((r + 1) * D' + 1) * Real.exp (-(16 * D' * r / 8)) ≤ 2 ^ (D' + 2) := by
  set q0 : ℝ := ((2 : ℝ) * Real.exp (-2)) ^ D'
  have he2 : Real.exp (-2) < 1 / 4 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [inv_lt_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hq0 : 0 ≤ q0 := by positivity
  have hq1 : q0 ≤ 1 / 2 := by
    have h1 : (2 : ℝ) * Real.exp (-2) ≤ 1 / 2 := by linarith
    calc q0 ≤ ((2 : ℝ) * Real.exp (-2)) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by linarith) hD
      _ ≤ 1 / 2 := by rw [pow_one]; exact h1
  have hterm : ∀ r : ℕ, (2 : ℝ) ^ ((r + 1) * D' + 1) * Real.exp (-(16 * D' * r / 8)) =
      2 ^ (D' + 1) * q0 ^ r := by
    intro r
    have e1 : Real.exp (-(16 * D' * r / 8)) = (Real.exp (-2)) ^ (D' * r) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e1]
    simp only [q0]
    rw [← pow_mul, mul_pow]
    have : (r + 1) * D' + 1 = D' + 1 + D' * r := by ring
    rw [this, pow_add]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hsum : ∑ r ∈ R, q0 ^ r ≤ 2 := by
    have hs : Summable (fun r : ℕ ↦ q0 ^ r) := summable_geometric_of_lt_one hq0 (by linarith)
    calc ∑ r ∈ R, q0 ^ r ≤ ∑' r : ℕ, q0 ^ r := hs.sum_le_tsum _ (fun _ _ ↦ by positivity)
      _ = (1 - q0)⁻¹ := tsum_geometric_of_lt_one hq0 (by linarith)
      _ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc (2 : ℝ) ^ (D' + 1) * ∑ r ∈ R, q0 ^ r ≤ 2 ^ (D' + 1) * 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 ^ (D' + 2) := by ring

set_option maxHeartbeats 1600000 in
theorem main975 (f : ℤ[X]) (hf : Irreducible f) (hd : 1 ≤ f.natDegree)
    (n0 : ℕ) (hpos : ∀ n : ℕ, n0 ≤ n → 1 ≤ f.eval (n : ℤ)) :
    ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ range (X + 1), (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) ≤ C * (X * Real.log X) := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  have ha0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hfQ : Irreducible (fQ f) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive (by omega))).mp hf
  obtain ⟨K, _, _, θ, hmin, hE⟩ := exists_theta f hfQ
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout f hfQ hd
  set a := f.leadingCoeff
  set E := RingOfIntegers.exponent θ
  set Bad : Finset ℕ := (a * (E : ℤ) * D).natAbs.primeFactors with hBad
  have hBad0 : (a * (E : ℤ) * D).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact mul_ne_zero (mul_ne_zero ha0 (by exact_mod_cast hE)) hD0
  have hgood3 : ∀ p, p.Prime → p ∉ Bad → ¬ (p : ℤ) ∣ a ∧ ¬ p ∣ E ∧ ¬ (p : ℤ) ∣ D := by
    intro p hp hpB
    have hnd : ¬ p ∣ (a * (E : ℤ) * D).natAbs := fun h ↦
      hpB (Nat.mem_primeFactors.mpr ⟨hp, h, hBad0⟩)
    rw [← Int.natCast_dvd] at hnd
    refine ⟨fun h ↦ hnd ?_, fun h ↦ hnd ?_, fun h ↦ hnd ?_⟩
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast h) _) _
    · exact dvd_mul_of_dvd_right h _
  have hgood : ∀ p, p.Prime → p ∉ Bad → ¬ (p : ℤ) ∣ f.leadingCoeff ∧ ¬ p ∣ E :=
    fun p hp hpB ↦ ⟨(hgood3 p hp hpB).1, (hgood3 p hp hpB).2.1⟩
  have hgoodD : ∀ p, p.Prime → p ∉ Bad → ¬ (p : ℤ) ∣ D := fun p hp hpB ↦ (hgood3 p hp hpB).2.2
  set D' := f.natDegree + 1 with hD'
  have hD'1 : 1 ≤ D' := by omega
  set κ : ℝ := 16 * D' with hκdef
  have hκ : 0 < κ := by positivity
  set Y0 : ℕ := ⌈Real.exp (4 * κ)⌉₊ + 3
  have hY0 : Real.exp (4 * κ) ≤ Y0 := by
    have := Nat.le_ceil (Real.exp (4 * κ)); push_cast [Y0]; linarith
  have hY3 : 3 ≤ Y0 := by omega
  obtain ⟨KA, hKA, hRA⟩ := rankin_rho hd hmin Bad hgood hB hD0 hgoodD 0 le_rfl
  obtain ⟨KB, hKB, hRB⟩ := rankin_rho hd hmin Bad hgood hB hD0 hgoodD κ hκ.le
  set κC : ℝ := Real.log (Y0 + 1) / 4 with hκCdef
  have hκC : 0 ≤ κC := by have := Real.log_natCast_nonneg (Y0 + 1); push_cast at this; positivity
  obtain ⟨KC, hKC, hRC⟩ := rankin_rho hd hmin Bad hgood hB hD0 hgoodD κC hκC
  set ε : ℝ := 1 / (8 * D') with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨Cε, hCε, hdiv⟩ := card_divisors_le_rpow hε
  obtain ⟨S0, hS01, hS0⟩ := natAbs_eval_le f
  set n1 := max n0 1
  set Cs : ℝ := ∑ n ∈ range n1, (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ)
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  set CC : ℝ := 2 * Cε * KC * Real.log (Y0 + 1) * (Y0 : ℝ) ^ ((1 : ℝ) / 4) with hCCdef
  have hCC : 0 ≤ CC := by
    have := Real.log_natCast_nonneg (Y0 + 1); push_cast at this; positivity
  set CAB : ℝ := 4 ^ D' * 2 * KA + 2 * KB * 2 ^ (D' + 2) with hCABdef
  refine ⟨Cs + 2 * CAB + CC, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max S0 n1) 3)] with X hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hXS : S0 ≤ X := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hX
  have hXn1 : n1 ≤ X := le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hX
  have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hX1 : 1 ≤ X := by omega
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hlogX1 : Real.log (X + 1) ≤ 2 * Real.log X := by
    calc Real.log (X + 1) ≤ Real.log ((X : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  -- split the sum at `n1`
  rw [← Finset.sum_filter_add_sum_filter_not (range (X + 1)) (· < n1)]
  have hsmall : ∑ n ∈ range (X + 1) with n < n1,
      (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) ≤ Cs := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; rw [Finset.mem_filter] at hn; exact Finset.mem_range.mpr hn.2
    · intro n _ _; positivity
  set SL := (range (X + 1)).filter (fun n ↦ ¬ n < n1)
  have hSL : SL ⊆ range (X + 1) := Finset.filter_subset _ _
  -- pointwise bound on the large range
  have hpt : ∀ n ∈ SL, (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) ≤
      4 ^ D' * dcount (Icc 1 X) (f.eval ((n : ℕ) : ℤ)).natAbs +
      ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) *
        dcount (TB X r) (f.eval ((n : ℕ) : ℤ)).natAbs +
      Cε * (X : ℝ) ^ ((1 : ℝ) / 8) * dcount (TC X Y0) (f.eval ((n : ℕ) : ℤ)).natAbs := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    have hn1 : n1 ≤ n := not_lt.mp hn.2
    have hfn : 1 ≤ f.eval (n : ℤ) := hpos n (le_trans (le_max_left _ _) hn1)
    have htoNat : (f.eval ((n : ℕ) : ℤ)).toNat = (f.eval ((n : ℕ) : ℤ)).natAbs := by omega
    rw [htoNat]
    have hN0' : (f.eval ((n : ℕ) : ℤ)).natAbs ≠ 0 := by omega
    set N := (f.eval ((n : ℕ) : ℤ)).natAbs
    have hN0 : N ≠ 0 := hN0'
    have hNX : N ≤ X ^ D' := by
      calc N ≤ S0 * n ^ f.natDegree := hS0 n (le_trans (le_max_right _ _) hn1)
        _ ≤ X * X ^ f.natDegree := Nat.mul_le_mul hXS (Nat.pow_le_pow_left (by omega) _)
        _ = X ^ D' := by rw [hD', pow_succ]; ring
    have h1 := tau_pointwise N X D' Y0 hN0 hX1 hNX
    have h2 : (#N.divisors : ℝ) ≤ Cε * (X : ℝ) ^ ((1 : ℝ) / 8) := by
      refine (hdiv N hN0).trans ?_
      apply mul_le_mul_of_nonneg_left _ hCε.le
      calc (N : ℝ) ^ ε ≤ ((X : ℝ) ^ D') ^ ε :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNX) hε.le
        _ = (X : ℝ) ^ ((1 : ℝ) / 8) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            congr 1; rw [hεdef]; field_simp
    have h3 : (#N.divisors : ℝ) * dcount (TC X Y0) N ≤
        Cε * (X : ℝ) ^ ((1 : ℝ) / 8) * dcount (TC X Y0) N :=
      mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    linarith
  have hTB : ∀ r, TB X r ⊆ Icc 1 X := fun r ↦ Finset.filter_subset _ _
  have hTC : TC X Y0 ⊆ Icc 1 X := Finset.filter_subset _ _
  -- sum the pointwise bound
  have hlarge : ∑ n ∈ SL, (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) ≤
      4 ^ D' * (2 * X * ∑ m ∈ Icc 1 X, (rho f m : ℝ) / m) +
      ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) * (2 * X * ∑ m ∈ TB X r, (rho f m : ℝ) / m) +
      Cε * (X : ℝ) ^ ((1 : ℝ) / 8) * (2 * X * ∑ m ∈ TC X Y0, (rho f m : ℝ) / m) := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm]
    gcongr with r hr
    · exact sum_dcount_le f X SL hSL _ subset_rfl
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_dcount_le f X SL hSL _ (hTB r)) (by positivity)
    · exact sum_dcount_le f X SL hSL _ hTC
  -- the three Rankin bounds
  have hA : ∑ m ∈ Icc 1 X, (rho f m : ℝ) / m ≤ KA * Real.log (X + 1) := by
    have := hRA (X + 1) (by omega) 0 le_rfl (by norm_num) (by simp) 1 one_pos (Icc 1 X)
      (fun m hm ↦ Nat.mem_smoothNumbers_of_lt (by have := (Finset.mem_Icc.mp hm).1; omega)
        (by have := (Finset.mem_Icc.mp hm).2; omega))
      (fun m hm ↦ by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    simpa using this
  have hBr : ∀ r ∈ Rset X Y0, ∑ m ∈ TB X r, (rho f m : ℝ) / m ≤
      KB * Real.exp (-(κ * r / 8)) * Real.log (X + 1) :=
    fun r hr ↦ termB hRB hκ hKB.le hY0 hY3 hX1 hr
  have hC : ∑ m ∈ TC X Y0, (rho f m : ℝ) / m ≤
      KC * ((X : ℝ) / Y0) ^ (-(1 / 4 : ℝ)) * Real.log (Y0 + 1) := by
    have hY0pos : (0 : ℝ) < Y0 := by exact_mod_cast (show 0 < Y0 by omega)
    have := hRC (Y0 + 1) (by omega) (1 / 4) (by norm_num) le_rfl (by rw [hκCdef]; push_cast; linarith)
      ((X : ℝ) / Y0) (by positivity) (TC X Y0) (fun m hm ↦ (Finset.mem_filter.mp hm).2.2)
      (fun m hm ↦ by
        have h := (Finset.mem_filter.mp hm).2.1
        rw [div_le_iff₀ hY0pos]; exact_mod_cast h.le)
    simpa using this
  -- combine
  have hAterm : 4 ^ D' * (2 * X * ∑ m ∈ Icc 1 X, (rho f m : ℝ) / m) ≤
      4 ^ D' * 2 * KA * (2 * (X * Real.log X)) := by
    calc _ ≤ 4 ^ D' * (2 * X * (KA * Real.log (X + 1))) := by gcongr
      _ ≤ 4 ^ D' * (2 * X * (KA * (2 * Real.log X))) := by gcongr
      _ = _ := by ring
  have hBterm : ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) *
      (2 * X * ∑ m ∈ TB X r, (rho f m : ℝ) / m) ≤ 2 * KB * 2 ^ (D' + 2) * (2 * (X * Real.log X)) := by
    calc _ ≤ ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) *
            (2 * X * (KB * Real.exp (-(κ * r / 8)) * Real.log (X + 1))) :=
          Finset.sum_le_sum fun r hr ↦ by gcongr; exact hBr r hr
      _ = 2 * X * KB * Real.log (X + 1) * ∑ r ∈ Rset X Y0, (2 : ℝ) ^ ((r + 1) * D' + 1) *
            Real.exp (-(16 * D' * r / 8)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ ↦ by rw [hκdef]; ring
      _ ≤ 2 * X * KB * Real.log (X + 1) * 2 ^ (D' + 2) := by
          have hl1 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
          exact mul_le_mul_of_nonneg_left (sum_weights_le D' hD'1 _)
            (mul_nonneg (by positivity) hl1)
      _ ≤ 2 * X * KB * (2 * Real.log X) * 2 ^ (D' + 2) := by gcongr
      _ = _ := by ring
  have hCterm : Cε * (X : ℝ) ^ ((1 : ℝ) / 8) * (2 * X * ∑ m ∈ TC X Y0, (rho f m : ℝ) / m) ≤
      CC * (X * Real.log X) := by
    have hY0pos : (0 : ℝ) < Y0 := by exact_mod_cast (show 0 < Y0 by omega)
    have hXpos : (0 : ℝ) < X := by positivity
    have hlY : 0 ≤ Real.log ((Y0 : ℝ) + 1) := by
      have := Real.log_natCast_nonneg (Y0 + 1); push_cast at this; exact this
    have e1 : ((X : ℝ) / Y0) ^ (-(1 / 4 : ℝ)) =
        (Y0 : ℝ) ^ ((1 : ℝ) / 4) * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.div_rpow hXpos.le hY0pos.le, Real.rpow_neg hY0pos.le, div_eq_mul_inv, inv_inv]
      ring_nf
    have e2 : (X : ℝ) ^ ((1 : ℝ) / 8) * (X : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
      rw [← Real.rpow_add hXpos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    calc Cε * (X : ℝ) ^ ((1 : ℝ) / 8) * (2 * X * ∑ m ∈ TC X Y0, (rho f m : ℝ) / m)
        ≤ Cε * (X : ℝ) ^ ((1 : ℝ) / 8) *
            (2 * X * (KC * ((X : ℝ) / Y0) ^ (-(1 / 4 : ℝ)) * Real.log (Y0 + 1))) := by gcongr
      _ = CC * X * ((X : ℝ) ^ ((1 : ℝ) / 8) * (X : ℝ) ^ (-(1 / 4 : ℝ))) := by
          rw [e1, hCCdef]; ring
      _ ≤ CC * X * 1 := by gcongr
      _ ≤ CC * (X * Real.log X) := by
          have hXX : (X : ℝ) ≤ X * Real.log X := by
            nlinarith [mul_le_mul_of_nonneg_left hlogX hXpos.le]
          exact (le_of_eq (mul_one _)).trans (mul_le_mul_of_nonneg_left hXX hCC)
  have hXlog : 1 ≤ (X : ℝ) * Real.log X := by nlinarith
  calc _ ≤ Cs + (4 ^ D' * 2 * KA * (2 * (X * Real.log X)) +
          2 * KB * 2 ^ (D' + 2) * (2 * (X * Real.log X)) + CC * (X * Real.log X)) := by
        have := hlarge
        linarith
    _ ≤ (Cs + 2 * CAB + CC) * (X * Real.log X) := by
        rw [hCABdef]; nlinarith

end LaneC976

end

/-! Q9: the final statement. -/

noncomputable section
open Polynomial Finset Filter Asymptotics

namespace LaneC976

theorem floor_int_eq_toNat (z : ℤ) : ⌊z⌋₊ = z.toNat := by
  rw [← Int.floor_toNat, Int.floor_int]; rfl

theorem erdos975_bound (f : ℤ[X]) (hf : Irreducible f) (hf_pos : ∀ᶠ n in atTop, 1 ≤ f.eval n) :
    ∃ C : ℝ, ∀ᶠ X : ℕ in atTop,
      ∑ n ∈ range (X + 1), (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) ≤ C * (X * Real.log X) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hf_pos
  have hpos : ∀ n : ℕ, N0.toNat ≤ n → 1 ≤ f.eval (n : ℤ) := fun n hn ↦ hN0 n (by omega)
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hd
  · -- constant polynomial
    obtain ⟨c, hc⟩ : ∃ c, f = C c := ⟨f.coeff 0, eq_C_of_natDegree_eq_zero h0⟩
    refine ⟨#c.toNat.divisors * 2, ?_⟩
    filter_upwards [eventually_ge_atTop 3] with X hX
    have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
    have hlogX : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9; linarith
    simp only [hc, eval_C, Finset.sum_const, card_range, nsmul_eq_mul]
    push_cast
    have hτ : 0 ≤ (#c.toNat.divisors : ℝ) := Nat.cast_nonneg _
    have h1 : (X : ℝ) + 1 ≤ 2 * (X * Real.log X) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hτ]
  · exact main975 f hf hd N0.toNat hpos

end LaneC976

open Filter Asymptotics in
theorem OMA.solution : type_of% @Erdos975.erdos_975.variants.upper_bound := by
  intro f hf hf_pos
  obtain ⟨C, hC⟩ := LaneC976.erdos975_bound f hf hf_pos
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hC
  refine IsBigO.of_bound (max C 0) ?_
  filter_upwards [eventually_ge_atTop ((X0 : ℝ) + 3)] with x hx
  set X := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg X0 : (0 : ℝ) ≤ X0)]
  have hXX0 : X0 ≤ X := Nat.le_floor (by linarith)
  have hXx : (X : ℝ) ≤ x := Nat.floor_le hx0
  have hX3 : (3 : ℝ) ≤ X := by
    have : (X0 : ℝ) + 3 ≤ x := hx
    have h3 : 3 ≤ X := Nat.le_floor (by push_cast; linarith [(Nat.cast_nonneg X0 : (0 : ℝ) ≤ X0)])
    exact_mod_cast h3
  have hsum := hX0 X hXX0
  have hlogX : 0 ≤ Real.log X := Real.log_natCast_nonneg _
  have hlx : Real.log X ≤ Real.log x := Real.log_le_log (by linarith) hXx
  have hS : Erdos975.Erdos975Sum f x =
      ∑ n ∈ range (X + 1), (#(f.eval ((n : ℕ) : ℤ)).toNat.divisors : ℝ) := by
    unfold Erdos975.Erdos975Sum
    rw [show Finset.Iic X = range (X + 1) by ext; simp [Nat.lt_succ_iff]]
    push_cast
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [ArithmeticFunction.sigma_zero_apply, LaneC976.floor_int_eq_toNat]
  have hS0 : 0 ≤ Erdos975.Erdos975Sum f x := by
    rw [hS]; exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg (by
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith); positivity), hS]
  calc _ ≤ C * (X * Real.log X) := hsum
    _ ≤ max C 0 * (X * Real.log X) := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (x * Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact mul_le_mul hXx hlx hlogX hx0
