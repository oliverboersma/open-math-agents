import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1

-- Step Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1
-- Credit: @JamesSlash
-- The ring of integers of Q(sqrt(-s)) for squarefree s = 3 mod 4 is Z[(1+sqrt(-s))/2], of discriminant -s.
-- Ported (Apache-2.0) from CBirkbeck/AINTLIB, BernoulliRegular/ImaginaryQuadratic/Foundations.lean
-- (discr_Kminus_natAbs_eq, stated there for primes p = 3 mod 4), generalized here to squarefree s.

open Polynomial NumberField

namespace Disc338

variable (s : ℕ) [Fact (Irreducible (X ^ 2 + C (s : ℚ)))]

theorem poly_monic : (X ^ 2 + C (s : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)

theorem poly_natDegree : (X ^ 2 + C (s : ℚ)).natDegree = 2 := natDegree_X_pow_add_C

abbrev Kq : Type := AdjoinRoot (X ^ 2 + C (s : ℚ))

theorem finrank_K : Module.finrank ℚ (Kq s) = 2 := by
  rw [(AdjoinRoot.powerBasis (poly_monic s).ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    poly_natDegree]

noncomputable abbrev rt : Kq s := AdjoinRoot.root (X ^ 2 + C (s : ℚ))

theorem rt_sq : rt s ^ 2 = -(s : Kq s) := by
  have h1 : (X ^ 2 + C (s : ℚ)).eval₂ (AdjoinRoot.of (X ^ 2 + C (s : ℚ))) (rt s) = 0 :=
    AdjoinRoot.eval₂_root _
  rw [eval₂_add, eval₂_X_pow, eval₂_C] at h1
  have h2 : (AdjoinRoot.of (X ^ 2 + C (s : ℚ))) (s : ℚ) = (s : Kq s) := map_natCast _ s
  linear_combination h1 - h2

noncomputable def al : Kq s := (1 + rt s) / 2

theorem two_al_sub_one : 2 * al s - 1 = rt s := by
  unfold al
  rw [mul_div_cancel₀ _ two_ne_zero]
  ring

theorem al_rel (h3 : s % 4 = 3) : al s ^ 2 - al s + (((s + 1) / 4 : ℕ) : Kq s) = 0 := by
  have h1 : (2 * al s - 1) ^ 2 = rt s ^ 2 := by rw [two_al_sub_one]
  rw [rt_sq] at h1
  have hc : ((((s + 1) / 4 : ℕ) : Kq s)) * 4 = (s : Kq s) + 1 := by
    have : ((s + 1) / 4) * 4 = s + 1 := Nat.div_mul_cancel (by omega)
    exact_mod_cast this
  have h4 : (4 : Kq s) ≠ 0 := by
    have : (4 : ℚ) ≠ 0 := by norm_num
    exact_mod_cast this
  have key : 4 * (al s ^ 2 - al s + (((s + 1) / 4 : ℕ) : Kq s)) = 0 := by
    linear_combination h1 + hc
  exact (mul_eq_zero.mp key).resolve_left h4

theorem al_int (h3 : s % 4 = 3) : IsIntegral ℤ (al s) := by
  refine ⟨X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℤ), ?_, ?_⟩
  · have heq : (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℤ) : ℤ[X]) =
        X ^ 2 - (X - C (((s + 1) / 4 : ℕ) : ℤ)) := by ring
    rw [heq]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; decide)
  · change aeval (al s) (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℤ)) = 0
    rw [map_add, map_sub, map_pow, aeval_X, aeval_C]
    have h := al_rel s h3
    convert h using 3
    rw [map_natCast]

theorem al_int_rat (h3 : s % 4 = 3) : IsIntegral ℚ (al s) := (al_int s h3).tower_top

theorem adjoin_al : Algebra.adjoin ℚ ({al s} : Set (Kq s)) = ⊤ := by
  apply top_le_iff.mp
  calc (⊤ : Subalgebra ℚ (Kq s))
      = Algebra.adjoin ℚ ({rt s} : Set (Kq s)) := AdjoinRoot.adjoinRoot_eq_top.symm
    _ ≤ Algebra.adjoin ℚ ({al s} : Set (Kq s)) := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        have hα := Algebra.self_mem_adjoin_singleton ℚ (al s)
        rw [show rt s = 2 * al s - 1 from (two_al_sub_one s).symm]
        exact sub_mem (mul_mem (Subalgebra.natCast_mem _ 2) hα) (one_mem _)

noncomputable def apb (h3 : s % 4 = 3) : PowerBasis ℚ (Kq s) :=
  PowerBasis.ofAdjoinEqTop (al_int_rat s h3) (adjoin_al s)

theorem apb_gen (h3 : s % 4 = 3) : (apb s h3).gen = al s := rfl

theorem apb_dim (h3 : s % 4 = 3) : (apb s h3).dim = 2 := by
  have h1 : Module.finrank ℚ (Kq s) = (apb s h3).dim := (apb s h3).finrank
  rw [finrank_K] at h1
  exact h1.symm

theorem al_minpoly (h3 : s % 4 = 3) :
    minpoly ℚ (al s) = X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) := by
  have hq_eq : (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) : ℚ[X]) =
      X ^ 2 - (X - C (((s + 1) / 4 : ℕ) : ℚ)) := by ring
  have hq_monic : (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) : ℚ[X]).Monic := by
    rw [hq_eq]; exact monic_X_pow_sub (by rw [degree_X_sub_C]; decide)
  have hq_aeval : aeval (al s) (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) : ℚ[X]) = 0 := by
    rw [map_add, map_sub, map_pow, aeval_X, aeval_C]
    have h := al_rel s h3
    simpa using h
  have hq_natDeg : (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) : ℚ[X]).natDegree = 2 := by
    rw [hq_eq, natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow 2
    · rw [natDegree_X_pow]
      exact lt_of_le_of_lt (natDegree_X_sub_C_le _) (by decide)
  have hmp_natDeg : (minpoly ℚ (al s)).natDegree = 2 := by
    have h1 : (apb s h3).dim = (minpoly ℚ (al s)).natDegree :=
      PowerBasis.ofAdjoinEqTop_dim _ _
    rw [apb_dim] at h1
    exact h1.symm
  have hmp_monic : (minpoly ℚ (al s)).Monic := minpoly.monic (al_int_rat s h3)
  obtain ⟨c, hc⟩ := minpoly.dvd ℚ (al s) hq_aeval
  have hc_monic : c.Monic := Monic.of_mul_monic_left hmp_monic (hc ▸ hq_monic)
  have hsum : (minpoly ℚ (al s)).natDegree + c.natDegree = 2 := by
    rw [← natDegree_mul hmp_monic.ne_zero hc_monic.ne_zero, ← hc, hq_natDeg]
  have hc_deg : c.natDegree = 0 := by omega
  have hc_eq : c = 1 := hc_monic.natDegree_eq_zero.mp hc_deg
  rw [hc, hc_eq, mul_one]

theorem rt_minpoly : minpoly ℚ (rt s) = X ^ 2 + C (s : ℚ) := by
  have h := AdjoinRoot.minpoly_root (f := X ^ 2 + C (s : ℚ)) (poly_monic s).ne_zero
  rw [(poly_monic s).leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

theorem norm_rt : Algebra.norm ℚ (rt s) = (s : ℚ) := by
  have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (AdjoinRoot.powerBasis (poly_monic s).ne_zero)
  have h2 := AdjoinRoot.minpoly_root (f := X ^ 2 + C (s : ℚ)) (poly_monic s).ne_zero
  rw [(poly_monic s).leadingCoeff, inv_one, C_1, mul_one] at h2
  rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim, poly_natDegree] at h1
  erw [h2] at h1
  have h3 : ((-1 : ℚ) ^ 2 * (X ^ 2 + C (s : ℚ)).coeff 0) = (s : ℚ) := by
    simp [coeff_add, coeff_X_pow]
  exact h1.trans h3

theorem discr_apb (h3 : s % 4 = 3) : Algebra.discr ℚ (apb s h3).basis = -(s : ℚ) := by
  rw [Algebra.discr_powerBasis_eq_norm ℚ (apb s h3), finrank_K]
  have hmp : minpoly ℚ (apb s h3).gen = X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) := by
    rw [apb_gen]; exact al_minpoly s h3
  rw [hmp]
  have hderiv : derivative (X ^ 2 - X + C (((s + 1) / 4 : ℕ) : ℚ) : ℚ[X]) = 2 * X - 1 := by
    simp [derivative_add, derivative_sub, derivative_X]
    ring
  rw [hderiv, map_sub, map_mul, map_ofNat, aeval_X, map_one, apb_gen,
    two_al_sub_one, norm_rt]
  norm_num

theorem discr_K (hsq : Squarefree s) (h3 : s % 4 = 3) :
    NumberField.discr (Kq s) = -(s : ℤ) := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 (Kq s))) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 (Kq s)),
      NumberField.RingOfIntegers.rank, finrank_K]
  let pb := apb s h3
  have hdim : pb.dim = 2 := apb_dim s h3
  let e : Fin 2 ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 (Kq s)) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let pbBas : Module.Basis (Fin 2) ℚ (Kq s) := pb.basis.reindex (finCongr hdim)
  let iB : Module.Basis (Fin 2) ℚ (Kq s) := (NumberField.integralBasis (Kq s)).reindex e.symm
  have h_pbBas_disc : Algebra.discr ℚ pbBas = -(s : ℚ) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
    exact discr_apb s h3
  have h_iB_disc : Algebra.discr ℚ iB = (NumberField.discr (Kq s) : ℚ) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex, ← NumberField.coe_discr]
  have h_pbBas_int : ∀ j : Fin 2, IsIntegral ℤ (pbBas j) := fun j ↦ by
    have : pbBas j = pb.basis ((finCongr hdim).symm j) := by simp [pbBas]
    rw [this, pb.basis_eq_pow]
    exact (al_int s h3).pow _
  let pbLift : Fin 2 → 𝓞 (Kq s) := fun j ↦ ⟨pbBas j, h_pbBas_int j⟩
  let P_int : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦
    (NumberField.RingOfIntegers.basis (Kq s)).repr (pbLift j) (e i)
  have h_toMatrix_eq : iB.toMatrix pbBas = P_int.map (algebraMap ℤ ℚ) := by
    ext i j
    change iB.repr (pbBas j) i = _
    rw [show iB = (NumberField.integralBasis (Kq s)).reindex e.symm from rfl,
      Module.Basis.repr_reindex_apply, Equiv.symm_symm]
    have h : (pbBas j : Kq s) = (algebraMap (𝓞 (Kq s)) (Kq s)) (pbLift j) := rfl
    rw [h, NumberField.integralBasis_repr_apply]
    rfl
  have h_vecMul : Matrix.vecMul (iB : Fin 2 → Kq s)
      ((P_int.map (algebraMap ℤ ℚ)).map (algebraMap ℚ (Kq s))) =
      (pbBas : Fin 2 → Kq s) := by
    funext j
    change ∑ i, (iB i : Kq s) * (algebraMap ℚ (Kq s)) ((P_int.map (algebraMap ℤ ℚ)) i j) =
      pbBas j
    have h_entry : ∀ i, (P_int.map (algebraMap ℤ ℚ)) i j = iB.repr (pbBas j) i := by
      intro i
      have := congrFun (congrFun h_toMatrix_eq.symm i) j
      change _ = iB.toMatrix pbBas i j
      exact this
    conv_lhs => rw [show (fun i ↦ (iB i : Kq s) *
      (algebraMap ℚ (Kq s)) ((P_int.map (algebraMap ℤ ℚ)) i j)) =
      (fun i ↦ (iB i : Kq s) * (algebraMap ℚ (Kq s)) (iB.repr (pbBas j) i)) from by
      funext i; rw [h_entry]]
    conv_rhs => rw [← iB.sum_repr (pbBas j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, mul_comm]
    all_goals rfl
  have h_discr_eq : Algebra.discr ℚ pbBas =
      (P_int.map (algebraMap ℤ ℚ)).det ^ 2 * Algebra.discr ℚ iB := by
    rw [← h_vecMul]
    exact Algebra.discr_of_matrix_vecMul _ _
  have h_det_map : (P_int.map (algebraMap ℤ ℚ)).det = (P_int.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) P_int
    change _ = (Int.castRingHom ℚ) P_int.det
    rw [this]
    rfl
  rw [h_pbBas_disc, h_iB_disc, h_det_map] at h_discr_eq
  have h_cast_eq : -(s : ℤ) = P_int.det ^ 2 * NumberField.discr (Kq s) := by
    exact_mod_cast h_discr_eq
  have h_abs : P_int.det.natAbs ^ 2 * (NumberField.discr (Kq s)).natAbs = s := by
    have h_prod_na : (P_int.det ^ 2 * NumberField.discr (Kq s)).natAbs = s := by
      rw [← h_cast_eq]; simp
    rw [Int.natAbs_mul, Int.natAbs_pow] at h_prod_na
    exact h_prod_na
  have h_unit : IsUnit P_int.det.natAbs := hsq _ ⟨(NumberField.discr (Kq s)).natAbs, by
    rw [← sq]; exact h_abs.symm⟩
  have h1 : P_int.det.natAbs = 1 := Nat.isUnit_iff.mp h_unit
  have h2 : P_int.det ^ 2 = 1 := by
    rw [← Int.natAbs_sq, h1]; norm_num
  rw [h2, one_mul] at h_cast_eq
  exact h_cast_eq.symm

end Disc338

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro s hs hsq hm
  letI : Fact (Irreducible (X ^ 2 + C (s : ℚ))) := ⟨OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.quad_irred hs⟩
  exact Disc338.discr_K s hsq (by omega)
