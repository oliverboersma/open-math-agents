import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1_H3_R1
import Mathlib

-- Step Hilbert17.hilbert_17th_problem.R1.H3.R1.H1 (Polynomial IVT for real closed fields)
-- Credit: @green-notes

/-!
Proves the Intermediate Value Theorem for polynomials over any ordered real closed field
(`Hilbert17.hilbert_17th_problem.R1.H3.R1.H1`) by showing every irreducible polynomial over `R`
has degree at most `2` (via Galois theory and 2-Sylow subgroups on the splitting field of
`(X ^ 2 + 1) * f`), then applying strong induction on polynomial degree.
-/

namespace Hilbert17H3R1H1

open Polynomial

private lemma irreducible_X_sq_add_one {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
  have hno : ∀ r : R, (X ^ 2 + 1 : R[X]).eval r ≠ 0 := by
    intro r
    simp only [eval_add, eval_pow, eval_X, eval_one]
    have : 0 < r ^ 2 + 1 := by positivity
    exact this.ne'
  have hne : (X ^ 2 + 1 : R[X]) ≠ 0 := fun h => hno 0 (by simp [h])
  have hnu : ¬ IsUnit (X ^ 2 + 1 : R[X]) := by
    intro hu
    have hd := natDegree_eq_zero_of_isUnit hu
    omega
  refine ⟨hnu, fun a b hab => ?_⟩
  have ha0 : a ≠ 0 := fun h => hne (by simp [hab, h])
  have hb0 : b ≠ 0 := fun h => hne (by simp [hab, h])
  have hsum : a.natDegree + b.natDegree = 2 := by
    rw [← natDegree_mul ha0 hb0, ← hab, hdeg]
  by_cases ha : a.natDegree = 0
  · left
    obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp ha
    rw [← hceq] at ha0 ⊢
    exact Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using ha0))
  · by_cases hb : b.natDegree = 0
    · right
      obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp hb
      rw [← hceq] at hb0 ⊢
      exact Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hb0))
    · have ha1 : a.natDegree = 1 := by omega
      have hlc : a.coeff 1 ≠ 0 := by
        simpa [leadingCoeff, ha1] using leadingCoeff_ne_zero.mpr ha0
      have ha_eq : a = C (a.coeff 1) * X + C (a.coeff 0) := by
        ext n
        rcases n with _ | _ | n
        · simp
        · simp
        · simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C_succ, mul_ite, mul_one, mul_zero, add_zero]
          simp [coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < n + 2)]
      let r : R := -(a.coeff 0) / a.coeff 1
      have har : a.eval r = 0 := by
        rw [ha_eq]
        simp only [eval_add, eval_mul, eval_C, eval_X, r]
        rw [mul_div_cancel₀ _ hlc]
        ring
      exfalso
      apply hno r
      rw [hab, eval_mul, har, zero_mul]

private lemma isSquare_of_adjoin_i {R L : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] [Field L] [Algebra R L] {i_L : L} (hi : i_L ^ 2 + 1 = 0)
    (z : IntermediateField.adjoin R {i_L}) : IsSquare z := by
  have hred : ∀ p : R[X], ∃ a b : R, aeval i_L p = algebraMap R L a + algebraMap R L b * i_L := by
    intro p
    let q := p % (X ^ 2 + 1)
    have hqdeg : q.natDegree < 2 := by
      have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
      rw [← hdeg2]
      exact natDegree_mod_lt p (by simp [hdeg2])
    have hpq : aeval i_L p = aeval i_L q := by
      have hdiv := EuclideanDomain.div_add_mod p (X ^ 2 + 1)
      conv_lhs => rw [← hdiv]
      simp [q, hi]
    have hq_eq : q = C (q.coeff 0) + C (q.coeff 1) * X := by
      ext n
      rcases n with _ | _ | n
      · simp
      · simp
      · simp only [coeff_add, coeff_C_succ, coeff_C_mul_X, zero_add]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨q.coeff 0, q.coeff 1, ?_⟩
    rw [hpq, hq_eq]
    simp
  obtain ⟨p, s, hzs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := R) (α := i_L) (z : L)).mp z.2
  obtain ⟨a₁, b₁, hp1⟩ := hred p
  obtain ⟨a₂, b₂, hs1⟩ := hred s
  have hz_pair : ∃ a b : R, (z : L) = algebraMap R L a + algebraMap R L b * i_L := by
    by_cases h0 : a₂ = 0 ∧ b₂ = 0
    · refine ⟨0, 0, ?_⟩
      rw [hzs, hs1, h0.1, h0.2]
      simp
    · have hden_pos : 0 < a₂ ^ 2 + b₂ ^ 2 := by
        rcases not_and_or.mp h0 with ha2 | hb2
        · have : 0 < a₂ ^ 2 := sq_pos_of_ne_zero ha2
          nlinarith [sq_nonneg b₂]
        · have : 0 < b₂ ^ 2 := sq_pos_of_ne_zero hb2
          nlinarith [sq_nonneg a₂]
      have hs_ne : aeval i_L s ≠ 0 := by
        intro hsz
        rw [hs1] at hsz
        have hmul : (algebraMap R L a₂ + algebraMap R L b₂ * i_L) *
            (algebraMap R L a₂ - algebraMap R L b₂ * i_L) = algebraMap R L (a₂ ^ 2 + b₂ ^ 2) := by
          simp only [map_add, map_pow]
          linear_combination -(algebraMap R L b₂ ^ 2) * hi
        rw [hsz, zero_mul] at hmul
        have hzero : algebraMap R L (a₂ ^ 2 + b₂ ^ 2) = 0 := hmul.symm
        have : a₂ ^ 2 + b₂ ^ 2 = 0 := (map_eq_zero (algebraMap R L)).mp hzero
        linarith
      let den := a₂ ^ 2 + b₂ ^ 2
      refine ⟨(a₁ * a₂ + b₁ * b₂) / den, (b₁ * a₂ - a₁ * b₂) / den, ?_⟩
      rw [hzs, div_eq_iff hs_ne]
      rw [hp1, hs1]
      have hden_ne : (den : R) ≠ 0 := hden_pos.ne'
      have hmul_eq : algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * a₂ - (b₁ * a₂ - a₁ * b₂) / den * b₂) =
          algebraMap R L a₁ := by
        congr 1
        field_simp [hden_ne]
        ring
      have hmul_eq2 : algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * b₂ + (b₁ * a₂ - a₁ * b₂) / den * a₂) =
          algebraMap R L b₁ := by
        congr 1
        field_simp [hden_ne]
        ring
      calc
        algebraMap R L a₁ + algebraMap R L b₁ * i_L
          = algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * a₂ - (b₁ * a₂ - a₁ * b₂) / den * b₂) +
            algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * b₂ + (b₁ * a₂ - a₁ * b₂) / den * a₂) * i_L := by
              rw [hmul_eq, hmul_eq2]
        _ = (algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den) +
              algebraMap R L ((b₁ * a₂ - a₁ * b₂) / den) * i_L) *
            (algebraMap R L a₂ + algebraMap R L b₂ * i_L) := by
              simp only [map_sub, map_add, map_mul]
              linear_combination -(algebraMap R L ((b₁ * a₂ - a₁ * b₂) / den) * algebraMap R L b₂) * hi
  obtain ⟨a, b, hz_eq⟩ := hz_pair
  have hdd : ∃ d : R, 0 ≤ d ∧ d ^ 2 = a ^ 2 + b ^ 2 := by
    obtain ⟨d, hd⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp (by positivity : 0 ≤ a ^ 2 + b ^ 2)
    rcases le_total 0 d with h0d | hd0
    · exact ⟨d, h0d, by linear_combination -hd⟩
    · exact ⟨-d, neg_nonneg.mpr hd0, by linear_combination -hd⟩
  obtain ⟨d, hd0, hdsq⟩ := hdd
  have hda : a ^ 2 ≤ d ^ 2 := by nlinarith [sq_nonneg b]
  have habs : |a| ≤ d := by
    rw [← abs_of_nonneg hd0]
    exact sq_le_sq.mp hda
  have hda1 : 0 ≤ (d + a) / 2 := by
    have := neg_le_of_abs_le habs
    linarith
  have hda2 : 0 ≤ (d - a) / 2 := by
    have := le_of_abs_le habs
    linarith
  have hu_ex : ∃ u : R, 0 ≤ u ∧ u ^ 2 = (d + a) / 2 := by
    obtain ⟨u, hu⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hda1
    rcases le_total 0 u with h0u | hu0
    · exact ⟨u, h0u, by linear_combination -hu⟩
    · exact ⟨-u, neg_nonneg.mpr hu0, by linear_combination -hu⟩
  have hv_ex : ∃ v : R, 0 ≤ v ∧ v ^ 2 = (d - a) / 2 := by
    obtain ⟨v, hv⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hda2
    rcases le_total 0 v with h0v | hv0
    · exact ⟨v, h0v, by linear_combination -hv⟩
    · exact ⟨-v, neg_nonneg.mpr hv0, by linear_combination -hv⟩
  obtain ⟨u, hu0, husq⟩ := hu_ex
  obtain ⟨v, hv0, hvsq⟩ := hv_ex
  have huv_sq : (2 * u * v) ^ 2 = b ^ 2 := by
    have : 4 * (u ^ 2 * v ^ 2) = d ^ 2 - a ^ 2 := by rw [husq, hvsq]; ring
    nlinarith [hdsq]
  have huv_eq : 2 * u * v = |b| := by
    have h0 : 0 ≤ 2 * u * v := by positivity
    rw [← sq_abs b] at huv_sq
    exact (sq_eq_sq₀ h0 (abs_nonneg b)).mp huv_sq
  let v' : R := if 0 ≤ b then v else -v
  have hv'sq : v' ^ 2 = (d - a) / 2 := by
    by_cases hb : 0 ≤ b <;> simp [v', hb, hvsq]
  have huv' : 2 * u * v' = b := by
    by_cases hb : 0 ≤ b
    · simp only [v', hb, ↓reduceIte]
      rw [huv_eq, abs_of_nonneg hb]
    · simp only [v', hb, ↓reduceIte, mul_neg]
      rw [huv_eq, abs_of_neg (lt_of_not_ge hb), neg_neg]
  let wL : L := algebraMap R L u + algebraMap R L v' * i_L
  have hwL_mem : wL ∈ IntermediateField.adjoin R {i_L} := by
    apply add_mem
    · exact IntermediateField.algebraMap_mem _ u
    · exact mul_mem (IntermediateField.algebraMap_mem _ v') (IntermediateField.mem_adjoin_simple_self R i_L)
  refine ⟨⟨wL, hwL_mem⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, wL]
  calc
    (z : L) = algebraMap R L a + algebraMap R L b * i_L := hz_eq
    _ = algebraMap R L (u ^ 2 - v' ^ 2) + algebraMap R L (2 * u * v') * i_L := by
        rw [husq, hv'sq, huv']
        have : (d + a) / 2 - (d - a) / 2 = a := by ring
        rw [this]
    _ = (algebraMap R L u + algebraMap R L v' * i_L) * (algebraMap R L u + algebraMap R L v' * i_L) := by
        simp only [map_sub, map_pow, map_mul, map_ofNat]
        linear_combination -(algebraMap R L v' ^ 2) * hi

private lemma natDegree_le_two_of_irreducible {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {f : R[X]} (hf : Irreducible f) :
    f.natDegree ≤ 2 := by
  let g : R[X] := (X ^ 2 + 1) * f
  have hf0 : f ≠ 0 := hf.ne_zero
  have hg0 : g ≠ 0 := mul_ne_zero (irreducible_X_sq_add_one (R := R)).ne_zero hf0
  let L := g.SplittingField
  have : FiniteDimensional R L := inferInstance
  have : Normal R L := inferInstance
  have : Algebra.IsSeparable R L := inferInstance
  have : IsGalois R L := ⟨⟩
  let G := L ≃ₐ[R] L
  have : Finite G := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPGroup : IsPGroup 2 G := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
    let E := IntermediateField.fixedField (S : Subgroup G)
    have hE_fin : Module.finrank R E = (S : Subgroup G).index := by
      have h1 : Module.finrank R E * Module.finrank E L = Module.finrank R L :=
        Module.finrank_mul_finrank R E L
      have h2 : Module.finrank E L = Nat.card (S : Subgroup G) :=
        IntermediateField.finrank_fixedField_eq_card (S : Subgroup G)
      have h3 : Module.finrank R L = Nat.card G :=
        (IsGalois.card_aut_eq_finrank R L).symm
      have h4 : (S : Subgroup G).index * Nat.card (S : Subgroup G) = Nat.card G :=
        Subgroup.index_mul_card (S : Subgroup G)
      have hpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
      nlinarith
    have hodd : Odd (Module.finrank R E) := by
      rw [hE_fin, Nat.odd_iff]
      have hndvd : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
      omega
    obtain ⟨α, hα⟩ := Field.exists_primitive_element R E
    have hmin_deg : (minpoly R α).natDegree = Module.finrank R E := by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite R α), hα, IntermediateField.finrank_top']
    have hodd_min : Odd (minpoly R α).natDegree := hmin_deg ▸ hodd
    obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd_min
    have hirr : Irreducible (minpoly R α) := minpoly.irreducible (IsIntegral.of_finite R α)
    have hdeg1 : (minpoly R α).natDegree = 1 := by
      obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      rcases hirr.isUnit_or_isUnit hs with hunit | hunit
      · exfalso
        have := natDegree_eq_zero_of_isUnit hunit
        rw [natDegree_X_sub_C] at this
        omega
      · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
          natDegree_eq_zero_of_isUnit hunit]
    have hidx1 : (S : Subgroup G).index = 1 := by omega
    have hStop : (S : Subgroup G) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hG_eq : IsPGroup 2 (⊤ : Subgroup G) := hStop ▸ S.isPGroup'
    exact hG_eq.of_equiv Subgroup.topEquiv
  have hsplits_g : Splits (g.map (algebraMap R L)) := Polynomial.SplittingField.splits g
  have hsplits_i : Splits ((X ^ 2 + 1 : R[X]).map (algebraMap R L)) :=
    hsplits_g.of_dvd (Polynomial.map_ne_zero hg0) (Polynomial.map_dvd _ (dvd_mul_right _ _))
  obtain ⟨i_L, hi_L⟩ := hsplits_i.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (irreducible_X_sq_add_one (R := R)).ne_zero]
    have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
    simp [this])
  have hi_sq : i_L ^ 2 + 1 = 0 := by
    simpa [Polynomial.eval_map] using hi_L
  let K₀ : IntermediateField R L := IntermediateField.adjoin R {i_L}
  have : FiniteDimensional K₀ L := FiniteDimensional.right R K₀ L
  have hfinK0L_one : Module.finrank K₀ L = 1 := by
    obtain ⟨k, hk⟩ := hPGroup.exists_card_eq
    have hdvd_pow : Module.finrank K₀ L ∣ 2 ^ k := by
      rw [← hk, IsGalois.card_aut_eq_finrank R L, ← Module.finrank_mul_finrank R K₀ L]
      exact dvd_mul_left _ _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_pow
    by_cases hm0 : m = 0
    · rw [hm, hm0, pow_zero]
    · exfalso
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      let G₀ := L ≃ₐ[K₀] L
      have : Finite G₀ := inferInstance
      have hG₀_card : Nat.card G₀ = 2 ^ m := by
        rw [IsGalois.card_aut_eq_finrank K₀ L, hm]
      have hdvd_sub : 2 ^ (m - 1) ∣ Nat.card G₀ := by
        rw [hG₀_card]
        exact Nat.pow_dvd_pow 2 (Nat.sub_le m 1)
      obtain ⟨M, hMcard⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd_sub
      let K₁ : IntermediateField K₀ L := IntermediateField.fixedField M
      have hfinK1 : Module.finrank K₁ L = 2 ^ (m - 1) := by
        rw [IntermediateField.finrank_fixedField_eq_card]
        exact hMcard
      have hfin01 : Module.finrank K₀ K₁ = 2 := by
        have hmul : Module.finrank K₀ K₁ * Module.finrank K₁ L = Module.finrank K₀ L :=
          Module.finrank_mul_finrank K₀ K₁ L
        rw [hfinK1, hm] at hmul
        have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
        have hpos : 0 < 2 ^ (m - 1) := by positivity
        nlinarith
      have hfin_dim : FiniteDimensional K₀ K₁ :=
        Module.finite_of_finrank_pos (by omega : 0 < Module.finrank K₀ K₁)
      have hne_bot : (⊥ : IntermediateField K₀ K₁) ≠ ⊤ := by
        intro hbot
        have := congrArg (fun E : IntermediateField K₀ K₁ => Module.finrank K₀ E) hbot
        simp only [IntermediateField.finrank_bot, IntermediateField.finrank_top', hfin01] at this
        omega
      have hmem_ex : ∃ β : K₁, β ∉ (⊥ : IntermediateField K₀ K₁) := by
        by_contra hall
        push Not at hall
        apply hne_bot
        ext x
        simp [hall x]
      obtain ⟨β, hβ⟩ := hmem_ex
      have hβ_int : IsIntegral K₀ β := IsIntegral.of_finite K₀ β
      have hdvd2 : (minpoly K₀ β).natDegree ∣ 2 := by
        rw [← hfin01]
        exact minpoly.degree_dvd hβ_int
      have hdeg_ne1 : (minpoly K₀ β).natDegree ≠ 1 := by
        intro h1
        apply hβ
        have htop1 : Module.finrank K₀ (IntermediateField.adjoin K₀ {β}) = 1 := by
          rw [IntermediateField.adjoin.finrank hβ_int, h1]
        have hbot1 : IntermediateField.adjoin K₀ {β} = ⊥ :=
          IntermediateField.finrank_eq_one_iff.mp htop1
        rw [← hbot1]
        exact IntermediateField.mem_adjoin_simple_self K₀ β
      have hdeg2 : (minpoly K₀ β).natDegree = 2 := by
        have hpos : 0 < (minpoly K₀ β).natDegree := minpoly.natDegree_pos hβ_int
        have hle2 : (minpoly K₀ β).natDegree ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
        omega
      let q := minpoly K₀ β
      have hq_monic : q.Monic := minpoly.monic hβ_int
      have hq_deg2 : q.natDegree = 2 := hdeg2
      have hq2 : q.coeff 2 = 1 := by simpa [q, hdeg2] using hq_monic.coeff_natDegree
      have hq_eq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
        ext n
        rcases n with _ | _ | _ | n
        · simp
        · simp
        · simp [hq2]
        · simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C_succ,
            mul_ite, mul_one, mul_zero, add_zero]
          have h2 : n + 3 ≠ 2 := by omega
          simp [h2, coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n + 3)]
      let disc : K₀ := (q.coeff 1) ^ 2 - 4 * q.coeff 0
      obtain ⟨d, hd⟩ := isSquare_of_adjoin_i hi_sq disc
      have hd_sq : d ^ 2 = disc := by linear_combination -hd
      let r : K₀ := (-(q.coeff 1) + d) / 2
      have hr_root : q.IsRoot r := by
        rw [Polynomial.IsRoot]
        have h2 : (2 : K₀) ≠ 0 := two_ne_zero
        have h4 : 4 * q.eval r = (2 * r + q.coeff 1) ^ 2 - ((q.coeff 1) ^ 2 - 4 * q.coeff 0) := by
          conv_lhs => rw [hq_eq]
          simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
          ring
        have hr2 : 2 * r + q.coeff 1 = d := by
          dsimp [r]
          rw [mul_div_cancel₀ _ h2]
          ring
        have h40 : 4 * q.eval r = 0 := by rw [h4, hr2]; dsimp [disc] at hd_sq; rw [hd_sq, sub_self]
        exact (mul_eq_zero.mp h40).resolve_left (by norm_num)
      have hirr_q : Irreducible q := minpoly.irreducible hβ_int
      have hq_deg1 : q.natDegree = 1 := by
        obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
        rcases hirr_q.isUnit_or_isUnit hs with hunit | hunit
        · exfalso
          have := natDegree_eq_zero_of_isUnit hunit
          rw [natDegree_X_sub_C] at this
          omega
        · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
            natDegree_eq_zero_of_isUnit hunit]
      omega
  have hfinK0 : Module.finrank R K₀ ≤ 2 := by
    have hi_int : IsIntegral R i_L := ⟨X ^ 2 + 1, by monicity!, by simp [hi_sq]⟩
    rw [IntermediateField.adjoin.finrank hi_int]
    have hdvd_i : minpoly R i_L ∣ (X ^ 2 + 1 : R[X]) := minpoly.dvd R i_L (by simp [hi_sq])
    have hle_i := Polynomial.natDegree_le_of_dvd hdvd_i (irreducible_X_sq_add_one (R := R)).ne_zero
    exact hle_i.trans (by compute_degree!)
  have hfinL : Module.finrank R L ≤ 2 := by
    rw [← Module.finrank_mul_finrank R K₀ L, hfinK0L_one, mul_one]
    exact hfinK0
  have hsplits_f : Splits (f.map (algebraMap R L)) :=
    hsplits_g.of_dvd (Polynomial.map_ne_zero hg0) (Polynomial.map_dvd _ (dvd_mul_left _ _))
  have hdvd_fin : f.natDegree ∣ Module.finrank R L := hf.natDegree_dvd_finrank hsplits_f
  have hpos_fin : 0 < Module.finrank R L := Module.finrank_pos
  exact (Nat.le_of_dvd hpos_fin hdvd_fin).trans hfinL

end Hilbert17H3R1H1

open Polynomial in
theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H1 := by
  intro R _ _ _ _ p a b hab ha hb
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h d ih =>
    by_cases hdeg0 : p.natDegree = 0
    · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
      simp only [eval_C] at ha hb
      linarith
    · by_cases hirr : Irreducible p
      · have hd2 : p.natDegree ≤ 2 := Hilbert17H3R1H1.natDegree_le_two_of_irreducible hirr
        have hcases : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
        rcases hcases with h1 | h2
        · let u := p.coeff 1
          let v := p.coeff 0
          have hu : u ≠ 0 := by
            intro h
            have hlc : p.leadingCoeff = 0 := by simpa [u, leadingCoeff, h1] using h
            exact leadingCoeff_ne_zero.mpr hirr.ne_zero hlc
          have hp_eq : p = C u * X + C v := by
            ext n
            rcases n with _ | _ | n
            · simp [v]
            · simp [u]
            · simp only [coeff_add, coeff_C_mul_X, coeff_C_succ, add_zero]
              split_ifs with h
              · omega
              · exact coeff_eq_zero_of_natDegree_lt (by omega)
          have hpa : u * a + v < 0 := by simpa [hp_eq] using ha
          have hpb : 0 < u * b + v := by simpa [hp_eq] using hb
          have hu_pos : 0 < u := by nlinarith
          refine ⟨-v / u, ?_, ?_, ?_⟩
          · rw [lt_div_iff₀ hu_pos]; linarith
          · rw [div_lt_iff₀ hu_pos]; linarith
          · simp [hp_eq, mul_div_cancel₀ _ hu]
        · let u := p.coeff 2
          let v := p.coeff 1
          let w := p.coeff 0
          have hu : u ≠ 0 := by
            intro h
            have hlc : p.leadingCoeff = 0 := by simpa [u, leadingCoeff, h2] using h
            exact leadingCoeff_ne_zero.mpr hirr.ne_zero hlc
          have hp_eq : p = C u * X ^ 2 + C v * X + C w := by
            ext n
            rcases n with _ | _ | _ | n
            · simp [w]
            · simp [v]
            · simp [u]
            · simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, mul_ite, mul_one, mul_zero,
                coeff_C_succ]
              have h2 : n + 3 ≠ 2 := by omega
              simp [h2, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n + 3)]
          have hdisc_neg : v ^ 2 - 4 * u * w < 0 := by
            by_contra hdisc
            have hdisc_nn : 0 ≤ v ^ 2 - 4 * u * w := le_of_not_gt hdisc
            obtain ⟨disc_sqrt, hd⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hdisc_nn
            have hdsq : disc_sqrt ^ 2 = v ^ 2 - 4 * u * w := by linear_combination -hd
            let r : R := (-v + disc_sqrt) / (2 * u)
            have hr_root : p.IsRoot r := by
              rw [Polynomial.IsRoot]
              have h2u : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu
              have h4 : 4 * u * p.eval r = (2 * u * r + v) ^ 2 - (v ^ 2 - 4 * u * w) := by
                rw [hp_eq]
                simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
                ring
              have hr2 : 2 * u * r + v = disc_sqrt := by
                dsimp [r]
                rw [mul_div_cancel₀ _ h2u]
                ring
              have h40 : 4 * u * p.eval r = 0 := by rw [h4, hr2, hdsq, sub_self]
              exact (mul_eq_zero.mp h40).resolve_left (mul_ne_zero (by norm_num) hu)
            have : p.natDegree = 1 := by
              obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
              rcases hirr.isUnit_or_isUnit hs with hunit | hunit
              · exfalso
                have := natDegree_eq_zero_of_isUnit hunit
                rw [natDegree_X_sub_C] at this
                omega
              · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
                  natDegree_eq_zero_of_isUnit hunit]
            omega
          have h4ua : 0 < 4 * u * p.eval a := by
            rw [hp_eq]
            simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
            nlinarith [sq_nonneg (2 * u * a + v)]
          have h4ub : 0 < 4 * u * p.eval b := by
            rw [hp_eq]
            simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
            nlinarith [sq_nonneg (2 * u * b + v)]
          nlinarith
      · have hp0 : p ≠ 0 := by intro h; simp [h] at ha
        have hpnu : ¬ IsUnit p := fun hu => hdeg0 (natDegree_eq_zero_of_isUnit hu)
        rw [irreducible_iff] at hirr
        push Not at hirr
        obtain ⟨q, r, hpqr, hqnu, hrnu⟩ := hirr hpnu
        have hq0 : q ≠ 0 := fun h => hp0 (by simp [hpqr, h])
        have hr0 : r ≠ 0 := fun h => hp0 (by simp [hpqr, h])
        have hqdeg : 0 < q.natDegree := by
          by_contra h0
          obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp (by omega : q.natDegree = 0)
          rw [← hceq] at hqnu hq0
          exact hqnu (Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hq0)))
        have hrdeg : 0 < r.natDegree := by
          by_contra h0
          obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp (by omega : r.natDegree = 0)
          rw [← hceq] at hrnu hr0
          exact hrnu (Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hr0)))
        have hsum : q.natDegree + r.natDegree = d := by
          rw [← natDegree_mul hq0 hr0, ← hpqr, hn]
        have hqa : q.eval a ≠ 0 := fun h => by
          have : p.eval a = 0 := by rw [hpqr, eval_mul, h, zero_mul]
          linarith
        have hqb : q.eval b ≠ 0 := fun h => by
          have : p.eval b = 0 := by rw [hpqr, eval_mul, h, zero_mul]
          linarith
        have hra : r.eval a ≠ 0 := fun h => by
          have : p.eval a = 0 := by rw [hpqr, eval_mul, h, mul_zero]
          linarith
        have hrb : r.eval b ≠ 0 := fun h => by
          have : p.eval b = 0 := by rw [hpqr, eval_mul, h, mul_zero]
          linarith
        have hpa_mul : q.eval a * r.eval a < 0 := by simpa [hpqr] using ha
        have hpb_mul : 0 < q.eval b * r.eval b := by simpa [hpqr] using hb
        rcases lt_or_gt_of_ne hqa with hqa_lt | hqa_gt
        · rcases lt_or_gt_of_ne hqb with hqb_lt | hqb_gt
          · have hra_gt : 0 < r.eval a := by nlinarith
            have hrb_lt : r.eval b < 0 := by nlinarith
            obtain ⟨c, hac, hcb, hrc⟩ := ih r.natDegree (by omega) (-r) (by simp [hra_gt]) (by simp [hrb_lt]) (natDegree_neg r)
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, show r.eval c = 0 by simpa using hrc, mul_zero]⟩
          · obtain ⟨c, hac, hcb, hqc⟩ := ih q.natDegree (by omega) q hqa_lt hqb_gt rfl
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, hqc, zero_mul]⟩
        · rcases lt_or_gt_of_ne hqb with hqb_lt | hqb_gt
          · obtain ⟨c, hac, hcb, hqc⟩ := ih q.natDegree (by omega) (-q) (by simp [hqa_gt]) (by simp [hqb_lt]) (natDegree_neg q)
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, show q.eval c = 0 by simpa using hqc, zero_mul]⟩
          · have hra_lt : r.eval a < 0 := by nlinarith
            have hrb_gt : 0 < r.eval b := by nlinarith
            obtain ⟨c, hac, hcb, hrc⟩ := ih r.natDegree (by omega) r hra_lt hrb_gt rfl
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, hrc, mul_zero]⟩
