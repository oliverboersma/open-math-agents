import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Prime-ideal Dirichlet sums from the Dedekind zeta pole and Euler product.
Adapted from Chris Birkbeck, Riccardo Brasca and the contributors to
CBirkbeck/chebotarev-density, revision
a00054a0e6bbc394b0e81de750db0cd2efc8bd88, under Apache-2.0.
The Euler product originally comes from flt-regular-bernoulli.
The comparison of rational reduction counts is independent of that source. -/
noncomputable section

open Filter Topology

theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero

theorem tendsto_ratio_one_of_div_atTop_pm_bounded
    {l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop)
    (h_le : ∃ C : ℝ, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in l, g s - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

theorem tendsto_ratio_one_of_log_pm_bounded (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
end
noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace Chebotarev

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}

noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n ↦ ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      lia
    exact_mod_cast Nat.card_congr hequiv

lemma sum_idealNormMultiplicity_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
    rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h ↦ h.2, fun h ↦
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_card_bridge : ∀ n : ℕ,
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
      Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
    fun n ↦ Nat.card_congr
      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
      tendsto_natCast_atTop_atTop).congr' ?_)
  filter_upwards with n
  simp only [Function.comp_apply, Real.rpow_one]
  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
  push_cast
  rfl

lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
      (sum_idealNormMultiplicity_isBigO L) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
      (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

private noncomputable def insertPiEquiv {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ) :=
  ((Finset.subtypeInsertEquivOption ha).arrowCongr (Equiv.refl ℕ)).trans Equiv.piOptionEquivProd

@[simp] private lemma insertPiEquiv_fst {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩ := rfl

@[simp] private lemma insertPiEquiv_snd {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) (i : {i // i ∈ s}) :
    (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := rfl

private lemma prodInsertAttach {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    ∏ i ∈ (insert a s).attach, g i.1 ^ e i =
      g a ^ (insertPiEquiv a s ha e).1 *
        ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i := by
  rw [insertPiEquiv_fst]
  conv_rhs => rw [show (∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i)
    = ∏ i ∈ s.attach, g i.1 ^ e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ from
    Finset.prod_congr rfl fun i _ ↦ by rw [insertPiEquiv_snd]]
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · exact fun x _ y _ h ↦ Subtype.ext (Subtype.mk.inj h)
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using ha

private lemma finsetGeometricProd_summable_and_hasSum {ι : Type*} (g : ι → ℂ)
    (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) :
    (Summable fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧
      HasSum (fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i)
        (∏ i ∈ s, (1 - g i)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ‖∏ i ∈ Finset.attach ∅, g i.1 ^ e i‖)
          = fun _ ↦ (1 : ℝ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact (hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℝ))).summable
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ∏ i ∈ Finset.attach ∅, g i.1 ^ e i)
          = fun _ ↦ (1 : ℂ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℂ))
  | insert a s ha ih =>
    obtain ⟨ihsum, ihhas⟩ := ih
    rw [Finset.prod_insert ha]
    have hgeo : HasSum (fun n : ℕ ↦ g a ^ n) (1 - g a)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hg a)
    have hgeosum : Summable (fun n : ℕ ↦ ‖g a ^ n‖) := by
      simp_rw [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hg a)
    have hprodsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) :=
      summable_mul_of_summable_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) :=
      Summable.mul_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHhas : HasSum (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ((1 - g a)⁻¹ * ∏ i ∈ s, (1 - g i)⁻¹) :=
      HasSum.mul (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeo ihhas hprodsum
    refine ⟨?_, ?_⟩
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ‖∏ i ∈ (insert a s).attach, g i.1 ^ e i‖)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).summable_iff.mpr hHsum
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ∏ i ∈ (insert a s).attach, g i.1 ^ e i)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).hasSum_iff.mpr hHhas

private lemma prod_natCast_cpow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ℂ) :
    (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

lemma norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h2 : 2 ≤ Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos (by lia), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2.trans_lt' one_lt_two) (by linarith)

theorem prod_eulerFactor_eq_tsum_exponentVector {s : ℂ} (hs : 1 < s.re)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    (∏ 𝔭 ∈ S, (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) =
      ∑' e : S →₀ ℕ, ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := norm_absNorm_cpow_neg_lt_one L hs
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hrw : ∀ e : S → ℕ,
      (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭) =
        ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := fun e ↦
    Finset.prod_congr rfl fun 𝔭 _ ↦ by
      rw [← Complex.cpow_nat_mul]
      ring_nf
  rw [← hHS.tsum_eq, ← (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).tsum_eq
    (fun e : S → ℕ ↦ ∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)]
  refine tsum_congr fun e ↦ ?_
  simp only [Finsupp.equivFunOnFinite_apply]
  rw [hrw]

theorem absNorm_prod_pow_of_primeIdeal
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) =
      ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭 := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ map_pow Ideal.absNorm 𝔭.1.1 (e 𝔭)

theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow {s : ℂ}
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    (∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s)) =
      (Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) : ℂ) ^ (-s) := by
  have hinner : ∀ 𝔭 ∈ S.attach,
      (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) =
        ((Ideal.absNorm 𝔭.1.1 ^ e 𝔭 : ℕ) : ℂ) ^ (-s) := fun 𝔭 _ ↦ by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    ring_nf
  rw [Finset.prod_congr rfl hinner, prod_natCast_cpow, absNorm_prod_pow_of_primeIdeal]

private instance instFiniteAbsNormFiber (n : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

private lemma tsum_absNormFiber {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) :
    (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}, g (Ideal.absNorm y.1.1))
      = idealNormMultiplicity L n • g n :=
  (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
    (tsum_const (g n))

theorem hasSum_nonzeroIdeal_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (NumberField.dedekindZeta L s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
    fun n ↦ by rw [tsum_absNormFiber L n fun k ↦ (k : ℂ) ^ (-s), nsmul_eq_mul]
  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
    fun n ↦ by
      rw [tsum_absNormFiber L n fun k ↦ ‖(k : ℂ) ^ (-s)‖, nsmul_eq_mul, norm_mul,
        Complex.norm_natCast]
  have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
    exact (summable_idealNormMultiplicity_mul_cpow_neg L hs).congr fun n ↦ (hnorm n).symm
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
      (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
      hsummable.of_norm
  have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
      = NumberField.dedekindZeta L s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
    exact tsum_congr hval
  exact hval_sum ▸ hsummable.of_norm.hasSum

open UniqueFactorizationMonoid in

private theorem factorization_primePow_apply
    (𝔭 𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (n : ℕ) :
    factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.2.2 𝔭.2.1).irreducible,
    normalize_eq, Multiset.count_singleton]
  split_ifs <;> simp_all [Subtype.ext_iff]

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_apply
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 =
      ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1 := by
  classical
  induction S using Finset.induction with
  | empty => rw [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty, factorization_one,
      Finsupp.coe_zero, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.attach_insert, Finset.prod_insert, Finset.sum_insert,
      factorization_mul (pow_ne_zero _ a.2.2)
        (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)), Finsupp.add_apply,
      Finset.prod_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)),
      Finset.sum_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)), ih] <;>
    · rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact ha ((Subtype.mk.inj hx) ▸ x.2)

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0 := by
  classical
  rw [factorization_prod_primePow_apply L S e 𝔮]
  simp_rw [factorization_primePow_apply L]
  by_cases h𝔮 : 𝔮 ∈ S
  · rw [if_pos h𝔮, Finset.sum_eq_single (⟨𝔮, h𝔮⟩ : {x // x ∈ S})]
    · rw [if_pos rfl]
    · rintro b _ hb
      rw [if_neg (fun h ↦ hb (Subtype.ext h.symm))]
    · exact fun h ↦ absurd (Finset.mem_attach S _) h
  · rw [if_neg h𝔮, Finset.sum_eq_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg (fun h : 𝔮 = b ↦ h𝔮 (h.symm ▸ hb))]

open UniqueFactorizationMonoid in

private noncomputable def primeFactorsOf (𝔞 : NonzeroIdeal L) :
    Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  (normalizedFactors 𝔞.1).toFinset.attach.map
    (⟨fun p : {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↦ (⟨p.1, by
        have hp := p.2
        rw [Multiset.mem_toFinset] at hp
        exact ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p.1 hp),
          (prime_of_normalized_factor p.1 hp).ne_zero⟩⟩ :
        {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}),
      fun a b h ↦ Subtype.ext (congrArg
        (fun x : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (x : Ideal (𝓞 L))) h)⟩ :
      {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↪ {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})

open UniqueFactorizationMonoid in

private theorem mem_primeFactorsOf (𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L))
    (hp : p ∈ normalizedFactors 𝔞.1) :
    ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p := by
  refine ⟨⟨p, ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
      (prime_of_normalized_factor p hp).ne_zero⟩⟩, ?_, rfl⟩
  rw [primeFactorsOf, Finset.mem_map]
  exact ⟨⟨p, by rwa [Multiset.mem_toFinset]⟩, Finset.mem_attach _ _, rfl⟩

open UniqueFactorizationMonoid in
private theorem factorization_idealOfExp_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (f : S →₀ ℕ) (𝔮 : S) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮 := by
  classical
  have hprod : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔭.1)
      = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭 :=
    Finset.prod_congr rfl fun 𝔭 _ ↦ by simp only [dif_pos 𝔭.2]
  rw [← hprod, factorization_prod_primePow_eq L S
    (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔮.1, if_pos 𝔮.2, dif_pos 𝔮.2]

open UniqueFactorizationMonoid in
private theorem prod_primePow_count_eq (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) :
    (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1 := by
  classical
  rw [show (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1)
      = ∏ p ∈ S.image (fun 𝔭 ↦ 𝔭.1), p ^ (normalizedFactors 𝔞.1).count p by
    rw [Finset.prod_image (fun x _ y _ h ↦ Subtype.ext h), ← Finset.prod_attach S
      (fun p ↦ p.1 ^ (normalizedFactors 𝔞.1).count p.1)]]
  rw [← Finset.prod_subset (s₁ := (normalizedFactors 𝔞.1).toFinset)
    (s₂ := S.image (fun 𝔭 ↦ 𝔭.1))
    (fun p hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      obtain ⟨𝔭, h𝔭S, rfl⟩ := hsupp p hp
      exact Finset.mem_image.mpr ⟨𝔭, h𝔭S, rfl⟩)
    (fun p _ hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      rw [Multiset.count_eq_zero_of_notMem hp, pow_zero])]
  conv_rhs => rw [← finprod_pow_count_eq_of_subsingleton_units 𝔞.2]
  exact (finprod_eq_finsetProd_of_mulSupport_subset _ (by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hc
    rw [Multiset.count_eq_zero_of_notMem hc, pow_zero] at hp
    exact hp rfl)).symm

omit [NumberField L] in

private theorem weight_prod_primePow (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭 := by
  classical
  have wpow : ∀ (𝔭 : Ideal (𝓞 L)) (_ : 𝔭 ≠ ⊥) (k : ℕ), w (𝔭 ^ k) = (w 𝔭) ^ k := by
    intro 𝔭 h𝔭 k
    induction k with
    | zero => simpa using hw_one
    | succ n ih => rw [pow_succ, hw_mul (pow_ne_zero _ h𝔭) h𝔭, ih, pow_succ]
  have key : ∀ T : Finset S, w (∏ 𝔭 ∈ T, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ T, (w 𝔭.1.1) ^ e 𝔭 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hw_one
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hw_mul (pow_ne_zero _ a.1.2.2)
          (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)),
        wpow a.1.1 a.1.2.2, ih]
  exact key S.attach

private theorem weighted_prod_eulerFactor_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L)
    (hidealOfExp : ∀ e : S →₀ ℕ,
      (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭)
    (hinj : Function.Injective idealOfExp) :
    (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : Set.range idealOfExp,
          w 𝔞.1.1 * (Ideal.absNorm 𝔞.1.1 : ℂ) ^ (-s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := fun 𝔭 ↦
    ((norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)).trans_lt
      (norm_absNorm_cpow_neg_lt_one L hs 𝔭)
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hsummand : ∀ e : S →₀ ℕ,
      (∏ 𝔭 ∈ S.attach, (w 𝔭.1.1 * (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s) := fun e ↦ by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      show (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) from
      Finset.prod_congr rfl fun 𝔭 _ ↦ by
        rw [← Complex.cpow_nat_mul]
        ring_nf,
      prod_absNorm_cpow_eq_absNorm_prod_pow_cpow L S (fun 𝔭 ↦ e 𝔭),
      ← weight_prod_primePow L w hw_one hw_mul S (fun 𝔭 ↦ e 𝔭), hidealOfExp e]
  have hHS' : HasSum
      (fun e : S →₀ ℕ ↦ w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s))
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) := by
    have hbase := (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).hasSum_iff.mpr hHS
    refine hbase.congr_fun fun e ↦ ?_
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply]
    exact (hsummand e).symm
  rw [← hHS'.tsum_eq]
  exact (tsum_range
    (fun 𝔞 : NonzeroIdeal L ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) hinj).symm

open UniqueFactorizationMonoid in

theorem weighted_eulerProduct_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set P := {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set Dw : NonzeroIdeal L → ℂ := fun 𝔞 ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) with hDw
  set idealOfExp : (S : Finset P) → (S →₀ ℕ) → NonzeroIdeal L :=
    fun S e ↦ ⟨∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭,
      Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)⟩ with hidealOfExp
  have hnormD : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖Dw 𝔞‖ := by
    refine ((hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun 𝔞 ↦ ?_)
    rw [hDw]
    exact (norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)
  have hinj : ∀ S : Finset P, Function.Injective (idealOfExp S) := by
    intro S e e' h
    rw [hidealOfExp, Subtype.mk.injEq] at h
    ext 𝔮
    rw [← factorization_idealOfExp_eq L S e 𝔮, ← factorization_idealOfExp_eq L S e' 𝔮, h]
  have hmem : ∀ (S : Finset P) (𝔞 : NonzeroIdeal L),
      (∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) →
      𝔞 ∈ Set.range (idealOfExp S) := by
    intro S 𝔞 hsupp
    refine ⟨Finsupp.onFinset S.attach
      (fun 𝔭 ↦ (normalizedFactors 𝔞.1).count 𝔭.1.1) (by simp), ?_⟩
    rw [hidealOfExp, Subtype.ext_iff]
    simpa only [Finsupp.onFinset_apply] using prod_primePow_count_eq L S 𝔞 hsupp
  have hpartial : ∀ S : Finset P,
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1 := by
    intro S
    exact weighted_prod_eulerFactor_eq_tsum L hs w hw_one hw_mul hw_norm S (idealOfExp S)
      (fun e ↦ rfl) (hinj S)
  refine HasProd.tprod_eq ?_
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun 𝔞 ↦ ‖Dw 𝔞‖)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨F.biUnion (primeFactorsOf L), fun S hS ↦ ?_⟩
  have hF_sub : ∀ 𝔞 ∈ F, 𝔞 ∈ Set.range (idealOfExp S) := by
    intro 𝔞 h𝔞F
    refine hmem S 𝔞 fun p hp ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := mem_primeFactorsOf L 𝔞 p hp
    exact ⟨𝔭, hS (Finset.mem_biUnion.mpr ⟨𝔞, h𝔞F, h𝔭⟩), rfl⟩
  rw [dist_eq_norm, hpartial S]
  have hsplit : ∑' 𝔞 : NonzeroIdeal L, Dw 𝔞 =
      (∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1) +
        ∑' 𝔞 : ↥(Set.range (idealOfExp S))ᶜ, Dw 𝔞.1 :=
    (hnormD.of_norm.tsum_subtype_add_tsum_subtype_compl _).symm
  rw [hsplit, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm (hnormD.subtype _)).trans_lt ?_
  refine lt_of_le_of_lt ?_ hF
  refine (hnormD.subtype _).tsum_le_tsum_of_inj
    (fun 𝔞 : ↥(Set.range (idealOfExp S))ᶜ ↦
      (⟨𝔞.1, fun h ↦ 𝔞.2 (hF_sub 𝔞.1 h)⟩ : {x // x ∉ F}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z : {x // x ∉ F} ↦ (z : NonzeroIdeal L)) h))
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hnormD.subtype _)

open UniqueFactorizationMonoid in

theorem dedekindZeta_eq_tprod_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hw := weighted_eulerProduct_eq_tsum L hs (fun _ ↦ 1) (by simp) (by simp) (by simp)
  simp only [one_mul] at hw
  exact (hw.trans (hasSum_nonzeroIdeal_absNorm_cpow L hs).tsum_eq).symm

theorem dedekindZeta_re_pos_of_one_lt (s : ℝ) (hs : 1 < s) :
    0 < (NumberField.dedekindZeta L (s : ℂ)).re := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
      norm_cast
    rw [hg]
    push_cast [hcast]
    ring
  have hsumC : Summable
      fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
    (summable_idealNormMultiplicity_mul_cpow_neg L hs').of_norm
  have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
  have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs']
    simp_rw [key]
    rw [Complex.re_tsum (by simpa only [key] using hsumC)]
    simp
  rw [hre]
  refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [hg]
    simp [idealNormMultiplicity_one]

end NumberFieldEulerProduct

end Chebotarev
end
noncomputable section

open Filter NumberField Topology Set

namespace Chebotarev

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

private theorem summable_nonzeroIdeal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) :=
  ((hasSum_nonzeroIdeal_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).summable.norm).congr
    fun I ↦ (Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by
      rw [Complex.neg_re, Complex.ofReal_re]

theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
  have hi : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K)) :=
    fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
  exact ((summable_nonzeroIdeal_absNorm_rpow hs).comp_injective hi).congr fun _ ↦ rfl

private theorem primeIdealZetaSum_nonneg (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    0 ≤ primeIdealZetaSum S s :=
  tsum_nonneg fun _ ↦ by positivity

private theorem primeIdealZetaSum_le_univ {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, ⟨mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun 𝔭 ↦ le_of_eq rfl) (summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs)

theorem primeIdealZetaSum_le_of_subset {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum T s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow T hs)

theorem primeIdealZetaSum_union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s := by
  let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
        fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
      invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← (summable_prime_absNorm_rpow (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
      {x | (x.1 : Ideal (𝓞 K)) ∈ S},
    ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
    ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

theorem primeIdealZetaSum_empty (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨fun x ↦ x.2.1⟩
  rw [primeIdealZetaSum_def, tsum_empty]

theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp [primeIdealZetaSum_empty]
  | insert a t ha ih =>
      have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
        disjoint_iUnion₂_right.2 fun i hi ↦
          hg (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
            (fun h ↦ ha (h ▸ hi))
      rw [Finset.set_biUnion_insert, primeIdealZetaSum_union_of_disjoint hdisj hs,
        Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]

theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem
    (hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) :
    primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    Equiv.subtypeEquivRight fun 𝔭 ↦
      ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

variable (K)

private theorem summable_prime2_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs).comp_injective
    (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨mem_univ _, h⟩, fun h ↦ h.2⟩).injective).congr
    fun _ ↦ rfl

private theorem two_le_absNorm_of_prime {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) :=
  have : (2 : ℕ) ≤ Ideal.absNorm 𝔭 := Nat.two_le_iff _ |>.2
    ⟨mt Ideal.absNorm_eq_zero_iff.1 hne, mt Ideal.absNorm_eq_one_iff.1 hp.ne_top⟩
  mod_cast this

private theorem absNorm_rpow_neg_lt_one {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ}
    (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by have := two_le_absNorm_of_prime K hp hne; linarith) (by linarith)

private theorem primeIdealHigherTail_term_le {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤
      2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ)) := by
  set x : ℝ := (Ideal.absNorm 𝔭 : ℝ)
  have hx : (2 : ℝ) ≤ x := two_le_absNorm_of_prime K hp hne
  have hxs_half : x ^ (-s) ≤ 1 / 2 :=
    calc x ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos zero_lt_two hx (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hden_pos : (0 : ℝ) < 1 - x ^ (-s) := by linarith
  have hinv_le : (1 - x ^ (-s))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos (by norm_num)]; linarith
  have hexp : x ^ (-(2 : ℝ) * s) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  rw [div_eq_mul_inv]
  calc x ^ (-(2 : ℝ) * s) * (1 - x ^ (-s))⁻¹
      ≤ x ^ (-(2 : ℝ)) * 2 := mul_le_mul hexp hinv_le (by positivity) (by positivity)
    _ = 2 * x ^ (-(2 : ℝ)) := by ring

theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  refine ⟨2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  have hbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤
        2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 ↦
    primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs
  have hnonneg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
      (by have := absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs; linarith)
  have hsummable_rhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    (summable_prime2_absNorm_rpow K one_lt_two).mul_left 2
  calc ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
      ≤ ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) :=
        (Summable.of_nonneg_of_le hnonneg hbound hsummable_rhs).tsum_le_tsum hbound hsummable_rhs
    _ = 2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := tsum_mul_left

private theorem primeIdealZetaSum_univ_eq_tsum_prime2 (s : ℝ) :
    primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def, ← (Equiv.subtypeEquivRight fun 𝔭 ↦
    ⟨fun h ↦ ⟨mem_univ _, h⟩, fun h ↦ h.2⟩).tsum_eq
    fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)]
  rfl

private theorem one_sub_absNorm_rpow_pos {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s) := by
  have := absNorm_rpow_neg_lt_one K hp hne hs
  linarith

private theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ - Real.log (1 - x) - x ∧ - Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have hden : 0 < 1 - x := by linarith
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  refine ⟨by have := Real.log_le_sub_one_of_pos hden; linarith, ?_⟩
  have key := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_one, Nat.cast_zero, zero_add,
    div_one, abs_of_nonneg hx0, Nat.reduceAdd] at key
  linarith [(abs_le.mp key).1]

private theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  refine ((Real.summable_log_one_add_of_summable
    (summable_prime2_absNorm_rpow K hs).neg).neg).congr fun 𝔭 ↦ ?_
  rw [sub_eq_add_neg]

private theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))⁻¹ with hg
  have hgpos : ∀ 𝔭, 0 < g 𝔭 :=
    fun 𝔭 ↦ inv_pos.mpr (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs)
  have hlogsum : Summable (fun 𝔭 ↦ Real.log (g 𝔭)) := by
    refine (summable_neg_log_one_sub_absNorm_rpow K hs).congr (fun 𝔭 ↦ ?_)
    rw [hg, Real.log_inv]
  have hCprod : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹)
      ((Real.exp (∑' 𝔭, Real.log (g 𝔭)) : ℝ) : ℂ) := by
    refine ((Real.hasProd_of_hasSum_log hgpos hlogsum.hasSum).map Complex.ofRealHom
      Complex.continuous_ofReal).congr_fun fun 𝔭 ↦ ?_
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe, hg]
    push_cast [Complex.ofReal_cpow (show (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) by positivity)]
    ring
  have hre : (dedekindZeta K (s : ℂ)).re = Real.exp (∑' 𝔭, Real.log (g 𝔭)) := by
    rw [dedekindZeta_eq_tprod_primeIdeal K (by simpa using hs), hCprod.tprod_eq,
      Complex.ofReal_re]
  rw [hre, Real.log_exp]
  exact tsum_congr fun 𝔭 ↦ by rw [hg, Real.log_inv]

private theorem abs_tsum_neg_log_one_sub_sub_rpow_le :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
          - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C := by
  obtain ⟨C, hC⟩ := primeIdealZetaHigherTail_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_tail hs1
  simp only [mem_Ioi] at hs1
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
  set h : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) with hh
  have hxbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) < 1 := fun 𝔭 ↦ absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs1
  have hxnn : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ Real.rpow_nonneg (by positivity) _
  have hfnn : ∀ 𝔭, 0 ≤ f 𝔭 := fun 𝔭 ↦ (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).1
  have hfle : ∀ 𝔭, f 𝔭 ≤ h 𝔭 := fun 𝔭 ↦ by
    refine (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).2.trans_eq ?_
    rw [hh]
    congr 1
    rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) 2, ← Real.rpow_mul (by positivity)]
    ring_nf
  have hsummh : Summable h := by
    have hnn : ∀ 𝔭, 0 ≤ h 𝔭 := fun 𝔭 ↦ by
      rw [hh]
      exact div_nonneg (Real.rpow_nonneg (by positivity) _)
        (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs1).le
    refine Summable.of_nonneg_of_le hnn (fun 𝔭 ↦ primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs1)
      ((summable_prime2_absNorm_rpow K one_lt_two).mul_left 2)
  have hsummf : Summable f := Summable.of_nonneg_of_le hfnn hfle hsummh
  rw [abs_of_nonneg (tsum_nonneg hfnn)]
  calc ∑' 𝔭, f 𝔭 ≤ ∑' 𝔭, h 𝔭 := hsummf.tsum_le_tsum hfle hsummh
    _ ≤ C := hs_tail

theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  obtain ⟨C, hC⟩ := abs_tsum_neg_log_one_sub_sub_rpow_le K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_bound hs1
  simp only [mem_Ioi] at hs1
  rwa [log_dedekindZeta_re_eq_tsum_neg_log_one_sub K hs1,
    primeIdealZetaSum_univ_eq_tsum_prime2 K s,
    ← (summable_neg_log_one_sub_absNorm_rpow K hs1).tsum_sub
      (summable_prime2_absNorm_rpow K hs1)]

theorem logDedekindZeta_sub_log_inv_sub_one_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum (univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL := tendsto_log_one_div_sub_one_atTop
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp (mem_Ioi.mp hs)).le

end Chebotarev
end

section
open NumberField Filter Set
open scoped Topology
namespace WeakDensity436
noncomputable section

abbrev Fibr (K : Type) [Field K] [NumberField K] (p : ℕ) :=
  {I : Ideal (𝓞 K) // I.absNorm=p}

lemma count_homs (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Nat.card (𝓞 K →+* ZMod p)=Nat.card (Fibr K p) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have sur (f : 𝓞 K →+* ZMod p) : Function.Surjective f := fun x => ⟨(x.val:ℕ),by simp⟩
  let g (f : 𝓞 K →+* ZMod p) : Fibr K p :=
    ⟨RingHom.ker f, (Nat.card_congr (f.quotientKerEquivOfSurjective (sur f)).toEquiv).trans (by simp [Nat.card_eq_fintype_card])⟩
  apply Nat.card_congr (Equiv.ofBijective g ⟨?_,?_⟩)
  · intro f h eq
    have e : RingHom.ker f=RingHom.ker h := congrArg Subtype.val eq
    ext x
    have d : x-((f x).val:ℕ) ∈ RingHom.ker f := by change f _=0; simp
    rw [e] at d
    change h _=0 at d
    simpa using (sub_eq_zero.mp (by simpa only [map_sub,map_natCast,ZMod.natCast_zmod_val] using d)).symm
  · rintro ⟨I,hi⟩
    letI := (Ideal.absNorm_ne_zero_iff I).mp (hi ▸ hp.ne_zero)
    letI := Fintype.ofFinite (𝓞 K ⧸ I)
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [←Nat.card_eq_fintype_card]; exact hi)
    refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk I),Subtype.ext ?_⟩
    ext x
    change e.symm (Ideal.Quotient.mk I x)=0 ↔ x∈I
    rw [map_eq_zero_iff _ e.symm.injective,Ideal.Quotient.eq_zero_iff_mem]

abbrev Targets (K : Type) [Field K] [NumberField K] (B : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | B < I.absNorm ∧ I.absNorm.Prime}

lemma project {K : Type} [Field K] [NumberField K] (I : Ideal (𝓞 K)) (h : I.IsPrime) (nz : I ≠ ⊥) :
    (I.under ℤ).absNorm.Prime ∧ (I.under ℤ).absNorm ^ I.inertiaDeg ℤ = I.absNorm := by
  letI := h
  letI : NeZero I := ⟨nz⟩
  exact ⟨Nat.absNorm_under_prime I,Ideal.absNorm_pow_inertiaDeg (I.under ℤ) I⟩

lemma fiber_bound {K : Type} [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (q : Nat.Primes) :
    let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
    let g (I : A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
    Finite (g ⁻¹' {q} : Set A) ∧ Nat.card (g ⁻¹' {q} : Set A) ≤ Module.finrank ℚ K := by
  classical
  dsimp only
  let T := Ideal.span ({(q.val:ℤ)} : Set ℤ)
  have tn : T≠⊥ := by simp [T,q.property.ne_zero]
  letI : T.IsMaximal := ((Ideal.span_singleton_prime (by exact_mod_cast q.property.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp q.property)).isMaximal tn
  let U := IsDedekindDomain.primesOverFinset T (𝓞 K)
  let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
  let g (I : A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
  let j (x : (g ⁻¹' {q} : Set A)) : U := ⟨x.1.1, by
    apply (IsDedekindDomain.mem_primesOverFinset_iff tn _).mpr
    refine ⟨x.1.2.2.1,?_⟩
    have eq : (x.1.1.under ℤ).absNorm = q.val := congrArg Subtype.val (show g x.1=q from x.2)
    rw [Ideal.liesOver_iff,← Int.ideal_span_absNorm_eq_self (x.1.1.under ℤ),eq]⟩
  have ji : Function.Injective j := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun v:U => (v:Ideal (𝓞 K))) eq))
  refine ⟨Finite.of_injective j ji,(Nat.card_le_card_of_injective j ji).trans ?_⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,U] using
    Ideal.card_primesOverFinset_le_finrank (S := 𝓞 K) (K := ℚ) (L := K) tn

end
end WeakDensity436
namespace Chebotarev
open Set
open scoped ENNReal
theorem tsum_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ)
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, f (g b) ≤ (d : ℝ≥0∞) * ∑' y, f y := by
  rw [← ENNReal.tsum_fiberwise (fun b ↦ f (g b)) g, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun y ↦ ?_)
  rw [tsum_congr (fun b : (g ⁻¹' {y} : Set β) ↦ by rw [b.2])]
  haveI := hfin y
  letI := Fintype.ofFinite (g ⁻¹' {y} : Set β)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  gcongr
  exact_mod_cast hfib y

/-- **Fibre-counting bound for real-valued sums.** The `ℝ`-valued companion of
`tsum_comp_le_card_fibre_mul`: for nonnegative summable `FA, FK` with `FA b ≤ FK (g b)` and every
fibre `g ⁻¹' {y}` finite of size `≤ d`, the sum `Σ_b FA b` is at most `d · Σ_y FK y`. -/
theorem tsum_real_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (FA : β → ℝ)
    (FK : γ → ℝ) (d : ℕ) (hsummA : Summable FA) (hsummK : Summable FK) (hnonnegA : ∀ b, 0 ≤ FA b)
    (hnonnegK : ∀ y, 0 ≤ FK y) (hterm : ∀ b, FA b ≤ FK (g b))
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, FA b ≤ (d : ℝ) * ∑' y, FK y := by
  have hchain : ∑' b, ENNReal.ofReal (FA b)
      ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
    calc ∑' b, ENNReal.ofReal (FA b) ≤ ∑' b, ENNReal.ofReal (FK (g b)) :=
          ENNReal.tsum_le_tsum fun b ↦ ENNReal.ofReal_le_ofReal (hterm b)
      _ ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
          tsum_comp_le_card_fibre_mul g (ENNReal.ofReal <| FK ·) d hfin hfib
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonnegA hsummA,
    ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK] at hchain
  rw [← ENNReal.toReal_ofReal (tsum_nonneg hnonnegA),
    ← ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg hnonnegK)),
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hchain
end Chebotarev
open NumberField Filter Set Chebotarev
open scoped Topology
namespace WeakDensity436
noncomputable section

lemma high_tail (K : Type) [Field K] [NumberField K] (B : ℕ) :
    ∃ C : ℝ, ∀ s : ℝ, 1<s → primeIdealZetaSum (Targets K B)ᶜ s ≤ C := by
  classical
  let S := (Targets K B)ᶜ
  let A := {I : Ideal (𝓞 K) // I∈S ∧ I.IsPrime ∧ I ≠ ⊥}
  let g (I:A) : Nat.Primes := ⟨(I.val.under ℤ).absNorm,(project I.val I.2.2.1 I.2.2.2).1⟩
  let w (n:ℕ) : ℝ := (n:ℝ)^(-(2:ℝ))+(if n≤B then 1 else 0)
  have ws : Summable w := (Real.summable_nat_rpow.mpr (by norm_num : -(2:ℝ)< -1)).add (by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_Iic B).subset
    intro n hn
    by_contra h; exact hn (if_neg h))
  have wn (n:ℕ) : 0≤w n := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by split_ifs <;> norm_num)
  refine ⟨Module.finrank ℚ K * ∑' q:Nat.Primes, w q.val,fun s hs => ?_⟩
  apply Chebotarev.tsum_real_comp_le_card_fibre_mul g _ _ _
    (summable_prime_absNorm_rpow S hs) (ws.comp_injective Subtype.val_injective)
    (fun _ => by positivity) (fun q => wn q.val)
    _ (fun q => (fiber_bound S q).1) (fun q => (fiber_bound S q).2)
  intro I
  let J := I.val
  have primes := (g I).property
  have eq : (g I).val ^ J.inertiaDeg ℤ=J.absNorm := (project J I.2.2.1 I.2.2.2).2
  letI : J.IsPrime := I.2.2.1
  letI : J.LiesOver (J.under ℤ) := Ideal.over_under J
  have fpos := Ideal.inertiaDeg_pos J ℤ
  have lo : (1:ℝ)≤(g I).val := by exact_mod_cast primes.one_le
  have pn : 0 < (g I).val := primes.pos
  have normlo : (g I).val ≤ J.absNorm := by rw [←eq]; exact Nat.le_self_pow (by omega) _
  change (J.absNorm:ℝ)^(-s) ≤ w (g I).val
  by_cases small : (g I).val ≤ B
  · have o : (J.absNorm:ℝ)^(-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast primes.one_le.trans normlo) (by linarith)
    dsimp [w]; rw [if_pos small]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (g I).val) (-(2:ℝ))]
  · have deg : 2≤J.inertiaDeg ℤ := by
      by_contra hh
      have e : J.inertiaDeg ℤ=1 := by omega
      rw [e,pow_one] at eq
      exact I.2.1 (show B<J.absNorm ∧ J.absNorm.Prime by rw [←eq]; exact ⟨by omega,primes⟩)
    dsimp only [w]; rw [if_neg small,add_zero,←eq,Nat.cast_pow,
      ←Real.rpow_natCast ((g I).val:ℝ) (J.inertiaDeg ℤ),←Real.rpow_mul (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le lo
    have hh : (2:ℝ)≤J.inertiaDeg ℤ := by exact_mod_cast deg
    nlinarith [mul_le_mul hh hs.le (by norm_num) (by positivity : (0:ℝ)≤J.inertiaDeg ℤ)]

lemma large_comparison (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ)
    (h : ∀ p>B, p.Prime → 2*Nat.card (Fibr E p) ≤ Nat.card (Fibr K p))
    (s : ℝ) (hs : 1<s) :
    2*primeIdealZetaSum (Targets E B) s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  classical
  have emb (p : ℕ) (hp : p>B) (pr : p.Prime) : Nonempty ((Bool × Fibr E p) ↪ Fibr K p) := by
    letI : Fintype (Fibr K p) := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) p).fintype
    letI : Fintype (Fibr E p) := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) p).fintype
    apply Function.Embedding.nonempty_of_card_le
    simpa [Fintype.card_prod,Nat.card_eq_fintype_card] using h p hp pr
  let A := {I : Ideal (𝓞 E) // I∈Targets E B ∧ I.IsPrime ∧ I≠⊥}
  let C := {I : Ideal (𝓞 K) // I∈(univ : Set (Ideal (𝓞 K))) ∧ I.IsPrime ∧ I≠⊥}
  let f (v : Bool × A) : Ideal (𝓞 K) := ((emb v.2.1.absNorm v.2.2.1.1 v.2.2.1.2).some (v.1,⟨v.2.1,rfl⟩)).1
  have eq (v : Bool × A) : (f v).absNorm=v.2.1.absNorm := ((emb _ v.2.2.1.1 v.2.2.1.2).some (v.1,⟨v.2.1,rfl⟩)).2
  let j (v : Bool × A) : C := ⟨f v,mem_univ _, Ideal.isPrime_of_irreducible_absNorm (by rw [eq]; exact v.2.2.1.2),
    fun h => v.2.2.1.2.ne_zero (by rw [←eq v,h,Ideal.absNorm_bot])⟩
  have inject : Function.Injective j := by
    rintro ⟨i,⟨I,hI⟩⟩ ⟨k,⟨J,hJ⟩⟩ ee
    have ee' := congrArg Subtype.val ee
    change f (i,⟨I,hI⟩)=f (k,⟨J,hJ⟩) at ee'
    have n := (eq (i,⟨I,hI⟩)).symm.trans ((congrArg Ideal.absNorm ee').trans (eq (k,⟨J,hJ⟩)))
    have agree {p q:ℕ} (hp : B<p) (pp:p.Prime) (hq:B<q) (pq:q.Prime)
        (a:Bool × Fibr E p) (b:Bool × Fibr E q) (e:p=q)
        (v : ((emb p hp pp).some a).1=((emb q hq pq).some b).1) :
        a.1=b.1 ∧ a.2.1=b.2.1 := by
      subst q
      have same := (emb p hp pp).some.injective (Subtype.ext v)
      cases same
      exact ⟨rfl,rfl⟩
    obtain ⟨ik,ij⟩ := agree hI.1.1 hI.1.2 hJ.1.1 hJ.1.2 (i,⟨I,rfl⟩) (k,⟨J,rfl⟩) n ee'
    exact Prod.ext ik (Subtype.ext ij)
  let w (v:A) := (v.1.absNorm:ℝ)^(-s)
  have summ : Summable w := summable_prime_absNorm_rpow (Targets E B) hs
  have bp : Summable (fun v:Bool × A => w v.2) :=
    (summable_prod_of_nonneg (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
      ⟨fun _ => summ,Summable.of_finite⟩
  have le := bp.tsum_le_tsum_of_inj j inject (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun v => show w v.2 ≤ ((j v).1.absNorm:ℝ)^(-s) by rw [show (j v).1.absNorm=v.2.1.absNorm from eq v])
    (summable_prime_absNorm_rpow univ hs)
  rw [bp.tsum_prod' (fun _ => summ),tsum_fintype,Fintype.sum_bool] at le
  rw [two_mul]
  exact le

theorem compare (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (B : ℕ) :
    ∃ p>B, p.Prime ∧ Nat.card (𝓞 K →+* ZMod p)<2*Nat.card (𝓞 E →+* ZMod p) := by
  classical
  by_contra! nope
  have h (p : ℕ) (hp : p>B) (pr : p.Prime) : 2*Nat.card (Fibr E p) ≤ Nat.card (Fibr K p) := by
    rw [←count_homs E p pr,←count_homs K p pr]
    exact nope p hp pr
  obtain ⟨C,tail⟩ := high_tail E B
  obtain ⟨a,low⟩ := log_minus_bounded_le_primeIdealZetaSum E
  obtain ⟨b,up⟩ := primeIdealZetaSum_le_log_plus_bounded K
  have pos : ∀ᶠ s in 𝓝[>] (1:ℝ), 1<s := self_mem_nhdsWithin
  obtain ⟨s,hs,left,right,big⟩ := (pos.and (low.and (up.and
    (tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop (2*a+2*C+b))))).exists
  have double := large_comparison E K B h s hs
  have add := primeIdealZetaSum_union_of_disjoint (S := Targets E B) (T := (Targets E B)ᶜ) disjoint_compl_right hs
  rw [union_compl_self] at add
  linarith [tail s hs]

end
end WeakDensity436

end

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1.H1 := WeakDensity436.compare
