import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Proof of vanishing of Serre intersection multiplicity for regular hypersurface quotients. -/

open IsLocalRing Module Ideal CategoryTheory Limits MonoidalCategory TensorProduct

namespace SerreH4Proof

section RegularLocal

lemma isRegularLocalRing_quotient_span_singleton
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1)
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    let I := Ideal.span ({x} : Set R)
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (fun h => (maximalIdeal.isMaximal R).ne_top
        (top_unique (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))))
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    IsRegularLocalRing (R ⧸ I) ∧ (maximalIdeal (R ⧸ I)).spanFinrank = n := by
  classical
  intro I _ _
  have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hm_map : (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hkrull_R : ringKrullDim R = (n + 1 : ℕ) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim]
  have hspan_le_n : (maximalIdeal (R ⧸ I)).spanFinrank ≤ n := by
    let k := ResidueField R
    have hfinrank : Module.finrank k (CotangentSpace R) = n + 1 := by
      have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
      rw [hkrull_R] at h1
      exact_mod_cast h1
    let v : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩
    have hv : v ≠ 0 := by
      intro h0
      rw [Ideal.toCotangent_eq_zero] at h0
      exact hx2 (by simpa [pow_two] using h0)
    let L : Submodule k (CotangentSpace R) := Submodule.span k {v}
    have hL_rank : Module.finrank k L = 1 := finrank_span_singleton hv
    let Q := CotangentSpace R ⧸ L
    have hQ_rank : Module.finrank k Q = n := by
      have hadd := Submodule.finrank_quotient_add_finrank L
      dsimp only [Q]
      omega
    let b := Module.finBasisOfFinrankEq k Q hQ_rank
    have hlift (i : Fin n) : ∃ y : maximalIdeal R,
        L.mkQ ((maximalIdeal R).toCotangent y) = b i := by
      obtain ⟨w, hw⟩ := Submodule.mkQ_surjective L (b i)
      obtain ⟨y, hy⟩ := Ideal.toCotangent_surjective (maximalIdeal R) w
      exact ⟨y, by rw [hy, hw]⟩
    choose y hy using hlift
    let yf : Fin n → R := fun i => (y i : R)
    let s : Set (maximalIdeal R) := insert ⟨x, hx⟩ (Set.range y)
    have hspan_cot : Submodule.span k ((maximalIdeal R).toCotangent '' s) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hbw : L.mkQ w ∈ Submodule.span k (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hbw
      obtain ⟨c, hc⟩ := hbw
      have hdiff : w - ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) ∈ L := by
        rw [← Submodule.ker_mkQ L, LinearMap.mem_ker, map_sub, map_sum]
        simp_rw [map_smul, hy]
        rw [hc, sub_self]
      rw [Submodule.mem_span_singleton] at hdiff
      obtain ⟨a, ha⟩ := hdiff
      have hw_eq : w = a • v + ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) := by
        rw [ha]; abel
      rw [hw_eq]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨⟨x, hx⟩, Set.mem_insert _ _, rfl⟩)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i)
          (Submodule.subset_span ⟨y i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩)
    have hspan_top : Submodule.span R s = ⊤ :=
      (CotangentSpace.span_image_eq_top_iff).mp hspan_cot
    have hm_eq : maximalIdeal R = Ideal.span (insert x (Set.range yf)) := by
      have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspan_top
      rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span] at hmap
      convert hmap.symm using 2
      ext z
      simp [s, yf, eq_comm]
    have hmq_eq : maximalIdeal (R ⧸ I) =
        Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) := by
      rw [← hm_map, hm_eq, Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨z, hz, rfl⟩
        rcases hz with rfl | ⟨i, rfl⟩
        · have hx0 : Ideal.Quotient.mk I z = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
          rw [hx0]
          exact Submodule.zero_mem _
        · exact Ideal.subset_span ⟨i, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨yf i, Or.inr ⟨i, rfl⟩, rfl⟩
    rw [hmq_eq]
    calc (Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i)))).spanFinrank
        ≤ (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ n := by
          have h1 : (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) =
              ((Finset.univ.image (fun i : Fin n => Ideal.Quotient.mk I (yf i))) : Set (R ⧸ I)) := by
            ext z; simp
          rw [h1, Set.ncard_coe_finset]
          exact Finset.card_image_le.trans (by simp)
  have hI_sf : I.spanFinrank ≤ 1 := by
    simpa [I] using Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)
  have hI_jac : I ≤ Ring.jacobson R := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    exact le_sInf fun m hm => (IsLocalRing.eq_maximalIdeal hm).symm ▸ hI_le
  have hkd := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hI_jac
  have hkd_ge : (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hkrull_R] at hkd
    have h1 : (I.spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hI_sf
    have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) + 1 :=
      hkd.trans (add_le_add le_rfl h1)
    cases hd : ringKrullDim (R ⧸ I) with
    | bot =>
      rw [hd] at h2
      simp at h2
    | coe a =>
      rw [hd] at h2
      have h2' : ((n + 1 : ℕ) : ℕ∞) ≤ a + 1 := WithBot.coe_le_coe.mp h2
      have ha : (n : ℕ∞) ≤ a := by
        cases a with
        | top => exact le_top
        | coe m =>
          norm_cast at h2' ⊢
          omega
      exact WithBot.coe_le_coe.mpr ha
  have hreg : IsRegularLocalRing (R ⧸ I) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R ⧸ I)
      ((Nat.cast_le.mpr hspan_le_n).trans hkd_ge)
  have hkd_le : ringKrullDim (R ⧸ I) ≤ (n : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact_mod_cast hspan_le_n
  have heq : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact le_antisymm hkd_le hkd_ge
  exact ⟨hreg, by exact_mod_cast heq⟩

lemma maximalIdeal_not_le_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1) :
    ¬ (maximalIdeal R ≤ maximalIdeal R ^ 2) := by
  intro hle
  have hm_bot : maximalIdeal R = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _)
      (by simpa [smul_eq_mul, pow_two] using hle)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  have h0 : (maximalIdeal R).spanFinrank = 0 := by simp [hm_bot]
  omega

/-- Every regular local ring is an integral domain. -/
theorem isDomain_of_isRegularLocalRing_aux (d : ℕ) :
    ∀ (R : Type*) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d → IsDomain R := by
  induction d with
  | zero =>
    intro R _ _ h0
    have hm_bot : maximalIdeal R = ⊥ := by
      have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
        have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), h0] at h2
        exact_mod_cast h2
      have hsub : Subsingleton (CotangentSpace R) :=
        Module.finrank_zero_iff.mp h1
      have hfield : IsField R := subsingleton_cotangentSpace_iff.mp hsub
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm_bot).toField
    infer_instance
  | succ n ih =>
    intro R _ _ hdim
    have hm_ne_sq := maximalIdeal_not_le_sq hdim
    have hm_not_min (p : Ideal R) (hp : p ∈ minimalPrimes R) : ¬ (maximalIdeal R ≤ p) := by
      intro hle
      have hp_prime : p.IsPrime := hp.1.1
      have hp_eq : p = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hp_prime.ne_top) hle
      have hkd0 : Ring.KrullDimLE 0 R := by
        rw [Ring.krullDimLE_zero_iff]
        intro q hq
        have hqp : q ≤ p := hp_eq ▸ IsLocalRing.le_maximalIdeal hq.ne_top
        have heq : q = p := le_antisymm hqp (hp.2 ⟨hq, bot_le⟩ hqp)
        rw [heq, hp_eq]
        exact maximalIdeal.isMaximal R
      have hle0 : ringKrullDim R ≤ 0 := Ring.krullDimLE_iff.mp hkd0
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim] at hle0
      have : (n + 1 : ℕ) ≤ 0 := by exact_mod_cast hle0
      omega
    have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
    have hex : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
      by_contra! hall
      have hsub' : (maximalIdeal R : Set R) ⊆
          ⋃ I ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R), (I : Set R) := by
        intro x hx
        by_cases hx2 : x ∈ maximalIdeal R ^ 2
        · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
        · obtain ⟨p, hp, hxp⟩ := hall x hx hx2
          exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
      have havoid := Ideal.subset_union_prime_finite (I := maximalIdeal R)
        (hfin.insert (maximalIdeal R ^ 2))
        (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
        (fun I hI hne1 _ => by
          rcases Set.mem_insert_iff.mp hI with rfl | hmin
          · exact (hne1 rfl).elim
          · exact hmin.1.1)
      obtain ⟨I, hI, hle⟩ := havoid.mp hsub'
      rcases Set.mem_insert_iff.mp hI with rfl | hmin
      · exact hm_ne_sq hle
      · exact hm_not_min I hmin hle
    obtain ⟨x, hx, hx2, hx_min⟩ := hex
    let I := Ideal.span ({x} : Set R)
    have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_unique (h ▸ hI_le))
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨hreg_q, hdim_q⟩ := isRegularLocalRing_quotient_span_singleton hdim hx hx2
    have hdom_q : IsDomain (R ⧸ I) := ih (R ⧸ I) hdim_q
    have hI_prime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp hdom_q
    obtain ⟨p, hp_min, hp_le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I) bot_le
    have hp_prime : p.IsPrime := hp_min.1.1
    have hp_le_mul : p ≤ maximalIdeal R • p := by
      intro y hy
      have hyI : y ∈ I := hp_le hy
      rw [Ideal.mem_span_singleton] at hyI
      obtain ⟨r, rfl⟩ := hyI
      have hr : r ∈ p := (hp_prime.mem_or_mem hy).resolve_left (hx_min p hp_min)
      simpa [smul_eq_mul] using Submodule.smul_mem_smul hx hr
    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p)
        hp_le_mul
        (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
    have hbot_prime : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    let _ : NoZeroDivisors R := ⟨fun {a b} hab => by
      have hmem : a * b ∈ (⊥ : Ideal R) := by simpa using hab
      rcases hbot_prime.mem_or_mem hmem with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)⟩
    exact NoZeroDivisors.to_isDomain R

theorem isDomain_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux (maximalIdeal R).spanFinrank R rfl

lemma exists_param_of_isRegularLocalRing {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ x ≠ 0 := by
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp (maximalIdeal_not_le_sq hdim)
  exact ⟨x, hx, hx2, fun h0 => hx2 (h0 ▸ zero_mem _)⟩

end RegularLocal

section FiniteProjRes

/-- Existence of a finite projective resolution of length at most `d`. -/
def HasFiniteProjRes (R : Type) [CommRing R] :
    ℕ → ∀ (N : Type) [AddCommGroup N] [Module R N], Prop
  | 0, N, _, _ => Module.Finite R N ∧ Module.Projective R N
  | n + 1, N, _, _ =>
      ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P),
        Module.Finite R P ∧ Module.Projective R P ∧
        ∃ (f : P →ₗ[R] N), Function.Surjective f ∧ HasFiniteProjRes R n (LinearMap.ker f)

lemma hasFiniteProjRes_of_equiv {R : Type} [CommRing R] {n : ℕ}
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : HasFiniteProjRes R n M) : HasFiniteProjRes R n N := by
  cases n with
  | zero =>
    obtain ⟨hfin, hproj⟩ := hM
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  | succ m =>
    obtain ⟨P, _, _, hfin, hproj, f, hf, hK⟩ := hM
    have hf' : Function.Surjective (e.toLinearMap.comp f) := e.surjective.comp hf
    have hker : LinearMap.ker (e.toLinearMap.comp f) = LinearMap.ker f := by
      ext x; simp [LinearMap.mem_ker]
    refine ⟨P, inferInstance, inferInstance, hfin, hproj, e.toLinearMap.comp f, hf', ?_⟩
    exact hasFiniteProjRes_of_equiv (LinearEquiv.ofEq _ _ hker.symm) hK

lemma hasFiniteProjRes_prod_right {R : Type} [CommRing R] {n : ℕ}
    {M P : Type} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (hM : HasFiniteProjRes R n M) : HasFiniteProjRes R n (M × P) := by
  cases n with
  | zero =>
    obtain ⟨hfin, hproj⟩ := hM
    exact ⟨inferInstance, inferInstance⟩
  | succ m =>
    obtain ⟨Q, _, _, hfinQ, hprojQ, f, hf, hK⟩ := hM
    let g : Q × P →ₗ[R] M × P := f.prodMap LinearMap.id
    have hg : Function.Surjective g := fun ⟨a, b⟩ => by
      obtain ⟨q, hq⟩ := hf a
      exact ⟨(q, b), by simp [g, hq]⟩
    let ek : LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
      { toFun := fun ⟨q, hq⟩ => ⟨(q, 0), by simp [g, LinearMap.mem_ker.mp hq]⟩
        invFun := fun ⟨⟨q, p⟩, hqp⟩ => ⟨q, by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [g, Prod.ext_iff] at h1
          exact h1.1⟩
        map_add' := fun _ _ => by ext <;> simp
        map_smul' := fun _ _ => by ext <;> simp
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨⟨q, p⟩, hqp⟩ => by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [g, Prod.ext_iff] at h1
          ext
          · rfl
          · exact h1.2.symm }
    exact ⟨Q × P, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
      hasFiniteProjRes_of_equiv ek hK⟩

/-- Schanuel's Lemma for two surjective linear maps from projective modules. -/
lemma schanuel_nonempty {R : Type} [CommRing R]
    {N P₁ P₂ : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup P₁] [Module R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Projective R P₂]
    (f₁ : P₁ →ₗ[R] N) (hf₁ : Function.Surjective f₁)
    (f₂ : P₂ →ₗ[R] N) (hf₂ : Function.Surjective f₂) :
    Nonempty ((LinearMap.ker f₁ × P₂) ≃ₗ[R] (LinearMap.ker f₂ × P₁)) := by
  let Q : Submodule R (P₁ × P₂) :=
    LinearMap.ker (f₁.comp (LinearMap.fst R P₁ P₂) - f₂.comp (LinearMap.snd R P₁ P₂))
  have hmemQ (p : P₁ × P₂) : p ∈ Q ↔ f₁ p.1 = f₂ p.2 := by
    simp [Q, LinearMap.mem_ker, sub_eq_zero]
  obtain ⟨s₂, hs₂⟩ := Module.projective_lifting_property f₁ f₂ hf₁
  obtain ⟨s₁, hs₁⟩ := Module.projective_lifting_property f₂ f₁ hf₂
  let e₂ : (LinearMap.ker f₁ × P₂) ≃ₗ[R] Q :=
    { toFun := fun ⟨⟨k, hk⟩, p₂⟩ => ⟨(k + s₂ p₂, p₂), by
        rw [hmemQ]
        simp [LinearMap.mem_ker.mp hk]
        exact LinearMap.congr_fun hs₂ p₂⟩
      invFun := fun ⟨⟨p₁, p₂⟩, hq⟩ => ⟨⟨p₁ - s₂ p₂, by
        rw [LinearMap.mem_ker, map_sub, (hmemQ _).mp hq]
        have h2 : f₁ (s₂ p₂) = f₂ p₂ := LinearMap.congr_fun hs₂ p₂
        rw [h2, sub_self]⟩, p₂⟩
      map_add' := fun _ _ => by ext <;> simp [add_assoc, add_left_comm]
      map_smul' := fun _ _ => by ext <;> simp [smul_add]
      left_inv := fun ⟨⟨k, hk⟩, p₂⟩ => by ext <;> simp
      right_inv := fun ⟨⟨p₁, p₂⟩, hq⟩ => by ext <;> simp }
  let e₁ : (LinearMap.ker f₂ × P₁) ≃ₗ[R] Q :=
    { toFun := fun ⟨⟨k, hk⟩, p₁⟩ => ⟨(p₁, k + s₁ p₁), by
        rw [hmemQ]
        simp [LinearMap.mem_ker.mp hk]
        exact (LinearMap.congr_fun hs₁ p₁).symm⟩
      invFun := fun ⟨⟨p₁, p₂⟩, hq⟩ => ⟨⟨p₂ - s₁ p₁, by
        rw [LinearMap.mem_ker, map_sub, ← (hmemQ _).mp hq]
        have h1 : f₂ (s₁ p₁) = f₁ p₁ := LinearMap.congr_fun hs₁ p₁
        rw [h1, sub_self]⟩, p₁⟩
      map_add' := fun _ _ => by ext <;> simp [add_assoc, add_left_comm]
      map_smul' := fun _ _ => by ext <;> simp [smul_add]
      left_inv := fun ⟨⟨k, hk⟩, p₁⟩ => by ext <;> simp
      right_inv := fun ⟨⟨p₁, p₂⟩, hq⟩ => by ext <;> simp }
  exact ⟨e₂.trans e₁.symm⟩

lemma exists_finite_free_surj {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (f : (Fin r → R) →ₗ[R] M), Function.Surjective f := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let e := s.equivFin
  let g : (Fin s.card → R) →ₗ[R] M :=
    Fintype.linearCombination R (fun i : Fin s.card => (e.symm i : M))
  refine ⟨s.card, g, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (Set.range fun i : Fin s.card => (e.symm i : M)) := by
    have hr : Set.range (fun i : Fin s.card => (e.symm i : M)) = (s : Set M) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).property
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
    rw [hr, hs]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, by simpa [g, Fintype.linearCombination_apply] using hc⟩

lemma hasFiniteProjRes_ker_of_succ {R : Type} [CommRing R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (N : Type) [AddCommGroup N] [Module R N]
      (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
      (f : P →ₗ[R] N) (_hf : Function.Surjective f),
      HasFiniteProjRes R (n + 1) N → HasFiniteProjRes R n (LinearMap.ker f) := by
  intro n
  induction n with
  | zero =>
    intro N _ _ P _ _ _ _ f hf hres
    obtain ⟨P', _, _, hfinP', hprojP', f', hf', hfinK', hprojK'⟩ := hres
    obtain ⟨e⟩ := schanuel_nonempty f hf f' hf'
    let i : LinearMap.ker f →ₗ[R] LinearMap.ker f' × P :=
      e.toLinearMap.comp (LinearMap.inl R (LinearMap.ker f) P')
    let p : LinearMap.ker f' × P →ₗ[R] LinearMap.ker f :=
      (LinearMap.fst R (LinearMap.ker f) P').comp e.symm.toLinearMap
    have hpi : p.comp i = LinearMap.id := by
      ext x; simp [p, i]
    have hprojK : Module.Projective R (LinearMap.ker f) :=
      Module.Projective.of_split i p hpi
    have hfinK : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.of_surjective p (Function.RightInverse.surjective (LinearMap.congr_fun hpi))
    exact ⟨hfinK, hprojK⟩
  | succ m ih =>
    intro N _ _ P _ _ _ _ f hf hres
    obtain ⟨P', _, _, hfinP', hprojP', f', hf', hK'⟩ := hres
    obtain ⟨e⟩ := schanuel_nonempty f hf f' hf'
    let _ : IsNoetherian R P := isNoetherian_of_isNoetherianRing_of_finite R P
    let _ : Module.Finite R (LinearMap.ker f) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) (LinearMap.ker f)
    let Q := Fin r → R
    let h : Q × P' →ₗ[R] LinearMap.ker f' × P :=
      e.toLinearMap.comp (g.prodMap LinearMap.id)
    have hh : Function.Surjective h :=
      e.surjective.comp (fun ⟨a, b⟩ => by
        obtain ⟨q, hq⟩ := hg a
        exact ⟨(q, b), by simp [hq]⟩)
    have hres_prod : HasFiniteProjRes R (m + 1) (LinearMap.ker f' × P) :=
      hasFiniteProjRes_prod_right hK'
    have hker_h : HasFiniteProjRes R m (LinearMap.ker h) :=
      ih (LinearMap.ker f' × P) (Q × P') h hh hres_prod
    let ek : LinearMap.ker h ≃ₗ[R] LinearMap.ker g :=
      { toFun := fun ⟨⟨q, p'⟩, hqp⟩ => ⟨q, by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [h] at h1
          exact h1.1⟩
        invFun := fun ⟨q, hq⟩ => ⟨(q, 0), by
          simp [h, LinearMap.mem_ker.mp hq]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun ⟨⟨q, p'⟩, hqp⟩ => by
          have h1 := LinearMap.mem_ker.mp hqp
          simp [h] at h1
          ext
          · rfl
          · exact h1.2.symm
        right_inv := fun ⟨_, _⟩ => rfl }
    exact ⟨Q, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
      hasFiniteProjRes_of_equiv ek hker_h⟩

/-- Helper equivalence `S ⊗[R] (Fin r → R) ≃ₗ[S] (Fin r → S)`. -/
noncomputable def baseChangeFinEquiv (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r : ℕ) :
    (S ⊗[R] (Fin r → R)) ≃ₗ[S] (Fin r → S) := by
  let toF : S ⊗[R] (Fin r → R) →ₗ[S] (Fin r → S) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s =>
          { toFun := fun v i => s * algebraMap R S (v i)
            map_add' := fun v₁ v₂ => by ext i; simp [mul_add]
            map_smul' := fun a v => by
              ext i
              simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
              ring }
        map_add' := fun s₁ s₂ => by apply LinearMap.ext; intro v; ext i; simp [add_mul]
        map_smul' := fun s₁ s₂ => by apply LinearMap.ext; intro v; ext i; simp [mul_assoc] }
  let invF : (Fin r → S) →ₗ[S] S ⊗[R] (Fin r → R) :=
    { toFun := fun u => ∑ i : Fin r, u i ⊗ₜ[R] Pi.single i (1 : R)
      map_add' := fun u₁ u₂ => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun s u => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul', smul_eq_mul] }
  refine LinearEquiv.ofLinearMap toF invF ?_ ?_
  · apply LinearMap.ext; intro u; ext j
    simp only [LinearMap.comp_apply, LinearMap.id_apply, toF, invF, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
      Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_eq_of_ne hij.symm]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  · apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro s v
    change invF (toF (s ⊗ₜ[R] v)) = s ⊗ₜ[R] v
    simp only [toF, invF, LinearMap.coe_mk, AddHom.coe_mk,
      TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul]
    have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (s * algebraMap R S (v i)) ⊗ₜ[R] Pi.single i (1 : R) = s ⊗ₜ[R] (v i • Pi.single i 1)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]

/-- Helper map `(R ⧸ I) ⊗[R] M →ₗ[R] M ⧸ (I • ⊤)` detecting membership in `I • ⊤`. -/
lemma mem_ideal_smul_top_of_one_tmul_eq_zero {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] {m : M}
    (h0 : (1 : R ⧸ I) ⊗ₜ[R] m = 0) : m ∈ I • (⊤ : Submodule R M) := by
  let f₀ : R →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    { toFun := fun a =>
        { toFun := fun z => Submodule.Quotient.mk (a • z)
          map_add' := fun z₁ z₂ => by simp [smul_add]
          map_smul' := fun s z => by simp only [RingHom.id_apply, smul_comm a s z]; rfl }
      map_add' := fun a₁ a₂ => by ext z; simp [add_smul]
      map_smul' := fun s a => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
          mul_smul, RingHom.id_apply]
        rfl }
  let f : (R ⧸ I) →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.liftQ I f₀ (fun a ha => by
      rw [LinearMap.mem_ker]
      ext z
      simp only [f₀, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top))
  have hf0 := congrArg (TensorProduct.lift f) h0
  simp only [TensorProduct.lift.tmul, map_zero] at hf0
  have h1 : f (1 : R ⧸ I) m = Submodule.Quotient.mk m := by
    change f (Submodule.Quotient.mk (1 : R)) m = _
    rw [Submodule.liftQ_apply]
    simp [f₀]
  rw [h1] at hf0
  exact (Submodule.Quotient.mk_eq_zero _).mp hf0

lemma exists_one_tmul_eq {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] (w : (R ⧸ I) ⊗[R] M) :
    ∃ z : M, (1 : R ⧸ I) ⊗ₜ[R] z = w := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c z =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨a • z, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add w₁ w₂ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [TensorProduct.tmul_add, hz₁, hz₂]⟩

lemma module_finite_baseChange_of_finite {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite S (S ⊗[R] M) := by
  obtain ⟨m, g, hg⟩ := exists_finite_free_surj (R := R) M
  exact Module.Finite.of_surjective
    ((LinearMap.baseChange S g).comp (baseChangeFinEquiv R S m).symm.toLinearMap)
    ((LinearMap.lTensor_surjective S hg).comp (baseChangeFinEquiv R S m).symm.surjective)

/-- Tensoring with `ResidueField R` detects zero finitely generated modules over a local ring. -/
lemma eq_bot_of_tensor_residueField_subsingleton
    {R : Type} [CommRing R] [IsLocalRing R]
    {L : Type} [AddCommGroup L] [Module R L] [Module.Finite R L]
    (hsub : Subsingleton (ResidueField R ⊗[R] L)) : Subsingleton L := by
  have htop : (⊤ : Submodule R L) ≤ maximalIdeal R • (⊤ : Submodule R L) := by
    intro x _
    have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := Subsingleton.elim _ _
    exact mem_ideal_smul_top_of_one_tmul_eq_zero (maximalIdeal R) h0
  have hbot : (⊤ : Submodule R L) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R L)
      (Module.Finite.fg_top) htop
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  exact ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule R L) := hbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule R L) := hbot ▸ Submodule.mem_top
    simp only [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩

/-- Over a local ring, a finitely generated projective module is isomorphic to `Fin r → R`. -/
lemma exists_fin_equiv_of_projective_local {R : Type} [CommRing R] [IsLocalRing R]
    {Z : Type} [AddCommGroup Z] [Module R Z] [Module.Finite R Z] [Module.Projective R Z] :
    ∃ r : ℕ, Nonempty ((Fin r → R) ≃ₗ[R] Z) := by
  let k := ResidueField R
  let _ : Module.Finite k (k ⊗[R] Z) := module_finite_baseChange_of_finite (R := R) (S := k) Z
  let r := Module.finrank k (k ⊗[R] Z)
  let b := Module.finBasisOfFinrankEq k (k ⊗[R] Z) rfl
  choose z hz using fun i : Fin r => exists_one_tmul_eq (maximalIdeal R) (b i)
  let φ : (Fin r → R) →ₗ[R] Z := Fintype.linearCombination R z
  have hφ_surj : Function.Surjective φ := by
    let C := Z ⧸ LinearMap.range φ
    have hC_sub : Subsingleton (k ⊗[R] C) := by
      refine ⟨fun u v => ?_⟩
      have hzero (w : k ⊗[R] C) : w = 0 := by
        induction w using TensorProduct.induction_on with
        | zero => rfl
        | tmul c q =>
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
          have hby : c ⊗ₜ[R] y ∈ Submodule.span k (Set.range b) := by
            rw [b.span_eq]; exact Submodule.mem_top
          rw [Submodule.mem_span_range_iff_exists_fun] at hby
          obtain ⟨coeff, hcoeff⟩ := hby
          let π : k ⊗[R] Z →ₗ[k] k ⊗[R] C :=
            LinearMap.baseChange k (LinearMap.range φ).mkQ
          have hπ : π (c ⊗ₜ[R] y) = c ⊗ₜ[R] (LinearMap.range φ).mkQ y := rfl
          rw [← hπ, ← hcoeff, map_sum]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [map_smul, ← hz i]
          change coeff i • ((1 : k) ⊗ₜ[R] (LinearMap.range φ).mkQ (z i)) = 0
          have hmem : z i ∈ LinearMap.range φ :=
            ⟨Pi.single i 1, by simp [φ, Fintype.linearCombination_apply]⟩
          have hq0 : (LinearMap.range φ).mkQ (z i) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr hmem
          rw [hq0, TensorProduct.tmul_zero, smul_zero]
        | add w₁ w₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
      rw [hzero u, hzero v]
    have hC_sub' : Subsingleton C := eq_bot_of_tensor_residueField_subsingleton hC_sub
    intro y
    have h0 : (LinearMap.range φ).mkQ y = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφ_surj
  have hφs (y : Z) : φ (s y) = y := LinearMap.congr_fun hs y
  let e_split : (Fin r → R) ≃ₗ[R] (Z × LinearMap.ker φ) :=
    { toFun := fun v => (φ v, ⟨v - s (φ v), by
        rw [LinearMap.mem_ker, map_sub, hφs (φ v), sub_self]⟩)
      invFun := fun ⟨y, ⟨w, _⟩⟩ => s y + w
      map_add' := fun _ _ => by ext <;> simp; ring
      map_smul' := fun _ _ => by ext <;> simp [smul_sub]
      left_inv := fun v => by simp
      right_inv := fun ⟨y, ⟨w, hw⟩⟩ => by
        have hfw : φ w = 0 := LinearMap.mem_ker.mp hw
        ext
        · simp [hfw, hφs]
        · simp [hfw, hφs] }
  let _ : Module.Finite R (LinearMap.ker φ) :=
    Module.Finite.of_surjective ((LinearMap.snd R Z (LinearMap.ker φ)).comp e_split.toLinearMap)
      (Prod.snd_surjective.comp e_split.surjective)
  have hker_sub : Subsingleton (k ⊗[R] LinearMap.ker φ) := by
    let e_base : (k ⊗[R] (Fin r → R)) ≃ₗ[k] (k ⊗[R] Z) × (k ⊗[R] LinearMap.ker φ) :=
      (LinearEquiv.baseChange R k _ _ e_split).trans
        (TensorProduct.prodRight R k k Z (LinearMap.ker φ))
    have hfr1 : Module.finrank k (k ⊗[R] (Fin r → R)) = r := by
      rw [(baseChangeFinEquiv R k r).finrank_eq, Module.finrank_pi]
      simp
    have hfr2 : Module.finrank k ((k ⊗[R] Z) × (k ⊗[R] LinearMap.ker φ)) =
        r + Module.finrank k (k ⊗[R] LinearMap.ker φ) := by
      rw [Module.finrank_prod]
    have hfr_eq : Module.finrank k (k ⊗[R] LinearMap.ker φ) = 0 := by
      have h3 := e_base.finrank_eq
      rw [hfr1, hfr2] at h3
      omega
    exact Module.finrank_zero_iff.mp hfr_eq
  have hker_sub' : Subsingleton (LinearMap.ker φ) :=
    eq_bot_of_tensor_residueField_subsingleton hker_sub
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have h0 : (⟨v, hv⟩ : LinearMap.ker φ) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val h0
  exact ⟨r, ⟨LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩⟩⟩

/-- Every finitely generated module over a regular local ring has a finite projective resolution
of length at most `dim R`. -/
theorem hasFiniteProjRes_of_isRegularLocalRing_aux (d : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d →
      ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
        HasFiniteProjRes R d N := by
  induction d with
  | zero =>
    intro R _ _ h0 N _ _ _
    have hm_bot : maximalIdeal R = ⊥ := by
      have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
        have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), h0] at h2
        exact_mod_cast h2
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp
        (subsingleton_cotangentSpace_iff.mp (Module.finrank_zero_iff.mp h1))
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm_bot).toField
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    intro R _ _ hdim N _ _ _
    let _ : IsDomain R := isDomain_of_isRegularLocalRing R
    obtain ⟨x, hx, hx2, hx_ne⟩ := exists_param_of_isRegularLocalRing hdim
    let I := Ideal.span ({x} : Set R)
    have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_unique (h ▸ hI_le))
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨hreg_q, hdim_q⟩ := isRegularLocalRing_quotient_span_singleton hdim hx hx2
    -- Step 1: Cover N by a finite free R-module F, with kernel K (which is x-regular!)
    obtain ⟨r₀, f₀, hf₀⟩ := exists_finite_free_surj (R := R) N
    let F₀ := Fin r₀ → R
    let K := LinearMap.ker f₀
    let _ : IsNoetherian R F₀ := isNoetherian_of_isNoetherianRing_of_finite R F₀
    let _ : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hK_reg : ∀ y : K, x • y = 0 → y = 0 := fun y hy => by
      ext i
      have hi : x * y.val i = 0 := congrFun (congrArg Subtype.val hy) i
      exact (mul_eq_zero.mp hi).resolve_left hx_ne
    -- Step 2: Prove by inner induction on m that any f.g. x-regular R-module M with
    -- HasFiniteProjRes (R ⧸ I) m ((R ⧸ I) ⊗[R] M) satisfies HasFiniteProjRes R m M!
    have hdescent : ∀ (m : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
        (∀ y : M, x • y = 0 → y = 0) →
        HasFiniteProjRes (R ⧸ I) m ((R ⧸ I) ⊗[R] M) →
        HasFiniteProjRes R m M := by
      intro m
      induction m with
      | zero =>
        intro M _ _ _ hregM hresM
        obtain ⟨hfin_q, hproj_q⟩ := hresM
        obtain ⟨r, ⟨e_q⟩⟩ := exists_fin_equiv_of_projective_local (R := R ⧸ I) (Z := (R ⧸ I) ⊗[R] M)
        choose z hz using fun i : Fin r => exists_one_tmul_eq I (e_q (Pi.single i 1))
        let φ : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R z
        have hbase_eq : LinearMap.baseChange (R ⧸ I) φ =
            e_q.toLinearMap.comp (baseChangeFinEquiv R (R ⧸ I) r).toLinearMap := by
          apply LinearMap.restrictScalars_injective R
          apply TensorProduct.ext'
          intro c v
          change LinearMap.baseChange (R ⧸ I) φ (c ⊗ₜ[R] v) =
            e_q (baseChangeFinEquiv R (R ⧸ I) r (c ⊗ₜ[R] v))
          rw [LinearMap.baseChange_tmul]
          have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
            ext j; simp [Finset.sum_apply, Pi.single_apply]
          conv_lhs => rw [hv, map_sum]
          rw [TensorProduct.tmul_sum]
          have h1 : ∀ i : Fin r, c ⊗ₜ[R] φ (v i • Pi.single i 1) =
              (c * Ideal.Quotient.mk I (v i)) • e_q (Pi.single i 1) := by
            intro i
            rw [map_smul, TensorProduct.tmul_smul]
            have hφi : φ (Pi.single i 1) = z i := by
              simp [φ, Fintype.linearCombination_apply]
            rw [hφi]
            have hc : c ⊗ₜ[R] z i = c • ((1 : R ⧸ I) ⊗ₜ[R] z i) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [hc, hz i, ← smul_assoc]
            congr 1
            rw [Algebra.smul_def, mul_comm]
            rfl
          simp_rw [h1, ← map_smul]
          rw [← map_sum]
          congr 1
          ext j
          simp [baseChangeFinEquiv, Finset.sum_apply, Pi.single_apply]
        have hbase_bij : Function.Bijective (LinearMap.baseChange (R ⧸ I) φ) := by
          rw [hbase_eq]
          exact e_q.bijective.comp (baseChangeFinEquiv R (R ⧸ I) r).bijective
        have hφ_surj : Function.Surjective φ := by
          let C := M ⧸ LinearMap.range φ
          have htop : (⊤ : Submodule R C) ≤ maximalIdeal R • (⊤ : Submodule R C) := by
            intro u _
            obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ u
            obtain ⟨t, ht⟩ := hbase_bij.2 ((1 : R ⧸ I) ⊗ₜ[R] y)
            obtain ⟨v, rfl⟩ := exists_one_tmul_eq I t
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] (y - φ v) = 0 := by
              rw [TensorProduct.tmul_sub, ← ht]; simp
            have hmemI : y - φ v ∈ I • (⊤ : Submodule R M) :=
              mem_ideal_smul_top_of_one_tmul_eq_zero I h0
            have hmem_m : y - φ v ∈ maximalIdeal R • (⊤ : Submodule R M) :=
              Submodule.smul_mono_left hI_le hmemI
            have hmk0 : (LinearMap.range φ).mkQ (φ v) = 0 :=
              (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
            have hmk : (LinearMap.range φ).mkQ y = (LinearMap.range φ).mkQ (y - φ v) := by
              rw [map_sub, hmk0, sub_zero]
            rw [hmk]
            refine Submodule.smul_induction_on hmem_m ?_ ?_
            · intro a ha m _
              rw [map_smul]
              exact Submodule.smul_mem_smul ha Submodule.mem_top
            · intro m₁ m₂ hm₁ hm₂
              rw [map_add]
              exact Submodule.add_mem _ hm₁ hm₂
          have hbot : (⊤ : Submodule R C) = ⊥ :=
            Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (⊤ : Submodule R C)
              (Module.Finite.fg_top) htop
              (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
          intro y
          have h0 : (LinearMap.range φ).mkQ y = 0 := by
            have hmem : (LinearMap.range φ).mkQ y ∈ (⊥ : Submodule R C) := hbot ▸ Submodule.mem_top
            simpa using hmem
          exact (Submodule.Quotient.mk_eq_zero _).mp h0
        have hker_le : LinearMap.ker φ ≤ maximalIdeal R • LinearMap.ker φ := by
          intro v hv
          have h0 : LinearMap.baseChange (R ⧸ I) φ ((1 : R ⧸ I) ⊗ₜ[R] v) = 0 := by
            rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, TensorProduct.tmul_zero]
          have h1 : (1 : R ⧸ I) ⊗ₜ[R] v = 0 := hbase_bij.1 (h0.trans (map_zero _).symm)
          have hcoord (i : Fin r) : v i ∈ I := by
            have hev := congrFun (congrArg (baseChangeFinEquiv R (R ⧸ I) r) h1) i
            simp only [baseChangeFinEquiv, map_zero, Pi.zero_apply] at hev
            change (1 : R ⧸ I) * Ideal.Quotient.mk I (v i) = 0 at hev
            rw [one_mul] at hev
            exact Ideal.Quotient.eq_zero_iff_mem.mp hev
          choose w hw using fun i : Fin r => Ideal.mem_span_singleton.mp (hcoord i)
          have hv_eq : v = x • w := by ext i; exact hw i
          have hw_ker : w ∈ LinearMap.ker φ := by
            rw [LinearMap.mem_ker]
            apply hregM (φ w)
            rw [← map_smul, ← hv_eq]
            exact LinearMap.mem_ker.mp hv
          rw [hv_eq]
          exact Submodule.smul_mem_smul hx hw_ker
        have hker_bot : LinearMap.ker φ = ⊥ :=
          Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (LinearMap.ker φ)
            (IsNoetherian.noetherian _) hker_le
            (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
        have hφ_inj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker_bot
        exact hasFiniteProjRes_of_equiv (LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩)
          ⟨inferInstance, inferInstance⟩
      | succ k ihk =>
        intro M _ _ _ hregM hresM
        obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) M
        let G := Fin r → R
        let L := LinearMap.ker g
        let _ : IsNoetherian R G := isNoetherian_of_isNoetherianRing_of_finite R G
        let _ : Module.Finite R L := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
        have hL_reg : ∀ y : L, x • y = 0 → y = 0 := fun y hy => by
          ext i
          have hi : x * y.val i = 0 := congrFun (congrArg Subtype.val hy) i
          exact (mul_eq_zero.mp hi).resolve_left hx_ne
        let gq : ((R ⧸ I) ⊗[R] G) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) := LinearMap.baseChange (R ⧸ I) g
        have hgq_surj : Function.Surjective gq := LinearMap.lTensor_surjective (R ⧸ I) hg
        let _ : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] G) :=
          Module.Finite.equiv (baseChangeFinEquiv R (R ⧸ I) r).symm
        let _ : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] G) :=
          Module.Projective.of_equiv (baseChangeFinEquiv R (R ⧸ I) r).symm
        have hker_gq : HasFiniteProjRes (R ⧸ I) k (LinearMap.ker gq) :=
          hasFiniteProjRes_ker_of_succ k ((R ⧸ I) ⊗[R] M) ((R ⧸ I) ⊗[R] G) gq hgq_surj hresM
        let ιq : ((R ⧸ I) ⊗[R] L) →ₗ[R ⧸ I] LinearMap.ker gq :=
          LinearMap.codRestrict (LinearMap.ker gq) (LinearMap.baseChange (R ⧸ I) L.subtype) (fun t => by
            rw [LinearMap.mem_ker]
            induction t using TensorProduct.induction_on with
            | zero => simp
            | tmul c y =>
              simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype, gq]
              rw [LinearMap.mem_ker.mp y.property, TensorProduct.tmul_zero]
            | add t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂])
        have hιq_bij : Function.Bijective ιq := by
          constructor
          · rw [injective_iff_map_eq_zero]
            intro t ht
            obtain ⟨y, rfl⟩ := exists_one_tmul_eq I t
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] y.val = 0 := congrArg Subtype.val ht
            have hcoord (i : Fin r) : y.val i ∈ I := by
              have hev := congrFun (congrArg (baseChangeFinEquiv R (R ⧸ I) r) h0) i
              simp only [baseChangeFinEquiv, map_zero, Pi.zero_apply] at hev
              change (1 : R ⧸ I) * Ideal.Quotient.mk I (y.val i) = 0 at hev
              rw [one_mul] at hev
              exact Ideal.Quotient.eq_zero_iff_mem.mp hev
            choose w hw using fun i : Fin r => Ideal.mem_span_singleton.mp (hcoord i)
            have hy_eq : y.val = x • w := by ext i; exact hw i
            have hw_L : w ∈ L := by
              rw [LinearMap.mem_ker]
              apply hregM (g w)
              rw [← map_smul, ← hy_eq]
              exact LinearMap.mem_ker.mp y.property
            have hy' : y = x • ⟨w, hw_L⟩ := Subtype.ext hy_eq
            rw [hy', ← TensorProduct.smul_tmul]
            have hx0 : x • (1 : R ⧸ I) = 0 := by
              rw [Algebra.smul_def, mul_one]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
            rw [hx0, TensorProduct.zero_tmul]
          · rintro ⟨u, hu⟩
            obtain ⟨v, rfl⟩ := exists_one_tmul_eq I u
            have h0 : (1 : R ⧸ I) ⊗ₜ[R] g v = 0 := LinearMap.mem_ker.mp hu
            have hmemI : g v ∈ I • (⊤ : Submodule R M) :=
              mem_ideal_smul_top_of_one_tmul_eq_zero I h0
            have hex_m : ∃ m : M, x • m = g v := by
              refine Submodule.smul_induction_on hmemI ?_ ?_
              · intro a ha m _
                obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
                exact ⟨c • m, by rw [smul_smul]⟩
              · rintro _ _ ⟨m₁, rfl⟩ ⟨m₂, rfl⟩
                exact ⟨m₁ + m₂, by rw [smul_add]⟩
            obtain ⟨m, hm⟩ := hex_m
            obtain ⟨w, rfl⟩ := hg m
            have hv_mem : v - x • w ∈ L := by
              rw [LinearMap.mem_ker, map_sub, map_smul, hm, sub_self]
            refine ⟨(1 : R ⧸ I) ⊗ₜ[R] ⟨v - x • w, hv_mem⟩, Subtype.ext ?_⟩
            change (1 : R ⧸ I) ⊗ₜ[R] (v - x • w) = (1 : R ⧸ I) ⊗ₜ[R] v
            rw [TensorProduct.tmul_sub, ← TensorProduct.smul_tmul]
            have hx0 : x • (1 : R ⧸ I) = 0 := by
              rw [Algebra.smul_def, mul_one]
              exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
            rw [hx0, TensorProduct.zero_tmul, sub_zero]
        have hresL : HasFiniteProjRes (R ⧸ I) k ((R ⧸ I) ⊗[R] L) :=
          hasFiniteProjRes_of_equiv (LinearEquiv.ofBijective ιq hιq_bij).symm hker_gq
        exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, g, hg,
          ihk L hL_reg hresL⟩
    let _ : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] K) :=
      module_finite_baseChange_of_finite (R := R) (S := R ⧸ I) K
    have hK_q : HasFiniteProjRes (R ⧸ I) n ((R ⧸ I) ⊗[R] K) :=
      ih (R ⧸ I) hdim_q ((R ⧸ I) ⊗[R] K)
    have hK_res : HasFiniteProjRes R n K := hdescent n K hK_reg hK_q
    exact ⟨F₀, inferInstance, inferInstance, inferInstance, inferInstance, f₀, hf₀, hK_res⟩

theorem hasFiniteProjRes_of_isRegularLocalRing
    (R : Type) [CommRing R] [IsRegularLocalRing R]
    (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] :
    HasFiniteProjRes R (maximalIdeal R).spanFinrank N :=
  hasFiniteProjRes_of_isRegularLocalRing_aux (maximalIdeal R).spanFinrank R rfl N

end FiniteProjRes

section TorLES

/-- Abbreviation for `Tor_i^R(M, N)` in `ModuleCat.{0} R`. -/
noncomputable abbrev torMod (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) : ModuleCat.{0} R :=
  ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- Functorial map on `Tor_i^R(M, -)` induced by a linear map `f : A →ₗ[R] B`. -/
noncomputable def torMap {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (i : ℕ) :
    torMod R M A i →ₗ[R] torMod R M B i :=
  (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom

/-- `Tor_0^R(M, N) ≃ₗ[R] M ⊗[R] N`. -/
noncomputable def torZeroEquiv (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    torMod R M N 0 ≃ₗ[R] (M ⊗[R] N) :=
  (((tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app
    (ModuleCat.of R N)).toLinearEquiv

lemma torZeroEquiv_naturality {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (x : torMod R M A 0) :
    torZeroEquiv R M B (torMap M f 0 x) = LinearMap.lTensor M f (torZeroEquiv R M A x) := by
  have hnat := (((tensoringLeft (ModuleCat.{0} R)).obj
    (ModuleCat.of R M)).leftDerivedZeroIsoSelf.hom.naturality (ModuleCat.ofHom f))
  exact congrArg (fun φ : torMod R M A 0 ⟶ ModuleCat.of R (M ⊗[R] B) => φ.hom x) hnat

lemma tor_succ_subsingleton_of_projective {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (i : ℕ) :
    Subsingleton (torMod R M N (i + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_Tor_succ_of_projective (ModuleCat.{0} R) (ModuleCat.of R M) (ModuleCat.of R N) i)

/-- Build a `ProjectiveResolution` from a projective chain complex whose `H_0` is `B` via `ε`
and `H_{n+1} = 0`. -/
noncomputable def projectiveResolutionOfExact {R : Type} [CommRing R]
    (B : Type) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{0} R) ℕ)
    (hproj : ∀ n, Module.Projective R (K.X n))
    (ε : (K.X 0) →ₗ[R] B)
    (hε_surj : Function.Surjective ε)
    (hε_comp : ∀ x : K.X 1, ε ((K.d 1 0).hom x) = 0)
    (hε_exact : ∀ x : K.X 0, ε x = 0 → ∃ y : K.X 1, (K.d 1 0).hom y = x)
    (hexact : ∀ n : ℕ, ∀ x : K.X (n + 1), (K.d (n + 1) n).hom x = 0 →
      ∃ y : K.X (n + 2), (K.d (n + 2) (n + 1)).hom y = x) :
    ProjectiveResolution (ModuleCat.of R B) := by
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B) :=
    (ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, by ext x; exact hε_comp x⟩
  have hπ0 : (π.f 0).hom = ε := by
    change ((ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, _⟩ |>.f 0).hom = ε
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have hq : QuasiIso π := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      -- In degree 0, both K.sc 0 and single₀.sc 0 have g = 0, so homologyι is an iso to opcycles!
      have hK_g0 : (K.sc 0).g = 0 := K.shape 0 _ (by simp)
      have hS_g0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).g = 0 :=
        ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).shape 0 _ (by simp)
      have _ : IsIso (K.homologyι 0) := ShortComplex.isIso_homologyι (K.sc 0) hK_g0
      have _ : IsIso (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) :=
        ShortComplex.isIso_homologyι _ hS_g0
      have hcomm : (HomologicalComplex.homologyMap π 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) =
          (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0) :=
        HomologicalComplex.homologyι_naturality π 0
      have hop_bij : Function.Bijective (HomologicalComplex.opcyclesMap π 0).hom := by
        constructor
        · intro u v huv
          have hp_surj : Function.Surjective (K.pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance
          obtain ⟨x, rfl⟩ := hp_surj u
          obtain ⟨y, rfl⟩ := hp_surj v
          have hsub : HomologicalComplex.opcyclesMap π 0 (K.pOpcycles 0 (x - y)) = 0 := by
            change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) = 0
            rw [map_sub, map_sub, huv, sub_self]
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom (x - y)) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom (x - y))
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          rw [hnat] at hsub
          have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).mp hsub
          have hSf0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f = 0 := by
            simp [HomologicalComplex.sc]; rfl
          obtain ⟨w, hw⟩ := hmem
          have hε0 : ε (x - y) = 0 := by
            rw [← hπ0]
            have hw0 : ((((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f).hom w = 0 := by
              rw [hSf0]; rfl
            exact hw.symm.trans hw0
          obtain ⟨z, hz⟩ := hε_exact (x - y) hε0
          have h0 : (K.pOpcycles 0).hom (x - y) = 0 := by
            rw [← hz]
            exact congrArg (fun φ : K.X 1 ⟶ K.opcycles 0 => φ.hom z) (K.d_pOpcycles 1 0)
          rw [map_sub] at h0
          exact sub_eq_zero.mp h0
        · intro w
          have hpS_surj : Function.Surjective
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          obtain ⟨b, rfl⟩ := hpS_surj w
          obtain ⟨x, hx⟩ := hε_surj b
          refine ⟨K.pOpcycles 0 x, ?_⟩
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom x) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom x)
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) = _
          rw [hnat]
          have hxb : (π.f 0).hom x = b := by
            have h1 : (π.f 0).hom x = ε x := LinearMap.congr_fun hπ0 x
            exact h1.trans hx
          exact congrArg
            (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom hxb
      have hop_iso : IsIso (HomologicalComplex.opcyclesMap π 0) :=
        ⟨ModuleCat.ofHom (LinearEquiv.ofBijective _ hop_bij).symm.toLinearMap,
          by ext u; exact (LinearEquiv.ofBijective _ hop_bij).left_inv u,
          by ext v; exact (LinearEquiv.ofBijective _ hop_bij).right_inv v⟩
      have hmul : HomologicalComplex.homologyMap π 0 =
          K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0 ≫
            inv (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) := by
        rw [← Category.assoc, ← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [hmul]
      infer_instance
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' π (m + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (m + 2) (m + 1) m (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      exact hexact m
  exact
    { complex := K
      projective := fun n => by
        let _ := hproj n
        infer_instance
      π := π
      quasiIso := hq }

/-- Exactness of `torMap` and connecting homomorphism for a short exact sequence `0 → A → B → C → 0`. -/
lemma horseshoe_tor_les {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : LinearMap.range i = LinearMap.ker p) :
    ∃ δ : ∀ n : ℕ, torMod R M C (n + 1) →ₗ[R] torMod R M A n,
      (∀ n, Function.Exact (δ n) (torMap M i n)) ∧
      (∀ n, Function.Exact (torMap M i n) (torMap M p n)) ∧
      (∀ n, Function.Exact (torMap M p (n + 1)) (δ n)) := by
  let PA : ProjectiveResolution (ModuleCat.of R A) := projectiveResolution (ModuleCat.of R A)
  let PC : ProjectiveResolution (ModuleCat.of R C) := projectiveResolution (ModuleCat.of R C)
  have hPA_proj (n : ℕ) : Module.Projective R (PA.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PA.complex.X n)
  have hPC_proj (n : ℕ) : Module.Projective R (PC.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PC.complex.X n)
  let εA : PA.complex.X 0 →ₗ[R] A := (PA.π.f 0).hom
  let εC : PC.complex.X 0 →ₗ[R] C := (PC.π.f 0).hom
  have hεA_surj : Function.Surjective εA :=
    (ModuleCat.epi_iff_surjective (PA.π.f 0)).mp inferInstance
  have hεC_surj : Function.Surjective εC :=
    (ModuleCat.epi_iff_surjective (PC.π.f 0)).mp inferInstance
  have hεA_comp (x : PA.complex.X 1) : εA ((PA.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X 1 ⟶ ModuleCat.of R A => φ.hom x) PA.complex_d_comp_π_f_zero
  have hεC_comp (x : PC.complex.X 1) : εC ((PC.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X 1 ⟶ ModuleCat.of R C => φ.hom x) PC.complex_d_comp_π_f_zero
  have hε_exact_of_res {X : Type} [AddCommGroup X] [Module R X]
      (PX : ProjectiveResolution (ModuleCat.of R X)) (x : PX.complex.X 0)
      (hx : (PX.π.f 0).hom x = 0) :
      ∃ y : PX.complex.X 1, (PX.complex.d 1 0).hom y = x := by
    -- Since PX.isColimitCokernelCofork is a colimit, the canonical quotient map factors through π.f 0!
    let Q := PX.complex.X 0 ⧸ LinearMap.range (PX.complex.d 1 0).hom
    let q : PX.complex.X 0 ⟶ ModuleCat.of R Q := ModuleCat.ofHom (LinearMap.range (PX.complex.d 1 0).hom).mkQ
    have hqw : (PX.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of R X ⟶ ModuleCat.of R Q :=
      PX.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PX.π.f 0 ≫ desc) = q :=
      PX.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PX.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PX.complex.X 0 ⟶ ModuleCat.of R Q => φ.hom x) hfac
      have hx0 : (PX.π.f 0).hom x = (0 : X) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hεA_exact := hε_exact_of_res PA
  have hεC_exact := hε_exact_of_res PC
  have hPA_exact (n : ℕ) (x : PA.complex.X (n + 1)) (hx : (PA.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PA.complex.X (n + 2), (PA.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PA.exact_succ n) x hx
  have hPC_exact (n : ℕ) (x : PC.complex.X (n + 1)) (hx : (PC.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PC.complex.X (n + 2), (PC.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PC.exact_succ n) x hx
  have hPA_dd (n : ℕ) (x : PA.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X (n + 2) ⟶ PA.complex.X n => φ.hom x)
      (PA.complex.d_comp_d (n + 2) (n + 1) n)
  have hPC_dd (n : ℕ) (x : PC.complex.X (n + 2)) :
      (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X (n + 2) ⟶ PC.complex.X n => φ.hom x)
      (PC.complex.d_comp_d (n + 2) (n + 1) n)
  -- Lift εC to s0 : PC.X 0 → B with p ∘ s0 = εC
  let _ := hPC_proj 0
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property p εC hp
  let εB : (PA.complex.X 0 × PC.complex.X 0) →ₗ[R] B := (i.comp εA).coprod s0
  -- Base lift h0 : PC.X 1 → PA.X 0
  have h_step0 : ∃ h0 : PC.complex.X 1 →ₗ[R] PA.complex.X 0,
      ∀ c : PC.complex.X 1, i (εA (h0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 := by
    let _ := hPC_proj 1
    let neg_s0_dC : PC.complex.X 1 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (-(s0.comp (PC.complex.d 1 0).hom)) (fun c => by
        rw [LinearMap.mem_ker, LinearMap.neg_apply, map_neg, LinearMap.comp_apply]
        have h1 : p (s0 ((PC.complex.d 1 0).hom c)) = εC ((PC.complex.d 1 0).hom c) :=
          LinearMap.congr_fun hs0 _
        rw [h1, hεC_comp, neg_zero])
    let mapA : PA.complex.X 0 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (i.comp εA) (fun a => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ← hip]
        exact ⟨εA a, rfl⟩)
    have hmapA_surj : Function.Surjective mapA := by
      rintro ⟨b, hb⟩
      rw [← hip] at hb
      obtain ⟨a, rfl⟩ := hb
      obtain ⟨x, rfl⟩ := hεA_surj a
      exact ⟨x, rfl⟩
    obtain ⟨h0, hh0⟩ := Module.projective_lifting_property mapA neg_s0_dC hmapA_surj
    refine ⟨h0, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hh0 c)
    change i (εA (h0 c)) = -(s0 ((PC.complex.d 1 0).hom c)) at hc
    rw [hc, neg_add_cancel]
  -- Inductive lift step
  have h_next : ∀ (n : ℕ) (hcur : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
      (∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
        (PA.complex.d (n + 1) n).hom a = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c))) →
      ∃ hnxt : PC.complex.X (n + 2) →ₗ[R] PA.complex.X (n + 1),
        ∀ c : PC.complex.X (n + 2),
          (PA.complex.d (n + 1) n).hom (hnxt c) + hcur ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 := by
    intro n hcur hpre
    let _ := hPC_proj (n + 2)
    let targ : PC.complex.X (n + 2) →ₗ[R] LinearMap.range (PA.complex.d (n + 1) n).hom :=
      LinearMap.codRestrict _ (-(hcur.comp (PC.complex.d (n + 2) (n + 1)).hom)) (fun c => hpre c)
    obtain ⟨hnxt, hhnxt⟩ := Module.projective_lifting_property
      (LinearMap.rangeRestrict (PA.complex.d (n + 1) n).hom) targ
      (LinearMap.surjective_rangeRestrict _)
    refine ⟨hnxt, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hhnxt c)
    change (PA.complex.d (n + 1) n).hom (hnxt c) = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c)) at hc
    rw [hc, neg_add_cancel]
  -- Build h n : PC.X (n + 1) → PA.X n together with the preimage invariant
  let buildAux : ∀ n : ℕ,
      Σ' (h : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
        ∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
          (PA.complex.d (n + 1) n).hom a = -(h ((PC.complex.d (n + 2) (n + 1)).hom c)) :=
    Nat.rec
      ⟨Classical.choose h_step0, fun c => by
        have h0 := Classical.choose_spec h_step0 ((PC.complex.d 2 1).hom c)
        rw [hPC_dd 0 c, map_zero, add_zero] at h0
        have he : εA (-(Classical.choose h_step0 ((PC.complex.d 2 1).hom c))) = 0 := by
          rw [map_neg, hi (h0.trans (map_zero i).symm), neg_zero]
        exact hεA_exact _ he⟩
      (fun n prev =>
        let hex := h_next n prev.1 prev.2
        ⟨Classical.choose hex, fun c => by
          have h1 := Classical.choose_spec hex ((PC.complex.d (n + 3) (n + 2)).hom c)
          rw [hPC_dd (n + 1) c, map_zero, add_zero] at h1
          have hneg : (PA.complex.d (n + 1) n).hom
              (-(Classical.choose hex ((PC.complex.d (n + 3) (n + 2)).hom c))) = 0 := by
            rw [map_neg, h1, neg_zero]
          exact hPA_exact n _ hneg⟩)
  let h (n : ℕ) : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n := (buildAux n).1
  have hh0 (c : PC.complex.X 1) :
      i (εA (h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 :=
    Classical.choose_spec h_step0 c
  have hh_succ (n : ℕ) (c : PC.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom (h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 :=
    Classical.choose_spec (h_next n (buildAux n).1 (buildAux n).2) c
  -- Build the chain complex KB with KB.X n = PA.X n × PC.X n
  let dB (n : ℕ) : ModuleCat.of R (PA.complex.X (n + 1) × PC.complex.X (n + 1)) ⟶
      ModuleCat.of R (PA.complex.X n × PC.complex.X n) :=
    ModuleCat.ofHom
      { toFun := fun x => ((PA.complex.d (n + 1) n).hom x.1 + h n x.2, (PC.complex.d (n + 1) n).hom x.2)
        map_add' := fun x y => by
          ext
          · change (PA.complex.d (n + 1) n).hom (x.1 + y.1) + h n (x.2 + y.2) =
              ((PA.complex.d (n + 1) n).hom x.1 + h n x.2) + ((PA.complex.d (n + 1) n).hom y.1 + h n y.2)
            rw [map_add, map_add]; abel
          · exact map_add (PC.complex.d (n + 1) n).hom x.2 y.2
        map_smul' := fun r x => by
          ext
          · change (PA.complex.d (n + 1) n).hom (r • x.1) + h n (r • x.2) =
              r • ((PA.complex.d (n + 1) n).hom x.1 + h n x.2)
            rw [map_smul, map_smul, smul_add]
          · exact map_smul (PC.complex.d (n + 1) n).hom r x.2 }
  have hdB_sq (n : ℕ) : (dB (n + 1) ≫ dB n) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    ext
    · change (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom a + h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      rw [map_add, hPA_dd n a, zero_add, hh_succ n c]
    · change (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      exact hPC_dd n c
  let KB : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R (PA.complex.X n × PC.complex.X n)) dB hdB_sq
  -- Short exact sequence of chain complexes 0 → PA → KB → PC → 0
  let ιK : PA.complex ⟶ KB :=
    { f := fun n => ModuleCat.ofHom (LinearMap.inl R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        ext
        · change ((KB.d (m + 1) m).hom (a, 0)).1 = (PA.complex.d (m + 1) m).hom a
          simp [KB, ChainComplex.of_d, dB]
        · change ((KB.d (m + 1) m).hom (a, 0)).2 = 0
          simp [KB, ChainComplex.of_d, dB] }
  let πK : KB ⟶ PC.complex :=
    { f := fun n => ModuleCat.ofHom (LinearMap.snd R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨a, c⟩
        change (PC.complex.d (m + 1) m).hom c = ((KB.d (m + 1) m).hom (a, c)).2
        simp [KB, ChainComplex.of_d, dB] }
  have hS_zero : (ιK ≫ πK) = 0 := by
    ext n a
    rfl
  let SK : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) := ShortComplex.mk ιK πK hS_zero
  -- Check KB is a ProjectiveResolution of B via εB!
  have hKB_proj (n : ℕ) : Module.Projective R (KB.X n) := by
    let _ := hPA_proj n
    let _ := hPC_proj n
    change Module.Projective R (PA.complex.X n × PC.complex.X n)
    infer_instance
  have hps0 (c : PC.complex.X 0) : p (s0 c) = εC c := LinearMap.congr_fun hs0 c
  have hεB_surj : Function.Surjective εB := fun b => by
    obtain ⟨c, hc⟩ := hεC_surj (p b)
    have hker : b - s0 c ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, hps0 c, hc, sub_self]
    rw [← hip] at hker
    obtain ⟨a0, ha0⟩ := hker
    obtain ⟨a, rfl⟩ := hεA_surj a0
    refine ⟨(a, c), ?_⟩
    change i (εA a) + s0 c = b
    rw [ha0, sub_add_cancel]
  have hεB_comp (x : KB.X 1) : εB ((KB.d 1 0).hom x) = 0 := by
    rcases x with ⟨a, c⟩
    change i (εA ((PA.complex.d 1 0).hom a + h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0
    rw [map_add, map_add, hεA_comp a, map_zero, zero_add, hh0 c]
  have hεB_exact (x : KB.X 0) (hx : εB x = 0) : ∃ y : KB.X 1, (KB.d 1 0).hom y = x := by
    rcases x with ⟨a, c⟩
    change i (εA a) + s0 c = 0 at hx
    have hpc : εC c = 0 := by
      have hp0 := congrArg p hx
      rw [map_add, map_zero, hps0 c] at hp0
      have hi0 : p (i (εA a)) = 0 := by
        rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
      rw [hi0, zero_add] at hp0
      exact hp0
    obtain ⟨c1, hc1⟩ := hεC_exact c hpc
    have ha_ker : εA (a - h 0 c1) = 0 := by
      apply hi
      rw [map_zero, map_sub, map_sub]
      have h1 := hh0 c1
      rw [hc1] at h1
      have hia : i (εA a) = - s0 c := eq_neg_of_add_eq_zero_left hx
      have hih : i (εA (h 0 c1)) = - s0 c := eq_neg_of_add_eq_zero_left h1
      rw [hia, hih, sub_self]
    obtain ⟨a1, ha1⟩ := hεA_exact _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    change ((PA.complex.d 1 0).hom a1 + h 0 c1, (PC.complex.d 1 0).hom c1) = (a, c)
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  have hKB_exact (n : ℕ) (x : KB.X (n + 1)) (hx : (KB.d (n + 1) n).hom x = 0) :
      ∃ y : KB.X (n + 2), (KB.d (n + 2) (n + 1)).hom y = x := by
    rcases x with ⟨a, c⟩
    have hx' : ((PA.complex.d (n + 1) n).hom a + h n c, (PC.complex.d (n + 1) n).hom c) = (0, 0) := by
      simpa [KB, ChainComplex.of_d, dB] using hx
    have hx1 : (PA.complex.d (n + 1) n).hom a + h n c = 0 := congrArg Prod.fst hx'
    have hx2 : (PC.complex.d (n + 1) n).hom c = 0 := congrArg Prod.snd hx'
    obtain ⟨c1, hc1⟩ := hPC_exact n c hx2
    have ha_ker : (PA.complex.d (n + 1) n).hom (a - h (n + 1) c1) = 0 := by
      rw [map_sub]
      have h1 := hh_succ n c1
      rw [hc1] at h1
      have h2 : (PA.complex.d (n + 1) n).hom a = - h n c := eq_neg_of_add_eq_zero_left hx1
      have h3 : (PA.complex.d (n + 1) n).hom (h (n + 1) c1) = - h n c := eq_neg_of_add_eq_zero_left h1
      rw [h2, h3, sub_self]
    obtain ⟨a1, ha1⟩ := hPA_exact n _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    have hd_eq : (KB.d (n + 2) (n + 1)).hom (a1, c1) =
        ((PA.complex.d (n + 2) (n + 1)).hom a1 + h (n + 1) c1,
          (PC.complex.d (n + 2) (n + 1)).hom c1) :=
      congrArg (fun φ : KB.X (n + 2) ⟶ KB.X (n + 1) => φ.hom (a1, c1))
        (ChainComplex.of_d _ dB (n + 1))
    rw [hd_eq]
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  let PB : ProjectiveResolution (ModuleCat.of R B) :=
    projectiveResolutionOfExact B KB hKB_proj εB hεB_surj hεB_comp hεB_exact hKB_exact
  have hcomm_i : (ιK.f 0 ≫ PB.π.f 0) = (PA.π.f 0 ≫ ModuleCat.ofHom i) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change εB (a, 0) = i (εA a)
    simp [εB]
  have hcomm_p : (πK.f 0 ≫ PC.π.f 0) = (PB.π.f 0 ≫ ModuleCat.ofHom p) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    change εC c = p (εB (a, c))
    simp only [εB, LinearMap.coprod_apply, map_add, LinearMap.comp_apply]
    have hi0 : p (i (εA a)) = 0 := by
      rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
    rw [hi0, zero_add, hps0 c]
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let SM : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
    SK.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hSM_exact : SM.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let split_n : (SK.map (HomologicalComplex.eval _ _ n)).Splitting :=
      { r := ModuleCat.ofHom (LinearMap.fst R (PA.complex.X n) (PC.complex.X n))
        s := ModuleCat.ofHom (LinearMap.inr R (PA.complex.X n) (PC.complex.X n))
        f_r := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl
        s_g := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; rfl
        id := by
          apply ModuleCat.hom_ext; apply LinearMap.ext; rintro ⟨a, c⟩
          change (a, 0) + (0, c) = (a, c)
          ext <;> simp }
    let split_Mn : (SM.map (HomologicalComplex.eval _ _ n)).Splitting :=
      split_n.map F
    exact split_Mn.shortExact
  let eA (n : ℕ) : torMod R M A n ≅ SM.X₁.homology n := PA.isoLeftDerivedObj F n
  let eB (n : ℕ) : torMod R M B n ≅ SM.X₂.homology n := PB.isoLeftDerivedObj F n
  let eC (n : ℕ) : torMod R M C n ≅ SM.X₃.homology n := PC.isoLeftDerivedObj F n
  let δ (n : ℕ) : torMod R M C (n + 1) →ₗ[R] torMod R M A n :=
    ((eC (n + 1)).hom ≫ hSM_exact.δ (n + 1) n rfl ≫ (eA n).inv).hom
  have htor_i_hom (n : ℕ) (x : torMod R M A n) :
      (eB n).hom.hom (torMap M i n x) = (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) :=
    congrArg (fun φ : torMod R M A n ⟶ SM.X₂.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom i) PA PB ιK hcomm_i F n)
  have htor_p_hom (n : ℕ) (x : torMod R M B n) :
      (eC n).hom.hom (torMap M p n x) = (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) :=
    congrArg (fun φ : torMod R M B n ⟶ SM.X₃.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom p) PB PC πK hcomm_p F n)
  have iso_hom_inv {X Y : ModuleCat.{0} R} (e : X ≅ Y) (y : Y) :
      e.hom.hom (e.inv.hom y) = y :=
    congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
  have iso_inv_hom {X Y : ModuleCat.{0} R} (e : X ≅ Y) (x : X) :
      e.inv.hom (e.hom.hom x) = x :=
    congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₁ (n + 1) n rfl)
    have h1 : torMap M i n x = 0 ↔
        (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) = 0 := by
      rw [← htor_i_hom n x]
      exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eA n).hom.hom x) hx
      refine ⟨(eC (n + 1)).inv.hom y, ?_⟩
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom ((eC (n + 1)).inv.hom y))) = x
      rw [iso_hom_inv (eC (n + 1)) y, hy]
      exact iso_inv_hom (eA n) x
    · rintro ⟨z, rfl⟩
      have hcomp := congrArg (fun φ : SM.X₃.homology (n + 1) ⟶ SM.X₂.homology n =>
        φ.hom ((eC (n + 1)).hom.hom z)) (hSM_exact.δ_comp (n + 1) n rfl)
      change (HomologicalComplex.homologyMap SM.f n).hom
        ((eA n).hom.hom ((eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom z)))) = 0
      rw [iso_hom_inv (eA n)]
      exact hcomp
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₂ n)
    have h1 : torMap M p n x = 0 ↔
        (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) = 0 := by
      rw [← htor_p_hom n x]
      exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eB n).hom.hom x) hx
      refine ⟨(eA n).inv.hom y, ?_⟩
      apply (eB n).toLinearEquiv.injective
      change (eB n).hom.hom (torMap M i n ((eA n).inv.hom y)) = (eB n).hom.hom x
      rw [htor_i_hom n, iso_hom_inv (eA n) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_i_hom n]
      have hzero : (HomologicalComplex.homologyMap SM.f n ≫ HomologicalComplex.homologyMap SM.g n) = 0 := by
        rw [← HomologicalComplex.homologyMap_comp, SM.zero, HomologicalComplex.homologyMap_zero]
      exact congrArg (fun φ : SM.X₁.homology n ⟶ SM.X₃.homology n => φ.hom ((eA n).hom.hom z)) hzero
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₃ (n + 1) n rfl)
    have h1 : δ n x = 0 ↔
        (hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x) = 0 := by
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x)) = 0 ↔ _
      exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eC (n + 1)).hom.hom x) hx
      refine ⟨(eB (n + 1)).inv.hom y, ?_⟩
      apply (eC (n + 1)).toLinearEquiv.injective
      change (eC (n + 1)).hom.hom (torMap M p (n + 1) ((eB (n + 1)).inv.hom y)) = (eC (n + 1)).hom.hom x
      rw [htor_p_hom (n + 1), iso_hom_inv (eB (n + 1)) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_p_hom (n + 1)]
      exact congrArg (fun φ : SM.X₂.homology (n + 1) ⟶ SM.X₁.homology n =>
        φ.hom ((eB (n + 1)).hom.hom z)) (hSM_exact.comp_δ (n + 1) n rfl)

lemma tor_subsingleton_of_hasFiniteProjRes {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] :
    ∀ (d : ℕ) (N : Type) [AddCommGroup N] [Module R N],
      HasFiniteProjRes R d N → ∀ i : ℕ, d < i → Subsingleton (torMod R M N i) := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hres i hi
    obtain ⟨_, hproj⟩ := hres
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact tor_succ_subsingleton_of_projective M N k
  | succ m ih =>
    intro N _ _ hres i hi
    obtain ⟨P, _, _, _, hprojP, f, hf, hK⟩ := hres
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    obtain ⟨δ, hδ_ex, _, hp_ex⟩ := horseshoe_tor_les M (LinearMap.ker f).subtype f
      (LinearMap.ker f).injective_subtype hf (by simp)
    have hK_sub : Subsingleton (torMod R M (LinearMap.ker f) k) := ih _ hK k (by omega)
    have hP_sub : Subsingleton (torMod R M P (k + 1)) := tor_succ_subsingleton_of_projective M P k
    refine ⟨fun x y => ?_⟩
    have h0 : δ k (x - y) = 0 := Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := (hp_ex k (x - y)).mp h0
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm

lemma module_finite_tensor_of_finite {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.Finite R (M ⊗[R] N) := by
  obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := R) N
  have hsurj : Function.Surjective (LinearMap.lTensor M g) :=
    LinearMap.lTensor_surjective M hg
  let φ : (Fin r → M) →ₗ[R] (M ⊗[R] (Fin r → R)) :=
    { toFun := fun u => ∑ j : Fin r, u j ⊗ₜ[R] Pi.single j (1 : R)
      map_add' := fun u v => by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul'] }
  have hφ_surj : Function.Surjective φ := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [φ]⟩
    | tmul m v =>
      refine ⟨fun j => v j • m, ?_⟩
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
      have hv : v = ∑ j : Fin r, v j • Pi.single j (1 : R) := by
        ext k; simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hv, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul]
    | add t₁ t₂ ih₁ ih₂ =>
      obtain ⟨u₁, hu₁⟩ := ih₁
      obtain ⟨u₂, hu₂⟩ := ih₂
      exact ⟨u₁ + u₂, by rw [map_add, hu₁, hu₂]⟩
  exact Module.Finite.of_surjective ((LinearMap.lTensor M g).comp φ) (hsurj.comp hφ_surj)

lemma tor_finite_of_hasFiniteProjRes {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∀ (d : ℕ) (N : Type) [AddCommGroup N] [Module R N],
      HasFiniteProjRes R d N → ∀ i : ℕ, Module.Finite R (torMod R M N i) := by
  intro d
  induction d with
  | zero =>
    intro N _ _ hres i
    obtain ⟨hfin, hproj⟩ := hres
    cases i with
    | zero =>
      let _ : Module.Finite R (M ⊗[R] N) := module_finite_tensor_of_finite M N
      exact Module.Finite.equiv (torZeroEquiv R M N).symm
    | succ k =>
      have _ : Subsingleton (torMod R M N (k + 1)) := tor_succ_subsingleton_of_projective M N k
      exact ⟨⟨∅, Submodule.eq_top_iff'.mpr fun (x : torMod R M N (k + 1)) => by
        rw [Subsingleton.elim x 0]; exact zero_mem _⟩⟩
  | succ m ih =>
    intro N _ _ hres i
    obtain ⟨P, _, _, hfinP, hprojP, f, hf, hK⟩ := hres
    cases i with
    | zero =>
      let _ : Module.Finite R N := Module.Finite.of_surjective f hf
      let _ : Module.Finite R (M ⊗[R] N) := module_finite_tensor_of_finite M N
      exact Module.Finite.equiv (torZeroEquiv R M N).symm
    | succ k =>
      obtain ⟨δ, _, _, hp_ex⟩ := horseshoe_tor_les M (LinearMap.ker f).subtype f
        (LinearMap.ker f).injective_subtype hf (by simp)
      have _ : Subsingleton (torMod R M P (k + 1)) := tor_succ_subsingleton_of_projective M P k
      have hδ_inj : Function.Injective (δ k) := by
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hp_ex k x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      have _ : Module.Finite R (torMod R M (LinearMap.ker f) k) := ih _ hK k
      let _ : IsNoetherian R (torMod R M (LinearMap.ker f) k) :=
        isNoetherian_of_isNoetherianRing_of_finite R _
      let e : torMod R M N (k + 1) ≃ₗ[R] LinearMap.range (δ k) :=
        LinearEquiv.ofInjective (δ k) hδ_inj
      let _ : Module.Finite R (LinearMap.range (δ k)) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      exact Module.Finite.equiv e.symm

/-- If `a : R` annihilates `M`, then `a` annihilates `Tor_i^R(M, N)`. -/
lemma tor_smul_eq_zero_left {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {a : R} (ha : ∀ m : M, a • m = 0) (i : ℕ) (x : torMod R M N i) : a • x = 0 := by
  let PN := projectiveResolution (ModuleCat.of R N)
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let e : torMod R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i :=
    PN.isoLeftDerivedObj F i
  have hx' : e.hom.hom (a • x) = 0 := by
    rw [map_smul]
    let K := (F.mapHomologicalComplex _).obj PN.complex
    have hsurj : Function.Surjective (K.homologyπ i) :=
      (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance
    obtain ⟨c, hc⟩ := hsurj (e.hom.hom x)
    rw [← hc, ← map_smul]
    have hc0 : a • c = 0 := by
      apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
      rw [map_smul, map_zero]
      have ht0 : ∀ t : M ⊗[R] PN.complex.X i, a • t = 0 := fun t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul m p => rw [TensorProduct.smul_tmul', ha m, TensorProduct.zero_tmul]
        | add t₁ t₂ ih₁ ih₂ => rw [smul_add, ih₁, ih₂, add_zero]
      exact ht0 ((K.iCycles i).hom c)
    rw [hc0, map_zero]
  exact e.toLinearEquiv.injective (hx'.trans (map_zero _).symm)

/-- If `b : R` annihilates `N`, then `b` annihilates `Tor_i^R(M, N)`. -/
lemma tor_smul_eq_zero_right {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {b : R} (hb : ∀ n : N, b • n = 0) (i : ℕ) (x : torMod R M N i) : b • x = 0 := by
  let PN := projectiveResolution (ModuleCat.of R N)
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let e : torMod R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i :=
    PN.isoLeftDerivedObj F i
  let multN : ModuleCat.of R N ⟶ ModuleCat.of R N :=
    ModuleCat.ofHom (b • LinearMap.id)
  have hmultN_zero : multN = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro n; exact hb n
  let multP : PN.complex ⟶ PN.complex :=
    { f := fun k => ModuleCat.ofHom (b • LinearMap.id)
      comm' := fun k l _ => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
        change (PN.complex.d k l).hom (b • y) = b • (PN.complex.d k l).hom y
        exact map_smul _ b y }
  have hcomm : (multP.f 0 ≫ PN.π.f 0) = (PN.π.f 0 ≫ multN) := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro y
    change (PN.π.f 0).hom (b • y) = b • (PN.π.f 0).hom y
    exact map_smul _ b y
  have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality multN PN PN multP hcomm F i
  have hmap0 : (F.leftDerived i).map multN = 0 := by
    rw [hmultN_zero]
    rw [Functor.leftDerived_map_eq F i (0 : ModuleCat.of R N ⟶ ModuleCat.of R N) (P := PN) (Q := PN) 0
      (by simp)]
    simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  rw [hmap0, Limits.zero_comp] at hnat
  have hFmult : ((F.mapHomologicalComplex _).map multP) =
      { f := fun k => ModuleCat.ofHom (b • LinearMap.id)
        comm' := fun k l _ => by
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro t
          change (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom (b • t) =
            b • (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom t
          exact map_smul _ b t } := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m p
    change m ⊗ₜ[R] (b • p) = b • (m ⊗ₜ[R] p)
    exact TensorProduct.tmul_smul b m p
  have hHmult (y : ((F.mapHomologicalComplex _).obj PN.complex).homology i) :
      (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map multP) i).hom y = b • y := by
    let K := (F.mapHomologicalComplex _).obj PN.complex
    have hsurj : Function.Surjective (K.homologyπ i) :=
      (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance
    obtain ⟨c, rfl⟩ := hsurj y
    have h1 : (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map multP) i).hom
        ((K.homologyπ i).hom c) =
        (K.homologyπ i).hom ((ShortComplex.cyclesMap
          ((HomologicalComplex.shortComplexFunctor _ _ i).map
            ((F.mapHomologicalComplex _).map multP))).hom c) :=
      congrArg (fun φ : K.cycles i ⟶ K.homology i => φ.hom c)
        (ShortComplex.homologyπ_naturality ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP)))
    rw [h1, ← map_smul]
    congr 1
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    have h2 : (K.iCycles i).hom ((ShortComplex.cyclesMap
        ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP))).hom c) =
        (((F.mapHomologicalComplex _).map multP).f i).hom ((K.iCycles i).hom c) :=
      congrArg (fun φ : K.cycles i ⟶ K.X i => φ.hom c)
        (ShortComplex.cyclesMap_i ((HomologicalComplex.shortComplexFunctor _ _ i).map
          ((F.mapHomologicalComplex _).map multP)))
    rw [h2, map_smul, hFmult]
    rfl
  have hx' : e.hom.hom (b • x) = 0 := by
    rw [map_smul, ← hHmult (e.hom.hom x)]
    have h0 := congrArg (fun φ : torMod R M N i ⟶ _ => φ.hom x) hnat
    exact h0.symm
  exact e.toLinearEquiv.injective (hx'.trans (map_zero _).symm)

/-- If `(P ⊔ Q).radical = maximalIdeal S`, then any finitely generated `S`-module annihilated
by `P ⊔ Q` has finite length. -/
lemma length_ne_top_of_annihilated_radical_eq_maximalIdeal
    {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {I : Ideal S} (hI : I.radical = maximalIdeal S)
    {X : Type} [AddCommGroup X] [Module S X] [Module.Finite S X]
    (hann : ∀ a ∈ I, ∀ x : X, a • x = 0) :
    Module.length S X ≠ ⊤ := by
  have hI_le : I ≤ maximalIdeal S := hI ▸ Ideal.le_radical
  have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ hI_le))
  let _ : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  have hkd0 : Ring.KrullDimLE 0 (S ⧸ I) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    let q := p.comap (Ideal.Quotient.mk I)
    have hq_prime : q.IsPrime := Ideal.IsPrime.comap (Ideal.Quotient.mk I)
    have hIq : I ≤ q := by
      intro a ha
      change Ideal.Quotient.mk I a ∈ p
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem p
    have hm_le_q : maximalIdeal S ≤ q := by
      rw [← hI]
      exact hq_prime.radical_le_iff.mpr hIq
    have hq_eq : q = maximalIdeal S :=
      le_antisymm (IsLocalRing.le_maximalIdeal hq_prime.ne_top) hm_le_q
    have hq_max : q.IsMaximal := hq_eq ▸ maximalIdeal.isMaximal S
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => hp.ne_top (Ideal.eq_top_of_isUnit_mem p h1 isUnit_one), fun J x hJp hxp hxJ => ?_⟩
    have hqJ : q ≤ J.comap (Ideal.Quotient.mk I) := fun a ha => hJp ha
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hyq : y ∉ q := hxp
    have hyJ : y ∈ J.comap (Ideal.Quotient.mk I) := hxJ
    have hJ_top : J.comap (Ideal.Quotient.mk I) = ⊤ := by
      by_contra hne
      exact hyq (hq_max.eq_of_le hne hqJ ▸ hyJ)
    have h1 : (1 : S) ∈ J.comap (Ideal.Quotient.mk I) := hJ_top ▸ Submodule.mem_top
    exact h1
  let _ : IsArtinianRing (S ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let _ : Module (S ⧸ I) X :=
    Module.compHom X (Ideal.Quotient.lift I (Module.toAddMonoidEnd S X)
      (fun a ha => AddMonoidHom.ext fun x => hann a ha x))
  have hst : IsScalarTower S (S ⧸ I) X :=
    ⟨fun s c x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      change (s * a) • x = s • (a • x)
      exact mul_smul s a x⟩
  let _ : Module.Finite (S ⧸ I) X := Module.Finite.of_restrictScalars_finite S (S ⧸ I) X
  let _ : IsNoetherian (S ⧸ I) X := isNoetherian_of_isNoetherianRing_of_finite (S ⧸ I) X
  let _ : IsArtinian (S ⧸ I) X := by
    obtain ⟨r, g, hg⟩ := exists_finite_free_surj (R := S ⧸ I) X
    exact isArtinian_of_surjective (Fin r → S ⧸ I) g hg
  rw [Module.length_eq_of_surjective (S := S) (R := S ⧸ I) (M := X) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end TorLES

section ChangeOfRings

/-- Finite-length additivity in `ℕ` for a short exact sequence. -/
lemma length_nat_add_of_exact {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hA : Module.length R A ≠ ⊤) (hC : Module.length R C ≠ ⊤) :
    Module.length R B ≠ ⊤ ∧
      (Module.length R B).toNat = (Module.length R A).toNat + (Module.length R C).toNat := by
  have heq := Module.length_eq_add_of_exact f g hf hg hex
  rw [← ENat.natCast_toNat hA, ← ENat.natCast_toNat hC, ← Nat.cast_add] at heq
  rw [heq]
  exact ⟨ENat.natCast_ne_top _, ENat.toNat_natCast _⟩

/-- If `A → B → C` is exact at `B` and both `A` and `C` have finite length, then `B` has finite
length equal to `ℓ(range f) + ℓ(range g)`. -/
lemma length_nat_of_exact_middle {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hex : Function.Exact f g)
    (hA : Module.length R A ≠ ⊤) (hC : Module.length R C ≠ ⊤) :
    Module.length R B ≠ ⊤ ∧
      Module.length R (LinearMap.range f) ≠ ⊤ ∧
      Module.length R (LinearMap.range g) ≠ ⊤ ∧
      (Module.length R B).toNat =
        (Module.length R (LinearMap.range f)).toNat +
          (Module.length R (LinearMap.range g)).toNat := by
  have hrf_le : Module.length R (LinearMap.range f) ≤ Module.length R A :=
    Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have hrf_fin : Module.length R (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hA hrf_le
  have hrg_le : Module.length R (LinearMap.range g) ≤ Module.length R C :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)
  have hrg_fin : Module.length R (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hC hrg_le
  have hker_eq : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hex
  have hkeq : Module.length R (LinearMap.ker g) = Module.length R (LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ hker_eq).length_eq
  have hker_fin : Module.length R (LinearMap.ker g) ≠ ⊤ := hkeq ▸ hrf_fin
  have hB := length_nat_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (fun b => by
      constructor
      · intro hb
        have hb0 : g b = 0 := congrArg Subtype.val hb
        exact ⟨⟨b, hb0⟩, rfl⟩
      · rintro ⟨⟨b, hb⟩, rfl⟩
        exact Subtype.ext hb)
    hker_fin hrg_fin
  refine ⟨hB.1, hrf_fin, hrg_fin, ?_⟩
  rw [hB.2, hkeq]

/-- Kernel-cokernel length identity for a composite `α : A →ₗ[R] B`, `β : B →ₗ[R] C`:
if `ker α`, `ker β`, and `B ⧸ range α` have finite length, then `ker (β ∘ α)` and
`range β ⧸ (range (β ∘ α)).comap (range β).subtype` have finite length and
`ℓ(ker (β ∘ α)) + ℓ(B ⧸ range α) = ℓ(ker α) + ℓ(ker β) + ℓ(range β ⧸ range (β ∘ α))`. -/
lemma length_ker_coker_comp {R : Type} [CommRing R]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C)
    (hka : Module.length R (LinearMap.ker α) ≠ ⊤)
    (hkb : Module.length R (LinearMap.ker β) ≠ ⊤)
    (hca : Module.length R (B ⧸ LinearMap.range α) ≠ ⊤) :
    let J : Submodule R (LinearMap.range β) :=
      (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
    Module.length R (LinearMap.ker (β.comp α)) ≠ ⊤ ∧
    Module.length R (LinearMap.range β ⧸ J) ≠ ⊤ ∧
    (Module.length R (LinearMap.ker (β.comp α))).toNat +
        (Module.length R (B ⧸ LinearMap.range α)).toNat =
      (Module.length R (LinearMap.ker α)).toNat +
        (Module.length R (LinearMap.ker β)).toNat +
        (Module.length R (LinearMap.range β ⧸ J)).toNat := by
  intro J
  let K : Submodule R B := LinearMap.ker β
  let I : Submodule R B := LinearMap.range α
  let IK : Submodule R K := I.comap K.subtype
  have hIK_fin : Module.length R IK ≠ ⊤ :=
    ne_top_of_le_ne_top hkb (Module.length_le_of_injective IK.subtype (Submodule.subtype_injective _))
  have hK_quot_fin : Module.length R (K ⧸ IK) ≠ ⊤ :=
    ne_top_of_le_ne_top hkb (Module.length_le_of_surjective IK.mkQ (Submodule.mkQ_surjective _))
  have hK_split := length_nat_add_of_exact IK.subtype IK.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ IK) hIK_fin hK_quot_fin
  -- SES A: 0 → ker α → ker (β ∘ α) → IK → 0
  let incl : LinearMap.ker α →ₗ[R] LinearMap.ker (β.comp α) :=
    LinearMap.codRestrict (LinearMap.ker (β.comp α)) (LinearMap.ker α).subtype (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        LinearMap.mem_ker.mp x.2, map_zero])
  let proj : LinearMap.ker (β.comp α) →ₗ[R] IK :=
    LinearMap.codRestrict IK
      (LinearMap.codRestrict K (α.comp (LinearMap.ker (β.comp α)).subtype) (fun x => x.2))
      (fun x => ⟨x.1, rfl⟩)
  have hincl_inj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun u : LinearMap.ker (β.comp α) => u.1) h)
  have hproj_surj : Function.Surjective proj := by
    rintro ⟨⟨b, hbK⟩, ⟨a, ha⟩⟩
    have ha_ker : a ∈ LinearMap.ker (β.comp α) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ha]
      exact hbK
    refine ⟨⟨a, ha_ker⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; exact ha
  have hexA : Function.Exact incl proj := fun x => by
    constructor
    · intro hx
      have h0 : α x.1 = 0 := congrArg (fun u => u.1.1) hx
      exact ⟨⟨x.1, h0⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      apply Subtype.ext; apply Subtype.ext; exact ha
  have hA_split := length_nat_add_of_exact incl proj hincl_inj hproj_surj hexA hka hIK_fin
  -- SES B: 0 → K ⧸ IK → B ⧸ I → range β ⧸ J → 0
  let φ : (B ⧸ I) →ₗ[R] (LinearMap.range β ⧸ J) :=
    I.liftQ (J.mkQ.comp β.rangeRestrict) (by
      rintro b ⟨a, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩)
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨⟨c, ⟨b, rfl⟩⟩, rfl⟩ := Submodule.Quotient.mk_surjective J y
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have hqJ_fin : Module.length R (LinearMap.range β ⧸ J) ≠ ⊤ :=
    ne_top_of_le_ne_top hca (Module.length_le_of_surjective φ hφ_surj)
  let ψ : (K ⧸ IK) →ₗ[R] (B ⧸ I) :=
    IK.liftQ (I.mkQ.comp K.subtype) (fun k hk => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hk)
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective IK u
    rw [Submodule.Quotient.mk_eq_zero]
    exact (Submodule.Quotient.mk_eq_zero I).mp hu
  have hexB : Function.Exact ψ φ := by
    intro u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective I u
    constructor
    · intro hu
      have hmem : β.rangeRestrict b ∈ J := (Submodule.Quotient.mk_eq_zero J).mp hu
      obtain ⟨a, ha⟩ := hmem
      have hk : b - α a ∈ K := by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr ha.symm
      refine ⟨Submodule.Quotient.mk ⟨b - α a, hk⟩, ?_⟩
      change Submodule.Quotient.mk (b - α a) = Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq]
      have : (b - α a) - b = -(α a) := by abel
      rw [this]
      exact neg_mem ⟨a, rfl⟩
    · rintro ⟨v, hv⟩
      obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective IK v
      rw [← hv]
      change Submodule.Quotient.mk (β.rangeRestrict k.1) = 0
      have hk0 : β.rangeRestrict k.1 = 0 := Subtype.ext k.2
      rw [hk0]
      rfl
  have hB_split := length_nat_add_of_exact ψ φ hψ_inj hφ_surj hexB hK_quot_fin hqJ_fin
  refine ⟨hA_split.1, hqJ_fin, ?_⟩
  dsimp only [K, I] at hK_split hA_split hB_split
  omega

/-- Lift an `S`-linear map `f : X →ₗ[S] A` to an `R`-linear map `(R ⊗[S] X) →ₗ[R] A`
when `A` is an `R`-module with `IsScalarTower S R A`. -/
noncomputable def liftBaseChange {S R X A : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [AddCommMonoid A] [Module S A] [Module R A] [IsScalarTower S R A]
    (f : X →ₗ[S] A) : (R ⊗[S] X) →ₗ[R] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r =>
        { toFun := fun x => r • f x
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun s x => by
            change r • f (s • x) = s • (r • f x)
            rw [map_smul, smul_comm] }
      map_add' := fun r₁ r₂ => by ext x; exact add_smul r₁ r₂ (f x)
      map_smul' := fun c r => by ext x; exact mul_smul c r (f x) }

/-- Base change of a projective module is projective. -/
lemma projective_baseChange {S R X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [Module.Projective S X] :
    Module.Projective R (R ⊗[S] X) := by
  refine Module.Projective.of_lifting_property' fun {A B} _ _ _ _ f g hf => ?_
  let _ : Module S A := Module.compHom A (algebraMap S R)
  let _ : Module S B := Module.compHom B (algebraMap S R)
  have _ : IsScalarTower S R A := ⟨fun s r a => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _ : IsScalarTower S R B := ⟨fun s r b => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  let gS : X →ₗ[S] B :=
    { toFun := fun x => g (1 ⊗ₜ[S] x)
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun s x => by
        change g (1 ⊗ₜ[S] (s • x)) = algebraMap S R s • g (1 ⊗ₜ[S] x)
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
          ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul,
          smul_eq_mul, mul_one] }
  obtain ⟨hS, hhS⟩ := Module.projective_lifting_property (f.restrictScalars S) gS hf
  let h : (R ⊗[S] X) →ₗ[R] A := liftBaseChange hS
  refine ⟨h, ?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  change f (r • hS x) = g (r ⊗ₜ[S] x)
  rw [map_smul]
  have h1 : f (hS x) = g (1 ⊗ₜ[S] x) := LinearMap.congr_fun hhS x
  rw [h1, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Over a domain `S`, a nonzero element `g : S` acts injectively on any projective `S`-module. -/
lemma smul_injective_of_projective_domain {S X : Type} [CommRing S] [IsDomain S]
    [AddCommGroup X] [Module S X] [Module.Projective S X]
    {g : S} (hg : g ≠ 0) :
    Function.Injective (fun x : X => g • x) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Finsupp.linearCombination S (id : X → X)) LinearMap.id
    (Finsupp.linearCombination_id_surjective S X)
  intro x y hxy
  change g • x = g • y at hxy
  have h0 : g • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hs0 : g • s (x - y) = 0 := by rw [← map_smul, h0, map_zero]
  have hsz : s (x - y) = 0 := by
    ext z
    have hz : g * (s (x - y)) z = 0 := congrArg (fun f : X →₀ S => f z) hs0
    exact (mul_eq_zero.mp hz).resolve_left hg
  have hxy0 : x - y = 0 := by
    have h1 : Finsupp.linearCombination S (id : X → X) (s (x - y)) = x - y :=
      LinearMap.congr_fun hs (x - y)
    rw [hsz, map_zero] at h1
    exact h1.symm
  exact sub_eq_zero.mp hxy0

/-- Concrete homology at `0` of a chain complex in `ModuleCat R` as `X_0 ⧸ range (d 1 0)`. -/
lemma homology_zero_equiv_quot_range {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    Nonempty (K.homology 0 ≃ₗ[R] (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom)) := by
  have hg0 : (K.sc' 1 0 0).g = 0 := K.shape 0 0 (by simp)
  have _ : IsIso (K.sc' 1 0 0).homologyι := ShortComplex.isIso_homologyι (K.sc' 1 0 0) hg0
  let e1 : K.homology 0 ≅ (K.sc' 1 0 0).homology :=
    K.homologyIsoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero
  let e2 : (K.sc' 1 0 0).homology ≅ (K.sc' 1 0 0).opcycles := asIso (K.sc' 1 0 0).homologyι
  let e3 : (K.sc' 1 0 0).opcycles ≅ ModuleCat.of R (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom) :=
    (K.sc' 1 0 0).moduleCatOpcyclesIso
  exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩

/-- Concrete homology at `k + 1` of a chain complex in `ModuleCat R` transported along linear
equivalences `e0, e1, e2`. -/
lemma homology_succ_equiv_of_iso {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (k : ℕ)
    {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module R A₀]
    [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
    (e₀ : A₀ ≃ₗ[R] K.X k) (e₁ : A₁ ≃ₗ[R] K.X (k + 1)) (e₂ : A₂ ≃ₗ[R] K.X (k + 2))
    (f : A₂ →ₗ[R] A₁) (g : A₁ →ₗ[R] A₀)
    (hf : ∀ x, e₁ (f x) = (K.d (k + 2) (k + 1)).hom (e₂ x))
    (hg : ∀ x, e₀ (g x) = (K.d (k + 1) k).hom (e₁ x)) :
    Nonempty (K.homology (k + 1) ≃ₗ[R]
      (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  let eH : K.homology (k + 1) ≅ (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    K.homologyIsoSc' (k + 2) (k + 1) k (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k) ≪≫
      (K.sc' (k + 2) (k + 1) k).moduleCatHomologyIso
  let eKer : LinearMap.ker g ≃ₗ[R] LinearMap.ker (K.d (k + 1) k).hom :=
    { toFun := fun x => ⟨e₁ x.1, by
        rw [LinearMap.mem_ker, ← hg x.1, x.2, map_zero]⟩
      invFun := fun y => ⟨e₁.symm y.1, by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, e₁.apply_symm_apply]
        exact y.2⟩
      map_add' := fun x y => Subtype.ext (map_add e₁ x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul e₁ r x.1)
      left_inv := fun x => Subtype.ext (e₁.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e₁.apply_symm_apply y.1) }
  have hsub : Submodule.map eKer.toLinearMap ((LinearMap.range f).comap (LinearMap.ker g).subtype) =
      LinearMap.range (K.sc' (k + 2) (k + 1) k).moduleCatToCycles := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨a, ha⟩, heq⟩
      refine ⟨e₂ a, Subtype.ext ?_⟩
      change (K.d (k + 2) (k + 1)).hom (e₂ a) = y
      rw [← hf a, ha]
      exact congrArg Subtype.val heq
    · rintro ⟨z, hz⟩
      have hz' : (K.d (k + 2) (k + 1)).hom z = y := congrArg Subtype.val hz
      let z' : K.X (k + 2) := z
      have hker_f : f (e₂.symm z') ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, hf, e₂.apply_symm_apply z']
        change (K.d (k + 1) k).hom ((K.d (k + 2) (k + 1)).hom z) = 0
        rw [hz']
        exact hy
      refine ⟨⟨f (e₂.symm z'), hker_f⟩, ⟨e₂.symm z', rfl⟩, Subtype.ext ?_⟩
      change e₁ (f (e₂.symm z')) = y
      rw [hf, e₂.apply_symm_apply z']
      exact hz'
  let eQ := Submodule.quotEquivOfEq _ _ hsub
  let eQuot : (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[R]
      (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    (Submodule.Quotient.equiv _ _ eKer rfl).trans eQ
  exact ⟨eH.toLinearEquiv.trans eQuot.symm⟩

/-- Base-change cancellation `M ⊗[R] (R ⊗[S] X) ≃ₗ[S] M ⊗[S] X` for a surjective `S → R`. -/
noncomputable def baseChangeTensorEquiv
    {S R M X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X]
    (hsurj : Function.Surjective (algebraMap S R)) :
    (M ⊗[R] (R ⊗[S] X)) ≃ₗ[S] (M ⊗[S] X) := by
  let _ : SMulCommClass R S M := ⟨fun r s m => by
    obtain ⟨a, rfl⟩ := hsurj r
    rw [algebraMap_smul, algebraMap_smul, smul_comm]⟩
  let _ : SMulCommClass S R M := SMulCommClass.symm R S M
  let _ : Module R (M ⊗[S] X) := TensorProduct.leftModule
  let _ : IsScalarTower S R (M ⊗[S] X) := ⟨fun s r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m x =>
      change ((s • r) • m) ⊗ₜ[S] x = s • ((r • m) ⊗ₜ[S] x)
      rw [smul_assoc, TensorProduct.smul_tmul']
    | add t₁ t₂ ih₁ ih₂ => rw [smul_add, smul_add, smul_add, ih₁, ih₂]⟩
  let inner (m : M) : (R ⊗[S] X) →ₗ[R] (M ⊗[S] X) :=
    liftBaseChange
      { toFun := fun x => m ⊗ₜ[S] x
        map_add' := fun x₁ x₂ => TensorProduct.tmul_add m x₁ x₂
        map_smul' := fun s x => TensorProduct.tmul_smul s m x }
  let fwdR : (M ⊗[R] (R ⊗[S] X)) →ₗ[R] (M ⊗[S] X) :=
    TensorProduct.lift
      { toFun := inner
        map_add' := fun m₁ m₂ => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (m₁ + m₂)) ⊗ₜ[S] x = (r • m₁) ⊗ₜ[S] x + (r • m₂) ⊗ₜ[S] x
          rw [smul_add, TensorProduct.add_tmul]
        map_smul' := fun c m => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (c • m)) ⊗ₜ[S] x = (c • (r • m)) ⊗ₜ[S] x
          rw [smul_comm] }
  let bwdS : (M ⊗[S] X) →ₗ[S] (M ⊗[R] (R ⊗[S] X)) :=
    TensorProduct.lift
      (LinearMap.mk₂ S (fun m x => m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
        (fun m₁ m₂ x => TensorProduct.add_tmul m₁ m₂ _)
        (fun s m x => (TensorProduct.smul_tmul' s m ((1 : R) ⊗ₜ[S] x)).symm)
        (fun m x₁ x₂ => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
        (fun s m x => by
          change m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] (s • x)) = s • (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
          rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
            ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
            TensorProduct.tmul_smul]
          exact algebraMap_smul R s (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))))
  refine LinearEquiv.ofLinearMap (fwdR.restrictScalars S) bwdS ?_ ?_
  · apply TensorProduct.ext'
    intro m x
    change ((1 : R) • m) ⊗ₜ[S] x = m ⊗ₜ[S] x
    rw [one_smul]
  · apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        change (r • m) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x) = m ⊗ₜ[R] (r ⊗ₜ[S] x)
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add u₁ u₂ ih₁ ih₂ =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
        rw [ih₁, ih₂]
    | add t₁ t₂ ih₁ ih₂ =>
      simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]

lemma baseChangeTensorEquiv_comm
    {S R M X Y : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (hsurj : Function.Surjective (algebraMap S R))
    (f : X →ₗ[S] Y) (t : M ⊗[R] (R ⊗[S] X)) :
    baseChangeTensorEquiv hsurj (LinearMap.lTensor M (LinearMap.baseChange R f) t) =
      LinearMap.lTensor M f (baseChangeTensorEquiv hsurj t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => rfl
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
  | add t₁ t₂ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂]

/-- If `δ : Tor_1(M, C) → Tor_0(M, A)` is exact with `torMap M i 0`, then
`ℓ(ker (lTensor M i)) = ℓ(range δ)`. -/
lemma length_ker_lTensor_eq_range_delta {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (δ : torMod R M C 1 →ₗ[R] torMod R M A 0)
    (hδ : Function.Exact δ (torMap M i 0)) :
    Module.length R (LinearMap.ker (LinearMap.lTensor M i)) =
      Module.length R (LinearMap.range δ) := by
  have hker_eq : LinearMap.ker (LinearMap.lTensor M i) =
      Submodule.map (torZeroEquiv R M A).toLinearMap (LinearMap.range δ) := by
    ext y
    obtain ⟨x, rfl⟩ := (torZeroEquiv R M A).surjective y
    constructor
    · intro hy
      have h0 : torMap M i 0 x = 0 := by
        apply (torZeroEquiv R M B).injective
        rw [map_zero, torZeroEquiv_naturality]
        exact hy
      obtain ⟨z, rfl⟩ := (hδ x).mp h0
      exact ⟨δ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, hz⟩
      have hx : x = δ z := (torZeroEquiv R M A).injective hz.symm
      rw [hx, LinearMap.mem_ker, ← torZeroEquiv_naturality, (hδ (δ z)).mpr ⟨z, rfl⟩, map_zero]
  rw [hker_eq]
  exact (Submodule.equivMapOfInjective (torZeroEquiv R M A).toLinearMap
    (torZeroEquiv R M A).injective (LinearMap.range δ)).symm.length_eq

/-- Pure linear-algebra helper for `H_2`: if `h = f ∘ p` with `p` surjective and `ker p = range d`,
then `ℓ(ker h ⧸ range d) = ℓ(ker f)`. -/
lemma length_quot_ker_comp_of_surj {R : Type} [CommRing R]
    {W X Y Z : Type} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (d : W →ₗ[R] X) (p : X →ₗ[R] Y) (f : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hp : Function.Surjective p) (hh : h = f.comp p)
    (hker : LinearMap.ker p = LinearMap.range d) :
    Module.length R (LinearMap.ker h ⧸ (LinearMap.range d).comap (LinearMap.ker h).subtype) =
      Module.length R (LinearMap.ker f) := by
  let φ : LinearMap.ker h →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (p.comp (LinearMap.ker h).subtype) (fun u => by
      change f (p u.1) = 0
      have hu : h u.1 = 0 := u.2
      exact (LinearMap.congr_fun hh u.1).symm.trans hu)
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨u, rfl⟩ := hp b
    have hu : h u = 0 := (LinearMap.congr_fun hh u).trans hb
    exact ⟨⟨u, hu⟩, rfl⟩
  have hφ_ker : LinearMap.ker φ = (LinearMap.range d).comap (LinearMap.ker h).subtype := by
    ext ⟨u, hu⟩
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    change p u = 0 ↔ u ∈ LinearMap.range d
    rw [← LinearMap.mem_ker, hker]
  exact ((Submodule.quotEquivOfEq _ _ hφ_ker.symm).trans (φ.quotKerEquivOfSurjective hφ_surj)).length_eq

/-- Pure linear-algebra helper for `H_1`: if `h = γ ∘ p` with `p` surjective, `ker p = range β`,
and `range d = range (β ∘ α)`, then `ℓ(ker h ⧸ range d) = ℓ(range β ⧸ range (β ∘ α)) + ℓ(ker γ)`. -/
lemma length_quot_ker_split {R : Type} [CommRing R]
    {W V U X Y Z : Type} [AddCommGroup W] [Module R W] [AddCommGroup V] [Module R V]
    [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (d : W →ₗ[R] X) (α : V →ₗ[R] U) (β : U →ₗ[R] X) (p : X →ₗ[R] Y) (γ : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hp : Function.Surjective p) (hh : h = γ.comp p)
    (hker_p : LinearMap.ker p = LinearMap.range β)
    (hrange_d : LinearMap.range d = LinearMap.range (β.comp α)) :
    Module.length R (LinearMap.ker h ⧸ (LinearMap.range d).comap (LinearMap.ker h).subtype) =
      Module.length R (LinearMap.range β ⧸
        (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype) +
        Module.length R (LinearMap.ker γ) := by
  let K0 := LinearMap.ker h
  let R1 : Submodule R K0 := (LinearMap.range d).comap K0.subtype
  let J : Submodule R (LinearMap.range β) :=
    (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
  have hβ_le_K0 : LinearMap.range β ≤ K0 := by
    rw [← hker_p]
    intro u hu
    change h u = 0
    rw [LinearMap.congr_fun hh u, LinearMap.comp_apply, LinearMap.mem_ker.mp hu, map_zero]
  let f1 : (LinearMap.range β ⧸ J) →ₗ[R] (K0 ⧸ R1) :=
    J.liftQ (R1.mkQ.comp (LinearMap.codRestrict K0 (LinearMap.range β).subtype
      (fun x => hβ_le_K0 x.2))) (by
        rintro ⟨u, hu⟩ hJ
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        change u ∈ LinearMap.range d
        rw [hrange_d]
        exact hJ)
  let g1 : (K0 ⧸ R1) →ₗ[R] LinearMap.ker γ :=
    R1.liftQ (LinearMap.codRestrict (LinearMap.ker γ) (p.comp K0.subtype) (fun u => by
      change γ (p u.1) = 0
      exact (LinearMap.congr_fun hh u.1).symm.trans u.2)) (by
        rintro ⟨u, hu⟩ huR1
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        change p u = 0
        have hmem : u ∈ LinearMap.range (β.comp α) := hrange_d ▸ huR1
        obtain ⟨a, rfl⟩ := hmem
        have : β (α a) ∈ LinearMap.range β := ⟨α a, rfl⟩
        rw [← hker_p] at this
        exact this)
  have hf1_inj : Function.Injective f1 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J y
    rw [Submodule.Quotient.mk_eq_zero]
    have hmem : x.1 ∈ LinearMap.range d := (Submodule.Quotient.mk_eq_zero R1).mp hy
    rw [hrange_d] at hmem
    exact hmem
  have hg1_surj : Function.Surjective g1 := by
    rintro ⟨b, hb⟩
    obtain ⟨u, rfl⟩ := hp b
    have hu : u ∈ K0 := by change h u = 0; exact (LinearMap.congr_fun hh u).trans hb
    exact ⟨Submodule.Quotient.mk ⟨u, hu⟩, rfl⟩
  have hex1 : Function.Exact f1 g1 := by
    intro y
    obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective R1 y
    constructor
    · intro hy
      have h0 : p u = 0 := congrArg Subtype.val hy
      have huβ : u ∈ LinearMap.range β := by rw [← hker_p]; exact h0
      exact ⟨Submodule.Quotient.mk ⟨u, huβ⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective J z
      rw [← hz]
      apply Subtype.ext
      change p v = 0
      rw [← LinearMap.mem_ker, hker_p]
      exact hv
  exact Module.length_eq_add_of_exact f1 g1 hf1_inj hg1_surj hex1

set_option maxHeartbeats 800000 in
/-- Core vanishing proof over abstract regular hypersurface quotient `R` and modules `M`, `N`. -/
lemma serre_h4_aux
    (S : Type) [CommRing S] [IsRegularLocalRing S] [IsDomain S]
    (g : S) (hg_ne : g ≠ 0)
    (R : Type) [CommRing R] [Algebra S R] [IsRegularLocalRing R]
    (hsurj : Function.Surjective (algebraMap S R))
    (hsurj_tmul : ∀ {X : Type} [AddCommGroup X] [Module S X] (u : R ⊗[S] X),
      ∃ x : X, (1 : R) ⊗ₜ[S] x = u)
    (hone_tmul_zero_iff : ∀ {X : Type} [AddCommGroup X] [Module S X] (x : X),
      (1 : R) ⊗ₜ[S] x = 0 ↔ ∃ y : X, g • y = x)
    (P Q : Ideal S) (hPQ : (P ⊔ Q).radical = maximalIdeal S)
    (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [Module.Finite S M] [Module.Finite R M]
    (N : Type) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower S R N]
    [Module.Finite S N] [Module.Finite R N]
    (hM_annP : ∀ a ∈ P, ∀ m : M, a • m = 0)
    (hN_annQ : ∀ a ∈ Q, ∀ n : N, a • n = 0)
    (hgN : ∀ n : N, g • n = 0) :
    Module.intersectionMultiplicity S M N = 0 := by
  -- Step 1: Projective resolution PN of N over S and base-changed objects Q_n = R ⊗[S] PN.X n
  let PN : ProjectiveResolution (ModuleCat.of S N) := projectiveResolution (ModuleCat.of S N)
  have hPN_proj (n : ℕ) : Module.Projective S (PN.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PN.complex.X n)
  have hPN_reg (n : ℕ) : Function.Injective (fun x : PN.complex.X n => g • x) := by
    let _ := hPN_proj n
    exact smul_injective_of_projective_domain hg_ne
  let εP : PN.complex.X 0 →ₗ[S] N := (PN.π.f 0).hom
  have hεP_surj : Function.Surjective εP :=
    (ModuleCat.epi_iff_surjective (PN.π.f 0)).mp inferInstance
  have hεP_comp (x : PN.complex.X 1) : εP ((PN.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X 1 ⟶ ModuleCat.of S N => φ.hom x) PN.complex_d_comp_π_f_zero
  have hεP_exact (x : PN.complex.X 0) (hx : εP x = 0) :
      ∃ y : PN.complex.X 1, (PN.complex.d 1 0).hom y = x := by
    let Quot := PN.complex.X 0 ⧸ LinearMap.range (PN.complex.d 1 0).hom
    let q : PN.complex.X 0 ⟶ ModuleCat.of S Quot :=
      ModuleCat.ofHom (LinearMap.range (PN.complex.d 1 0).hom).mkQ
    have hqw : (PN.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of S N ⟶ ModuleCat.of S Quot :=
      PN.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PN.π.f 0 ≫ desc) = q :=
      PN.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PN.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PN.complex.X 0 ⟶ ModuleCat.of S Quot => φ.hom x) hfac
      have hx0 : (PN.π.f 0).hom x = (0 : N) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hPN_exact (n : ℕ) (x : PN.complex.X (n + 1)) (hx : (PN.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PN.complex.X (n + 2), (PN.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PN.exact_succ n) x hx
  have hPN_dd (n : ℕ) (x : PN.complex.X (n + 2)) :
      (PN.complex.d (n + 1) n).hom ((PN.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X (n + 2) ⟶ PN.complex.X n => φ.hom x)
      (PN.complex.d_comp_d (n + 2) (n + 1) n)
  -- Define (R ⊗[S] PN.complex.X n) = R ⊗[S] PN.complex.X n and dQ n : (R ⊗[S] PN.complex.X (n+1)) →ₗ[R] (R ⊗[S] PN.complex.X n)
  have hQ_proj (n : ℕ) : Module.Projective R ((R ⊗[S] PN.complex.X n)) := by
    let _ := hPN_proj n
    exact projective_baseChange
  let dQ (n : ℕ) : (R ⊗[S] PN.complex.X (n + 1)) →ₗ[R] (R ⊗[S] PN.complex.X n) :=
    LinearMap.baseChange R (PN.complex.d (n + 1) n).hom
  have hdQ_tmul (n : ℕ) (r : R) (x : PN.complex.X (n + 1)) :
      dQ n (r ⊗ₜ[S] x) = r ⊗ₜ[S] ((PN.complex.d (n + 1) n).hom x) := rfl
  have hdQ_sq (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) : dQ n (dQ (n + 1) u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hdQ_tmul, hPN_dd n x, TensorProduct.tmul_zero]
  -- Step 2: Augmentation εQ : (R ⊗[S] PN.complex.X 0) →ₗ[R] N and exactness of Q_•
  let εQ : (R ⊗[S] PN.complex.X 0) →ₗ[R] N := liftBaseChange εP
  have hεQ_tmul (r : R) (x : PN.complex.X 0) : εQ (r ⊗ₜ[S] x) = r • εP x := rfl
  have hεQ_surj : Function.Surjective εQ := fun n => by
    obtain ⟨x, rfl⟩ := hεP_surj n
    exact ⟨1 ⊗ₜ[S] x, by rw [hεQ_tmul, one_smul]⟩
  have hεQ_comp (u : (R ⊗[S] PN.complex.X 1)) : εQ (dQ 0 u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hεQ_tmul, hεP_comp x, smul_zero]
  have hεQ_exact (u : (R ⊗[S] PN.complex.X 0)) (hu : εQ u = 0) : ∃ v : (R ⊗[S] PN.complex.X 1), dQ 0 v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hεQ_tmul, one_smul] at hu
    obtain ⟨y, hy⟩ := hεP_exact x hu
    exact ⟨1 ⊗ₜ[S] y, by rw [hdQ_tmul, hy]⟩
  have hQ_exact_ge2 (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) (hu : dQ (n + 1) u = 0) :
      ∃ v : (R ⊗[S] PN.complex.X (n + 3)), dQ (n + 2) v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul] at hu
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp hu
    have hdy : (PN.complex.d (n + 1) n).hom y = 0 := by
      apply hPN_reg n
      dsimp only
      rw [smul_zero, ← map_smul, hy, hPN_dd n x]
    obtain ⟨z, hz⟩ := hPN_exact n y hdy
    have hdxz : (PN.complex.d (n + 2) (n + 1)).hom (x - g • z) = 0 := by
      rw [map_sub, map_smul, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := hPN_exact (n + 1) (x - g • z) hdxz
    refine ⟨1 ⊗ₜ[S] w, ?_⟩
    rw [hdQ_tmul, hw, TensorProduct.tmul_sub]
    have hgz0 : (1 : R) ⊗ₜ[S] (g • z) = 0 := (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩
    rw [hgz0, sub_zero]
  -- Step 3: Define B0, Z1, B1 and the 3 short exact sequences over R
  let B0 : Submodule R (R ⊗[S] PN.complex.X 0) := LinearMap.range (dQ 0)
  let _ : AddCommGroup B0 := Submodule.addCommGroup B0
  let Z1 : Submodule R (R ⊗[S] PN.complex.X 1) := LinearMap.ker (dQ 0)
  let _ : AddCommGroup Z1 := Submodule.addCommGroup Z1
  let dQ1_to_Z1 : (R ⊗[S] PN.complex.X 2) →ₗ[R] Z1 := LinearMap.codRestrict Z1 (dQ 1) (fun u => hdQ_sq 0 u)
  let B1 : Submodule R Z1 := LinearMap.range dQ1_to_Z1
  let _ : AddCommGroup B1 := Submodule.addCommGroup B1
  -- Construct ψ : Z1 →ₗ[R] N with ker ψ = B1 and ψ surjective
  have hZ1_exists_y (u : Z1) :
      ∃ y : PN.complex.X 0, ∃ x : PN.complex.X 1,
        (1 : R) ⊗ₜ[S] x = u.1 ∧ g • y = (PN.complex.d 1 0).hom x := by
    obtain ⟨x, hx⟩ := hsurj_tmul u.1
    have h0 : (1 : R) ⊗ₜ[S] (PN.complex.d 1 0).hom x = 0 := by
      rw [← hdQ_tmul 0 1 x, hx]
      exact u.2
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp h0
    exact ⟨y, x, hx, hy⟩
  have hψ_well_def (u : Z1) (x₁ x₂ : PN.complex.X 1) (y₁ y₂ : PN.complex.X 0)
      (hx₁ : (1 : R) ⊗ₜ[S] x₁ = u.1) (hx₂ : (1 : R) ⊗ₜ[S] x₂ = u.1)
      (hy₁ : g • y₁ = (PN.complex.d 1 0).hom x₁)
      (hy₂ : g • y₂ = (PN.complex.d 1 0).hom x₂) :
      εP y₁ = εP y₂ := by
    have hdiff0 : (1 : R) ⊗ₜ[S] (x₁ - x₂) = 0 := by
      rw [TensorProduct.tmul_sub, hx₁, hx₂, sub_self]
    obtain ⟨z, hz⟩ := (hone_tmul_zero_iff _).mp hdiff0
    have hy_diff : y₁ - y₂ = (PN.complex.d 1 0).hom z := by
      apply hPN_reg 0
      dsimp only
      rw [smul_sub, hy₁, hy₂, ← map_sub, ← hz, map_smul]
    have hε0 : εP (y₁ - y₂) = 0 := by rw [hy_diff, hεP_comp z]
    rw [map_sub] at hε0
    exact sub_eq_zero.mp hε0
  let ψFun (u : Z1) : N := εP (Classical.choose (hZ1_exists_y u))
  have hψ_eq (u : Z1) (x : PN.complex.X 1) (y : PN.complex.X 0)
      (hx : (1 : R) ⊗ₜ[S] x = u.1) (hy : g • y = (PN.complex.d 1 0).hom x) :
      ψFun u = εP y := by
    have hspec := Classical.choose_spec (hZ1_exists_y u)
    obtain ⟨x0, hx0, hy0⟩ := hspec
    exact hψ_well_def u x0 x _ y hx0 hx hy0 hy
  let ψ : Z1 →ₗ[R] N :=
    { toFun := ψFun
      map_add' := fun u₁ u₂ => by
        obtain ⟨y₁, x₁, hx₁, hy₁⟩ := hZ1_exists_y u₁
        obtain ⟨y₂, x₂, hx₂, hy₂⟩ := hZ1_exists_y u₂
        rw [hψ_eq u₁ x₁ y₁ hx₁ hy₁, hψ_eq u₂ x₂ y₂ hx₂ hy₂, ← map_add]
        exact hψ_eq (u₁ + u₂) (x₁ + x₂) (y₁ + y₂)
          (by rw [TensorProduct.tmul_add, hx₁, hx₂]; rfl)
          (by rw [smul_add, map_add, hy₁, hy₂])
      map_smul' := fun r u => by
        obtain ⟨s, rfl⟩ := hsurj r
        obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
        rw [hψ_eq u x y hx hy]
        change ψFun ((algebraMap S R s) • u) = (algebraMap S R s) • εP y
        rw [algebraMap_smul R s (εP y), ← map_smul]
        exact hψ_eq ((algebraMap S R s) • u) (s • x) (s • y)
          (by
            change (1 : R) ⊗ₜ[S] (s • x) = (algebraMap S R s) • u.1
            rw [← hx, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
              ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
              smul_eq_mul, mul_one])
          (by rw [smul_comm, hy, map_smul]) }
  have hψ_surj : Function.Surjective ψ := fun n => by
    obtain ⟨y, rfl⟩ := hεP_surj n
    have hgy : εP (g • y) = 0 := by rw [map_smul]; exact hgN (εP y)
    obtain ⟨x, hx⟩ := hεP_exact (g • y) hgy
    have hu_mem : (1 : R) ⊗ₜ[S] x ∈ Z1 := by
      rw [LinearMap.mem_ker, hdQ_tmul, hx]
      exact (hone_tmul_zero_iff _).mpr ⟨y, rfl⟩
    refine ⟨⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩, ?_⟩
    exact hψ_eq ⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩ x y rfl hx.symm
  have hB1_eq_ker_ψ : B1 = LinearMap.ker ψ := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj_tmul w
      rw [LinearMap.mem_ker]
      have h1 : ψ (dQ1_to_Z1 (1 ⊗ₜ[S] z)) = εP 0 :=
        hψ_eq (dQ1_to_Z1 (1 ⊗ₜ[S] z)) ((PN.complex.d 2 1).hom z) 0 rfl
          (by rw [smul_zero, hPN_dd 0 z])
      rw [h1, map_zero]
    · intro hu
      rw [LinearMap.mem_ker] at hu
      obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
      have hεy : εP y = 0 := (hψ_eq u x y hx hy).symm.trans hu
      obtain ⟨z, hz⟩ := hεP_exact y hεy
      have hdxz : (PN.complex.d 1 0).hom (x - g • z) = 0 := by
        rw [map_sub, map_smul, hz, hy, sub_self]
      obtain ⟨w, hw⟩ := hPN_exact 0 (x - g • z) hdxz
      refine ⟨1 ⊗ₜ[S] w, Subtype.ext ?_⟩
      change dQ 1 (1 ⊗ₜ[S] w) = u.1
      rw [hdQ_tmul, hw, TensorProduct.tmul_sub, (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩, sub_zero, hx]
  -- Exactness of SES 1, SES 2, SES 3
  have hSES1 : LinearMap.range B0.subtype = LinearMap.ker εQ := by
    rw [Submodule.range_subtype]
    ext u
    exact ⟨by rintro ⟨v, rfl⟩; exact hεQ_comp v, fun hu => hεQ_exact u hu⟩
  have hSES2 : LinearMap.range Z1.subtype = LinearMap.ker (dQ 0).rangeRestrict := by
    rw [Submodule.range_subtype]
    ext u
    simp [Z1, LinearMap.mem_ker]
  have hSES3 : LinearMap.range B1.subtype = LinearMap.ker ψ := by
    rw [Submodule.range_subtype]
    exact hB1_eq_ker_ψ
  -- Step 4: Shifted complex Q_shift is a ProjectiveResolution of B1 over R
  let dQ_shift (n : ℕ) : ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 3))) ⟶ ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2))) :=
    ModuleCat.ofHom (dQ (n + 2))
  have hdQ_shift_sq (n : ℕ) : (dQ_shift (n + 1) ≫ dQ_shift n) = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro u; exact hdQ_sq (n + 2) u
  let Qshift : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2)))) dQ_shift hdQ_shift_sq
  have hQshift_d (n : ℕ) : (Qshift.d (n + 1) n).hom = dQ (n + 2) := by
    change (ChainComplex.of.d (fun k => ModuleCat.of R ((R ⊗[S] PN.complex.X (k + 2)))) dQ_shift (n + 1) n).hom =
      dQ (n + 2)
    rw [ChainComplex.of_d]
    rfl
  let p2 : (R ⊗[S] PN.complex.X 2) →ₗ[R] B1 := dQ1_to_Z1.rangeRestrict
  have hp2_surj : Function.Surjective p2 := dQ1_to_Z1.surjective_rangeRestrict
  have hp2_comp (u : Qshift.X 1) : p2 ((Qshift.d 1 0).hom u) = 0 := by
    rw [hQshift_d 0]
    apply Subtype.ext; apply Subtype.ext
    exact hdQ_sq 1 u
  have hp2_exact (u : Qshift.X 0) (hu : p2 u = 0) :
      ∃ v : Qshift.X 1, (Qshift.d 1 0).hom v = u := by
    rw [hQshift_d 0]
    have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
    exact hQ_exact_ge2 0 u h0
  have hQshift_exact (n : ℕ) (u : Qshift.X (n + 1)) (hu : (Qshift.d (n + 1) n).hom u = 0) :
      ∃ v : Qshift.X (n + 2), (Qshift.d (n + 2) (n + 1)).hom v = u := by
    rw [hQshift_d n] at hu
    rw [hQshift_d (n + 1)]
    exact hQ_exact_ge2 (n + 1) u hu
  let PB1 : ProjectiveResolution (ModuleCat.of R B1) :=
    projectiveResolutionOfExact B1 Qshift (fun n => hQ_proj (n + 2)) p2
      hp2_surj hp2_comp hp2_exact hQshift_exact
  -- Step 5: S-linear isomorphism M ⊗[R] (R ⊗[S] PN.complex.X n) ≃ₗ[S] M ⊗[S] PN.complex.X n
  let eMQ (n : ℕ) : (M ⊗[R] (R ⊗[S] PN.complex.X n)) ≃ₗ[S] (M ⊗[S] PN.complex.X n) :=
    baseChangeTensorEquiv (S := S) (R := R) (M := M) (X := PN.complex.X n) hsurj
  have heMQ_comm (n : ℕ) (t : M ⊗[R] (R ⊗[S] PN.complex.X (n + 1))) :
      eMQ n (LinearMap.lTensor M (dQ n) t) =
        LinearMap.lTensor M (PN.complex.d (n + 1) n).hom (eMQ (n + 1) t) :=
    baseChangeTensorEquiv_comm (S := S) (R := R) (M := M) hsurj
      (PN.complex.d (n + 1) n).hom t
  -- Step 6: Express Tor^S(M, N) via M ⊗_R Q_•
  let FS := (tensoringLeft (ModuleCat.{0} S)).obj (ModuleCat.of S M)
  let KSN : ChainComplex (ModuleCat.{0} S) ℕ := (FS.mapHomologicalComplex _).obj PN.complex
  have hTorS_iso (i : ℕ) : Nonempty (torMod S M N i ≃ₗ[S] KSN.homology i) :=
    ⟨(PN.isoLeftDerivedObj FS i).toLinearEquiv⟩
  have hTorS_zero : Nonempty (torMod S M N 0 ≃ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0)))) := by
    obtain ⟨e1⟩ := hTorS_iso 0
    obtain ⟨e2⟩ := homology_zero_equiv_quot_range KSN
    let q : KSN.X 0 →ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      ((Submodule.mkQ (LinearMap.range (LinearMap.lTensor M (dQ 0)))).restrictScalars S).comp
        (eMQ 0).symm.toLinearMap
    have hq_surj : Function.Surjective q :=
      (Submodule.mkQ_surjective _).comp (eMQ 0).symm.surjective
    have hq_ker : LinearMap.ker q = LinearMap.range (KSN.d 1 0).hom := by
      ext y
      change Submodule.Quotient.mk ((eMQ 0).symm y) = 0 ↔ y ∈ LinearMap.range (KSN.d 1 0).hom
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨t, ht⟩
        let y' : M ⊗[S] PN.complex.X 0 := y
        refine ⟨eMQ 1 t, ?_⟩
        change LinearMap.lTensor M (PN.complex.d 1 0).hom (eMQ 1 t) = y'
        rw [← heMQ_comm 0 t, ht, (eMQ 0).apply_symm_apply y']
      · rintro ⟨z, rfl⟩
        let z' : M ⊗[S] PN.complex.X 1 := z
        refine ⟨(eMQ 1).symm z', ?_⟩
        apply (eMQ 0).injective
        rw [heMQ_comm 0, (eMQ 1).apply_symm_apply z']
        exact ((eMQ 0).apply_symm_apply (LinearMap.lTensor M (PN.complex.d 1 0).hom z')).symm
    let eQ0 : (KSN.X 0 ⧸ LinearMap.range (KSN.d 1 0).hom) ≃ₗ[S]
        ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    exact ⟨e1.trans (e2.trans eQ0)⟩
  have hTorS_succ_len (k : ℕ) :
      Module.length S (torMod S M N (k + 1)) =
        Module.length R (LinearMap.ker (LinearMap.lTensor M (dQ k)) ⧸
          (LinearMap.range (LinearMap.lTensor M (dQ (k + 1)))).comap
            (LinearMap.ker (LinearMap.lTensor M (dQ k))).subtype) := by
    obtain ⟨e1⟩ := hTorS_iso (k + 1)
    let fS := (LinearMap.lTensor M (dQ (k + 1))).restrictScalars S
    let gS := (LinearMap.lTensor M (dQ k)).restrictScalars S
    obtain ⟨e2⟩ := homology_succ_equiv_of_iso KSN k (eMQ k) (eMQ (k + 1)) (eMQ (k + 2))
      fS gS (fun t => heMQ_comm (k + 1) t) (fun t => heMQ_comm k t)
    let KR := LinearMap.ker (LinearMap.lTensor M (dQ k))
    let RR : Submodule R KR := (LinearMap.range (LinearMap.lTensor M (dQ (k + 1)))).comap KR.subtype
    let q : LinearMap.ker gS →ₗ[S] (KR ⧸ RR) :=
      { toFun := fun u => Submodule.Quotient.mk ⟨u.1, u.2⟩
        map_add' := fun u v => rfl
        map_smul' := fun s u => by
          change Submodule.Quotient.mk (s • (⟨u.1, u.2⟩ : KR)) =
            s • Submodule.Quotient.mk (⟨u.1, u.2⟩ : KR)
          rfl }
    have hq_surj : Function.Surjective q := by
      intro w
      obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective RR w
      exact ⟨⟨u, hu⟩, rfl⟩
    have hq_ker : LinearMap.ker q = (LinearMap.range fS).comap (LinearMap.ker gS).subtype := by
      ext ⟨u, hu⟩
      change Submodule.Quotient.mk (⟨u, hu⟩ : KR) = 0 ↔ u ∈ LinearMap.range fS
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    let e3 : (LinearMap.ker gS ⧸ (LinearMap.range fS).comap (LinearMap.ker gS).subtype) ≃ₗ[S]
        (KR ⧸ RR) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    rw [e1.length_eq, e2.length_eq, e3.length_eq,
      Module.length_eq_of_surjective (S := S) (R := R) hsurj]
  -- Compare Tor_m^R(M, B1) with Tor_{m+2}^S(M, N) for m ≥ 1!
  let FR := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let KRB1 : ChainComplex (ModuleCat.{0} R) ℕ := (FR.mapHomologicalComplex _).obj PB1.complex
  have hTorS_ge3 (k : ℕ) :
      Module.length S (torMod S M N (k + 3)) = Module.length R (torMod R M B1 (k + 1)) := by
    have eR1 : torMod R M B1 (k + 1) ≃ₗ[R] KRB1.homology (k + 1) :=
      (PB1.isoLeftDerivedObj FR (k + 1)).toLinearEquiv
    obtain ⟨eR2⟩ := homology_succ_equiv_of_iso KRB1 k
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 2))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 3))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (k + 4))))
      (LinearMap.lTensor M (dQ (k + 3)))
      (LinearMap.lTensor M (dQ (k + 2)))
      (fun t => by
        change LinearMap.lTensor M (dQ (k + 3)) t = LinearMap.lTensor M (Qshift.d (k + 2) (k + 1)).hom t
        rw [hQshift_d (k + 1)])
      (fun t => by
        change LinearMap.lTensor M (dQ (k + 2)) t = LinearMap.lTensor M (Qshift.d (k + 1) k).hom t
        rw [hQshift_d k])
    rw [hTorS_succ_len (k + 2), eR1.length_eq, eR2.length_eq]
  -- Step 7: All Tor_i^R(M, N) have finite length and vanish for i > d
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hN_res : HasFiniteProjRes R d N := hasFiniteProjRes_of_isRegularLocalRing R N
  have hTorR_sub (i : ℕ) (hi : d < i) : Subsingleton (torMod R M N i) :=
    tor_subsingleton_of_hasFiniteProjRes M d N hN_res i hi
  have hTorR_fin (i : ℕ) : Module.Finite R (torMod R M N i) :=
    tor_finite_of_hasFiniteProjRes M d N hN_res i
  have hTorR_len_fin (i : ℕ) : Module.length R (torMod R M N i) ≠ ⊤ := by
    let _ : Module.Finite R (torMod R M N i) := hTorR_fin i
    let _ : Module S (torMod R M N i) := Module.compHom _ (algebraMap S R)
    let _ : IsScalarTower S R (torMod R M N i) :=
      ⟨fun s r x => by
        obtain ⟨a, rfl⟩ := hsurj r
        rw [Algebra.smul_def, mul_smul]; rfl⟩
    let _ : Module.Finite S (torMod R M N i) := by
      obtain ⟨r, g', hg'⟩ := exists_finite_free_surj (R := R) (torMod R M N i)
      let liftS : (Fin r → S) →ₗ[S] (Fin r → R) :=
        { toFun := fun v j => algebraMap S R (v j)
          map_add' := fun u v => by ext j; exact map_add _ _ _
          map_smul' := fun s v => by
            ext j
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def, map_mul] }
      have hliftS : Function.Surjective liftS := fun w => by
        refine ⟨fun j => Classical.choose (hsurj (w j)), ?_⟩
        ext j; exact Classical.choose_spec (hsurj (w j))
      exact Module.Finite.of_surjective ((g'.restrictScalars S).comp liftS) (hg'.comp hliftS)
    rw [← Module.length_eq_of_surjective (S := S) (R := R) hsurj]
    refine length_ne_top_of_annihilated_radical_eq_maximalIdeal hPQ fun a ha x => ?_
    rw [Submodule.mem_sup] at ha
    obtain ⟨p, hp, q, hq, rfl⟩ := ha
    change (algebraMap S R (p + q)) • x = 0
    rw [map_add, add_smul]
    have hp0 : (algebraMap S R p) • x = 0 :=
      tor_smul_eq_zero_left (R := R) M N (a := algebraMap S R p)
        (fun m => by rw [algebraMap_smul]; exact hM_annP p hp m) i x
    have hq0 : (algebraMap S R q) • x = 0 :=
      tor_smul_eq_zero_right (R := R) M N (b := algebraMap S R q)
        (fun n => by rw [algebraMap_smul]; exact hN_annQ q hq n) i x
    rw [hp0, hq0, add_zero]
  -- Step 8: Long exact sequences for SES 1, SES 2, SES 3
  obtain ⟨δ1, hδ1_1, hδ1_2, hδ1_3⟩ := horseshoe_tor_les (R := R) M (A := B0) B0.subtype εQ
    (Submodule.subtype_injective B0) hεQ_surj hSES1
  obtain ⟨δ2, hδ2_1, hδ2_2, hδ2_3⟩ := horseshoe_tor_les (R := R) M (A := Z1) (C := B0)
    Z1.subtype (dQ 0).rangeRestrict
    (Submodule.subtype_injective Z1) (dQ 0).surjective_rangeRestrict hSES2
  obtain ⟨δ3, hδ3_1, hδ3_2, hδ3_3⟩ := horseshoe_tor_les (R := R) M (A := B1) (B := Z1) (C := N)
    B1.subtype ψ (Submodule.subtype_injective B1) hψ_surj hSES3
  -- Tor_k^R(M, B0) ≃ Tor_{k+1}^R(M, N) for k ≥ 1
  have hTorB0_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 2) ≃ₗ[R] torMod R M B0 (k + 1)) := by
    let _ := hQ_proj 0
    have hsub1 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) k
    have hsub2 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) (k + 1)
    have hbij : Function.Bijective (δ1 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ1_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ1_1 (k + 1) y).mp (Subsingleton.elim _ _)
    exact ⟨LinearEquiv.ofBijective (δ1 (k + 1)) hbij⟩
  -- Tor_k^R(M, Z1) ≃ Tor_{k+2}^R(M, N) for k ≥ 1
  have hTorZ1_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 3) ≃ₗ[R] torMod R M Z1 (k + 1)) := by
    let _ := hQ_proj 1
    have hsub1 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) k
    have hsub2 : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) (k + 1)
    have hbij : Function.Bijective (δ2 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ2_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ2_1 (k + 1) y).mp (Subsingleton.elim _ _)
    obtain ⟨e1⟩ := hTorB0_equiv (k + 1)
    exact ⟨e1.trans (LinearEquiv.ofBijective (δ2 (k + 1)) hbij)⟩
  -- Step 9: Low-degree identifications (i = 0, 1, 2) via α, β, γ
  let α : (M ⊗[R] B1) →ₗ[R] (M ⊗[R] Z1) := LinearMap.lTensor M B1.subtype
  let β : (M ⊗[R] Z1) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 1)) := LinearMap.lTensor M Z1.subtype
  let γ : (M ⊗[R] B0) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 0)) := LinearMap.lTensor M B0.subtype
  let Lp1 : (M ⊗[R] (R ⊗[S] PN.complex.X 1)) →ₗ[R] (M ⊗[R] B0) := LinearMap.lTensor M (dQ 0).rangeRestrict
  let Lp2 : (M ⊗[R] (R ⊗[S] PN.complex.X 2)) →ₗ[R] (M ⊗[R] B1) := LinearMap.lTensor M p2
  have hLp1_surj : Function.Surjective Lp1 :=
    LinearMap.lTensor_surjective M (dQ 0).surjective_rangeRestrict
  have hLp2_surj : Function.Surjective Lp2 :=
    LinearMap.lTensor_surjective M hp2_surj
  have hd0_fac : LinearMap.lTensor M (dQ 0) = γ.comp Lp1 := by
    rw [← LinearMap.lTensor_comp]; rfl
  have hd1_fac : LinearMap.lTensor M (dQ 1) = (β.comp α).comp Lp2 := by
    rw [LinearMap.comp_assoc, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]; rfl
  have hker_Lp1 : LinearMap.ker Lp1 = LinearMap.range β :=
    LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES2.symm)
      (dQ 0).surjective_rangeRestrict)
  have hker_Lp2 : LinearMap.ker Lp2 = LinearMap.range (LinearMap.lTensor M (dQ 2)) := by
    have hex_d2 : Function.Exact (dQ 2) p2 := fun u => by
      constructor
      · intro hu
        have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
        exact hQ_exact_ge2 0 u h0
      · rintro ⟨v, rfl⟩
        apply Subtype.ext; apply Subtype.ext; exact hdQ_sq 1 v
    exact LinearMap.exact_iff.mp (lTensor_exact M hex_d2 hp2_surj)
  -- ker γ ≃ Tor_1^R(M, N)
  have hker_γ_len : Module.length R (LinearMap.ker γ) = Module.length R (torMod R M N 1) := by
    let _ := hQ_proj 0
    have hsub : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) 0
    have hδ1_inj : Function.Injective (δ1 0) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := (hδ1_3 0 x).mp hx
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact hz.symm
    rw [length_ker_lTensor_eq_range_delta M B0.subtype (δ1 0) (hδ1_1 0),
      (LinearEquiv.ofInjective (δ1 0) hδ1_inj).length_eq.symm]
  -- ker β ≃ Tor_1^R(M, B0) ≃ Tor_2^R(M, N)
  have hker_β_len : Module.length R (LinearMap.ker β) = Module.length R (torMod R M N 2) := by
    let _ := hQ_proj 1
    have hsub : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) 0
    have hδ2_inj : Function.Injective (δ2 0) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨z, hz⟩ := (hδ2_3 0 x).mp hx
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact hz.symm
    obtain ⟨eB0⟩ := hTorB0_equiv 0
    rw [length_ker_lTensor_eq_range_delta M Z1.subtype (δ2 0) (hδ2_1 0),
      (LinearEquiv.ofInjective (δ2 0) hδ2_inj).length_eq.symm, eB0.length_eq]
  -- ker α ≃ range (δ3 0)
  have hker_α_len : Module.length R (LinearMap.ker α) = Module.length R (LinearMap.range (δ3 0)) :=
    length_ker_lTensor_eq_range_delta M B1.subtype (δ3 0) (hδ3_1 0)
  -- coker α ≃ M ⊗_R N ≃ Tor_0^R(M, N)
  have hcoker_α_len :
      Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α) = Module.length R (torMod R M N 0) := by
    have hsurj : Function.Surjective (LinearMap.lTensor M ψ) :=
      LinearMap.lTensor_surjective M hψ_surj
    have hker : LinearMap.ker (LinearMap.lTensor M ψ) = LinearMap.range α :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES3.symm) hψ_surj)
    let e1 := (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((LinearMap.lTensor M ψ).quotKerEquivOfSurjective hsurj)
    rw [e1.length_eq, (torZeroEquiv R M N).length_eq]
  -- s_0 = t_0
  have hs0_len : Module.length S (torMod S M N 0) = Module.length R (torMod R M N 0) := by
    obtain ⟨eS0⟩ := hTorS_zero
    rw [eS0.length_eq,
      Module.length_eq_of_surjective (S := S) (R := R) hsurj]
    have hrange_d0 : LinearMap.range (LinearMap.lTensor M (dQ 0)) = LinearMap.range γ := by
      rw [hd0_fac, LinearMap.range_comp, LinearMap.range_eq_top.mpr hLp1_surj, Submodule.map_top]
    have hsurj : Function.Surjective (LinearMap.lTensor M εQ) :=
      LinearMap.lTensor_surjective M hεQ_surj
    have hker : LinearMap.ker (LinearMap.lTensor M εQ) = LinearMap.range γ :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES1.symm) hεQ_surj)
    let e := (Submodule.quotEquivOfEq _ _ (hrange_d0.trans hker.symm)).trans
      ((LinearMap.lTensor M εQ).quotKerEquivOfSurjective hsurj)
    rw [e.length_eq, (torZeroEquiv R M N).length_eq]
  -- s_2 = ℓ(ker (β ∘ α))
  have hs2_len : Module.length S (torMod S M N 2) = Module.length R (LinearMap.ker (β.comp α)) := by
    rw [hTorS_succ_len 1]
    exact length_quot_ker_comp_of_surj (LinearMap.lTensor M (dQ 2)) Lp2 (β.comp α)
      (LinearMap.lTensor M (dQ 1)) hLp2_surj hd1_fac hker_Lp2
  -- s_1 = t_1 + ℓ(range β ⧸ J) where J = (range (β ∘ α)).comap (range β).subtype
  let J : Submodule R (LinearMap.range β) :=
    (LinearMap.range (β.comp α)).comap (LinearMap.range β).subtype
  have hs1_split : Module.length S (torMod S M N 1) =
      Module.length R (LinearMap.range β ⧸ J) + Module.length R (torMod R M N 1) := by
    rw [hTorS_succ_len 0, ← hker_γ_len]
    have hrange_d1 : LinearMap.range (LinearMap.lTensor M (dQ 1)) = LinearMap.range (β.comp α) := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨Lp2 u, (LinearMap.congr_fun hd1_fac u).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨u, rfl⟩ := hLp2_surj b
        exact ⟨u, LinearMap.congr_fun hd1_fac u⟩
    exact length_quot_ker_split (LinearMap.lTensor M (dQ 1)) α β Lp1 γ
      (LinearMap.lTensor M (dQ 0)) hLp1_surj hd0_fac hker_Lp1 hrange_d1
  -- Step 10: Assemble integer lengths and telescope!
  have hka_fin : Module.length R (LinearMap.ker α) ≠ ⊤ := by
    rw [hker_α_len]
    exact ne_top_of_le_ne_top (hTorR_len_fin 1)
      (Module.length_le_of_surjective (δ3 0).rangeRestrict (δ3 0).surjective_rangeRestrict)
  have hkb_fin : Module.length R (LinearMap.ker β) ≠ ⊤ := hker_β_len ▸ hTorR_len_fin 2
  have hca_fin : Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α) ≠ ⊤ :=
    hcoker_α_len ▸ hTorR_len_fin 0
  have hKC := length_ker_coker_comp α β hka_fin hkb_fin hca_fin
  -- Define s_i, t_i, r_k as integers
  let s (i : ℕ) : ℤ := ((Module.length S (torMod S M N i)).toNat : ℤ)
  let t (i : ℕ) : ℤ := ((Module.length R (torMod R M N i)).toNat : ℤ)
  let r (k : ℕ) : ℤ := ((Module.length R (LinearMap.range (δ3 k))).toNat : ℤ)
  -- Base identity: s 0 - s 1 + s 2 = r 0 - t 1 + t 2
  have hbase : s 0 - s 1 + s 2 = r 0 - t 1 + t 2 := by
    have hs0 : (Module.length S (torMod S M N 0)).toNat = (Module.length R (torMod R M N 0)).toNat :=
      congrArg ENat.toNat hs0_len
    have hs1 : (Module.length S (torMod S M N 1)).toNat =
        (Module.length R (LinearMap.range β ⧸ J)).toNat + (Module.length R (torMod R M N 1)).toNat := by
      have heq := hs1_split
      rw [← ENat.natCast_toNat hKC.2.1, ← ENat.natCast_toNat (hTorR_len_fin 1), ← Nat.cast_add] at heq
      rw [heq, ENat.toNat_natCast]
    have hs2 : (Module.length S (torMod S M N 2)).toNat =
        (Module.length R (LinearMap.ker (β.comp α))).toNat :=
      congrArg ENat.toNat hs2_len
    have hka : (Module.length R (LinearMap.ker α)).toNat =
        (Module.length R (LinearMap.range (δ3 0))).toNat :=
      congrArg ENat.toNat hker_α_len
    have hkb : (Module.length R (LinearMap.ker β)).toNat =
        (Module.length R (torMod R M N 2)).toNat :=
      congrArg ENat.toNat hker_β_len
    have hca : (Module.length R ((M ⊗[R] Z1) ⧸ LinearMap.range α)).toNat =
        (Module.length R (torMod R M N 0)).toNat :=
      congrArg ENat.toNat hcoker_α_len
    have hnat := hKC.2.2
    rw [← hs2, hca, hka, hkb] at hnat
    dsimp only [s, t, r, J] at *
    omega
  -- Inductive relation for k ≥ 1: s (k + 2) = (r k + r (k - 1)) + (t (k + 2) - t k)
  -- Indexed by m : ℕ (with k = m + 1): s (m + 3) = r (m + 1) + r m + t (m + 3) - t (m + 1)
  have hstep (m : ℕ) : s (m + 3) = r (m + 1) + r m + t (m + 3) - t (m + 1) := by
    obtain ⟨eZ⟩ := hTorZ1_equiv m
    have hZ_fin : Module.length R (torMod R M Z1 (m + 1)) ≠ ⊤ := by
      rw [← eZ.length_eq]; exact hTorR_len_fin (m + 3)
    have hZ_len : (Module.length R (torMod R M Z1 (m + 1))).toNat =
        (Module.length R (torMod R M N (m + 3))).toNat :=
      congrArg ENat.toNat eZ.length_eq.symm
    -- Exactness at Tor_{m+1}^R(M, B1): δ3 (m + 1) → torMap B1.subtype (m + 1)
    have hB1_mid := length_nat_of_exact_middle (δ3 (m + 1)) (torMap M B1.subtype (m + 1))
      (hδ3_1 (m + 1)) (hTorR_len_fin (m + 2)) hZ_fin
    -- Exactness at Tor_{m+1}^R(M, Z1): torMap B1.subtype (m + 1) → torMap ψ (m + 1)
    have hZ1_mid := length_nat_of_exact_middle (torMap M B1.subtype (m + 1)) (torMap M ψ (m + 1))
      (hδ3_2 (m + 1)) hB1_mid.1 (hTorR_len_fin (m + 1))
    -- Exactness at Tor_{m+1}^R(M, N): torMap ψ (m + 1) → δ3 m
    have hN_mid : (Module.length R (torMod R M N (m + 1))).toNat =
        (Module.length R (LinearMap.range (torMap M ψ (m + 1)))).toNat +
          (Module.length R (LinearMap.range (δ3 m))).toNat := by
      have hker_eq : LinearMap.ker (δ3 m) = LinearMap.range (torMap M ψ (m + 1)) :=
        LinearMap.exact_iff.mp (hδ3_3 m)
      have hrf_fin : Module.length R (LinearMap.ker (δ3 m)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hTorR_len_fin (m + 1))
          (Module.length_le_of_injective (LinearMap.ker (δ3 m)).subtype (Submodule.subtype_injective _))
      have hrg_fin : Module.length R (LinearMap.range (δ3 m)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hTorR_len_fin (m + 1))
          (Module.length_le_of_surjective (δ3 m).rangeRestrict (δ3 m).surjective_rangeRestrict)
      have hsplit := length_nat_add_of_exact (LinearMap.ker (δ3 m)).subtype (δ3 m).rangeRestrict
        (Submodule.subtype_injective _) (δ3 m).surjective_rangeRestrict
        (fun b => by
          constructor
          · intro hb; exact ⟨⟨b, congrArg Subtype.val hb⟩, rfl⟩
          · rintro ⟨⟨b, hb⟩, rfl⟩; exact Subtype.ext hb)
        hrf_fin hrg_fin
      rw [hsplit.2, (LinearEquiv.ofEq _ _ hker_eq).length_eq]
    have hs_eq : (Module.length S (torMod S M N (m + 3))).toNat =
        (Module.length R (torMod R M B1 (m + 1))).toNat :=
      congrArg ENat.toNat (hTorS_ge3 m)
    dsimp only [s, t, r]
    omega
  -- Vanishing above d + 2: for all i > d + 2, s i = 0
  have ht_zero (i : ℕ) (hi : d < i) : t i = 0 := by
    have _ : Subsingleton (torMod R M N i) := hTorR_sub i hi
    simp [t]
  have hr_zero (k : ℕ) (hk : d ≤ k) : r k = 0 := by
    have _ : Subsingleton (torMod R M N (k + 1)) := hTorR_sub (k + 1) (by omega)
    have _ : Subsingleton (LinearMap.range (δ3 k)) :=
      ⟨fun ⟨_, ⟨a, ha⟩⟩ ⟨_, ⟨b, hb⟩⟩ =>
        Subtype.ext (ha.symm.trans ((congrArg (δ3 k) (Subsingleton.elim a b)).trans hb))⟩
    simp [r]
  have hs_zero (i : ℕ) (hi : d + 2 < i) : s i = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 3 := ⟨i - 3, by omega⟩
    rw [hstep m, hr_zero (m + 1) (by omega), hr_zero m (by omega),
      ht_zero (m + 3) (by omega), ht_zero (m + 1) (by omega)]
    ring
  -- Telescope: ∑ i ∈ Finset.range (d + 3), (-1)^i * s i = 0
  have hsum_tail (n : ℕ) :
      ∑ m ∈ Finset.range n, (-1 : ℤ) ^ (m + 3) * s (m + 3) =
        (-1 : ℤ) ^ (n + 2) * r n - r 0 +
          (-1 : ℤ) ^ (n + 2) * t (n + 2) + (-1 : ℤ) ^ (n + 1) * t (n + 1) + t 1 - t 2 := by
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      ring
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hstep k]
      have hp1 : (-1 : ℤ) ^ (k + 3) = -((-1 : ℤ) ^ (k + 2)) := by rw [pow_succ]; ring
      have hp2 : (-1 : ℤ) ^ (k + 2) = -((-1 : ℤ) ^ (k + 1)) := by rw [pow_succ]; ring
      rw [hp1, hp2]
      ring
  have hsum_zero : ∑ i ∈ Finset.range (d + 3), (-1 : ℤ) ^ i * s i = 0 := by
    have hsplit : ∑ i ∈ Finset.range (d + 3), (-1 : ℤ) ^ i * s i =
        (s 0 - s 1 + s 2) + ∑ m ∈ Finset.range d, (-1 : ℤ) ^ (m + 3) * s (m + 3) := by
      have h1 : d + 3 = 3 + d := by omega
      rw [h1, Finset.sum_range_add]
      have h3 : ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i * s i = s 0 - s 1 + s 2 := by
        simp [Finset.sum_range_succ]; ring
      rw [h3]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [add_comm 3 m]
    rw [hsplit, hbase, hsum_tail d, hr_zero d le_rfl,
      ht_zero (d + 2) (by omega), ht_zero (d + 1) (by omega)]
    ring
  -- Conclude Module.intersectionMultiplicity S M N = 0
  unfold Module.intersectionMultiplicity
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (d + 3))]
  · exact hsum_zero
  · intro i hi
    simp only [Function.mem_support, ne_eq, Finset.mem_coe, Finset.mem_range] at hi ⊢
    by_contra hle
    have h0 : s i = 0 := hs_zero i (by omega)
    exact hi (by dsimp [s] at h0; rw [h0, mul_zero])

/-- Main theorem (H4): Vanishing of Serre intersection multiplicity on a regular hypersurface
`R = S / (g)` when `g ∈ P ∩ Q` and `√(P + Q) = m_S`. -/
theorem serre_h4_main
    (S : Type) [CommRing S] [IsRegularLocalRing S]
    (g : S) (_hg_mem : g ∈ maximalIdeal S) (hg_ne : g ≠ 0)
    (hR_reg : IsRegularLocalRing (S ⧸ Ideal.span {g}))
    (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hgP : g ∈ P) (hgQ : g ∈ Q)
    (hPQ : (P ⊔ Q).radical = maximalIdeal S) :
    Module.intersectionMultiplicity S (S ⧸ P) (S ⧸ Q) = 0 := by
  let _ : IsDomain S := isDomain_of_isRegularLocalRing S
  let I : Ideal S := Ideal.span {g}
  have hI_le_P : I ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgP)
  have hI_le_Q : I ≤ Q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ)
  have hM_annP : ∀ a ∈ P, ∀ m : S ⧸ P, a • m = 0 := fun a ha m => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk P (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (P.mul_mem_right s ha)
  have hN_annQ : ∀ a ∈ Q, ∀ n : S ⧸ Q, a • n = 0 := fun a ha n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective n
    change Ideal.Quotient.mk Q (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Q.mul_mem_right s ha)
  let _ : IsRegularLocalRing (S ⧸ I) := hR_reg
  let _ : Module (S ⧸ I) (S ⧸ P) :=
    Module.compHom (S ⧸ P) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ P))
      (fun a ha => AddMonoidHom.ext fun m => hM_annP a (hI_le_P ha) m))
  let _ : Module (S ⧸ I) (S ⧸ Q) :=
    Module.compHom (S ⧸ Q) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ Q))
      (fun a ha => AddMonoidHom.ext fun n => hN_annQ a (hI_le_Q ha) n))
  let _ : IsScalarTower S (S ⧸ I) (S ⧸ P) :=
    ⟨fun s r m => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • m = s • (a • m)
      exact mul_smul s a m⟩
  let _ : IsScalarTower S (S ⧸ I) (S ⧸ Q) :=
    ⟨fun s r n => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • n = s • (a • n)
      exact mul_smul s a n⟩
  let _ : Module.Finite S (S ⧸ P) :=
    Module.Finite.of_surjective (Submodule.mkQ P) (Submodule.mkQ_surjective P)
  let _ : Module.Finite S (S ⧸ Q) :=
    Module.Finite.of_surjective (Submodule.mkQ Q) (Submodule.mkQ_surjective Q)
  let _ : Module.Finite (S ⧸ I) (S ⧸ P) := Module.Finite.of_restrictScalars_finite S (S ⧸ I) (S ⧸ P)
  let _ : Module.Finite (S ⧸ I) (S ⧸ Q) := Module.Finite.of_restrictScalars_finite S (S ⧸ I) (S ⧸ Q)
  refine serre_h4_aux S g hg_ne (S ⧸ I) Ideal.Quotient.mk_surjective
    (fun {X} _ _ u => exists_one_tmul_eq I u)
    (fun {X} _ _ x => ?_) P Q hPQ (S ⧸ P) (S ⧸ Q) hM_annP hN_annQ (hN_annQ g hgQ)
  constructor
  · intro h0
    have hmem : x ∈ I • (⊤ : Submodule S X) :=
      mem_ideal_smul_top_of_one_tmul_eq_zero I h0
    have hle : I • (⊤ : Submodule S X) ≤ LinearMap.range (g • (LinearMap.id : X →ₗ[S] X)) := by
      rw [Submodule.smul_le]
      rintro a ha y -
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨s • y, by change g • (s • y) = (g * s) • y; rw [mul_smul]⟩
    obtain ⟨y, hy⟩ := hle hmem
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    rw [← TensorProduct.smul_tmul]
    have hg0 : g • (1 : S ⧸ I) = 0 := by
      change Ideal.Quotient.mk I (g * 1) = 0
      rw [mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hg0, TensorProduct.zero_tmul]

end ChangeOfRings

end SerreH4Proof

theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.H4 :=
  SerreH4Proof.serre_h4_main
