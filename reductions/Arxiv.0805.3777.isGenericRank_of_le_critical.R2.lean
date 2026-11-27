import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! Friedland's critical tensor-rank conjecture, reduced at fixed first dimension and fixed difference
between the other two dimensions. One family is the five-slice format with gap one.
In each other family, two successive parity seeds suffice for width-two growth beyond a finite cutoff.
The remaining base and border tests use finite integer grids of factor coordinates.
See [Friedland, Conjecture 5.1](https://arxiv.org/abs/0805.3777). -/

namespace FriedlandRectReduction

open Arxiv.«0805.3777» Set Filter
open scoped Topology

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

lemma vanishing_on_polynomial_image {I J : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (F : J → MvPolynomial I ℂ) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : I → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P = 0 := by
  classical
  have hn : ¬ AlgebraicIndependent ℂ F := by
    intro h
    have hc := h.cardinalMk_le_trdeg
    rw [MvPolynomial.trdeg_of_isDomain] at hc
    have : Fintype.card J ≤ Fintype.card I := by simpa [Cardinal.mk_fintype] using hc
    omega
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  obtain ⟨P, ha, hP⟩ := hn
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← eval_substitution F x P, ha, map_zero]

/-- Agreement with a lower-dimensional chart on a product of infinite subsets
extends to a polynomial identity on the entire parameter space. -/
lemma generic_chart_relation {I J K : Type} [Fintype I] [Fintype J]
    (hd : Fintype.card I < Fintype.card J) (chart : J → MvPolynomial I ℂ)
    (full : J → MvPolynomial K ℂ)
    (hnormal : ∀ x : K → ℂ, (∀ i, x i ≠ 0) →
      ∃ y : I → ℂ, ∀ j, MvPolynomial.eval x (full j) = MvPolynomial.eval y (chart j)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ x : K → ℂ, MvPolynomial.eval (fun j => MvPolynomial.eval x (full j)) P = 0 := by
  classical
  obtain ⟨P, hP, hvanish⟩ := vanishing_on_polynomial_image hd chart
  have hpoly : MvPolynomial.aeval full P = 0 := by
    apply MvPolynomial.funext_set (fun _ : K => ({0}ᶜ : Set ℂ))
      (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro x hx
    have hx0 (i : K) : x i ≠ 0 := hx i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := hnormal x hx0
    rw [eval_substitution full x P, funext hy, map_zero]
    exact hvanish y
  refine ⟨P, hP, fun x => ?_⟩
  rw [← eval_substitution full x P, hpoly, map_zero]

lemma zero_is_simple (ds : List ℕ) : Holor.CPRankMax1 (0 : Holor ℂ ds) := by
  induction ds with
  | nil => exact .nil _
  | cons n ds ih =>
    have h := Holor.CPRankMax1.cons (0 : Holor ℂ [n]) (0 : Holor ℂ ds) ih
    have he : Holor.mul (0 : Holor ℂ [n]) (0 : Holor ℂ ds) = (0 : Holor ℂ (n :: ds)) := by
      funext i
      change (0 : ℂ) * 0 = 0
      simp
    rwa [he] at h

lemma decomposition_of_rank_bound {ds : List ℕ} (T : Holor ℂ ds) (r : ℕ) (hr : T.cprank ≤ r) :
    Holor.CPRankMax r T := by
  classical
  have hmin : Holor.CPRankMax T.cprank T :=
    Nat.find_spec (p := fun k => Holor.CPRankMax k T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩
  induction r, hr using Nat.le_induction with
  | base => exact hmin
  | succ k _ ih => simpa using Holor.CPRankMax.succ k 0 T (zero_is_simple ds) ih

lemma finite_sum_of_simple {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : Holor.CPRankMax r T) :
    ∃ u : Fin r → Holor ℂ ds, (∀ i, Holor.CPRankMax1 (u i)) ∧ ∑ i, u i = T := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ k x y hx hy ih =>
    obtain ⟨u, hu, hs⟩ := ih
    refine ⟨Fin.cons x u, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hu j
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hs]

/-- The explicit triple of natural-number indices in a rectangular holor. -/
lemma rectangular_indices (d e f : ℕ) :
    ∃ E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f, ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ := by
  let mk (z : Fin d × Fin e × Fin f) : HolorIndex [d,e,f] :=
    ⟨[z.1.val,z.2.1.val,z.2.2.val],.cons z.1.isLt (.cons z.2.1.isLt (.cons z.2.2.isLt .nil))⟩
  have hb : Function.Bijective mk := by
    constructor
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
      have he := congrArg Subtype.val h
      simp [mk] at he
      exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))
    · rintro ⟨is,h⟩
      cases h with | cons hi h =>
        cases h with | cons hj h =>
          cases h with | cons hk h =>
            cases h
            exact ⟨(⟨_,hi⟩,⟨_,hj⟩,⟨_,hk⟩),rfl⟩
  exact ⟨(Equiv.ofBijective mk hb).symm, fun _ _ _ => rfl⟩

/-- Absorb the trailing scalar of a simple holor into its last vector. -/
lemma simple_coordinates {d e f : ℕ} {T : Holor ℂ [d,e,f]} (h : Holor.CPRankMax1 T) :
    ∃ (a : Fin d → ℂ) (b : Fin e → ℂ) (c : Fin f → ℂ), ∀ i j k,
      T ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ = a i * b j * c k := by
  cases h with
  | cons a yz hyz =>
    cases hyz with
    | cons b zs hzs =>
      cases hzs with
      | cons c z hz =>
        refine ⟨fun i => a ⟨[i.val],.cons i.isLt .nil⟩,
          fun j => b ⟨[j.val],.cons j.isLt .nil⟩,
          fun k => c ⟨[k.val],.cons k.isLt .nil⟩ * z ⟨[],.nil⟩, ?_⟩
        intro i j k
        change a _ * (b _ * (c _ * z _)) = a _ * b _ * (c _ * z _)
        rw [mul_assoc]
        rfl

/-- A low-rank holor is a coordinatewise sum of products of vector entries. -/
lemma sum_coordinates {d e f : ℕ} (E : HolorIndex [d,e,f] ≃ Fin d × Fin e × Fin f)
    (hE : ∀ (i : Fin d) (j : Fin e) (k : Fin f),
      E.symm (i,j,k) = ⟨[i.val,j.val,k.val],.cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩)
    (T : Holor ℂ [d,e,f]) (r : ℕ) (hr : T.cprank ≤ r) :
    ∃ (a : Fin r → Fin d → ℂ) (b : Fin r → Fin e → ℂ) (c : Fin r → Fin f → ℂ),
      ∀ q, (∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) = T q := by
  classical
  obtain ⟨u,hu,hT⟩ := finite_sum_of_simple (decomposition_of_rank_bound T r hr)
  choose a b c habc using fun t => simple_coordinates (hu t)
  refine ⟨a,b,c,fun q => ?_⟩
  have term (t : Fin r) := habc t (E q).1 (E q).2.1 (E q).2.2
  have at_q := Finset.sum_apply (M := fun _ : HolorIndex [d,e,f] => ℂ) q
    (Finset.univ : Finset (Fin r)) (fun t => fun v => u t v)
  refine (Finset.sum_congr rfl (fun t _ => ?_)).trans (at_q.symm.trans (congrFun hT q))
  simpa only [← hE,Prod.mk.eta,Equiv.symm_apply_apply] using (term t).symm

/-- Scaling the first two factors to first coordinate one removes two
parameters per summand. Their product is absorbed into the third factor. -/
lemma rectangular_polynomial {J : Type} [Fintype J] (d e f r : ℕ)
    (E : J ≃ Fin (d+1) × Fin (e+1) × Fin f) (hd : r*(d+(e+f)) < Fintype.card J) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧
      ∀ (a : Fin r → Fin (d+1) → ℂ) (b : Fin r → Fin (e+1) → ℂ) (c : Fin r → Fin f → ℂ),
        MvPolynomial.eval (fun q => ∑ t, a t (E q).1 * b t (E q).2.1 * c t (E q).2.2) P = 0 := by
  classical
  let Raw := Fin r × (Fin (d+1) ⊕ (Fin (e+1) ⊕ Fin f))
  let Chart := Fin r × (Fin d ⊕ (Fin e ⊕ Fin f))
  let raw (q : J) : MvPolynomial Raw ℂ :=
    ∑ t : Fin r, MvPolynomial.X (t,Sum.inl (E q).1) * MvPolynomial.X (t,Sum.inr (Sum.inl (E q).2.1)) *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  let chart (q : J) : MvPolynomial Chart ℂ :=
    ∑ t : Fin r, Fin.cases 1 (fun i => MvPolynomial.X (t,Sum.inl i)) (E q).1 *
      Fin.cases 1 (fun j => MvPolynomial.X (t,Sum.inr (Sum.inl j))) (E q).2.1 *
      MvPolynomial.X (t,Sum.inr (Sum.inr (E q).2.2))
  have hnorm (x : Raw → ℂ) (hx : ∀ j, x j ≠ 0) :
      ∃ y : Chart → ℂ, ∀ q, MvPolynomial.eval x (raw q) = MvPolynomial.eval y (chart q) := by
    let y : Chart → ℂ := fun (t,s) => match s with
      | .inl i => x (t,.inl i.succ) / x (t,.inl 0)
      | .inr (.inl j) => x (t,.inr (.inl j.succ)) / x (t,.inr (.inl 0))
      | .inr (.inr k) => x (t,.inr (.inr k)) * x (t,.inl 0) * x (t,.inr (.inl 0))
    refine ⟨y,fun q => ?_⟩
    simp only [raw,chart,map_sum,map_mul,MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro t _
    have ha (i : Fin (d+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun i : Fin d => MvPolynomial.X (t,Sum.inl i)) i) =
          x (t,.inl i) / x (t,.inl 0) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hx]
      · simp [y]
    have hb (j : Fin (e+1)) :
        MvPolynomial.eval y (Fin.cases 1 (fun j : Fin e => MvPolynomial.X (t,Sum.inr (Sum.inl j))) j) =
          x (t,.inr (.inl j)) / x (t,.inr (.inl 0)) := by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [hx]
      · simp [y]
    rw [ha,hb]
    dsimp only [y]
    field_simp [hx]
  have hcard : Fintype.card Chart < Fintype.card J := by
    simpa only [Chart,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin] using hd
  obtain ⟨P,hP,hzero⟩ := generic_chart_relation hcard chart raw hnorm
  refine ⟨P,hP,fun a b c => ?_⟩
  let x : Raw → ℂ := fun (t,s) => match s with
    | .inl i => a t i
    | .inr (.inl j) => b t j
    | .inr (.inr k) => c t k
  simpa only [raw,x,map_sum,map_mul,MvPolynomial.eval_X] using hzero x

/-- For any rectangular format, ranks whose normalized parameter count falls
below the number of tensor entries have nowhere dense closure. -/
theorem lower_of_count (a b c r : ℕ) (hdim : (a+b+c-2)*r < a*b*c) :
    interior (closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r}) = ∅ := by
  classical
  obtain _|d := a
  · simp at hdim
  obtain _|e := b
  · simp at hdim
  obtain ⟨E,hE⟩ := rectangular_indices (d+1) (e+1) c
  let _ : Fintype (HolorIndex [d+1,e+1,c]) := Fintype.ofEquiv _ E.symm
  have hd : r*(d+(e+c)) < Fintype.card (HolorIndex [d+1,e+1,c]) := by
    rw [Fintype.card_congr E]
    have h : d.succ+e.succ+c-2 = d+(e+c) := by omega
    simpa only [Fintype.card_prod,Fintype.card_fin,h,Nat.mul_comm (d+(e+c)) r,Nat.mul_assoc,
      Nat.succ_eq_add_one] using hdim
  obtain ⟨P,hP,hzero⟩ := rectangular_polynomial d e c r E hd
  let Z := {T : Holor ℂ [d+1,e+1,c] | MvPolynomial.eval T P = 0}
  have hclosed : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have hsub : {T : Holor ℂ [d+1,e+1,c] | T.cprank ≤ r} ⊆ Z := by
    intro T hT
    obtain ⟨x,y,z,h⟩ := sum_coordinates E hE T r hT
    change MvPolynomial.eval T P = 0
    simpa only [funext h] using hzero x y z
  have hempty : interior Z = ∅ := interior_polynomial_zero_locus P hP
  apply Set.subset_empty_iff.mp
  simpa only [hempty] using interior_mono (closure_minimal hsub hclosed)

end FriedlandRectReduction

namespace FriedlandRectReduction.Dominance

open Set Filter
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

end FriedlandRectReduction.Dominance

namespace FriedlandRectReduction

open Dominance
open Arxiv.«0805.3777»

/-- If the derivative of the sum of simple tensors is surjective at one
configuration, a dense open set has CP rank at most the number of summands. -/
theorem upper_of_witness {a b c r : ℕ} (h :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k) +
          x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    ∃ U : Set (Holor ℂ [a,b,c]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨x,y,z,hspan⟩ := h
  let consIdx (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds := {
    toFun := fun
      | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
      | ⟨[], h⟩ => nomatch h
    invFun := fun q => ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
    left_inv := by
      rintro ⟨l, hl⟩
      cases l with
      | nil => cases hl
      | cons i is => rfl
    right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl }
  let nilIdx : HolorIndex [] ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨[], .nil⟩
    left_inv := by rintro ⟨l, hl⟩; cases hl; rfl
    right_inv := by intro q; cases q; rfl }
  let point (i : Fin a) (j : Fin b) (k : Fin c) : HolorIndex [a,b,c] :=
    ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩
  have triple (q : HolorIndex [a,b,c]) : ∃ i j k, q = point i j k := by
    obtain ⟨⟨i,q⟩,rfl⟩ := (consIdx a [b,c]).symm.surjective q
    obtain ⟨⟨j,q⟩,rfl⟩ := (consIdx b [c]).symm.surjective q
    obtain ⟨⟨k,q⟩,rfl⟩ := (consIdx c []).symm.surjective q
    obtain ⟨⟨⟩,rfl⟩ := nilIdx.symm.surjective q
    exact ⟨i,j,k,rfl⟩
  let _ : Finite (HolorIndex [a,b,c]) := Finite.of_surjective
    (fun q : Fin a × Fin b × Fin c => point q.1 q.2.1 q.2.2) (by
      intro q
      obtain ⟨i,j,k,rfl⟩ := triple q
      exact ⟨(i,j,k),rfl⟩)
  let _ : Fintype (HolorIndex [a,b,c]) := Fintype.ofFinite _
  let P := Fin r × (Fin a ⊕ (Fin b ⊕ Fin c))
  let entry {n : ℕ} (q : HolorIndex [n]) : Fin n := (consIdx n [] q).1
  let first (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inl (entry (HolorIndex.take (ds₁ := [a]) (ds₂ := [b,c]) q)))
  let second (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let third (t : Fin r) (q : HolorIndex [a,b,c]) : P :=
    (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [b]) (ds₂ := [c])
      (HolorIndex.drop (ds₁ := [a]) (ds₂ := [b,c]) q)))))
  let pack (A : Fin r → Fin a → ℂ) (B : Fin r → Fin b → ℂ) (C : Fin r → Fin c → ℂ) (q : P) : ℂ :=
    q.2.elim (A q.1) (Sum.elim (B q.1) (C q.1))
  let φ (v : P → ℂ) (q : HolorIndex [a,b,c]) :=
    ∑ t : Fin r, v (first t q) * (v (second t q) * v (third t q))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack x y z)
    intro Y
    obtain ⟨u,v,w,hw⟩ := hspan fun i j k => Y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro q
    obtain ⟨i,j,k,rfl⟩ := triple q
    exact hw i j k
  let F (q : HolorIndex [a,b,c]) : MvPolynomial P ℂ :=
    ∑ t : Fin r, MvPolynomial.X (first t q) *
      (MvPolynomial.X (second t q) * MvPolynomial.X (third t q))
  have he : (fun v : P → ℂ => fun q => MvPolynomial.eval v (F q)) = φ := by
    funext v q
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ),isOpen_interior,hd,?_⟩
  intro T hT
  obtain ⟨v,rfl⟩ := interior_subset hT
  let fa (t : Fin r) (i : HolorIndex [a]) := v (t, Sum.inl (entry i))
  let fb (t : Fin r) (j : HolorIndex [b]) := v (t, Sum.inr (.inl (entry j)))
  let fc (t : Fin r) (k : HolorIndex [c]) := v (t, Sum.inr (.inr (entry k)))
  have hv : (φ v : Holor ℂ [a,b,c]) = ∑ t, Holor.mul (fa t) (Holor.mul (fb t) (fc t)) := by
    funext q
    rw [eval_holor_sum]
    rfl
  rw [hv]
  exact Nat.find_min' _ (tensor_sum_rank fa fb fc)

end FriedlandRectReduction

namespace FriedlandRectReduction

private lemma positive_round {D k n u v : ℕ} (hD : 0<D) (hid : D*k+u=4*n+v)
    (hpos : v<u) (hsize : u≤v+D) : n ⌈/⌉ D = k/4+1 := by
  let q := k/4
  have lq : 4*q ≤ k := by dsimp [q]; omega
  have uq : k+1 ≤ 4*(q+1) := by dsimp [q]; omega
  have lo : D*q < n := by nlinarith only [hid, hpos, Nat.mul_le_mul_left D lq]
  have hi : n ≤ D*(q+1) := by nlinarith only [hid, hsize, Nat.mul_le_mul_left D uq]
  refine le_antisymm ((ceilDiv_le_iff_le_mul hD).mpr hi) ?_
  by_contra! he
  exact (not_lt_of_ge ((ceilDiv_le_iff_le_mul hD).mp (show n ⌈/⌉ D ≤ q by dsimp [q]; omega))) lo

private lemma nonpositive_round {D k n u v : ℕ} (hD : 0<D) (hid : D*k+u=4*n+v)
    (huv : u≤v) (hsize : v<u+D) : n ⌈/⌉ D = (k+3)/4 := by
  let q := (k+3)/4
  have uq : k ≤ 4*q := by dsimp [q]; omega
  have hi : n ≤ D*q := by nlinarith only [hid, huv, Nat.mul_le_mul_left D uq]
  refine le_antisymm ((ceilDiv_le_iff_le_mul hD).mpr hi) ?_
  by_contra! he
  have hl : 4*(n ⌈/⌉ D)+1 ≤ k := by omega
  have hn : n ≤ D*(n ⌈/⌉ D) := (ceilDiv_le_iff_le_mul hD).mp le_rfl
  nlinarith only [hid, hsize, hn, Nat.mul_le_mul_left D hl]

private lemma tail_formula {a m s : ℕ} (ha : 3≤a) (hm : a+s+3+(a-2)+a*(a-2)^2+a*s^2 ≤ m) :
    a*m*(m+s) ⌈/⌉ (a+m+(m+s)-2) = if s<a-2 then a*(2*m+s-(a-2))/4+1 else (a*(2*m+s-(a-2))+3)/4 := by
  let h := a-2
  let D := 2*m+h+s
  let k := a*(2*m+s-h)
  let n := a*m*(m+s)
  have hsub : h ≤ 2*m+s := by dsimp [h]; omega
  have hrem : (if s<h then a*h^2-a*s^2 else a*s^2-a*h^2+1) ≤ D := by
    dsimp [D,h]
    split <;> omega
  have hp : 0<D := by dsimp [D,h]; omega
  have hd : a+m+(m+s)-2 = D := by dsimp [D,h]; omega
  have hid : D*k+a*h^2 = 4*n+a*s^2 := by
    have hx := congrArg (fun x : ℕ => (2*m+h+s)*a*x) (Nat.sub_add_cancel hsub)
    dsimp only [D,k,n]
    nlinarith only [hx]
  rw [hd]
  change n ⌈/⌉ D = if s<h then k/4+1 else (k+3)/4
  by_cases hs : s<h
  · rw [if_pos hs] at hrem ⊢
    apply positive_round hp hid _ (by omega)
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hs (by decide)) (by omega)
  · rw [if_neg hs] at hrem ⊢
    apply nonpositive_round hp hid _ (by omega)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private lemma tail_add_two {a m s : ℕ} (ha : 3≤a) (hm : a+s+3+(a-2)+a*(a-2)^2+a*s^2 ≤ m) :
    a*(m+2)*(m+2+s) ⌈/⌉ (a+(m+2)+(m+2+s)-2) = (a*m*(m+s) ⌈/⌉ (a+m+(m+s)-2)) + a := by
  rw [tail_formula ha (show a+s+3+(a-2)+a*(a-2)^2+a*s^2 ≤ m+2 by omega), tail_formula ha hm]
  have hb : a-2 ≤ 2*m+s := by omega
  have hs : 2*(m+2)+s-(a-2) = (2*m+s-(a-2))+4 := by omega
  rw [hs, Nat.mul_add, Nat.mul_comm a 4]
  by_cases h : s<a-2
  · simp only [if_pos h, Nat.add_mul_div_left _ _ (by decide : 0<4)]
    omega
  · simp only [if_neg h]
    rw [show a*(2*m+s-(a-2))+4*a+3 = (a*(2*m+s-(a-2))+3)+4*a by omega,
      Nat.add_mul_div_left _ _ (by decide : 0<4)]

lemma rank_add_two_mul {a m s : ℕ} (ha : 3 ≤ a) (hm : a+s+3+(a-2)+a*(a-2)^2+a*s^2 ≤ m) (t : ℕ) :
    a*(m+2*t)*(m+2*t+s) ⌈/⌉ (a+(m+2*t)+(m+2*t+s)-2) = (a*m*(m+s) ⌈/⌉ (a+m+(m+s)-2))+a*t := by
  let R (k : ℕ) := a*k*(k+s) ⌈/⌉ (a+k+(k+s)-2)
  change R (m+2*t) = R m+a*t
  have step (k : ℕ) (hk : a+s+3+(a-2)+a*(a-2)^2+a*s^2 ≤ k) : R (k+2) = R k+a := tail_add_two ha hk
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, step _ (by omega), ih, Nat.mul_succ, Nat.add_assoc]

end FriedlandRectReduction

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2

open Arxiv.«0805.3777» Set
open scoped Topology

/-- The five-slice family with successive final dimensions has a spanning tangent configuration. -/
def H1 : Prop :=
  ∀ m : ℕ, 5 ≤ m →
    let r := 5*m*(m+1) ⌈/⌉ (5+m+(m+1)-2)
    ∃ x : Fin r → Fin 5 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m+1) → ℂ,
      ∀ T : Fin 5 → Fin m → Fin (m+1) → ℂ, ∃ u : Fin r → Fin 5 → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+1) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))

/-- For every other fixed first dimension and gap, test the admissible base sizes through the second seed. -/
def H2 : Prop :=
  ∀ a s m : ℕ, 3 ≤ a → (a,s) ≠ (5,1) → a ≤ m →
    let N := a+s+3+(a-2)+a*(a-2)^2+a*s^2
    m ≤ N+1 → m+s ≤ (a-1)*(m-1) → (∀ p : ℕ, (a,m,m+s) ≠ (3,2*p+1,2*p+1)) →
    let r := a*m*(m+s) ⌈/⌉ (a+m+(m+s)-2)
    let D := 2*a*m*(m+s)+1
    let val (u : Fin D) : ℂ := u.val
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin m → Fin D, ∃ z : Fin r → Fin (m+s) → Fin D,
      ∀ T : Fin a → Fin m → Fin (m+s) → ℂ, ∃ u : Fin r → Fin a → ℂ,
        ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m+s) → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(val (y t j)*val (z t k)) + val (x t i)*(v t j*val (z t k)) +
            val (x t i)*(val (y t j)*w t k))

/-- Test a width-two border at each admissible parity seed. The regular coordinates are the left summands. -/
def H3 : Prop :=
  ∀ a s d : ℕ, 3 ≤ a → (a,s) ≠ (5,1) → a ≤ d →
    let N := a+s+3+(a-2)+a*(a-2)^2+a*s^2
    (d=N ∨ d=N+1) → d+s ≤ (a-1)*(d-1) → (∀ p : ℕ, (a,d,d+s) ≠ (3,2*p+1,2*p+1)) →
    let e := d+s
    let r := a*d*e ⌈/⌉ (a+d+e-2)
    let D := 2*a*(d+2)*(e+2)+1
    let B := Fin 2 ⊕ Fin d
    let C := Fin 2 ⊕ Fin e
    let val (z : Fin D) : ℂ := z.val
    ∃ X : Fin a → Fin a → Fin D, ∃ Y : Fin a → B → Fin D, ∃ Z : Fin a → C → Fin D,
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin d → Fin D, ∃ z : Fin r → Fin e → Fin D,
      ∀ T : Fin a → B → C → ℂ, ∃ U : Fin a → Fin a → ℂ, ∃ V : Fin a → B → ℂ, ∃ W : Fin a → C → ℂ,
        ∃ v w : Fin r → Fin 2 → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
          T i j k = (∑ t, (U t i*(val (Y t j)*val (Z t k)) + val (X t i)*(V t j*val (Z t k)) +
            val (X t i)*(val (Y t j)*W t k))) +
          ∑ t, (val (x t i)*(j.elim (v t) (fun _ => 0)*k.elim (fun _ => 0) (fun l => val (z t l))) +
            val (x t i)*(j.elim (fun _ => 0) (fun l => val (y t l))*k.elim (w t) (fun _ => 0)))

/-- A spanning base and its width-two border grow by any number of regular blocks. -/
def H4 : Prop :=
  let spans (a d e r : ℕ) : Prop :=
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin d → ℂ, ∃ z : Fin r → Fin e → ℂ,
      ∀ T : Fin a → Fin d → Fin e → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin d → ℂ,
        ∃ w : Fin r → Fin e → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
  let border (a d e r : ℕ) : Prop :=
    let B := Fin 2 ⊕ Fin d
    let C := Fin 2 ⊕ Fin e
    ∃ X : Fin a → Fin a → ℂ, ∃ Y : Fin a → B → ℂ, ∃ Z : Fin a → C → ℂ,
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin d → ℂ, ∃ z : Fin r → Fin e → ℂ,
      ∀ T : Fin a → B → C → ℂ, ∃ U : Fin a → Fin a → ℂ, ∃ V : Fin a → B → ℂ, ∃ W : Fin a → C → ℂ,
        ∃ v w : Fin r → Fin 2 → ℂ, ∀ i j k, (j.isLeft=true ∨ k.isLeft=true) →
          T i j k = (∑ t, (U t i*(Y t j*Z t k) + X t i*(V t j*Z t k) + X t i*(Y t j*W t k))) +
            ∑ t, (x t i*(j.elim (v t) (fun _ => 0)*k.elim (fun _ => 0) (z t)) +
              x t i*(j.elim (fun _ => 0) (y t)*k.elim (w t) (fun _ => 0)))
  ∀ a d e base t : ℕ, 3 ≤ a → spans a d e base → border a d e base →
    spans a (d+2*t) (e+2*t) (base+a*t)

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2

open Arxiv.«0805.3777» Set
open scoped Topology

private lemma generic_of_spanning (a b c : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (span : let r := a*b*c ⌈/⌉ (a+b+c-2)
      ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin c → ℂ,
        ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
          ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
            T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))) :
    IsGenericRank [a,b,c] (a*b*c ⌈/⌉ (a+b+c-2)) := by
  classical
  let d := a+b+c-2
  let r := a*b*c ⌈/⌉ d
  have hd : 0<d := by dsimp [d]; omega
  have habc : 0<a*b*c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hrpos : 0<r := by
    by_contra! hz
    have he : a*b*c≤d*0 := (ceilDiv_le_iff_le_mul hd).mp hz
    omega
  have hcost : d*(r-1)<a*b*c := by
    by_contra! he
    have hsmall : r≤r-1 := (ceilDiv_le_iff_le_mul hd).mpr he
    omega
  obtain ⟨U,hu,hU,hi⟩ := @FriedlandRectReduction.upper_of_witness a b c r span
  let K := closure {T : Holor ℂ [a,b,c] | T.cprank ≤ r-1}
  have hl : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (FriedlandRectReduction.lower_of_count a b c (r-1) hcost)
  refine ⟨U ∩ Kᶜ,hu.inter isClosed_closure.isOpen_compl,hU.inter_of_isOpen_left hl hu,?_⟩
  intro T ht
  have hup := hi T ht.1
  have hlo : ¬ T.cprank≤r-1 := fun he => ht.2 (subset_closure he)
  change T.cprank=r
  omega

/-- Choose a seed with the same parity as the desired second dimension and apply width-two growth. -/
theorem main : H1 → H2 → H3 → H4 → type_of% @Arxiv.«0805.3777».isGenericRank_of_le_critical := by
  intro h₁ h₂ h₃ h₄ a b c ha hab hbc hcrit hexc
  obtain ⟨s,rfl⟩ : ∃ s, c=b+s := ⟨c-b,by omega⟩
  apply generic_of_spanning a b (b+s) ha hab hbc
  by_cases special : (a,s)=(5,1)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj special
    exact h₁ b hab
  let N := a+s+3+(a-2)+a*(a-2)^2+a*s^2
  let R (m : ℕ) := a*m*(m+s) ⌈/⌉ (a+m+(m+s)-2)
  let spans (d e r : ℕ) : Prop :=
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin d → ℂ, ∃ z : Fin r → Fin e → ℂ,
      ∀ T : Fin a → Fin d → Fin e → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin d → ℂ,
        ∃ w : Fin r → Fin e → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(y t j*z t k) + x t i*(v t j*z t k) + x t i*(y t j*w t k))
  have seed (k : ℕ) (hak : a ≤ k) (hk : k ≤ N+1) (hc : k+s ≤ (a-1)*(k-1))
      (hx : ∀ p : ℕ, (a,k,k+s) ≠ (3,2*p+1,2*p+1)) : spans k (k+s) (R k) := by
    obtain ⟨X,Y,Z,hw⟩ := h₂ a s k ha special hak hk hc hx
    exact ⟨fun t i => ((X t i).val : ℂ),fun t j => ((Y t j).val : ℂ),fun t k => ((Z t k).val : ℂ),hw⟩
  change spans b (b+s) (R b)
  by_cases early : b ≤ N+1
  · exact seed b hab early hcrit hexc
  let d := N+(b-N)%2
  let t := (b-N)/2
  have hd : d=N ∨ d=N+1 := by dsimp [d]; omega
  have hNd : N≤d := by omega
  have grow : b=d+2*t := by dsimp [d,t]; omega
  have had : a≤d := by dsimp [N] at hNd; omega
  have hsd : s+2≤d := by dsimp [N] at hNd; omega
  have hdc : d+s ≤ (a-1)*(d-1) := by
    have h := Nat.mul_le_mul_right (d-1) (show 2 ≤ a-1 by omega)
    omega
  have hdx : ∀ p : ℕ, (a,d,d+s) ≠ (3,2*p+1,2*p+1) := by
    intro p hp
    apply hexc (p+t)
    simp only [Prod.mk.injEq] at hp ⊢
    exact ⟨hp.1,by omega,by omega⟩
  have hr : R (d+2*t) = R d+a*t := FriedlandRectReduction.rank_add_two_mul ha hNd t
  rw [grow,hr,show d+2*t+s=(d+s)+2*t by omega]
  apply h₄ a d (d+s) (R d) t ha (seed d had (by omega) hdc hdx)
  obtain ⟨X,Y,Z,x,y,z,hw⟩ := h₃ a s d ha special had hd hdc hdx
  exact ⟨fun t i => ((X t i).val : ℂ),fun t j => ((Y t j).val : ℂ),fun t k => ((Z t k).val : ℂ),
    fun t i => ((x t i).val : ℂ),fun t j => ((y t j).val : ℂ),fun t k => ((z t k).val : ℂ),hw⟩

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2
