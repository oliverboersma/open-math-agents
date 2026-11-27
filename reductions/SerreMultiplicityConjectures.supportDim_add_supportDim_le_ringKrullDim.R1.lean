import FormalConjectures.Wikipedia.SerreMultiplicityConjectures

-- Reduction SerreMultiplicityConjectures.supportDim_add_supportDim_le_ringKrullDim.R1 of Dimension inequality.
-- Credit: @ItsNotTheGabs
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Serre's Dimension Inequality: Reduction to Complete Unramified & Cohen Structure Steps

Serre's dimension inequality states that if `(R, m)` is a regular local ring and `M, N` are finitely
generated `R`-modules such that `M ⊗[R] N` has finite length, then
`Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R`.

Following Serre (*Local Algebra*, Ch. V, Part B, §3, Theorem 3), this file carries out in `main`:
1. **Reduction from modules to prime quotients:** replacing arbitrary finitely generated `M, N`
   by prime ideals `P, Q` realizing `supportDim R M` and `supportDim R N` with
   `(P ⊔ Q).radical = maximalIdeal R`.
2. **Countable descent (Downward Löwenheim–Skolem for regular local rings):** constructing a
   countable pure local subring `Rsub ⊆ R` (transferred to `Type 0` via `Shrink`) that remains a
   Noetherian regular local ring of the same Krull dimension and preserves the prime chains and
   `m`-primarity of `P ⊔ Q`. This bridges the arbitrary universe `u` of the target statement to
   universe-monomorphic (`Type`) hypotheses `H1`–`H4`.
3. **Reduction to complete regular local rings** via `H1` (Noetherianity and Krull dimension
   invariance of `maximalIdeal`-adic completion).
4. **Ramified mixed-characteristic deduction** via Serre's positivity-vs-vanishing argument:
   lifting a complete ramified regular local ring `R` to a complete unramified regular local ring
   `S` of dimension `dim R + 1` with `R ≃+* S ⧸ (g)` (`H3`), applying the unramified dimension
   inequality and positivity theorem (`H2`), and ruling out equality `dim + dim = dim R + 1` by
   vanishing of `intersectionMultiplicity S (S ⧸ P') (S ⧸ Q')` for modules annihilated by `g` (`H4`).

The four hypotheses `H1`–`H4` isolate the genuinely distinct classical theorems missing from Mathlib:
- `H1`: `m`-adic completion of a Noetherian local ring is Noetherian and preserves quotient Krull
  dimensions (Stacks 05GH, 07NV).
- `H2`: Serre's dimension inequality for complete equicharacteristic and unramified mixed-char
  regular local rings, together with positivity of `intersectionMultiplicity` in the unramified
  mixed-char equality case (Serre [Se00], Ch. V.B.6, via Cohen's theorem and reduction to the
  diagonal).
- `H3`: Cohen's presentation of a complete ramified regular local ring as a hypersurface quotient
  `S ⧸ (g)` of a complete unramified regular local ring of dimension `dim R + 1`.
- `H4`: Vanishing of `Module.intersectionMultiplicity S (S ⧸ P) (S ⧸ Q)` when a nonzero element
  `g ∈ P ∩ Q` cuts out a regular local quotient `S ⧸ (g)` (change-of-rings Tor long exact sequence).
-/

namespace OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1

open IsLocalRing Module TensorProduct Ideal

/-- `m`-adic completion of a Noetherian local ring is Noetherian and preserves the Krull dimension
of every quotient `R ⧸ I`. -/
def H1 : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsNoetherianRing (AdicCompletion (maximalIdeal R) R) ∧
    ∀ (I : Ideal R),
      ringKrullDim (AdicCompletion (maximalIdeal R) R ⧸
        I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
      ringKrullDim (R ⧸ I)

/-- Serre's dimension inequality for complete equicharacteristic and complete unramified
mixed-characteristic regular local rings, together with positivity of the intersection multiplicity
in the unramified mixed-characteristic equality case. -/
def H2 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R],
    ((ringChar (ResidueField R) : R) = 0 ∨
      (ringChar (ResidueField R) : R) ∉ maximalIdeal R ^ 2) →
    ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
      (P ⊔ Q).radical = maximalIdeal R →
      ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) ≤ ringKrullDim R ∧
      ((ringChar (ResidueField R) : R) ≠ 0 →
        ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R →
        0 < Module.intersectionMultiplicity R (R ⧸ P) (R ⧸ Q))

/-- Cohen's structure presentation of a complete ramified mixed-characteristic regular local ring:
it is a quotient `S ⧸ (g)` of a complete unramified regular local ring `S` of dimension
`dim R + 1` by a nonzero element `g ∈ maximalIdeal S`. -/
def H3 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R],
    (ringChar (ResidueField R) : R) ≠ 0 →
    (ringChar (ResidueField R) : R) ∈ maximalIdeal R ^ 2 →
    ∃ (S : Type) (_ : CommRing S) (_ : IsRegularLocalRing S)
      (_ : IsAdicComplete (maximalIdeal S) S) (g : S) (f : S →+* R),
      (ringChar (ResidueField S) : S) ∉ maximalIdeal S ^ 2 ∧
      g ∈ maximalIdeal S ∧ g ≠ 0 ∧
      Function.Surjective f ∧ RingHom.ker f = Ideal.span {g} ∧
      ringKrullDim S = ringKrullDim R + 1

/-- Vanishing of Serre's intersection multiplicity over a regular local ring `S` for prime
quotients `S ⧸ P` and `S ⧸ Q` killed by a common nonzero element `g ∈ maximalIdeal S` such that
`S ⧸ (g)` is regular. -/
def H4 : Prop :=
  ∀ (S : Type) [CommRing S] [IsRegularLocalRing S]
    (g : S), g ∈ maximalIdeal S → g ≠ 0 →
    IsRegularLocalRing (S ⧸ Ideal.span {g}) →
    ∀ (P Q : Ideal S) [P.IsPrime] [Q.IsPrime],
      g ∈ P → g ∈ Q →
      (P ⊔ Q).radical = maximalIdeal S →
      Module.intersectionMultiplicity S (S ⧸ P) (S ⧸ Q) = 0

lemma countable_subring_closure {R : Type*} [Ring R] {s : Set R} (hs : s.Countable) :
    (Subring.closure s : Set R).Countable := by
  let gen : ℕ → Set R := Nat.rec (s ∪ {0, 1}) fun _ T =>
    T ∪ (fun x => -x) '' T ∪ (fun p : R × R => p.1 + p.2) '' (T ×ˢ T) ∪
      (fun p : R × R => p.1 * p.2) '' (T ×ˢ T)
  have hgen_mono : Monotone gen := monotone_nat_of_le_succ fun n x hx =>
    Or.inl (Or.inl (Or.inl hx))
  have hgen_count : ∀ n, (gen n).Countable := fun n => by
    induction n with
    | zero => exact hs.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih =>
      exact ((ih.union (ih.image _)).union ((ih.prod ih).image _)).union ((ih.prod ih).image _)
  let U : Subring R :=
    { carrier := ⋃ n, gen n
      zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
      one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
      neg_mem' := fun hx => by
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨n + 1, Or.inl (Or.inl (Or.inr ⟨_, hn, rfl⟩))⟩
      add_mem' := fun hx hy => by
        obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp hx
        obtain ⟨n₂, hn₂⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨max n₁ n₂ + 1, Or.inl (Or.inr ⟨(_, _), ?_, rfl⟩)⟩
        exact ⟨hgen_mono (le_max_left _ _) hn₁, hgen_mono (le_max_right _ _) hn₂⟩
      mul_mem' := fun hx hy => by
        obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp hx
        obtain ⟨n₂, hn₂⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨max n₁ n₂ + 1, Or.inr ⟨(_, _), ?_, rfl⟩⟩
        exact ⟨hgen_mono (le_max_left _ _) hn₁, hgen_mono (le_max_right _ _) hn₂⟩ }
  have hle : Subring.closure s ≤ U := Subring.closure_le.mpr fun x hx =>
    Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩
  exact (Set.countable_iUnion hgen_count).mono hle

lemma support_subset_closedPoint_of_isFiniteLength {R : Type*} [CommRing R] [IsLocalRing R]
    {X : Type*} [AddCommGroup X] [Module R X] (h : IsFiniteLength R X) :
    Module.support R X ⊆ {IsLocalRing.closedPoint R} := by
  induction h with
  | of_subsingleton =>
    simp [Module.support_eq_empty]
  | @of_simple_quotient M _ _ N _ _ ih =>
    have hsupp := Module.support_of_exact (f := N.subtype) (g := N.mkQ)
      (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_subtype]))
      N.injective_subtype N.mkQ_surjective
    rw [hsupp]
    refine Set.union_subset ih ?_
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    rw [e.support_eq]
    intro p hp
    have hle := Module.annihilator_le_of_mem_support hp
    rw [Ideal.annihilator_quotient] at hle
    simp only [Set.mem_singleton_iff]
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) hle)

lemma mem_support_tensorProduct_of_mem {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {p : PrimeSpectrum R} (hM : p ∈ Module.support R M) (hN : p ∈ Module.support R N) :
    p ∈ Module.support R (M ⊗[R] N) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hM hN ⊢
  let K := p.asIdeal.ResidueField
  have : Nontrivial (K ⊗[R] M) := hM
  have : Nontrivial (K ⊗[R] N) := hN
  have e : K ⊗[R] (M ⊗[R] N) ≃ₗ[K] (K ⊗[R] M) ⊗[K] (K ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.distribBaseChange R K M N
  refine e.toEquiv.nontrivial_congr.mpr ?_
  obtain ⟨u, hu⟩ := exists_ne (0 : K ⊗[R] M)
  obtain ⟨v, hv⟩ := exists_ne (0 : K ⊗[R] N)
  let bM := Module.Basis.ofVectorSpace K (K ⊗[R] M)
  let bN := Module.Basis.ofVectorSpace K (K ⊗[R] N)
  have hcoordM : ∃ i, bM.repr u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (bM.repr.injective (by ext i; simp [h i]))
  obtain ⟨i, hφ⟩ := hcoordM
  have hcoordN : ∃ j, bN.repr v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (bN.repr.injective (by ext j; simp [h j]))
  obtain ⟨j, hψ⟩ := hcoordN
  let φ : (K ⊗[R] M) →ₗ[K] K := bM.coord i
  let ψ : (K ⊗[R] N) →ₗ[K] K := bN.coord j
  let B : (K ⊗[R] M) ⊗[K] (K ⊗[R] N) →ₗ[K] K :=
    TensorProduct.lift (LinearMap.mk₂ K (fun x y => φ x * ψ y)
      (fun x₁ x₂ y => by simp [add_mul])
      (fun c x y => by simp [mul_assoc])
      (fun x y₁ y₂ => by simp [mul_add])
      (fun c x y => by simp [mul_left_comm]))
  refine ⟨⟨u ⊗ₜ[K] v, 0, fun h => ?_⟩⟩
  have hB : B (u ⊗ₜ[K] v) = B 0 := congrArg B h
  simp only [B, TensorProduct.lift.tmul, LinearMap.mk₂_apply, map_zero, mul_eq_zero] at hB
  rcases hB with h1 | h2
  · exact hφ h1
  · exact hψ h2

lemma exists_ltSeries_of_krullDim_eq_natCast {α : Type*} [Preorder α] {n : ℕ}
    (h : Order.krullDim α = (n : WithBot ℕ∞)) :
    ∃ c : LTSeries α, c.length = n := by
  have hne : Nonempty α := by
    rw [← Order.krullDim_ne_bot_iff, h]
    exact WithBot.coe_ne_bot
  cases n with
  | zero =>
    obtain ⟨a⟩ := hne
    exact ⟨RelSeries.singleton _ a, rfl⟩
  | succ k =>
    by_contra hno
    push Not at hno
    have hle : Order.krullDim α ≤ (k : WithBot ℕ∞) := by
      rw [Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      refine iSup_le fun c => ?_
      have hc_le : (c.length : WithBot ℕ∞) ≤ ((k + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr (le_iSup (fun s : LTSeries α => (s.length : ℕ∞)) c)
      have hc_nat : c.length ≤ k + 1 := by exact_mod_cast hc_le
      have hc_lt : c.length < k + 1 := lt_of_le_of_ne hc_nat (hno c)
      exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp hc_lt)
    rw [h] at hle
    have : k + 1 ≤ k := by exact_mod_cast hle
    omega

lemma ringKrullDim_quotient_eq_natCast {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ n : ℕ, ringKrullDim (R ⧸ I) = (n : WithBot ℕ∞) := by
  have hle : ringKrullDim (R ⧸ I) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (ringKrullDim_quotient_le I).trans (ringKrullDim_le_spanFinrank_maximalIdeal R)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hne_bot : ringKrullDim (R ⧸ I) ≠ ⊥ := by
    intro hbot
    have hnn := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
    rw [hbot] at hnn
    exact absurd hnn (by decide)
  cases h : ringKrullDim (R ⧸ I) with
  | bot => exact absurd h hne_bot
  | coe e =>
    cases e with
    | top =>
      rw [h] at hle
      have htop : (⊤ : ℕ∞) ≤ ((maximalIdeal R).spanFinrank : ℕ∞) := WithBot.coe_le_coe.mp hle
      exact absurd (top_le_iff.mp htop) (ENat.natCast_ne_top _)
    | coe n =>
      exact ⟨n, rfl⟩

lemma exists_prime_ge_with_ringKrullDim_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ (P : Ideal R) (_ : P.IsPrime), I ≤ P ∧ ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ I) := by
  obtain ⟨n, hn⟩ := ringKrullDim_quotient_eq_natCast I hI
  have hkd : Order.krullDim (PrimeSpectrum.zeroLocus (I : Set R)) = (n : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient, hn]
  obtain ⟨c, hc⟩ := exists_ltSeries_of_krullDim_eq_natCast hkd
  let P : Ideal R := c.head.1.asIdeal
  have hIP : I ≤ P := fun x hx => c.head.2 hx
  refine ⟨P, c.head.1.isPrime, hIP, le_antisymm ?_ ?_⟩
  · exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIP)
  · rw [hn, ringKrullDim_quotient, Order.krullDim]
    let c' : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
      { length := c.length
        toFun := fun i => ⟨(c i).1, by
          simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
          exact c.monotone (Fin.zero_le i)⟩
        step := fun i => c.step i }
    have hge : (c'.length : WithBot ℕ∞) ≤
        ⨆ s : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)), (s.length : WithBot ℕ∞) :=
      le_iSup (fun s : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) =>
        (s.length : WithBot ℕ∞)) c'
    simpa [c', hc] using hge

lemma exists_countable_regularLocal_subring {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsRegularLocalRing R₀)
      (P₀ Q₀ : Ideal R₀) (_ : P₀.IsPrime) (_ : Q₀.IsPrime),
      (P₀ ⊔ Q₀).radical = maximalIdeal R₀ ∧
      ringKrullDim (R ⧸ P) ≤ ringKrullDim (R₀ ⧸ P₀) ∧
      ringKrullDim (R ⧸ Q) ≤ ringKrullDim (R₀ ⧸ Q₀) ∧
      ringKrullDim R₀ = ringKrullDim R := by
  classical
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm
  have hmFG : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  have hmFin : ((maximalIdeal R).generators : Set R).Finite :=
    Submodule.FG.finite_generators hmFG
  obtain ⟨cR, hcR⟩ := exists_ltSeries_of_krullDim_eq_natCast (α := PrimeSpectrum R) hd
  have hwR : ∀ i : Fin cR.length, ∃ x : R,
      x ∈ (cR i.succ).asIdeal ∧ x ∉ (cR i.castSucc).asIdeal := fun i => by
    have hlt : (cR i.castSucc).asIdeal < (cR i.succ).asIdeal := cR.step i
    exact SetLike.exists_of_lt hlt
  obtain ⟨r, hr⟩ := ringKrullDim_quotient_eq_natCast P ‹P.IsPrime›.ne_top
  obtain ⟨cP, hcP⟩ := exists_ltSeries_of_krullDim_eq_natCast
    (α := PrimeSpectrum.zeroLocus (P : Set R)) (by rw [← ringKrullDim_quotient, hr])
  have hwP : ∀ i : Fin cP.length, ∃ x : R,
      x ∈ (cP i.succ).1.asIdeal ∧ x ∉ (cP i.castSucc).1.asIdeal := fun i => by
    have hlt : (cP i.castSucc).1.asIdeal < (cP i.succ).1.asIdeal := cP.step i
    exact SetLike.exists_of_lt hlt
  obtain ⟨s, hs⟩ := ringKrullDim_quotient_eq_natCast Q ‹Q.IsPrime›.ne_top
  obtain ⟨cQ, hcQ⟩ := exists_ltSeries_of_krullDim_eq_natCast
    (α := PrimeSpectrum.zeroLocus (Q : Set R)) (by rw [← ringKrullDim_quotient, hs])
  have hwQ : ∀ i : Fin cQ.length, ∃ x : R,
      x ∈ (cQ i.succ).1.asIdeal ∧ x ∉ (cQ i.castSucc).1.asIdeal := fun i => by
    have hlt : (cQ i.castSucc).1.asIdeal < (cQ i.succ).1.asIdeal := cQ.step i
    exact SetLike.exists_of_lt hlt
  have hgenRad : ∀ g : (maximalIdeal R).generators, ∃ (k : ℕ) (a b : R),
      a ∈ P ∧ b ∈ Q ∧ a + b = (g : R) ^ k := fun g => by
    have hmem : (g : R) ∈ maximalIdeal R :=
      ((maximalIdeal R).span_generators).le (Ideal.subset_span g.2)
    have hg : (g : R) ∈ (P ⊔ Q).radical := hPQ.symm ▸ hmem
    obtain ⟨k, hk⟩ := hg
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hk
    exact ⟨k, a, b, ha, hb, hab⟩
  let S₀ : Set R :=
    (maximalIdeal R).generators ∪
    Set.range (fun i => (hwR i).choose) ∪
    Set.range (fun i => (hwP i).choose) ∪
    Set.range (fun i => (hwQ i).choose) ∪
    Set.range (fun g : (maximalIdeal R).generators => (hgenRad g).choose_spec.choose) ∪
    Set.range (fun g : (maximalIdeal R).generators =>
      (hgenRad g).choose_spec.choose_spec.choose)
  have hS₀_count : S₀.Countable := by
    have : Finite (maximalIdeal R).generators := hmFin.to_subtype
    exact (((((hmFin.countable.union (Set.countable_range _)).union
      (Set.countable_range _)).union (Set.countable_range _)).union
      (Set.countable_range _)).union (Set.countable_range _))
  let linWit : (B : Subring R) → List B × B → Set R := fun B p =>
    if h : (p.2 : R) ∈ Ideal.span (Set.range (fun i : Fin p.1.length => (p.1.get i : R))) then
      Set.range ((Submodule.mem_span_range_iff_exists_fun R).mp h).choose
    else ∅
  let step : Subring R → Subring R := fun B =>
    Subring.closure ((B : Set R) ∪
      Set.range (fun x : B => if h : IsUnit (x : R) then ((h.unit⁻¹ : Rˣ) : R) else 0) ∪
      ⋃ p : List B × B, linWit B p)
  have hle_step : ∀ B : Subring R, B ≤ step B := fun B x hx =>
    Subring.subset_closure (Or.inl (Or.inl hx))
  have hcount_step : ∀ B : Subring R, Countable B → Countable (step B) := fun B hB => by
    have : Countable B := hB
    have h1 : (B : Set R).Countable := Set.countable_coe_iff.mp hB
    have h2 : (Set.range (fun x : B =>
        if h : IsUnit (x : R) then ((h.unit⁻¹ : Rˣ) : R) else 0)).Countable :=
      Set.countable_range _
    have h3 : (⋃ p : List B × B, linWit B p).Countable := by
      refine Set.countable_iUnion fun p => ?_
      dsimp only [linWit]
      split_ifs
      · exact Set.countable_range _
      · exact Set.countable_empty
    have hunion : ((B : Set R) ∪
        Set.range (fun x : B => if h : IsUnit (x : R) then ((h.unit⁻¹ : Rˣ) : R) else 0) ∪
        ⋃ p : List B × B, linWit B p).Countable := (h1.union h2).union h3
    exact Set.countable_coe_iff.mpr (countable_subring_closure hunion)
  let A : ℕ → Subring R := fun n => step^[n] (Subring.closure S₀)
  have hA_succ : ∀ n, A (n + 1) = step (A n) := fun n => Function.iterate_succ_apply' step n _
  have hA_mono : Monotone A := monotone_nat_of_le_succ fun n => by
    rw [hA_succ]
    exact hle_step (A n)
  have hA_count : ∀ n, Countable (A n) := fun n => by
    induction n with
    | zero => exact Set.countable_coe_iff.mpr (countable_subring_closure hS₀_count)
    | succ n ih =>
      rw [hA_succ]
      exact hcount_step (A n) ih
  let Rsub : Subring R := ⨆ n, A n
  have hmem_Rsub : ∀ x : R, x ∈ Rsub ↔ ∃ n, x ∈ A n := fun x =>
    Subring.mem_iSup_of_directed hA_mono.directed_le
  have hS₀_sub : S₀ ⊆ (Rsub : Set R) := fun x hx =>
    (hmem_Rsub x).mpr ⟨0, Subring.subset_closure hx⟩
  have hRsub_count : Countable Rsub := by
    have hset : (Rsub : Set R) = ⋃ n, (A n : Set R) := by
      ext x
      simpa [Set.mem_iUnion] using hmem_Rsub x
    exact Set.countable_coe_iff.mpr (hset ▸ Set.countable_iUnion fun n =>
      Set.countable_coe_iff.mp (hA_count n))
  have hUnit : ∀ x : Rsub, IsUnit x ↔ IsUnit (x : R) := fun x => by
    refine ⟨fun hx => hx.map Rsub.subtype, fun hx => ?_⟩
    obtain ⟨n, hn⟩ := (hmem_Rsub x.1).mp x.2
    have hinv_mem : ((hx.unit⁻¹ : Rˣ) : R) ∈ Rsub := by
      refine (hmem_Rsub _).mpr ⟨n + 1, ?_⟩
      rw [hA_succ]
      refine Subring.subset_closure (Or.inl (Or.inr ?_))
      refine ⟨⟨x.1, hn⟩, ?_⟩
      simp [hx]
    refine ⟨⟨x, ⟨((hx.unit⁻¹ : Rˣ) : R), hinv_mem⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext hx.unit.mul_inv
    · exact Subtype.ext hx.unit.inv_mul
  have : IsLocalRing Rsub := IsLocalRing.of_nonunits_add fun {x y} hx hy => by
    rw [mem_nonunits_iff] at hx hy ⊢
    rw [hUnit] at hx hy ⊢
    have h1 : (x : R) ∈ maximalIdeal R := hx
    have h2 : (y : R) ∈ maximalIdeal R := hy
    exact (maximalIdeal R).add_mem h1 h2
  have hmax_sub : maximalIdeal Rsub = (maximalIdeal R).comap Rsub.subtype := by
    ext x
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hUnit]
  have hex_stage : ∀ (L : List Rsub) (b : Rsub), ∃ n : ℕ, (b : R) ∈ A n ∧ ∀ x ∈ L, (x : R) ∈ A n := by
    intro L b
    induction L with
    | nil =>
      obtain ⟨n, hn⟩ := (hmem_Rsub b.1).mp b.2
      exact ⟨n, hn, by simp⟩
    | cons a tl ih =>
      obtain ⟨n₁, hb₁, htl⟩ := ih
      obtain ⟨n₂, ha₂⟩ := (hmem_Rsub a.1).mp a.2
      refine ⟨max n₁ n₂, hA_mono (le_max_left _ _) hb₁, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact hA_mono (le_max_right _ _) ha₂
      · exact hA_mono (le_max_left _ _) (htl x hxtl)
  have hPure : ∀ (L : List Rsub) (b : Rsub),
      (b : R) ∈ Ideal.span (Set.range (fun i : Fin L.length => (L.get i : R))) →
      b ∈ Ideal.span (Set.range (fun i : Fin L.length => L.get i)) := fun L b hb => by
    obtain ⟨n, hbn, hLn⟩ := hex_stage L b
    let L' : List (A n) := L.attach.map fun ⟨x, hx⟩ => ⟨x.1, hLn x hx⟩
    have hlen : L'.length = L.length := by simp [L']
    have hget : ∀ i : Fin L'.length, (L'.get i : R) = (L.get (i.cast hlen) : R) := fun i => by
      simp [L']
    have hb' : (b : R) ∈ Ideal.span (Set.range (fun i : Fin L'.length => (L'.get i : R))) := by
      convert hb using 2
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.cast hlen, (hget i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.cast hlen.symm, by simpa using hget (i.cast hlen.symm)⟩
    let cFun : Fin L'.length → R := ((Submodule.mem_span_range_iff_exists_fun R).mp hb').choose
    have hcFun_eq : ∑ i : Fin L'.length, cFun i * (L'.get i : R) = (b : R) := by
      simpa [smul_eq_mul] using ((Submodule.mem_span_range_iff_exists_fun R).mp hb').choose_spec
    have hcFun_mem : ∀ i : Fin L'.length, cFun i ∈ Rsub := fun i => by
      refine (hmem_Rsub _).mpr ⟨n + 1, ?_⟩
      rw [hA_succ]
      refine Subring.subset_closure (Or.inr ?_)
      refine Set.mem_iUnion.mpr ⟨(L', ⟨b.1, hbn⟩), ?_⟩
      dsimp only [linWit]
      rw [dif_pos hb']
      exact ⟨i, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i : Fin L.length => ⟨cFun (i.cast hlen.symm), hcFun_mem _⟩, ?_⟩
    apply Subtype.ext
    push_cast
    simp only [smul_eq_mul]
    rw [← hcFun_eq]
    refine Fintype.sum_equiv (finCongr hlen.symm) _ _ fun i => ?_
    have hget' : (L.get i : R) = (L'.get (i.cast hlen.symm) : R) := by
      simpa using (hget (i.cast hlen.symm)).symm
    exact congrArg (cFun (i.cast hlen.symm) * ·) hget'
  have : IsNoetherianRing Rsub := (isNoetherianRing_iff_ideal_fg Rsub).mpr fun I => by
    let J : Ideal R := I.map Rsub.subtype
    have hJfg : J.FG := IsNoetherian.noetherian J
    obtain ⟨T, hT⟩ := hJfg
    have hfin_sub : ∀ t : T, ∃ F : Finset Rsub, (F : Set Rsub) ⊆ (I : Set Rsub) ∧
        (t : R) ∈ Ideal.span (Rsub.subtype '' (F : Set Rsub)) := fun t => by
      have htJ : (t : R) ∈ J := hT ▸ Ideal.subset_span t.2
      have htSpan : (t : R) ∈ Submodule.span R (Rsub.subtype '' (I : Set Rsub)) := htJ
      obtain ⟨U, hUsub, hUt⟩ := Submodule.mem_span_finite_of_mem_span htSpan
      have hU_im : ∀ u : U, ∃ a : Rsub, a ∈ I ∧ (a : R) = u := fun u => hUsub u.2
      let F : Finset Rsub := U.attach.image fun u => (hU_im u).choose
      refine ⟨F, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨u, _, rfl⟩
        exact (hU_im u).choose_spec.1
      · refine Ideal.span_mono ?_ hUt
        intro y hy
        exact ⟨(hU_im ⟨y, hy⟩).choose, Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩,
          (hU_im ⟨y, hy⟩).choose_spec.2⟩
    let F : Finset Rsub := T.attach.biUnion fun t => (hfin_sub t).choose
    have hFI : (F : Set Rsub) ⊆ (I : Set Rsub) := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_biUnion] at hx
      obtain ⟨t, _, hxt⟩ := hx
      exact (hfin_sub t).choose_spec.1 hxt
    have hJ_le : J ≤ Ideal.span (Rsub.subtype '' (F : Set Rsub)) := by
      rw [← hT, Ideal.span_le]
      intro t ht
      have hmem := (hfin_sub ⟨t, ht⟩).choose_spec.2
      refine Ideal.span_mono ?_ hmem
      refine Set.image_mono ?_
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, hx⟩
    refine ⟨F, le_antisymm (Ideal.span_le.mpr hFI) fun b hb => ?_⟩
    have hbJ : (b : R) ∈ Ideal.span (Rsub.subtype '' (F : Set Rsub)) :=
      hJ_le (Ideal.mem_map_of_mem Rsub.subtype hb)
    let L : List Rsub := F.toList
    have hrange_R : Set.range (fun i : Fin L.length => (L.get i : R)) =
        Rsub.subtype '' (F : Set Rsub) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨L.get i, Finset.mem_toList.mp (List.get_mem L i), rfl⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr ha)
        exact ⟨i, congrArg Subtype.val hi⟩
    have hrange_sub : Set.range (fun i : Fin L.length => L.get i) = (F : Set Rsub) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.mem_toList.mp (List.get_mem L i)
      · intro ha
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr ha)
        exact ⟨i, hi⟩
    rw [← hrange_sub]
    exact hPure L b (hrange_R.symm ▸ hbJ)
  let Gsub : Finset Rsub := hmFin.toFinset.attach.image fun g =>
    ⟨g.1, hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hmFin.mem_toFinset.mp g.2))))))⟩
  have hmax_span : maximalIdeal Rsub = Ideal.span (Gsub : Set Rsub) := by
    refine le_antisymm ?_ (Ideal.span_le.mpr fun x hx => ?_)
    · intro y hy
      have hyR : (y : R) ∈ maximalIdeal R := by
        rw [hmax_sub] at hy
        exact hy
      rw [← (maximalIdeal R).span_generators] at hyR
      let L : List Rsub := Gsub.toList
      have hrange_R : Set.range (fun i : Fin L.length => (L.get i : R)) =
          (maximalIdeal R).generators := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          have hmem := Finset.mem_toList.mp (List.get_mem L i)
          rcases Finset.mem_image.mp hmem with ⟨g, _, hgx⟩
          dsimp only
          rw [← hgx]
          exact hmFin.mem_toFinset.mp g.2
        · intro hz
          have hmem : (⟨z, hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hz)))))⟩ : Rsub) ∈
              Gsub := Finset.mem_image.mpr ⟨⟨z, hmFin.mem_toFinset.mpr hz⟩,
            Finset.mem_attach _ _, rfl⟩
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hmem)
          exact ⟨i, congrArg Subtype.val hi⟩
      have hrange_sub : Set.range (fun i : Fin L.length => L.get i) = (Gsub : Set Rsub) := by
        ext a
        constructor
        · rintro ⟨i, rfl⟩
          exact Finset.mem_toList.mp (List.get_mem L i)
        · intro ha
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr ha)
          exact ⟨i, hi⟩
      rw [← hrange_sub]
      exact hPure L y (hrange_R.symm ▸ hyR)
    · rw [Finset.mem_coe] at hx
      rcases Finset.mem_image.mp hx with ⟨g, _, rfl⟩
      rw [hmax_sub]
      show (g : R) ∈ maximalIdeal R
      exact ((maximalIdeal R).span_generators).le (Ideal.subset_span (hmFin.mem_toFinset.mp g.2))
  have hspan_le : (maximalIdeal Rsub).spanFinrank ≤ d := by
    rw [hmax_span]
    calc (Ideal.span (Gsub : Set Rsub)).spanFinrank
        ≤ (Gsub : Set Rsub).ncard := Submodule.spanFinrank_span_le_ncard_of_finite Gsub.finite_toSet
      _ = Gsub.card := Set.ncard_coe_finset Gsub
      _ ≤ hmFin.toFinset.attach.card := Finset.card_image_le
      _ = hmFin.toFinset.card := Finset.card_attach
      _ = ((maximalIdeal R).generators : Set R).ncard := (Set.ncard_eq_toFinset_card _ hmFin).symm
      _ = d := Submodule.FG.generators_ncard hmFG
  have hd_le : (d : WithBot ℕ∞) ≤ ringKrullDim Rsub := by
    let cR' : LTSeries (PrimeSpectrum Rsub) :=
      { length := cR.length
        toFun := fun i => PrimeSpectrum.comap Rsub.subtype (cR i)
        step := fun i => by
          refine lt_of_le_of_ne (Ideal.comap_mono (le_of_lt (cR.step i))) fun heq => ?_
          have hmem_sub : (hwR i).choose ∈ Rsub :=
            hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))))
          have h1 : (⟨(hwR i).choose, hmem_sub⟩ : Rsub) ∈
              (cR i.succ).asIdeal.comap Rsub.subtype := (hwR i).choose_spec.1
          rw [← heq] at h1
          exact (hwR i).choose_spec.2 h1 }
    have hge : (cR'.length : WithBot ℕ∞) ≤ ringKrullDim Rsub := by
      rw [ringKrullDim, Order.krullDim]
      exact le_iSup (fun s : LTSeries (PrimeSpectrum Rsub) => (s.length : WithBot ℕ∞)) cR'
    simpa [cR', hcR] using hge
  have hdim_sub : ringKrullDim Rsub = (d : WithBot ℕ∞) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal Rsub).trans (Nat.cast_le.mpr hspan_le))
      hd_le
  have : IsRegularLocalRing Rsub :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Rsub (hdim_sub ▸ Nat.cast_le.mpr hspan_le)
  let Psub : Ideal Rsub := P.comap Rsub.subtype
  let Qsub : Ideal Rsub := Q.comap Rsub.subtype
  have : Psub.IsPrime := Ideal.comap_isPrime Rsub.subtype P
  have : Qsub.IsPrime := Ideal.comap_isPrime Rsub.subtype Q
  have hPQ_sub : (Psub ⊔ Qsub).radical = maximalIdeal Rsub := by
    refine le_antisymm ?_ ?_
    · rw [← Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal Rsub).isPrime]
      exact Ideal.radical_mono (sup_le (IsLocalRing.le_maximalIdeal ‹Psub.IsPrime›.ne_top)
        (IsLocalRing.le_maximalIdeal ‹Qsub.IsPrime›.ne_top))
    · rw [hmax_span, Ideal.span_le]
      intro x hx
      rw [Finset.mem_coe] at hx
      rcases Finset.mem_image.mp hx with ⟨g, _, rfl⟩
      let g' : (maximalIdeal R).generators := ⟨g.1, hmFin.mem_toFinset.mp g.2⟩
      refine ⟨(hgenRad g').choose, ?_⟩
      have ha_mem : (hgenRad g').choose_spec.choose ∈ Rsub :=
        hS₀_sub (Or.inl (Or.inr ⟨g', rfl⟩))
      have hb_mem : (hgenRad g').choose_spec.choose_spec.choose ∈ Rsub :=
        hS₀_sub (Or.inr ⟨g', rfl⟩)
      have haP : (⟨(hgenRad g').choose_spec.choose, ha_mem⟩ : Rsub) ∈ Psub :=
        (hgenRad g').choose_spec.choose_spec.choose_spec.1
      have hbQ : (⟨(hgenRad g').choose_spec.choose_spec.choose, hb_mem⟩ : Rsub) ∈ Qsub :=
        (hgenRad g').choose_spec.choose_spec.choose_spec.2.1
      have hsum : (⟨(hgenRad g').choose_spec.choose, ha_mem⟩ : Rsub) +
          ⟨(hgenRad g').choose_spec.choose_spec.choose, hb_mem⟩ =
          (⟨g.1, hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            (hmFin.mem_toFinset.mp g.2))))))⟩ : Rsub) ^ (hgenRad g').choose := by
        apply Subtype.ext
        simpa using (hgenRad g').choose_spec.choose_spec.choose_spec.2.2
      rw [← hsum]
      exact Submodule.add_mem_sup haP hbQ
  have hP_le : ringKrullDim (R ⧸ P) ≤ ringKrullDim (Rsub ⧸ Psub) := by
    let cP' : LTSeries (PrimeSpectrum.zeroLocus (Psub : Set Rsub)) :=
      { length := cP.length
        toFun := fun i => ⟨PrimeSpectrum.comap Rsub.subtype (cP i).1, by
          simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
          intro x hx
          exact (cP i).2 hx⟩
        step := fun i => by
          refine lt_of_le_of_ne (Ideal.comap_mono (le_of_lt (cP.step i))) fun heq => ?_
          have hmem_sub : (hwP i).choose ∈ Rsub :=
            hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
          have h1 : (⟨(hwP i).choose, hmem_sub⟩ : Rsub) ∈
              (cP i.succ).1.asIdeal.comap Rsub.subtype := (hwP i).choose_spec.1
          rw [← heq] at h1
          exact (hwP i).choose_spec.2 h1 }
    rw [hr, ringKrullDim_quotient, Order.krullDim]
    have hge : (cP'.length : WithBot ℕ∞) ≤
        ⨆ s : LTSeries (PrimeSpectrum.zeroLocus (Psub : Set Rsub)), (s.length : WithBot ℕ∞) :=
      le_iSup (fun s : LTSeries (PrimeSpectrum.zeroLocus (Psub : Set Rsub)) =>
        (s.length : WithBot ℕ∞)) cP'
    simpa [cP', hcP] using hge
  have hQ_le : ringKrullDim (R ⧸ Q) ≤ ringKrullDim (Rsub ⧸ Qsub) := by
    let cQ' : LTSeries (PrimeSpectrum.zeroLocus (Qsub : Set Rsub)) :=
      { length := cQ.length
        toFun := fun i => ⟨PrimeSpectrum.comap Rsub.subtype (cQ i).1, by
          simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
          intro x hx
          exact (cQ i).2 hx⟩
        step := fun i => by
          refine lt_of_le_of_ne (Ideal.comap_mono (le_of_lt (cQ.step i))) fun heq => ?_
          have hmem_sub : (hwQ i).choose ∈ Rsub :=
            hS₀_sub (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
          have h1 : (⟨(hwQ i).choose, hmem_sub⟩ : Rsub) ∈
              (cQ i.succ).1.asIdeal.comap Rsub.subtype := (hwQ i).choose_spec.1
          rw [← heq] at h1
          exact (hwQ i).choose_spec.2 h1 }
    rw [hs, ringKrullDim_quotient, Order.krullDim]
    have hge : (cQ'.length : WithBot ℕ∞) ≤
        ⨆ s : LTSeries (PrimeSpectrum.zeroLocus (Qsub : Set Rsub)), (s.length : WithBot ℕ∞) :=
      le_iSup (fun s : LTSeries (PrimeSpectrum.zeroLocus (Qsub : Set Rsub)) =>
        (s.length : WithBot ℕ∞)) cQ'
    simpa [cQ', hcQ] using hge
  have : Countable Rsub := hRsub_count
  have : Small.{0} Rsub := Countable.toSmall Rsub
  let R₀ : Type := Shrink.{0} Rsub
  let e : Rsub ≃+* R₀ := (Shrink.ringEquiv (α := Rsub)).symm
  have : IsRegularLocalRing R₀ := IsRegularLocalRing.of_ringEquiv e
  let P₀ : Ideal R₀ := Psub.map e.toRingHom
  let Q₀ : Ideal R₀ := Qsub.map e.toRingHom
  have : P₀.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q₀.IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨R₀, inferInstance, inferInstance, P₀, Q₀, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · have hrad : (P₀ ⊔ Q₀).radical = (Psub ⊔ Qsub).radical.map e.toRingHom := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [Ideal.mem_radical_iff, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨y, ⟨n, ?_⟩, rfl⟩
        rw [← Ideal.map_sup, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hn
        obtain ⟨z, hz, hze⟩ := hn
        have hzy : z = y ^ n := e.injective (by simpa [map_pow] using hze)
        exact hzy ▸ hz
      · rintro ⟨z, ⟨n, hn⟩, hze⟩
        have hzy : z = y := e.injective hze
        subst hzy
        refine ⟨n, ?_⟩
        rw [← Ideal.map_sup, ← map_pow]
        exact Ideal.mem_map_of_mem e.toRingHom hn
    rw [hrad, hPQ_sub]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · exact hP_le.trans_eq (ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv Psub P₀ e rfl))
  · exact hQ_le.trans_eq (ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv Qsub Q₀ e rfl))
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim_sub, hd]

lemma prime_dim_ineq_of_complete (h2 : H2) (h3 : H3) (h4 : H4)
    (R : Type) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) :
    ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) ≤ ringKrullDim R := by
  by_cases hchar : (ringChar (ResidueField R) : R) = 0 ∨
      (ringChar (ResidueField R) : R) ∉ maximalIdeal R ^ 2
  · exact (h2 R hchar P Q hPQ).1
  · push Not at hchar
    obtain ⟨S, hCommS, hRegS, hCompS, g, f, hunram, hg_mem, hg_ne, hf_surj, hf_ker, hdimS⟩ :=
      h3 R hchar.1 hchar.2
    let _ : CommRing S := hCommS
    have : IsRegularLocalRing S := hRegS
    have : IsAdicComplete (maximalIdeal S) S := hCompS
    have : IsRegularLocalRing (S ⧸ Ideal.span {g}) := by
      have e : S ⧸ Ideal.span {g} ≃+* R :=
        (Ideal.quotEquivOfEq hf_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hf_surj)
      exact IsRegularLocalRing.of_ringEquiv e.symm
    let P' : Ideal S := P.comap f
    let Q' : Ideal S := Q.comap f
    have : P'.IsPrime := Ideal.comap_isPrime f P
    have : Q'.IsPrime := Ideal.comap_isPrime f Q
    have hgP : g ∈ P' := by
      have : g ∈ RingHom.ker f := hf_ker ▸ Ideal.subset_span rfl
      show f g ∈ P
      rw [RingHom.mem_ker.mp this]
      exact P.zero_mem
    have hgQ : g ∈ Q' := by
      have : g ∈ RingHom.ker f := hf_ker ▸ Ideal.subset_span rfl
      show f g ∈ Q
      rw [RingHom.mem_ker.mp this]
      exact Q.zero_mem
    have hPQ' : (P' ⊔ Q').radical = maximalIdeal S := by
      refine le_antisymm ?_ ?_
      · rw [← Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal S).isPrime]
        exact Ideal.radical_mono (sup_le (IsLocalRing.le_maximalIdeal ‹P'.IsPrime›.ne_top)
          (IsLocalRing.le_maximalIdeal ‹Q'.IsPrime›.ne_top))
      · rw [Ideal.radical_eq_sInf, le_sInf_iff]
        intro r ⟨hPQr, hrPrime⟩
        have hker_le : RingHom.ker f ≤ r := by
          rw [hf_ker, Ideal.span_le, Set.singleton_subset_iff]
          exact hPQr (Ideal.mem_sup_left hgP)
        have hrmap_prime : (r.map f).IsPrime :=
          Ideal.map_isPrime_of_surjective hf_surj hker_le
        have hPQ_le_rmap : P ⊔ Q ≤ r.map f := by
          refine sup_le ?_ ?_
          · intro x hx
            obtain ⟨y, rfl⟩ := hf_surj x
            exact Ideal.mem_map_of_mem f (hPQr (Ideal.mem_sup_left hx))
          · intro x hx
            obtain ⟨y, rfl⟩ := hf_surj x
            exact Ideal.mem_map_of_mem f (hPQr (Ideal.mem_sup_right hx))
        have hrmap_eq : r.map f = maximalIdeal R := by
          refine le_antisymm (IsLocalRing.le_maximalIdeal hrmap_prime.ne_top) ?_
          rw [← hPQ, ← hrmap_prime.radical]
          exact Ideal.radical_mono hPQ_le_rmap
        have hmax_comap : ((maximalIdeal R).comap f).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective f hf_surj
        have hcomap_max : (maximalIdeal R).comap f = maximalIdeal S :=
          IsLocalRing.eq_maximalIdeal hmax_comap
        rw [← hcomap_max, ← hrmap_eq, Ideal.comap_map_of_surjective' f hf_surj,
          sup_eq_left.mpr hker_le]
    have hdimP : ringKrullDim (S ⧸ P') = ringKrullDim (R ⧸ P) := by
      let gP : S →+* R ⧸ P := (Ideal.Quotient.mk P).comp f
      have hgP_surj : Function.Surjective gP := Ideal.Quotient.mk_surjective.comp hf_surj
      have hgP_ker : RingHom.ker gP = P' := by
        ext x
        simp [gP, P', Ideal.Quotient.eq_zero_iff_mem]
      exact ringKrullDim_eq_of_ringEquiv
        ((Ideal.quotEquivOfEq hgP_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hgP_surj))
    have hdimQ : ringKrullDim (S ⧸ Q') = ringKrullDim (R ⧸ Q) := by
      let gQ : S →+* R ⧸ Q := (Ideal.Quotient.mk Q).comp f
      have hgQ_surj : Function.Surjective gQ := Ideal.Quotient.mk_surjective.comp hf_surj
      have hgQ_ker : RingHom.ker gQ = Q' := by
        ext x
        simp [gQ, Q', Ideal.Quotient.eq_zero_iff_mem]
      exact ringKrullDim_eq_of_ringEquiv
        ((Ideal.quotEquivOfEq hgQ_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hgQ_surj))
    have hS_res := h2 S (Or.inr hunram) P' Q' hPQ'
    have hcharS_ne : (ringChar (ResidueField S) : S) ≠ 0 := fun h0 =>
      hunram (h0.symm ▸ (maximalIdeal S ^ 2).zero_mem)
    have hchi_zero : Module.intersectionMultiplicity S (S ⧸ P') (S ⧸ Q') = 0 :=
      h4 S g hg_mem hg_ne inferInstance P' Q' hgP hgQ hPQ'
    have hne_eq : ringKrullDim (S ⧸ P') + ringKrullDim (S ⧸ Q') ≠ ringKrullDim S := fun heq => by
      have hpos := hS_res.2 hcharS_ne heq
      rw [hchi_zero] at hpos
      exact lt_irrefl 0 hpos
    have hle_S : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) ≤ ringKrullDim R + 1 := by
      rw [← hdimP, ← hdimQ, ← hdimS]
      exact hS_res.1
    have hne_S : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) ≠ ringKrullDim R + 1 := by
      rw [← hdimP, ← hdimQ, ← hdimS]
      exact hne_eq
    obtain ⟨nP, hnP⟩ := ringKrullDim_quotient_eq_natCast P ‹P.IsPrime›.ne_top
    obtain ⟨nQ, hnQ⟩ := ringKrullDim_quotient_eq_natCast Q ‹Q.IsPrime›.ne_top
    have hnR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm
    rw [hnP, hnQ, hnR] at hle_S hne_S ⊢
    have hle_nat : nP + nQ ≤ (maximalIdeal R).spanFinrank + 1 := by exact_mod_cast hle_S
    have hne_nat : nP + nQ ≠ (maximalIdeal R).spanFinrank + 1 := fun h => by
      apply hne_S
      exact_mod_cast h
    have : nP + nQ ≤ (maximalIdeal R).spanFinrank := by omega
    exact_mod_cast this

lemma prime_dim_ineq_type0 (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4)
    (R : Type) [CommRing R] [IsRegularLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : (P ⊔ Q).radical = maximalIdeal R) :
    ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) ≤ ringKrullDim R := by
  let Rhat := AdicCompletion (maximalIdeal R) R
  have : IsNoetherianRing Rhat := (h1 R).1
  have hdim_hat : ringKrullDim Rhat = ringKrullDim R := by
    have h0 := (h1 R).2 ⊥
    rw [Ideal.map_bot] at h0
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot Rhat),
      ← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
    exact h0
  have : IsRegularLocalRing Rhat := by
    rw [isRegularLocalRing_iff, AdicCompletion.spanFinrank_maximalIdeal_eq, hdim_hat,
      ← isRegularLocalRing_iff]
    infer_instance
  let f := algebraMap R Rhat
  let J₁ : Ideal Rhat := P.map f
  let J₂ : Ideal Rhat := Q.map f
  have hJ₁_ne : J₁ ≠ ⊤ := by
    intro htop
    have hle : J₁ ≤ maximalIdeal Rhat := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.map_mono (IsLocalRing.le_maximalIdeal ‹P.IsPrime›.ne_top)
    exact (IsLocalRing.maximalIdeal.isMaximal Rhat).ne_top (top_le_iff.mp (htop ▸ hle))
  have hJ₂_ne : J₂ ≠ ⊤ := by
    intro htop
    have hle : J₂ ≤ maximalIdeal Rhat := by
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.map_mono (IsLocalRing.le_maximalIdeal ‹Q.IsPrime›.ne_top)
    exact (IsLocalRing.maximalIdeal.isMaximal Rhat).ne_top (top_le_iff.mp (htop ▸ hle))
  obtain ⟨P', hP'prime, hJ₁P', hdimP'⟩ := exists_prime_ge_with_ringKrullDim_eq J₁ hJ₁_ne
  obtain ⟨Q', hQ'prime, hJ₂Q', hdimQ'⟩ := exists_prime_ge_with_ringKrullDim_eq J₂ hJ₂_ne
  have hPQ'_rad : (P' ⊔ Q').radical = maximalIdeal Rhat := by
    refine le_antisymm ?_ ?_
    · rw [← Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal Rhat).isPrime]
      exact Ideal.radical_mono (sup_le (IsLocalRing.le_maximalIdeal hP'prime.ne_top)
        (IsLocalRing.le_maximalIdeal hQ'prime.ne_top))
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hPQ.ge
        (maximalIdeal R).fg_of_isNoetherianRing
      intro x hx
      refine ⟨k, ?_⟩
      have hpow : (maximalIdeal Rhat) ^ k ≤ P' ⊔ Q' := by
        rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
        exact (Ideal.map_mono hk).trans (by rw [Ideal.map_sup]; exact sup_le_sup hJ₁P' hJ₂Q')
      exact hpow (Ideal.pow_mem_pow hx k)
  have hres := prime_dim_ineq_of_complete h2 h3 h4 Rhat P' Q' hPQ'_rad
  rw [hdimP', hdimQ', (h1 R).2 P, (h1 R).2 Q, hdim_hat] at hres
  exact hres

theorem main : H1 → H2 → H3 → H4 →
    type_of% @SerreMultiplicityConjectures.supportDim_add_supportDim_le_ringKrullDim := by
  intro h1 h2 h3 h4 R _ _ M N _ _ _ _ _ _ hfin
  by_cases hM : Subsingleton M
  · simp [Module.supportDim_eq_bot_of_subsingleton]
  by_cases hN : Subsingleton N
  · simp [Module.supportDim_eq_bot_of_subsingleton]
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
  have hAnnM : Module.annihilator R M ≠ ⊤ := by
    intro htop
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact hm (by simpa using (Module.mem_annihilator.mp (htop.symm ▸ Submodule.mem_top : (1 : R) ∈ _)) m)
  have hAnnN : Module.annihilator R N ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := exists_ne (0 : N)
    exact hn (by simpa using (Module.mem_annihilator.mp (htop.symm ▸ Submodule.mem_top : (1 : R) ∈ _)) n)
  obtain ⟨P, hPprime, hAnnMP, hdimP⟩ :=
    exists_prime_ge_with_ringKrullDim_eq (Module.annihilator R M) hAnnM
  obtain ⟨Q, hQprime, hAnnNQ, hdimQ⟩ :=
    exists_prime_ge_with_ringKrullDim_eq (Module.annihilator R N) hAnnN
  have hPQ : (P ⊔ Q).radical = maximalIdeal R := by
    refine le_antisymm ?_ ?_
    · rw [← Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal R).isPrime]
      exact Ideal.radical_mono (sup_le (IsLocalRing.le_maximalIdeal hPprime.ne_top)
        (IsLocalRing.le_maximalIdeal hQprime.ne_top))
    · rw [Ideal.radical_eq_sInf, le_sInf_iff]
      intro r ⟨hPQr, hrPrime⟩
      let rp : PrimeSpectrum R := ⟨r, hrPrime⟩
      have hrM : rp ∈ Module.support R M :=
        Module.mem_support_iff_of_finite.mpr (hAnnMP.trans (le_sup_left.trans hPQr))
      have hrN : rp ∈ Module.support R N :=
        Module.mem_support_iff_of_finite.mpr (hAnnNQ.trans (le_sup_right.trans hPQr))
      have hrMN : rp ∈ Module.support R (M ⊗[R] N) :=
        mem_support_tensorProduct_of_mem hrM hrN
      have hr_eq : rp = IsLocalRing.closedPoint R :=
        support_subset_closedPoint_of_isFiniteLength hfin hrMN
      exact (congrArg PrimeSpectrum.asIdeal hr_eq).ge
  obtain ⟨R₀, hComm₀, hReg₀, P₀, Q₀, hP₀, hQ₀, hPQ₀, hleP, hleQ, hdimR₀⟩ :=
    exists_countable_regularLocal_subring P Q hPQ
  let _ : CommRing R₀ := hComm₀
  have : IsRegularLocalRing R₀ := hReg₀
  have h0 := prime_dim_ineq_type0 h1 h2 h3 h4 R₀ P₀ Q₀ hPQ₀
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, ← hdimP, ← hdimQ, ← hdimR₀]
  exact (add_le_add hleP hleQ).trans h0

end OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
