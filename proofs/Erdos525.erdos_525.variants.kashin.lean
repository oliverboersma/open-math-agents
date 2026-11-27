import FormalConjectures.ErdosProblems.«525»

/-!
# Erdős Problem 525, Kashin's theorem: `m(f) < δ` for almost all `±1` polynomials

Original proof (no reused formalization). For every `δ > 0`, the proportion of degree-`n`
polynomials with `±1` coefficients whose minimum modulus on the unit circle is below `δ`
tends to `1`.

Route (elementary; no local CLT library, no Kac–Rice):
* Pair decomposition: pairing the coefficients `j` and `n - j` and resampling each pair through an
  exactly two-to-one map, `e^{-inθ} f(e^{2iθ}) = R(θ) + i I(θ)` where `R` and `I` depend on
  independent sign vectors (given the pair types `t`).
* `HT` (`hT_holds`): the pair types are typical (Hoeffding by counting, plus a net).
* `HZ` (`hZ_holds`): `R` has `≥ c₀ n` separated zeros in `[π/8, 3π/8]` w.h.p. (second moment of
  `Σ R(α)R(α+h)`, Isserlis-type fourth-moment identity, intermediate value theorem).
* `HH` (`hH_of`): given the zeros, `I` is small at one of them w.h.p., by the second moment
  method for a smoothed count `Σ ψ(I(ξ))`, from four estimates:
  `S1` (one-point smoothed local limit, `S1_holds`), `S2` (two-point upper bound, `S2_holds`),
  `S3` (few resonant points / bad pairs, `S3_holds`), `S4` (variance `≈ K`, `S4_holds`).
  `S1`, `S2` go through Fourier inversion of a bump (`avg_schwartz`, `avg_schwartz2`), Gaussian
  cores, a Fejér-kernel equidistribution argument in one and two dimensions for the intermediate
  frequencies, and Schwartz decay for the far tail.

Mathematical source: B. S. Kashin, *The properties of random trigonometric polynomials with ±1
coefficients*, Vestnik Moskov. Univ. (1987); the route here is our own (brainstormed with Claude
Fable and Gemini; every step formalized from scratch).
-/

/-!
# Erdős 525 (Kashin), part 0: the oversampled pair decomposition

Local copies of the Erdős 525 definitions (the submission will use the real ones).
We pair the coefficients `j` and `n - j` (`j < K = ⌊(n+1)/2⌋`) and resample each pair through
`pmap : Bool × ℤˣ × ℤˣ → ℤˣ × ℤˣ`, `pmap (t, a, b) = if t then (a, a) else (-b, b)`, which is exactly
two-to-one. On the circle `z = e^{2iθ}` the rotated polynomial is `R θ + i I θ`, where `R` only uses
the `a`-coordinates of pairs with `t = true` (and the middle coefficient), and `I` only uses the
`b`-coordinates of pairs with `t = false`.
-/

open Finset MeasureTheory Real FourierTransform

noncomputable section

namespace K525

/-- Local copy of `Erdos525.eval`. -/
def eval {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (z : ℂ) : ℂ :=
  ∑ j, ((ε j : ℤ) : ℂ) * z ^ (j : ℕ)

/-- Number of pairs. -/
def K (n : ℕ) : ℕ := (n + 1) / 2

/-- Number of unpaired (middle) coefficients: `1` if `n` is even, else `0`. -/
def r (n : ℕ) : ℕ := n + 1 - 2 * K n

lemma two_K_add_r (n : ℕ) : 2 * K n + r n = n + 1 := by unfold r K; omega

lemma r_le_one (n : ℕ) : r n ≤ 1 := by unfold r K; omega

/-- The index map `(Fin K ⊕ Fin K) ⊕ Fin r → Fin (n+1)`: `p ↦ p`, `p ↦ n - p`, middle `↦ K`. -/
def idx (n : ℕ) : (Fin (K n) ⊕ Fin (K n)) ⊕ Fin (r n) → Fin (n + 1)
  | Sum.inl (Sum.inl p) => ⟨p, by have := p.2; unfold K at this; omega⟩
  | Sum.inl (Sum.inr p) => ⟨n - p, by omega⟩
  | Sum.inr i => ⟨K n + i, by have := i.2; have := two_K_add_r n; omega⟩

lemma idx_injective (n : ℕ) : Function.Injective (idx n) := by
  intro x y h
  have hK : 2 * K n ≤ n + 1 := by unfold K; omega
  have hr := r_le_one n
  have hKr := two_K_add_r n
  rcases x with (p | p) | i <;> rcases y with (q | q) | j <;>
    simp only [idx, Fin.mk.injEq] at h <;>
    first
    | (congr 2; exact Fin.ext (by omega))
    | (congr 1; exact Fin.ext (by omega))
    | (exfalso; have := p.2; have := q.2; omega)
    | (exfalso; have := p.2; have := j.2; omega)
    | (exfalso; have := i.2; have := q.2; omega)
    | (exfalso; have := p.2; have := i.2; omega)

lemma idx_bijective (n : ℕ) : Function.Bijective (idx n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨idx_injective n, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  have := two_K_add_r n
  omega

/-- The index equivalence. -/
def idxEquiv (n : ℕ) : ((Fin (K n) ⊕ Fin (K n)) ⊕ Fin (r n)) ≃ Fin (n + 1) :=
  Equiv.ofBijective _ (idx_bijective n)

/-- The two-to-one resampling of a pair. -/
def pmap : Bool × ℤˣ × ℤˣ → ℤˣ × ℤˣ := fun w => if w.1 then (w.2.1, w.2.1) else (-w.2.2, w.2.2)

lemma card_fiber_pmap (v : ℤˣ × ℤˣ) : Fintype.card {w // pmap w = v} = 2 := by
  revert v; decide

/-- The oversampled sample space. -/
abbrev Ω (n : ℕ) := (Fin (K n) → Bool × ℤˣ × ℤˣ) × (Fin (r n) → ℤˣ)

/-- Fiber counting through a coordinatewise map with fibers of constant size. -/
lemma sum_comp_pi {ι W X M : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [Fintype X]
    [DecidableEq X] [AddCommMonoid M] (g : W → X) (m : ℕ)
    (hg : ∀ x, Fintype.card {w // g w = x} = m) (G : (ι → X) → M) :
    ∑ y : ι → W, G (fun i => g (y i)) = (m ^ Fintype.card ι) • ∑ x : ι → X, G x := by
  rw [← Fintype.sum_fiberwise' (fun y : ι → W => fun i => g (y i)) G, Finset.smul_sum]
  congr 1; ext x
  rw [Finset.sum_const, Finset.card_univ]
  congr 1
  have e : {y : ι → W // (fun i => g (y i)) = x} ≃ ∀ i, {w // g w = x i} :=
    (Equiv.subtypeEquivRight (fun y => funext_iff)).trans
      (Equiv.subtypePiEquivPi (p := fun i w => g w = x i))
  rw [Fintype.card_congr e, Fintype.card_pi]
  simp [hg]

/-- Assemble a coefficient vector from pairs and middle coefficients. -/
def Ψ {n : ℕ} (x : (Fin (K n) → ℤˣ × ℤˣ) × (Fin (r n) → ℤˣ)) : Fin (n + 1) → ℤˣ :=
  (Sum.elim (Sum.elim (fun p => (x.1 p).1) (fun p => (x.1 p).2)) x.2) ∘ (idxEquiv n).symm

lemma Ψ_idx {n : ℕ} (x : (Fin (K n) → ℤˣ × ℤˣ) × (Fin (r n) → ℤˣ))
    (s : (Fin (K n) ⊕ Fin (K n)) ⊕ Fin (r n)) :
    Ψ x (idx n s) = Sum.elim (Sum.elim (fun p => (x.1 p).1) (fun p => (x.1 p).2)) x.2 s := by
  unfold Ψ
  simp only [Function.comp_apply]
  congr 1
  exact (idxEquiv n).symm_apply_apply s

lemma Ψ_bijective (n : ℕ) : Function.Bijective (@Ψ n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro x y h
    have h' : ∀ s, Ψ x (idx n s) = Ψ y (idx n s) := fun s => by rw [h]
    simp only [Ψ_idx] at h'
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [Prod.mk.injEq]
    refine ⟨funext fun p => Prod.ext (h' (Sum.inl (Sum.inl p))) (h' (Sum.inl (Sum.inr p))),
      funext fun i => h' (Sum.inr i)⟩
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units_int]
    rw [show (2 * 2 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, two_K_add_r]

/-- The coefficient vector of an oversampled point. -/
def Φ {n : ℕ} (ω : Ω n) : Fin (n + 1) → ℤˣ := Ψ (fun p => pmap (ω.1 p), ω.2)

/-- Averages transfer: summing `G ∘ Φ` over `Ω n` is `2 ^ K` times summing `G`. -/
lemma sum_Φ {M : Type*} [AddCommMonoid M] (n : ℕ) (G : (Fin (n + 1) → ℤˣ) → M) :
    ∑ ω : Ω n, G (Φ ω) = (2 ^ K n) • ∑ ε : Fin (n + 1) → ℤˣ, G ε := by
  calc ∑ ω : Ω n, G (Φ ω)
      = ∑ c : Fin (r n) → ℤˣ, ∑ y : Fin (K n) → Bool × ℤˣ × ℤˣ, G (Φ (y, c)) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ c : Fin (r n) → ℤˣ, (2 ^ K n) • ∑ x : Fin (K n) → ℤˣ × ℤˣ, G (Ψ (x, c)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        have := sum_comp_pi (ι := Fin (K n)) pmap 2 card_fiber_pmap (fun x => G (Ψ (x, c)))
        simpa [Φ] using this
    _ = (2 ^ K n) • ∑ x : (Fin (K n) → ℤˣ × ℤˣ) × (Fin (r n) → ℤˣ), G (Ψ x) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.smul_sum]
    _ = (2 ^ K n) • ∑ ε : Fin (n + 1) → ℤˣ, G ε := by
        rw [(Ψ_bijective n).sum_comp G]

/-- Frequency of pair `p`. -/
def kk (n : ℕ) (p : Fin (K n)) : ℝ := (n : ℝ) - 2 * (p : ℝ)

/-- The real part process. -/
def RR {n : ℕ} (ω : Ω n) (θ : ℝ) : ℝ :=
  ∑ i, (((ω.2 i : ℤˣ) : ℤ) : ℝ) +
    ∑ p, (if (ω.1 p).1 then 2 * ((((ω.1 p).2.1 : ℤˣ) : ℤ) : ℝ) else 0) * Real.cos (kk n p * θ)

/-- The imaginary part process. -/
def II {n : ℕ} (ω : Ω n) (θ : ℝ) : ℝ :=
  ∑ p, (if (ω.1 p).1 then 0 else 2 * ((((ω.1 p).2.2 : ℤˣ) : ℤ) : ℝ)) * Real.sin (kk n p * θ)

lemma exp_rot (n m : ℕ) (θ : ℝ) :
    Complex.exp (-(n : ℂ) * θ * Complex.I) * Complex.exp (2 * θ * Complex.I) ^ m
      = Complex.exp (↑((2 * (m : ℝ) - n) * θ) * Complex.I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma pair_term (n : ℕ) (p : Fin (K n)) (w : Bool × ℤˣ × ℤˣ) (θ : ℝ) :
    Complex.exp (-(n : ℂ) * θ * Complex.I) *
      ((((pmap w).1 : ℤ) : ℂ) * Complex.exp (2 * θ * Complex.I) ^ (p : ℕ) +
        (((pmap w).2 : ℤ) : ℂ) * Complex.exp (2 * θ * Complex.I) ^ (n - (p : ℕ)))
      = (((if w.1 then 2 * (((w.2.1 : ℤˣ) : ℤ) : ℝ) else 0) * Real.cos (kk n p * θ) : ℝ) : ℂ) +
        (((if w.1 then 0 else 2 * (((w.2.2 : ℤˣ) : ℤ) : ℝ)) * Real.sin (kk n p * θ) : ℝ) : ℂ)
          * Complex.I := by
  have hp : (p : ℕ) ≤ n := by have := p.2; unfold K at this; omega
  have hA : ∀ (E z c1 c2 : ℂ) (a b : ℕ), E * (c1 * z ^ a + c2 * z ^ b)
      = c1 * (E * z ^ a) + c2 * (E * z ^ b) := by intros; ring
  rw [hA, exp_rot, exp_rot]
  have e1 : (2 * ((p : ℕ) : ℝ) - n) * θ = -(kk n p * θ) := by unfold kk; ring
  have e2 : (2 * (((n - (p : ℕ) : ℕ)) : ℝ) - n) * θ = kk n p * θ := by
    unfold kk; rw [Nat.cast_sub hp]; ring
  rw [e1, e2]
  set x := kk n p * θ
  have hc : ((Real.cos x : ℝ) : ℂ) = (Complex.exp (↑x * Complex.I) +
      Complex.exp (↑(-x) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]; push_cast; ring_nf
  have hs : ((Real.sin x : ℝ) : ℂ) = (Complex.exp (↑(-x) * Complex.I) -
      Complex.exp (↑x * Complex.I)) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin]; push_cast; ring_nf
  obtain ⟨t, a, b⟩ := w
  cases t
  · simp only [pmap, Bool.false_eq_true, ↓reduceIte, Units.val_neg, Int.cast_neg, zero_mul,
      Complex.ofReal_zero, zero_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
    rw [hs]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp only [pmap, ↓reduceIte, zero_mul, Complex.ofReal_zero, add_zero, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_intCast]
    rw [hc]
    ring

lemma middle_term (n : ℕ) (i : Fin (r n)) (θ : ℝ) :
    Complex.exp (-(n : ℂ) * θ * Complex.I) * Complex.exp (2 * θ * Complex.I) ^ (K n + (i : ℕ))
      = 1 := by
  have hi : (i : ℕ) = 0 := by have := i.2; have := r_le_one n; omega
  have hn : n = 2 * K n := by
    have := i.2; have := two_K_add_r n; have hK : K n = (n + 1) / 2 := rfl; omega
  rw [exp_rot, hi, add_zero]
  have : (2 * ((K n : ℕ) : ℝ) - n) * θ = 0 := by
    rw [show (n : ℝ) = 2 * (K n : ℝ) by exact_mod_cast hn]; ring
  rw [this]; simp

/-- **The rotated polynomial on the circle is `RR + i II`.** -/
theorem rot_eval {n : ℕ} (ω : Ω n) (θ : ℝ) :
    Complex.exp (-(n : ℂ) * θ * Complex.I) * eval (Φ ω) (Complex.exp (2 * θ * Complex.I))
      = (RR ω θ : ℂ) + (II ω θ : ℂ) * Complex.I := by
  unfold eval
  rw [← (idxEquiv n).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hΦ : ∀ s, Φ ω (idx n s) = Sum.elim (Sum.elim (fun p => (pmap (ω.1 p)).1)
      (fun p => (pmap (ω.1 p)).2)) ω.2 s := fun s => Ψ_idx _ s
  simp only [idxEquiv, Equiv.ofBijective_apply, hΦ, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hpair : ∀ p : Fin (K n), (idx n (Sum.inl (Sum.inl p)) : ℕ) = p := fun p => rfl
  have hpair' : ∀ p : Fin (K n), (idx n (Sum.inl (Sum.inr p)) : ℕ) = n - p := fun p => rfl
  have hmid : ∀ i : Fin (r n), (idx n (Sum.inr i) : ℕ) = K n + i := fun i => rfl
  simp_rw [hpair, hpair', hmid, pair_term]
  unfold RR II
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Complex.ofReal_intCast]
  have hm : ∀ i : Fin (r n), Complex.exp (-(n : ℂ) * θ * Complex.I) *
      ((((ω.2 i : ℤˣ) : ℤ) : ℂ) * Complex.exp (2 * θ * Complex.I) ^ (K n + (i : ℕ)))
      = (((ω.2 i : ℤˣ) : ℤ) : ℂ) := fun i => by
    rw [mul_left_comm, middle_term, mul_one]
  simp_rw [hm]
  ring


/-- Fourier inversion for a Schwartz function, written as an integral. -/
lemma schwartz_inv (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ψ x = ∫ ξ : ℝ, Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
  have h := ψ.continuous.fourierInv_fourier_eq ψ.integrable (by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable)
  have := congrFun h x
  rw [← this, Real.fourierInv_eq']
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1; ext ξ; congr 3; push_cast; ring

/-- The sum of `exp (2π i ξ u c)` over the two signs `u`. -/
lemma sum_units_exp (ξ c : ℝ) :
    ∑ u : ℤˣ, Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c)) * Complex.I)
      = 2 * (Real.cos (2 * π * ξ * c) : ℂ) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- Averaging a character over sign vectors gives a product of cosines. -/
lemma sum_signs_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (ξ : ℝ) :
    ∑ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, 2 * (Real.cos (2 * π * ξ * c i) : ℂ) := by
  have : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, Complex.exp (↑(2 * π * ξ * (((b i : ℤ) : ℝ) * c i)) * Complex.I) := by
    intro b
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) =>
    Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c i)) * Complex.I))]
  simp_rw [sum_units_exp]

/-- **Smoothed small-ball identity.** -/
theorem avg_schwartz {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : SchwartzMap ℝ ℂ) (c : ι → ℝ) :
    (∑ b : ι → ℤˣ, ψ (∑ i, ((b i : ℤ) : ℝ) * c i)) / 2 ^ Fintype.card ι
      = ∫ ξ : ℝ, 𝓕 (ψ : ℝ → ℂ) ξ * ∏ i, (Real.cos (2 * π * ξ * c i) : ℂ) := by
  have hint : ∀ b : ι → ℤˣ, Integrable (fun ξ : ℝ =>
      Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
        * 𝓕 (ψ : ℝ → ℂ) ξ) := by
    intro b
    have hF : Integrable (𝓕 (ψ : ℝ → ℂ)) := by
      rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable
    refine hF.bdd_mul (c := 1) ?_ ?_
    · fun_prop
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      rw [Complex.norm_exp]
      simp
  simp_rw [schwartz_inv ψ]
  rw [← integral_finsetSum _ (fun b _ => hint b)]
  rw [div_eq_mul_inv, mul_comm, ← integral_const_mul]
  congr 1
  ext ξ
  rw [← Finset.sum_mul, sum_signs_exp c ξ, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  field_simp

/-- The bump of width `δ`: `1` on `[-δ/4, δ/4]`, supported in `(-δ/2, δ/2)`. -/
def bumpR (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) :=
  ⟨δ / 4, δ / 2, by positivity, by linarith⟩

lemma bumpR_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (fun x : ℝ => ((bumpR δ hδ x : ℝ) : ℂ)) :=
  (bumpR δ hδ).hasCompactSupport.comp_left Complex.ofReal_zero

lemma bumpR_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ((bumpR δ hδ x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (bumpR δ hδ).contDiff

/-- The bump as a Schwartz function. -/
def psi (δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  (bumpR_hasCompactSupport δ hδ).toSchwartzMap (bumpR_contDiff δ hδ)

lemma psi_apply (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : psi δ hδ x = ((bumpR δ hδ x : ℝ) : ℂ) := rfl

lemma bumpR_nonneg (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : 0 ≤ bumpR δ hδ x := (bumpR δ hδ).nonneg

lemma bumpR_le_one (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : bumpR δ hδ x ≤ 1 := (bumpR δ hδ).le_one

lemma bumpR_eq_zero (δ : ℝ) (hδ : 0 < δ) {x : ℝ} (hx : δ / 2 ≤ |x|) : bumpR δ hδ x = 0 := by
  apply Function.notMem_support.mp
  rw [(bumpR δ hδ).support_eq]
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
  exact hx

/-- A positive smoothed value forces `|x| < δ / 2`. -/
lemma lt_of_bumpR_pos (δ : ℝ) (hδ : 0 < δ) {x : ℝ} (hx : 0 < bumpR δ hδ x) : |x| < δ / 2 := by
  by_contra h
  rw [bumpR_eq_zero δ hδ (not_lt.mp h)] at hx
  exact lt_irrefl _ hx

/-- Rapid decay of the Fourier transform. -/
lemma fourier_psi_decay (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, |ξ| ^ k * ‖𝓕 (psi δ hδ : ℝ → ℂ) ξ‖ ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ k 0 (𝓕 (psi δ hδ)), by positivity, fun ξ => ?_⟩
  have := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 (psi δ hδ)) k ξ
  rw [Real.norm_eq_abs] at this
  rwa [SchwartzMap.fourier_coe] at this


/-! ## Assembly: Kashin's theorem from three interface statements -/

/-- Local copy of `Erdos525.m`. -/
def mm {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : ℝ :=
  sInf ((fun z ↦ ‖eval ε z‖) '' Metric.sphere (0 : ℂ) 1)

open scoped Classical in
/-- Local copy of `Erdos525.prob`. -/
def prob (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / 2 ^ (n + 1)

lemma mm_le {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (θ : ℝ) :
    mm ε ≤ ‖eval ε (Complex.exp (2 * θ * Complex.I))‖ := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
  · refine ⟨_, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp]
    simp

lemma norm_eval_Φ {n : ℕ} (ω : Ω n) (θ : ℝ) :
    ‖eval (Φ ω) (Complex.exp (2 * θ * Complex.I))‖
      = ‖(RR ω θ : ℂ) + (II ω θ : ℂ) * Complex.I‖ := by
  rw [← rot_eval ω θ, norm_mul, Complex.norm_exp]
  simp

lemma norm_eval_Φ_of_RR {n : ℕ} (ω : Ω n) (θ : ℝ) (h : RR ω θ = 0) :
    ‖eval (Φ ω) (Complex.exp (2 * θ * Complex.I))‖ = |II ω θ| := by
  rw [norm_eval_Φ, h]
  simp

/-- The data seen by `RR`: pair types with `a`-signs, and the middle coefficients. -/
abbrev Al (n : ℕ) := (Fin (K n) → Bool × ℤˣ) × (Fin (r n) → ℤˣ)

/-- Join `RR`-data and `b`-signs. -/
def join {n : ℕ} (x : Al n × (Fin (K n) → ℤˣ)) : Ω n :=
  (fun p => ((x.1.1 p).1, (x.1.1 p).2, x.2 p), x.1.2)

lemma join_bijective (n : ℕ) : Function.Bijective (@join n) := by
  constructor
  · rintro ⟨⟨y, c⟩, b⟩ ⟨⟨y', c'⟩, b'⟩ h
    simp only [join, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' := fun p => congrFun h1 p
    simp only [Prod.mk.injEq] at h1'
    simp only [Prod.mk.injEq]
    exact ⟨⟨funext fun p => Prod.ext (h1' p).1 (h1' p).2.1, h2⟩, funext fun p => (h1' p).2.2⟩
  · rintro ⟨y, c⟩
    exact ⟨⟨⟨fun p => ((y p).1, (y p).2.1), c⟩, fun p => (y p).2.2⟩, rfl⟩

/-- The pair types of `RR`-data. -/
def tOf {n : ℕ} (a : Al n) : Fin (K n) → Bool := fun p => (a.1 p).1

/-- `RR` through `RR`-data. -/
def RRa {n : ℕ} (a : Al n) (θ : ℝ) : ℝ :=
  ∑ i, (((a.2 i : ℤˣ) : ℤ) : ℝ) +
    ∑ p, (if (a.1 p).1 then 2 * ((((a.1 p).2 : ℤˣ) : ℤ) : ℝ) else 0) * Real.cos (kk n p * θ)

/-- `II` through pair types and `b`-signs. -/
def IIt {n : ℕ} (t : Fin (K n) → Bool) (b : Fin (K n) → ℤˣ) (θ : ℝ) : ℝ :=
  ∑ p, (if t p then 0 else 2 * (((b p : ℤˣ) : ℤ) : ℝ)) * Real.sin (kk n p * θ)

lemma RR_join {n : ℕ} (x : Al n × (Fin (K n) → ℤˣ)) (θ : ℝ) : RR (join x) θ = RRa x.1 θ := rfl

lemma II_join {n : ℕ} (x : Al n × (Fin (K n) → ℤˣ)) (θ : ℝ) :
    II (join x) θ = IIt (tOf x.1) x.2 θ := rfl

/-- Typical pair types: the type indicator has small exponential sums at all frequencies. -/
def Typical (n : ℕ) (t : Fin (K n) → Bool) : Prop :=
  ∀ x : ℝ, ‖∑ p, (if t p then (-1 / 2 : ℂ) else 1 / 2) * Complex.exp (↑(kk n p * x) * Complex.I)‖
    ≤ (n : ℝ) ^ (3 / 5 : ℝ)

/-- A structured set of points: in `[π/8, 3π/8]`, at least `c₀ n` of them, `c₀/n`-separated. -/
def Structured (c₀ : ℝ) (n : ℕ) (Ξ : Finset ℝ) : Prop :=
  (↑Ξ : Set ℝ) ⊆ Set.Icc (π / 8) (3 * π / 8) ∧ c₀ * n ≤ Ξ.card ∧
    ∀ ξ ∈ Ξ, ∀ ξ' ∈ Ξ, ξ ≠ ξ' → c₀ / n ≤ |ξ - ξ'|

open scoped Classical in
/-- Interface 1: pair types are typical with high probability. -/
def HT : Prop :=
  ∀ η > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (1 - η) * 2 ^ K n ≤ ((univ.filter fun t : Fin (K n) → Bool => Typical n t).card : ℝ)

open scoped Classical in
/-- Interface 2: `RR` has a structured set of zeros with high probability. -/
def HZ : Prop :=
  ∀ η > (0 : ℝ), ∃ c₀ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (1 - η) * Fintype.card (Al n) ≤
      ((univ.filter fun a : Al n => ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧ ∀ ξ ∈ Ξ, RRa a ξ = 0).card : ℝ)

open scoped Classical in
/-- Interface 3: for typical types, `II` is small at one of any structured set of points,
with high probability over the `b`-signs. -/
def HH : Prop :=
  ∀ δ > (0 : ℝ), ∀ η > (0 : ℝ), ∀ c₀ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∀ t : Fin (K n) → Bool, Typical n t → ∀ Ξ : Finset ℝ, Structured c₀ n Ξ →
      (1 - η) * 2 ^ K n ≤
        ((univ.filter fun b : Fin (K n) → ℤˣ => ∃ ξ ∈ Ξ, |IIt t b ξ| < δ).card : ℝ)

lemma card_Al (n : ℕ) : (Fintype.card (Al n) : ℝ) = 2 ^ (n + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_units_int]
  push_cast
  rw [show ((4 : ℝ)) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, two_K_add_r]

open scoped Classical in
/-- Counting through the type map. -/
lemma card_tOf (n : ℕ) (T : (Fin (K n) → Bool) → Prop) :
    ((univ.filter fun a : Al n => T (tOf a)).card : ℝ)
      = ((univ.filter T).card : ℝ) * (2 ^ K n * 2 ^ r n) := by
  have key := sum_comp_pi (ι := Fin (K n)) (W := Bool × ℤˣ) (X := Bool) (M := ℕ) Prod.fst 2
    (fun x => by revert x; decide) (fun t => if T t then 1 else 0)
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ y : Fin (K n) → Bool × ℤˣ,
      ∑ c : Fin (r n) → ℤˣ, (if T (tOf (y, c)) then 1 else 0)
        = 2 ^ r n * (if T (fun p => (y p).1) then 1 else 0) := by
    intro y
    have : ∀ c : Fin (r n) → ℤˣ, (if T (tOf (y, c)) then 1 else 0)
        = (if T (fun p => (y p).1) then 1 else 0) := fun c => rfl
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_fun, Fintype.card_units_int]
  simp_rw [h]
  rw [← Finset.mul_sum, key]
  simp only [Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

open scoped Classical in
lemma card_filter_real {α : Type*} [Fintype α] (P : α → Prop) :
    ((univ.filter P).card : ℝ) = ∑ x, if P x then (1 : ℝ) else 0 := by
  rw [Finset.card_filter]; push_cast; rfl

open scoped Classical in
lemma sum_not {α : Type*} [Fintype α] (P : α → Prop) :
    (∑ x, if ¬ P x then (1 : ℝ) else 0) = Fintype.card α - ∑ x, if P x then (1 : ℝ) else 0 := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  have : ∀ x, ((if ¬ P x then (1 : ℝ) else 0) + if P x then 1 else 0) = 1 := fun x => by
    split_ifs <;> simp_all
  simp_rw [this]; simp

open scoped Classical in
/-- The lower bound behind `kashin_of`, for one `n`. -/
lemma prob_lower (n : ℕ) (δ η c₀ : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hT : (1 - η) * 2 ^ K n ≤ ((univ.filter fun t : Fin (K n) → Bool => Typical n t).card : ℝ))
    (hZ : (1 - η) * Fintype.card (Al n) ≤
      ((univ.filter fun a : Al n => ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧
        ∀ ξ ∈ Ξ, RRa a ξ = 0).card : ℝ))
    (hH : ∀ t : Fin (K n) → Bool, Typical n t → ∀ Ξ : Finset ℝ, Structured c₀ n Ξ →
      (1 - η) * 2 ^ K n ≤
        ((univ.filter fun b : Fin (K n) → ℤˣ => ∃ ξ ∈ Ξ, |IIt t b ξ| < δ).card : ℝ)) :
    (1 - 2 * η) * (1 - η) ≤ prob n fun f ↦ mm f < δ := by
  set Zg : Al n → Prop := fun a => ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧ ∀ ξ ∈ Ξ, RRa a ξ = 0
  set G : Al n → Prop := fun a => Typical n (tOf a) ∧ Zg a
  have hAl := card_Al n
  have hKr : (2 : ℝ) ^ K n * (2 ^ K n * 2 ^ r n) = 2 ^ (n + 1) := by
    rw [← mul_assoc, ← pow_add, ← pow_add]; congr 1; have := two_K_add_r n; omega
  have hTt : (Fintype.card (Fin (K n) → Bool) : ℝ) = 2 ^ K n := by
    simp [Fintype.card_fun]
  -- few atypical types
  have hnT : (∑ a : Al n, if ¬ Typical n (tOf a) then (1 : ℝ) else 0) ≤ η * 2 ^ (n + 1) := by
    have h0 := card_tOf n (fun t => ¬ Typical n t)
    rw [card_filter_real, card_filter_real] at h0
    rw [card_filter_real] at hT
    have h0' : (∑ a : Al n, if ¬ Typical n (tOf a) then (1 : ℝ) else 0)
        = (∑ x : Fin (K n) → Bool, if ¬ Typical n x then (1 : ℝ) else 0) * (2 ^ K n * 2 ^ r n) := by
      convert h0 using 3; split_ifs <;> rfl
    calc _ = _ := h0'
      _ = (∑ x : Fin (K n) → Bool, (1 - if Typical n x then (1 : ℝ) else 0))
            * (2 ^ K n * 2 ^ r n) := by
          congr 1; refine Finset.sum_congr rfl (fun x _ => ?_); split_ifs <;> simp_all
      _ = (2 ^ K n - ∑ x : Fin (K n) → Bool, if Typical n x then (1 : ℝ) else 0)
            * (2 ^ K n * 2 ^ r n) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hTt.symm]; simp
      _ ≤ η * 2 ^ (n + 1) := by
          rw [← hKr]
          have : (0 : ℝ) ≤ 2 ^ K n * 2 ^ r n := by positivity
          nlinarith
  have hnZ : (∑ a : Al n, if ¬ Zg a then (1 : ℝ) else 0) ≤ η * 2 ^ (n + 1) := by
    rw [sum_not, hAl]
    rw [card_filter_real, hAl] at hZ
    linarith
  -- many good `RR`-data
  have hG : (1 - 2 * η) * 2 ^ (n + 1) ≤ ∑ a : Al n, if G a then (1 : ℝ) else 0 := by
    have hpt : ∀ a : Al n, (1 : ℝ) ≤ (if G a then 1 else 0) + (if ¬ Typical n (tOf a) then 1 else 0)
        + (if ¬ Zg a then 1 else 0) := by
      intro a; simp only [G]; split_ifs <;> simp_all
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Al n))) => hpt a)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
    simp only [nsmul_eq_mul, mul_one] at hs
    rw [hAl] at hs
    linarith
  -- count the polynomials with a small value
  have hpos : ∀ a : Al n, G a → (1 - η) * 2 ^ K n ≤
      ∑ b : Fin (K n) → ℤˣ, (if mm (Φ (join (a, b))) < δ then (1 : ℝ) else 0) := by
    rintro a ⟨ha, Ξ, hΞ, hz⟩
    refine (hH _ ha Ξ hΞ).trans ?_
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_le_sum (fun b _ => ?_)
    split_ifs with h1 h2 <;> try norm_num
    exfalso; apply h2
    obtain ⟨ξ, hξ, hlt⟩ := h1
    calc mm (Φ (join (a, b))) ≤ ‖eval (Φ (join (a, b))) (Complex.exp (2 * ξ * Complex.I))‖ :=
          mm_le _ ξ
      _ = |II (join (a, b)) ξ| := norm_eval_Φ_of_RR _ ξ (by rw [RR_join]; exact hz ξ hξ)
      _ < δ := by rw [II_join]; exact hlt
  have e1 := sum_Φ (M := ℝ) n (fun ε => if mm ε < δ then 1 else 0)
  rw [nsmul_eq_mul] at e1
  push_cast at e1
  rw [← (join_bijective n).sum_comp (fun ω => if mm (Φ ω) < δ then (1 : ℝ) else 0),
    Fintype.sum_prod_type] at e1
  have hmain : (1 - 2 * η) * (1 - η) * 2 ^ (n + 1) * 2 ^ K n
      ≤ 2 ^ K n * ∑ ε : Fin (n + 1) → ℤˣ, if mm ε < δ then (1 : ℝ) else 0 := by
    rw [← e1]
    calc (1 - 2 * η) * (1 - η) * 2 ^ (n + 1) * 2 ^ K n
        = ((1 - 2 * η) * 2 ^ (n + 1)) * ((1 - η) * 2 ^ K n) := by ring
      _ ≤ (∑ a : Al n, if G a then (1 : ℝ) else 0) * ((1 - η) * 2 ^ K n) := by
          exact mul_le_mul_of_nonneg_right hG (by
            have : 0 ≤ 1 - η := by linarith
            positivity)
      _ = ∑ a : Al n, if G a then (1 - η) * 2 ^ K n else 0 := by
          rw [Finset.sum_mul]; congr 1; ext a; split_ifs <;> simp
      _ ≤ ∑ a : Al n, ∑ b : Fin (K n) → ℤˣ,
            (if mm (Φ (join (a, b))) < δ then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          split_ifs with h
          · exact hpos a h
          · exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)
  have hK0 : (0 : ℝ) < 2 ^ K n := by positivity
  have hfin : (1 - 2 * η) * (1 - η) * 2 ^ (n + 1)
      ≤ ∑ ε : Fin (n + 1) → ℤˣ, if mm ε < δ then (1 : ℝ) else 0 := by
    have := hmain
    rw [mul_comm ((2 : ℝ) ^ K n)] at this
    exact le_of_mul_le_mul_right this hK0
  unfold prob
  rw [le_div_iff₀ (by positivity), card_filter_real]
  exact hfin

lemma prob_le_one (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) : prob n P ≤ 1 := by
  classical
  unfold prob
  rw [div_le_one (by positivity)]
  have := Finset.card_filter_le (univ : Finset (Fin (n + 1) → ℤˣ)) P
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_units_int] at this
  exact_mod_cast this

/-- **Kashin's theorem from the three interfaces.** -/
theorem kashin_of (hT : HT) (hZ : HZ) (hH : HH) (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ ↦ prob n fun f ↦ mm f < δ) Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := min (ε / 4) (1 / 4) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 2 := by have := min_le_right (ε / 4) (1 / 4); linarith
  have hηε : η ≤ ε / 4 := min_le_left _ _
  obtain ⟨c₀, hc₀, hZ⟩ := hZ η hη0
  have h := ((hT η hη0).and (hZ.and (hH δ hδ η hη0 c₀ hc₀))).exists_forall_of_atTop
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN n hn
  have lo := prob_lower n δ η c₀ hη0.le hη1 h1 h2 h3
  have hi := prob_le_one n (fun f ↦ mm f < δ)
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith


/-! ## Interface 1 (`HT`): Hoeffding plus a net -/

/-- The sign of a type. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by cases b <;> simp [sg]

lemma sum_exp_sign {k : ℕ} (c : Fin k → ℝ) (l : ℝ) :
    ∑ t : Fin k → Bool, Real.exp (l * ∑ p, sg (t p) * c p)
      = ∏ p, (2 * Real.cosh (l * c p)) := by
  have h : ∀ t : Fin k → Bool, Real.exp (l * ∑ p, sg (t p) * c p)
      = ∏ p, Real.exp (l * (sg (t p) * c p)) := by
    intro t; rw [← Real.exp_sum, Finset.mul_sum]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun p (b : Bool) => Real.exp (l * (sg b * c p)))]
  congr 1; ext p
  simp only [Fintype.sum_bool, sg, ↓reduceIte, Bool.false_eq_true, Real.cosh_eq]
  ring_nf

open scoped Classical in
/-- **Hoeffding's inequality** for sign sums, by counting. -/
lemma hoeffding {k : ℕ} (c : Fin k → ℝ) (V : ℝ) (hV0 : 0 < V) (hV : ∑ p, c p ^ 2 ≤ V)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ((univ.filter fun t : Fin k → Bool => μ ≤ ∑ p, sg (t p) * c p).card : ℝ)
      ≤ 2 ^ k * Real.exp (-(μ ^ 2 / (2 * V))) := by
  set l := μ / V with hl
  have hl0 : 0 ≤ l := div_nonneg hμ hV0.le
  rw [card_filter_real]
  calc (∑ t : Fin k → Bool, if μ ≤ ∑ p, sg (t p) * c p then (1 : ℝ) else 0)
      ≤ ∑ t : Fin k → Bool, Real.exp (l * (∑ p, sg (t p) * c p - μ)) := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        split_ifs with h
        · exact Real.one_le_exp (mul_nonneg hl0 (by linarith))
        · exact (Real.exp_pos _).le
    _ = Real.exp (-(l * μ)) * ∑ t : Fin k → Bool, Real.exp (l * ∑ p, sg (t p) * c p) := by
        rw [Finset.mul_sum]; congr 1; ext t
        rw [← Real.exp_add]; ring_nf
    _ = Real.exp (-(l * μ)) * ∏ p, (2 * Real.cosh (l * c p)) := by rw [sum_exp_sign]
    _ ≤ Real.exp (-(l * μ)) * ∏ p, (2 * Real.exp ((l * c p) ^ 2 / 2)) := by
        gcongr with p
        exact Real.cosh_le_exp_half_sq _
    _ = 2 ^ k * Real.exp (-(l * μ) + l ^ 2 * (∑ p, c p ^ 2) / 2) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.mul_sum, Finset.sum_div]
        rw [mul_comm, mul_assoc, ← Real.exp_add]
        congr 2
        rw [add_comm]; congr 1
        refine Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 ^ k * Real.exp (-(μ ^ 2 / (2 * V))) := by
        gcongr
        rw [hl]
        have : ((μ / V) ^ 2 * ∑ p, c p ^ 2) / 2 ≤ ((μ / V) ^ 2 * V) / 2 := by gcongr
        have e : -(μ / V * μ) + ((μ / V) ^ 2 * V) / 2 = -(μ ^ 2 / (2 * V)) := by
          field_simp; ring
        linarith

open scoped Classical in
/-- Two-sided Hoeffding. -/
lemma hoeffding_abs {k : ℕ} (c : Fin k → ℝ) (V : ℝ) (hV0 : 0 < V) (hV : ∑ p, c p ^ 2 ≤ V)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ((univ.filter fun t : Fin k → Bool => μ ≤ |∑ p, sg (t p) * c p|).card : ℝ)
      ≤ 2 * (2 ^ k * Real.exp (-(μ ^ 2 / (2 * V)))) := by
  have h1 := hoeffding c V hV0 hV μ hμ
  have h2 := hoeffding (fun p => - c p) V hV0 (by simpa using hV) μ hμ
  simp only [mul_neg, Finset.sum_neg_distrib] at h2
  have hsub : (univ.filter fun t : Fin k → Bool => μ ≤ |∑ p, sg (t p) * c p|) ⊆
      (univ.filter fun t : Fin k → Bool => μ ≤ ∑ p, sg (t p) * c p) ∪
      (univ.filter fun t : Fin k → Bool => μ ≤ -∑ p, sg (t p) * c p) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ht ⊢
    rcases le_abs'.mp ht with h | h
    · right; linarith
    · left; exact h
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' : ((univ.filter fun t : Fin k → Bool => μ ≤ |∑ p, sg (t p) * c p|).card : ℝ) ≤
      ((univ.filter fun t : Fin k → Bool => μ ≤ ∑ p, sg (t p) * c p).card : ℝ) +
      ((univ.filter fun t : Fin k → Bool => μ ≤ -∑ p, sg (t p) * c p).card : ℝ) := by
    exact_mod_cast hc
  linarith


/-- The type-indicator exponential sum. -/
def Ssum {n : ℕ} (t : Fin (K n) → Bool) (x : ℝ) : ℂ :=
  ∑ p, (if t p then (-1 / 2 : ℂ) else 1 / 2) * Complex.exp (↑(kk n p * x) * Complex.I)

lemma kk_pos (n : ℕ) (p : Fin (K n)) : 0 < kk n p := by
  have := p.2; unfold K at this; unfold kk
  have : (2 * (p : ℕ) : ℝ) < n := by
    have : 2 * (p : ℕ) < n := by omega
    exact_mod_cast this
  linarith

lemma kk_le (n : ℕ) (p : Fin (K n)) : kk n p ≤ n := by
  unfold kk; have : (0 : ℝ) ≤ p := Nat.cast_nonneg _; linarith

lemma kk_int (n : ℕ) (p : Fin (K n)) : kk n p = (((n : ℤ) - 2 * (p : ℤ) : ℤ) : ℝ) := by
  unfold kk; push_cast; ring

lemma coef_eq (b : Bool) : (if b then (-1 / 2 : ℂ) else 1 / 2) = ((sg b / 2 : ℝ) : ℂ) := by
  cases b <;> simp [sg]

lemma Ssum_eq {n : ℕ} (t : Fin (K n) → Bool) (x : ℝ) :
    Ssum t x = ((∑ p, sg (t p) * (Real.cos (kk n p * x) / 2) : ℝ) : ℂ)
      + ((∑ p, sg (t p) * (Real.sin (kk n p * x) / 2) : ℝ) : ℂ) * Complex.I := by
  unfold Ssum
  simp_rw [coef_eq, Complex.exp_mul_I]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

lemma norm_Ssum_le {n : ℕ} (t : Fin (K n) → Bool) (x : ℝ) :
    ‖Ssum t x‖ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * x) / 2)|
      + |∑ p, sg (t p) * (Real.sin (kk n p * x) / 2)| := by
  rw [Ssum_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  simp

lemma Ssum_periodic {n : ℕ} (t : Fin (K n) → Bool) (x : ℝ) (j : ℤ) :
    Ssum t (x + j * (2 * π)) = Ssum t x := by
  unfold Ssum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  have : Complex.exp (↑(kk n p * (j * (2 * π))) * Complex.I) = 1 := by
    rw [kk_int]
    have := Complex.exp_int_mul_two_pi_mul_I (((n : ℤ) - 2 * (p : ℤ)) * j)
    rw [← this]; congr 1; push_cast; ring
  rw [this, mul_one]

lemma norm_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)
      = Complex.exp (↑b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

lemma Ssum_lip {n : ℕ} (t : Fin (K n) → Bool) (x y : ℝ) :
    ‖Ssum t x - Ssum t y‖ ≤ (K n : ℝ) * n / 2 * |x - y| := by
  unfold Ssum
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖(if t p then (-1 / 2 : ℂ) else 1 / 2) * Complex.exp (↑(kk n p * x) * Complex.I) -
        (if t p then (-1 / 2 : ℂ) else 1 / 2) * Complex.exp (↑(kk n p * y) * Complex.I)‖
      ≤ ∑ _p : Fin (K n), (n : ℝ) / 2 * |x - y| := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [← mul_sub, norm_mul]
        have hc : ‖(if t p then (-1 / 2 : ℂ) else 1 / 2)‖ = 1 / 2 := by
          split_ifs <;> norm_num
        rw [hc]
        have := norm_exp_sub_exp (kk n p * x) (kk n p * y)
        rw [← mul_sub, abs_mul, abs_of_pos (kk_pos n p)] at this
        have hk := kk_le n p
        have : kk n p * |x - y| ≤ n * |x - y| := by gcongr
        nlinarith [norm_nonneg (Complex.exp (↑(kk n p * x) * Complex.I) -
          Complex.exp (↑(kk n p * y) * Complex.I))]
    _ = (K n : ℝ) * n / 2 * |x - y| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


lemma Ssum_net {n : ℕ} (t : Fin (K n) → Bool) (L : ℕ) (hL : 0 < L) (μ : ℝ)
    (h : ∀ m < L, |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)| < μ ∧
      |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)| < μ) (x : ℝ) :
    ‖Ssum t x‖ ≤ 2 * μ + (K n : ℝ) * n / 2 * (2 * π / L) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  set x' := toIcoMod hp 0 x with hx'
  have hmem := toIcoMod_mem_Ico' hp x
  rw [← hx'] at hmem
  have hxx : Ssum t x = Ssum t x' := by
    have e := toIcoMod_add_toIcoDiv_zsmul hp 0 x
    rw [← hx', zsmul_eq_mul] at e
    rw [← e, Ssum_periodic]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set m := ⌊x' * L / (2 * π)⌋₊ with hm
  have hq0 : 0 ≤ x' * L / (2 * π) := by have := hmem.1; positivity
  have hmL : m < L := by
    rw [hm, Nat.floor_lt hq0]
    rw [div_lt_iff₀ hp]
    have := hmem.2
    nlinarith
  have hm1 : (m : ℝ) ≤ x' * L / (2 * π) := Nat.floor_le hq0
  have hm2 : x' * L / (2 * π) < m + 1 := Nat.lt_floor_add_one _
  set y := 2 * π * m / L
  have hy1 : y ≤ x' := by
    simp only [y]; rw [div_le_iff₀ hLr]
    rw [le_div_iff₀ hp] at hm1; nlinarith
  have hy2 : x' - y ≤ 2 * π / L := by
    simp only [y]
    rw [div_lt_iff₀ hp] at hm2
    have : x' * L < 2 * π * m + 2 * π := by nlinarith
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hLr]
    linarith
  obtain ⟨h1, h2⟩ := h m hmL
  rw [hxx]
  calc ‖Ssum t x'‖ ≤ ‖Ssum t y‖ + ‖Ssum t x' - Ssum t y‖ := norm_le_insert' _ _
    _ ≤ (|∑ p, sg (t p) * (Real.cos (kk n p * y) / 2)| +
          |∑ p, sg (t p) * (Real.sin (kk n p * y) / 2)|) + (K n : ℝ) * n / 2 * |x' - y| :=
        add_le_add (norm_Ssum_le t y) (Ssum_lip t x' y)
    _ ≤ 2 * μ + (K n : ℝ) * n / 2 * (2 * π / L) := by
        have hab : |x' - y| ≤ 2 * π / L := by rw [abs_of_nonneg (by linarith)]; exact hy2
        have : (K n : ℝ) * n / 2 * |x' - y| ≤ (K n : ℝ) * n / 2 * (2 * π / L) := by gcongr
        linarith

lemma tendsto_poly_exp :
    Filter.Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (1 / 5 : ℝ) / 8)))
      Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 5 : ℝ) / 8) Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp hg).const_mul (4 * 8 ^ 10)
  rw [mul_zero] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp_apply]
  have : ((n : ℝ) ^ (1 / 5 : ℝ) / 8) ^ 10 = (n : ℝ) ^ 2 / 8 ^ 10 := by
    rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [this]; field_simp

open scoped Classical in
/-- **Interface 1 holds.** -/
theorem hT_holds : HT := by
  intro η hη
  have hlim := tendsto_poly_exp
  have hev1 := (hlim.eventually (gt_mem_nhds hη))
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 4 * π ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop _)
  filter_upwards [hev1, hev2, Filter.eventually_ge_atTop 1] with n h1 h2 h3
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h3
  have hK1 : 1 ≤ K n := by unfold K; omega
  have hKn : (K n : ℝ) ≤ n := by
    have : K n ≤ n := by unfold K; omega
    exact_mod_cast this
  have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK1
  set L := n ^ 2 with hL
  have hL0 : 0 < L := by positivity
  set μ := ((n : ℝ) ^ (3 / 5 : ℝ) - π) / 2 with hμ
  have hμ0 : 0 ≤ μ := by rw [hμ]; nlinarith [Real.pi_pos]
  have hμ4 : (n : ℝ) ^ (3 / 5 : ℝ) / 4 ≤ μ := by rw [hμ]; nlinarith [Real.pi_pos]
  set V := (K n : ℝ) / 4 with hV
  have hV0 : 0 < V := by positivity
  -- each net point fails rarely
  have hcos : ∀ m : ℕ, ∑ p : Fin (K n), (Real.cos (kk n p * (2 * π * m / L)) / 2) ^ 2 ≤ V := by
    intro m
    calc _ ≤ ∑ _p : Fin (K n), (1 / 4 : ℝ) := Finset.sum_le_sum (fun p _ => by
            have := Real.cos_sq_le_one (kk n p * (2 * π * m / L)); nlinarith)
      _ = V := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsin : ∀ m : ℕ, ∑ p : Fin (K n), (Real.sin (kk n p * (2 * π * m / L)) / 2) ^ 2 ≤ V := by
    intro m
    calc _ ≤ ∑ _p : Fin (K n), (1 / 4 : ℝ) := Finset.sum_le_sum (fun p _ => by
            have := Real.sin_sq_le_one (kk n p * (2 * π * m / L)); nlinarith)
      _ = V := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  set E := Real.exp (-(μ ^ 2 / (2 * V)))
  -- the bad set is covered by the net failures
  have hcover : (univ.filter fun t : Fin (K n) → Bool => ¬ Typical n t) ⊆
      (Finset.range L).biUnion (fun m =>
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)|) ∪
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)|)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_contra hc
    push Not at hc
    apply ht
    intro x
    refine (Ssum_net t L hL0 μ (fun m hm => hc m hm) x).trans ?_
    have : (K n : ℝ) * n / 2 * (2 * π / L) ≤ π := by
      rw [hL]; push_cast
      rw [show (K n : ℝ) * n / 2 * (2 * π / (n : ℝ) ^ 2) = (K n : ℝ) / n * π by
        field_simp]
      have : (K n : ℝ) / n ≤ 1 := by rw [div_le_one (by linarith)]; exact hKn
      nlinarith [Real.pi_pos]
    rw [hμ]; linarith
  have hbad : ((univ.filter fun t : Fin (K n) → Bool => ¬ Typical n t).card : ℝ)
      ≤ L * (2 * (2 * (2 ^ K n * E))) := by
    have hc1 := Finset.card_le_card hcover
    have hc2 := Finset.card_biUnion_le (s := Finset.range L) (t := fun m =>
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)|) ∪
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)|))
    have hc3 : ((univ.filter fun t : Fin (K n) → Bool => ¬ Typical n t).card : ℝ) ≤
        ∑ m ∈ Finset.range L, (((univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)|).card : ℝ) +
        ((univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)|).card : ℝ)) := by
      have := hc1.trans hc2
      have h4 : ∀ m ∈ Finset.range L, ((univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)|) ∪
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)|)).card ≤
          (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.cos (kk n p * (2 * π * m / L)) / 2)|).card +
        (univ.filter fun t : Fin (K n) → Bool =>
          μ ≤ |∑ p, sg (t p) * (Real.sin (kk n p * (2 * π * m / L)) / 2)|).card :=
        fun m _ => Finset.card_union_le _ _
      have h5 := this.trans (Finset.sum_le_sum h4)
      exact_mod_cast h5
    refine hc3.trans ?_
    calc _ ≤ ∑ _m ∈ Finset.range L, (2 * (2 ^ K n * E) + 2 * (2 ^ K n * E)) :=
          Finset.sum_le_sum (fun m _ => add_le_add
            (hoeffding_abs _ V hV0 (hcos m) μ hμ0) (hoeffding_abs _ V hV0 (hsin m) μ hμ0))
      _ = L * (2 * (2 * (2 ^ K n * E))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the failure probability is small
  have hE : (L : ℝ) * (2 * (2 * E)) ≤ η := by
    have hexp : -(μ ^ 2 / (2 * V)) ≤ -((n : ℝ) ^ (1 / 5 : ℝ) / 8) := by
      rw [neg_le_neg_iff, hV]
      have h65 : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 5 : ℝ) * n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
        rw [show (3 / 5 : ℝ) * ((2 : ℕ) : ℝ) = 1 / 5 + 1 by norm_num,
          Real.rpow_add (by linarith), Real.rpow_one]
      have hμ2 : (n : ℝ) ^ (1 / 5 : ℝ) * n / 16 ≤ μ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hμ4 2
        rw [div_pow, h65] at this
        linarith
      rw [le_div_iff₀ (by positivity)]
      have : (n : ℝ) ^ (1 / 5 : ℝ) / 8 * (2 * (K n / 4)) ≤ (n : ℝ) ^ (1 / 5 : ℝ) * n / 16 := by
        have : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by positivity
        nlinarith
      linarith
    have := Real.exp_le_exp.mpr hexp
    have hL' : (L : ℝ) = (n : ℝ) ^ 2 := by rw [hL]; push_cast; ring
    rw [hL']
    have : (n : ℝ) ^ 2 * (2 * (2 * E)) ≤ 4 * (n : ℝ) ^ 2 *
        Real.exp (-((n : ℝ) ^ (1 / 5 : ℝ) / 8)) := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  -- conclude
  have htot : ((univ.filter fun t : Fin (K n) → Bool => Typical n t).card : ℝ) +
      ((univ.filter fun t : Fin (K n) → Bool => ¬ Typical n t).card : ℝ) = 2 ^ K n := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (K n) → Bool)))
      (fun t => Typical n t)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  have : ((univ.filter fun t : Fin (K n) → Bool => ¬ Typical n t).card : ℝ) ≤ η * 2 ^ K n := by
    refine hbad.trans ?_
    have h2K : (0 : ℝ) < 2 ^ K n := by positivity
    nlinarith
  linarith


/-! ## Trigonometric sums over the frequencies `kk n p` -/

/-- **Dirichlet bound** for the frequency set `{n - 2p : p < K}`. -/
lemma dirichlet (n : ℕ) (x : ℝ) (hs : Real.sin x ≠ 0) :
    ‖∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I)‖ ≤ 1 / |Real.sin x| := by
  set w := Complex.exp (↑(-2 * x) * Complex.I) with hw
  have hterm : ∀ p : ℕ, Complex.exp (↑(((n : ℝ) - 2 * (p : ℝ)) * x) * Complex.I)
      = Complex.exp (↑((n : ℝ) * x) * Complex.I) * w ^ p := by
    intro p
    rw [hw, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  have hsum : ∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I)
      = Complex.exp (↑((n : ℝ) * x) * Complex.I) * ∑ p ∈ Finset.range (K n), w ^ p := by
    rw [Finset.mul_sum]
    have hr := Fin.sum_univ_eq_sum_range (fun p : ℕ =>
      Complex.exp (↑(((n : ℝ) - 2 * (p : ℝ)) * x) * Complex.I)) (K n)
    simp only [kk]
    rw [hr]
    exact Finset.sum_congr rfl (fun p _ => hterm p)
  have hw1 : ‖w - 1‖ = 2 * |Real.sin x| := by
    rw [hw, show (↑(-2 * x) * Complex.I) = Complex.I * ↑(-2 * x) by ring,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show -2 * x / 2 = -x by ring, Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg]
    norm_num
  have hwne : w ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hw1
    have : 0 < |Real.sin x| := abs_pos.mpr hs
    linarith
  rw [hsum, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, geom_sum_eq hwne, norm_div, hw1]
  have hwn : ‖w ^ K n - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hw, Complex.norm_exp_ofReal_mul_I, one_pow, norm_one]; norm_num
  have hpos : 0 < |Real.sin x| := abs_pos.mpr hs
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith


/-- The cosine sum over the frequencies. -/
def Dc (n : ℕ) (x : ℝ) : ℝ := ∑ p : Fin (K n), Real.cos (kk n p * x)

/-- Telescoping: `2 sin x · Dc x = sin ((n+1)x) - sin (r x)`. -/
lemma Dc_mul_sin (n : ℕ) (x : ℝ) :
    2 * Real.sin x * Dc n x = Real.sin (((n : ℝ) + 1) * x) - Real.sin ((r n : ℝ) * x) := by
  unfold Dc
  rw [Finset.mul_sum]
  have hr0 := Fin.sum_univ_eq_sum_range
    (fun p : ℕ => 2 * Real.sin x * Real.cos (((n : ℝ) - 2 * p) * x)) (K n)
  simp only [kk]
  rw [hr0]
  · have hstep : ∀ p : ℕ, 2 * Real.sin x * Real.cos (((n : ℝ) - 2 * p) * x)
        = Real.sin (((n : ℝ) + 1 - 2 * p) * x) - Real.sin (((n : ℝ) + 1 - 2 * ((p + 1 : ℕ) : ℝ)) * x) := by
      intro p
      have e1 : ((n : ℝ) + 1 - 2 * p) * x = ((n : ℝ) - 2 * p) * x + x := by ring
      have e2 : ((n : ℝ) + 1 - 2 * ((p + 1 : ℕ) : ℝ)) * x = ((n : ℝ) - 2 * p) * x - x := by
        push_cast; ring
      rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
    simp_rw [hstep]
    rw [Finset.sum_range_sub' (fun p : ℕ => Real.sin (((n : ℝ) + 1 - 2 * p) * x)) (K n)]
    have hr : ((n : ℝ) + 1 - 2 * ((K n : ℕ) : ℝ)) = (r n : ℝ) := by
      have := two_K_add_r n
      have : ((n : ℕ) : ℝ) + 1 = 2 * (K n : ℝ) + r n := by exact_mod_cast this.symm
      linarith
    rw [hr]; simp

lemma Dc_eq (n : ℕ) (x : ℝ) (hs : Real.sin x ≠ 0) :
    Dc n x = (Real.sin (((n : ℝ) + 1) * x) - Real.sin ((r n : ℝ) * x)) / (2 * Real.sin x) := by
  rw [← Dc_mul_sin]; field_simp

lemma abs_Dc_le (n : ℕ) (x : ℝ) (hs : Real.sin x ≠ 0) : |Dc n x| ≤ 1 / |Real.sin x| := by
  rw [Dc_eq n x hs, abs_div, abs_mul, abs_two]
  have h1 : |Real.sin (((n : ℝ) + 1) * x) - Real.sin ((r n : ℝ) * x)| ≤ 2 := by
    refine (abs_sub _ _).trans ?_
    linarith [Real.abs_sin_le_one (((n : ℝ) + 1) * x), Real.abs_sin_le_one ((r n : ℝ) * x)]
  have hpos : 0 < |Real.sin x| := abs_pos.mpr hs
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-- The step `h = 3π / (4K)` makes neighbouring values negatively correlated. -/
def hstep (n : ℕ) : ℝ := 3 * π / (4 * K n)

lemma Dc_hstep_le (n : ℕ) (hn : 10 ≤ n) : Dc n (hstep n) ≤ -1 / (2 * hstep n) + 1 := by
  have hK : (5 : ℝ) ≤ K n := by
    have : 5 ≤ K n := by unfold K; omega
    exact_mod_cast this
  set h := hstep n with hh
  have hpos : 0 < h := by rw [hh, hstep]; positivity
  have hle : h ≤ 1 / 2 := by
    rw [hh, hstep, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2]
  have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_gt_three])
  have hsinle : Real.sin h ≤ h := Real.sin_le hpos.le
  have hcos : 1 - h ^ 2 / 2 ≤ Real.cos h := Real.one_sub_sq_div_two_le_cos
  have hr := r_le_one n
  have hKr := two_K_add_r n
  have hnK : ((n : ℝ) + 1) * h = 3 * π / 2 + (r n : ℝ) * h := by
    have : ((n : ℕ) : ℝ) + 1 = 2 * (K n : ℝ) + r n := by exact_mod_cast hKr.symm
    rw [this, hh, hstep]; field_simp; ring
  rw [Dc_eq n h hsin.ne', hnK]
  have hsin1 : Real.sin (3 * π / 2 + (r n : ℝ) * h) = -Real.cos ((r n : ℝ) * h) := by
    rw [Real.sin_add]
    have : 3 * π / 2 = π + π / 2 := by ring
    rw [this, Real.sin_add, Real.cos_add]; simp
  rw [hsin1]
  -- numerator ≤ -cos h
  have hnum : -Real.cos ((r n : ℝ) * h) - Real.sin ((r n : ℝ) * h) ≤ -Real.cos h := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with h0 | h1
    · rw [h0]; simp
      have := Real.cos_le_one h; linarith
    · rw [h1]; simp; linarith
  have hcpos : 0 < Real.cos h := by nlinarith
  calc (-Real.cos ((r n : ℝ) * h) - Real.sin ((r n : ℝ) * h)) / (2 * Real.sin h)
      ≤ -Real.cos h / (2 * Real.sin h) := by gcongr
    _ ≤ -Real.cos h / (2 * h) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    _ ≤ -1 / (2 * h) + 1 := by
        rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith


/-! ## Fourth moments of symmetric coordinates (abstract) -/

section Moments

variable {Ωs J : Type*} [Fintype Ωs] [Fintype J] [DecidableEq J]

/-- The sign picked up by a product of four coordinates when coordinate `m` is flipped. -/
def flipSign (m j k j' k' : J) : ℝ :=
  (if j = m then -1 else 1) * (if k = m then -1 else 1) * (if j' = m then -1 else 1) *
    (if k' = m then -1 else 1)

/-- If no pairing of four indices holds, some index occurs an odd number of times. -/
lemma exists_odd (j k j' k' : J) (h1 : ¬ (j = k ∧ j' = k')) (h2 : ¬ (j = j' ∧ k = k'))
    (h3 : ¬ (j = k' ∧ k = j')) : ∃ m, flipSign m j k j' k' = -1 := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hjj : j = j'
    · subst hjj
      refine ⟨k', ?_⟩; unfold flipSign
      have : j ≠ k' := fun h => h1 ⟨rfl, h⟩
      simp [this]
    · by_cases hjk' : j = k'
      · subst hjk'
        refine ⟨j', ?_⟩; unfold flipSign
        simp [Ne.symm hjj, hjj]
      · refine ⟨j', ?_⟩; unfold flipSign
        have hjk'2 : j' ≠ k' := fun h => h1 ⟨rfl, h⟩
        simp [hjj, Ne.symm hjk'2]
  · by_cases hjj : j = j'
    · subst hjj
      refine ⟨k, ?_⟩; unfold flipSign
      have hkk : k ≠ k' := fun h => h2 ⟨rfl, h⟩
      simp [hjk, Ne.symm hkk]
    · by_cases hjk' : j = k'
      · subst hjk'
        refine ⟨k, ?_⟩; unfold flipSign
        have hkj : k ≠ j' := fun h => h3 ⟨rfl, h⟩
        simp [hjk, Ne.symm hkj]
      · refine ⟨j, ?_⟩; unfold flipSign
        simp [hjk, hjj, hjk', Ne.symm hjk, Ne.symm hjj, Ne.symm hjk']

variable (Z : J → Ωs → ℝ) (σ : J → Ωs ≃ Ωs)
  (hflip : ∀ j ω, Z j (σ j ω) = -Z j ω) (hfix : ∀ j k ω, k ≠ j → Z k (σ j ω) = Z k ω)

include hflip hfix in
lemma coord_flip (m j : J) (ω : Ωs) : Z j (σ m ω) = (if j = m then -1 else 1) * Z j ω := by
  split_ifs with h
  · subst h; rw [hflip]; ring
  · rw [hfix m j ω h]; ring

include hflip hfix in
/-- Odd products have zero sum. -/
lemma sum_four_eq_zero (j k j' k' : J) (h1 : ¬ (j = k ∧ j' = k')) (h2 : ¬ (j = j' ∧ k = k'))
    (h3 : ¬ (j = k' ∧ k = j')) :
    ∑ ω, Z j ω * Z k ω * Z j' ω * Z k' ω = 0 := by
  obtain ⟨m, hm⟩ := exists_odd j k j' k' h1 h2 h3
  have hinv := Fintype.sum_equiv (σ m) (fun ω => Z j (σ m ω) * Z k (σ m ω) * Z j' (σ m ω) *
    Z k' (σ m ω)) (fun ω => Z j ω * Z k ω * Z j' ω * Z k' ω) (fun ω => rfl)
  simp_rw [coord_flip Z σ hflip hfix m] at hinv
  have : ∀ ω, (if j = m then -1 else 1) * Z j ω * ((if k = m then -1 else 1) * Z k ω) *
      ((if j' = m then -1 else 1) * Z j' ω) * ((if k' = m then -1 else 1) * Z k' ω)
      = flipSign m j k j' k' * (Z j ω * Z k ω * Z j' ω * Z k' ω) := by
    intro ω; unfold flipSign; ring
  simp_rw [this, ← Finset.mul_sum, hm] at hinv
  linarith

include hflip hfix in
lemma sum_two (j k : J) (h : j ≠ k) : ∑ ω, Z j ω * Z k ω = 0 := by
  have hinv := Fintype.sum_equiv (σ j) (fun ω => Z j (σ j ω) * Z k (σ j ω))
    (fun ω => Z j ω * Z k ω) (fun ω => rfl)
  simp_rw [hflip, hfix j k _ (Ne.symm h)] at hinv
  simp only [neg_mul, Finset.sum_neg_distrib] at hinv
  linarith

end Moments


section Variance

variable {Ωs J : Type*} [Fintype Ωs] [Fintype J] [DecidableEq J]
  (Z : J → Ωs → ℝ) (σ : J → Ωs ≃ Ωs)
  (hflip : ∀ j ω, Z j (σ j ω) = -Z j ω) (hfix : ∀ j k ω, k ≠ j → Z k (σ j ω) = Z k ω)
  (hbd : ∀ j ω, |Z j ω| ≤ 2)
  (hind : ∀ j k, j ≠ k → (Fintype.card Ωs : ℝ) * ∑ ω, Z j ω ^ 2 * Z k ω ^ 2
    = (∑ ω, Z j ω ^ 2) * ∑ ω, Z k ω ^ 2)

/-- The quadratic form. -/
def Qf (A : J → J → ℝ) (ω : Ωs) : ℝ := ∑ j, ∑ k, A j k * Z j ω * Z k ω

include hflip hfix in
lemma sum_Qf (A : J → J → ℝ) :
    ∑ ω, Qf Z A ω = ∑ j, A j j * ∑ ω, Z j ω ^ 2 := by
  have hjk : ∀ j k, ∑ ω, A j k * Z j ω * Z k ω = if j = k then A j j * ∑ ω, Z j ω ^ 2 else 0 := by
    intro j k
    split_ifs with h
    · subst h; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)
    · have := sum_two Z σ hflip hfix j k h
      calc _ = A j k * ∑ ω, Z j ω * Z k ω := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)
        _ = 0 := by rw [this, mul_zero]
  unfold Qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [hjk]
  rw [Finset.sum_ite_eq]; simp

lemma abs_four_le (hbd : ∀ j ω, |Z j ω| ≤ 2) (j k j' k' : J) (ω : Ωs) :
    |Z j ω * Z k ω * Z j' ω * Z k' ω| ≤ 16 := by
  rw [abs_mul, abs_mul, abs_mul]
  have := hbd j ω; have := hbd k ω; have := hbd j' ω; have := hbd k' ω
  have := abs_nonneg (Z j ω); have := abs_nonneg (Z k ω); have := abs_nonneg (Z j' ω)
  have := abs_nonneg (Z k' ω)
  calc |Z j ω| * |Z k ω| * |Z j' ω| * |Z k' ω| ≤ 2 * 2 * 2 * 2 := by gcongr
    _ = 16 := by norm_num

include hflip hfix hbd hind in
/-- **Variance of a symmetric quadratic form.** -/
lemma var_Qf (A : J → J → ℝ) :
    ∑ ω, Qf Z A ω ^ 2 - (∑ ω, Qf Z A ω) ^ 2 / Fintype.card Ωs
      ≤ 32 * Fintype.card Ωs * ∑ j, ∑ k, A j k ^ 2 := by
  set N := (Fintype.card Ωs : ℝ)
  by_cases hN : N = 0
  · have h0 : Fintype.card Ωs = 0 := by simpa [N] using hN
    have : IsEmpty Ωs := Fintype.card_eq_zero_iff.mp h0
    simp [hN]
  have hNpos : 0 < N := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
  set s : J → ℝ := fun j => ∑ ω, Z j ω ^ 2
  set S : J → J → J → J → ℝ := fun j k j' k' => ∑ ω, Z j ω * Z k ω * Z j' ω * Z k' ω
  set C : J → J → J → J → ℝ := fun j k j' k' =>
    S j k j' k' - (if j = k ∧ j' = k' then s j * s j' / N else 0)
  have hs_le : ∀ j, s j ≤ 4 * N := by
    intro j
    calc s j ≤ ∑ _ω : Ωs, (4 : ℝ) := Finset.sum_le_sum (fun ω _ => by
            have := hbd j ω; have := abs_nonneg (Z j ω)
            rw [← sq_abs]; nlinarith)
      _ = 4 * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hs0 : ∀ j, 0 ≤ s j := fun j => Finset.sum_nonneg (fun ω _ => sq_nonneg _)
  have hS_abs : ∀ j k j' k', |S j k j' k'| ≤ 16 * N := by
    intro j k j' k'
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _ω : Ωs, (16 : ℝ) := Finset.sum_le_sum (fun ω _ => abs_four_le Z hbd _ _ _ _ ω)
      _ = 16 * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- C vanishes off the two pairings
  have hC0 : ∀ j k j' k', ¬ (j = j' ∧ k = k') → ¬ (j = k' ∧ k = j') → C j k j' k' = 0 := by
    intro j k j' k' h2 h3
    by_cases h1 : j = k ∧ j' = k'
    · obtain ⟨rfl, rfl⟩ := h1
      have hjj : j ≠ j' := fun h => h2 ⟨h, h⟩
      simp only [C, S, s, and_self, ↓reduceIte]
      have e : ∑ ω, Z j ω * Z j ω * Z j' ω * Z j' ω = ∑ ω, Z j ω ^ 2 * Z j' ω ^ 2 :=
        Finset.sum_congr rfl (fun ω _ => by ring)
      rw [e, sub_eq_zero, eq_div_iff hN]
      linarith [hind j j' hjj]
    · simp only [C, S, h1, ↓reduceIte, sub_zero]
      exact sum_four_eq_zero Z σ hflip hfix j k j' k' h1 h2 h3
  have hC_abs : ∀ j k j' k', |C j k j' k'| ≤ 16 * N := by
    intro j k j' k'
    simp only [C]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have hS0 : 0 ≤ S j j j' j' := Finset.sum_nonneg (fun ω _ => by
        have : Z j ω * Z j ω * Z j' ω * Z j' ω = (Z j ω * Z j' ω) ^ 2 := by ring
        rw [this]; exact sq_nonneg _)
      have hp : 0 ≤ s j * s j' / N := by have := hs0 j; have := hs0 j'; positivity
      have hp2 : s j * s j' / N ≤ 16 * N := by
        rw [div_le_iff₀ hNpos]
        have := hs_le j; have := hs_le j'; have := hs0 j; have := hs0 j'
        nlinarith
      have := hS_abs j j j' j'
      rw [abs_le] at this ⊢; constructor <;> linarith
    · simpa using hS_abs j k j' k'
  -- expand
  have hexp : ∑ ω, Qf Z A ω ^ 2 - (∑ ω, Qf Z A ω) ^ 2 / N
      = ∑ j, ∑ k, ∑ j', ∑ k', A j k * A j' k' * C j k j' k' := by
    rw [sum_Qf Z σ hflip hfix A]
    have h1 : ∑ ω, Qf Z A ω ^ 2 = ∑ j, ∑ k, ∑ j', ∑ k', A j k * A j' k' * S j k j' k' := by
      simp only [Qf, S, sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      refine Finset.sum_congr rfl (fun ω _ => by ring)
    have h2 : (∑ j, A j j * s j) ^ 2 / N
        = ∑ j, ∑ k, ∑ j', ∑ k', A j k * A j' k' *
            (if j = k ∧ j' = k' then s j * s j' / N else 0) := by
      have hin : ∀ j k, ∑ j', ∑ k', A j k * A j' k' *
          (if j = k ∧ j' = k' then s j * s j' / N else 0)
          = if j = k then ∑ j', A j j * A j' j' * (s j * s j' / N) else 0 := by
        intro j k
        split_ifs with hjk
        · subst hjk; refine Finset.sum_congr rfl (fun j' _ => ?_)
          rw [Finset.sum_eq_single j' (fun k' _ hk => by simp [Ne.symm hk]) (by simp)]
          simp
        · exact Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun k' _ => by simp [hjk]))
      simp_rw [hin, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sq, Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j' _ => by ring)
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    simp only [C]; ring
  rw [hexp]
  -- bound the inner double sum for fixed (j, k)
  have hinner : ∀ j k, ∑ j', ∑ k', A j k * A j' k' * C j k j' k'
      ≤ 16 * N * (|A j k| * (|A j k| + |A k j|)) := by
    intro j k
    have hsupp : ∀ j' k', A j k * A j' k' * C j k j' k' ≤
        16 * N * |A j k| * ((if j' = j ∧ k' = k then |A j' k'| else 0) +
          (if j' = k ∧ k' = j then |A j' k'| else 0)) := by
      intro j' k'
      by_cases h2 : j = j' ∧ k = k'
      · obtain ⟨rfl, rfl⟩ := h2
        have := hC_abs j k j k
        have e : A j k * A j k * C j k j k ≤ |A j k| * |A j k| * (16 * N) := by
          calc _ ≤ |A j k * A j k * C j k j k| := le_abs_self _
            _ = |A j k| * |A j k| * |C j k j k| := by rw [abs_mul, abs_mul]
            _ ≤ _ := by gcongr
        simp only [and_self, ↓reduceIte]
        have : 0 ≤ (if j = k ∧ k = j then |A j k| else 0) := by split_ifs <;> simp
        have h16 : 0 ≤ 16 * N * |A j k| := by positivity
        nlinarith [mul_nonneg h16 this]
      · by_cases h3 : j = k' ∧ k = j'
        · obtain ⟨rfl, rfl⟩ := h3
          have := hC_abs j k k j
          have e : A j k * A k j * C j k k j ≤ |A j k| * |A k j| * (16 * N) := by
            calc _ ≤ |A j k * A k j * C j k k j| := le_abs_self _
              _ = |A j k| * |A k j| * |C j k k j| := by rw [abs_mul, abs_mul]
              _ ≤ _ := by gcongr
          simp only [and_self, ↓reduceIte]
          have : 0 ≤ (if k = j ∧ j = k then |A k j| else 0) := by split_ifs <;> simp
          have h16 : 0 ≤ 16 * N * |A j k| := by positivity
          nlinarith [mul_nonneg h16 this]
        · rw [hC0 j k j' k' h2 h3, mul_zero]
          have : 0 ≤ ((if j' = j ∧ k' = k then |A j' k'| else 0) +
            (if j' = k ∧ k' = j then |A j' k'| else 0)) := by
            split_ifs <;> simp [abs_nonneg]
          have : 0 ≤ 16 * N * |A j k| := by positivity
          positivity
    calc ∑ j', ∑ k', A j k * A j' k' * C j k j' k'
        ≤ ∑ j', ∑ k', 16 * N * |A j k| * ((if j' = j ∧ k' = k then |A j' k'| else 0) +
          (if j' = k ∧ k' = j then |A j' k'| else 0)) :=
          Finset.sum_le_sum (fun j' _ => Finset.sum_le_sum (fun k' _ => hsupp j' k'))
      _ = 16 * N * |A j k| * (|A j k| + |A k j|) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp),
            Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, true_and]
          rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp),
            Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
          simp
      _ = 16 * N * (|A j k| * (|A j k| + |A k j|)) := by ring
  calc ∑ j, ∑ k, ∑ j', ∑ k', A j k * A j' k' * C j k j' k'
      ≤ ∑ j, ∑ k, 16 * N * (|A j k| * (|A j k| + |A k j|)) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hinner j k))
    _ = 16 * N * (∑ j, ∑ k, A j k ^ 2 + ∑ j, ∑ k, |A j k| * |A k j|) := by
        simp only [← Finset.mul_sum, mul_add, Finset.sum_add_distrib, sq_abs, ← sq]
    _ ≤ 16 * N * (∑ j, ∑ k, A j k ^ 2 + ∑ j, ∑ k, A j k ^ 2) := by
        have h : ∑ j, ∑ k, |A j k| * |A k j| ≤ ∑ j, ∑ k, (A j k ^ 2 / 2 + A k j ^ 2 / 2) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => by
            nlinarith [sq_abs (A j k), sq_abs (A k j), sq_nonneg (|A j k| - |A k j|)]))
        have h3 : ∑ j, ∑ k, (A j k ^ 2 / 2 + A k j ^ 2 / 2)
            = (∑ j, ∑ k, A j k ^ 2) / 2 + (∑ j, ∑ k, A k j ^ 2) / 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_div]
        have h4 : ∑ j, ∑ k, A k j ^ 2 = ∑ j, ∑ k, A j k ^ 2 := Finset.sum_comm
        have hY : ∑ j, ∑ k, |A j k| * |A k j| ≤ ∑ j, ∑ k, A j k ^ 2 := by linarith
        have h16 : 0 ≤ 16 * N := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h16
    _ = 32 * N * ∑ j, ∑ k, A j k ^ 2 := by ring

end Variance


/-! ## The coordinates of `RRa` as symmetric variables -/

/-- Independence of two coordinates of a uniform function space, by counting. -/
lemma pi_indep {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] (p q : ι) (hpq : p ≠ q)
    (f g : W → ℝ) :
    (∑ _y : ι → W, (1 : ℝ)) * ∑ y : ι → W, f (y p) * g (y q)
      = (∑ y : ι → W, f (y p)) * ∑ y : ι → W, g (y q) := by
  have e1 : ∀ y : ι → W, f (y p) * g (y q) = ∏ i, (if i = p then f (y i) else
      if i = q then g (y i) else 1) := by
    intro y
    rw [Finset.prod_ite, Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one]
    rw [Finset.filter_eq' (s := univ), Finset.filter_filter]
    have : (univ.filter fun i => ¬ i = p ∧ i = q) = {q} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨Ne.symm hpq, rfl⟩
    rw [this]; simp
  have e2 : ∀ y : ι → W, f (y p) = ∏ i, (if i = p then f (y i) else 1) := by
    intro y; rw [Finset.prod_ite_eq']; simp
  have e3 : ∀ y : ι → W, g (y q) = ∏ i, (if i = q then g (y i) else 1) := by
    intro y; rw [Finset.prod_ite_eq']; simp
  have e4 : ∀ _y : ι → W, (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := fun _ => by simp
  simp_rw [e1]
  conv_lhs => arg 1; rw [show (∑ _y : ι → W, (1 : ℝ)) = ∑ y : ι → W, ∏ _i : ι, (1 : ℝ) by simp]
  simp_rw [e2, e3]
  rw [← Fintype.prod_sum (fun i (w : W) => (1 : ℝ)),
    ← Fintype.prod_sum (fun i (w : W) => if i = p then f w else if i = q then g w else 1),
    ← Fintype.prod_sum (fun i (w : W) => if i = p then f w else 1),
    ← Fintype.prod_sum (fun i (w : W) => if i = q then g w else 1),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hp : i = p
  · subst hp; simp [hpq, Ne.symm hpq, mul_comm]
  · by_cases hq : i = q
    · subst hq; simp [hp]
    · simp [hp, hq]

variable {n : ℕ}

/-- Coordinates of `RR`-data. -/
def Zc (j : Fin (K n) ⊕ Fin (r n)) (a : Al n) : ℝ :=
  match j with
  | Sum.inl p => if (a.1 p).1 then 2 * ((((a.1 p).2 : ℤˣ) : ℤ) : ℝ) else 0
  | Sum.inr i => (((a.2 i : ℤˣ) : ℤ) : ℝ)

/-- The weights of `RRa`. -/
def vc (x : ℝ) (j : Fin (K n) ⊕ Fin (r n)) : ℝ :=
  match j with
  | Sum.inl p => Real.cos (kk n p * x)
  | Sum.inr _ => 1

lemma RRa_eq (a : Al n) (x : ℝ) : RRa a x = ∑ j, vc x j * Zc j a := by
  rw [Fintype.sum_sum_type]
  unfold RRa vc Zc
  rw [add_comm]; simp only [one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => by ring)

/-- The flip of one coordinate. -/
def flipFun (j : Fin (K n) ⊕ Fin (r n)) (a : Al n) : Al n :=
  match j with
  | Sum.inl p => (Function.update a.1 p ((a.1 p).1, -(a.1 p).2), a.2)
  | Sum.inr i => (a.1, Function.update a.2 i (-(a.2 i)))

lemma flipFun_invol (j : Fin (K n) ⊕ Fin (r n)) : Function.Involutive (flipFun j) := by
  intro a
  rcases j with p | i
  · simp only [flipFun, Function.update_self, neg_neg, Function.update_idem]
    ext q <;> simp [Function.update_apply] <;> split_ifs <;> simp_all
  · simp only [flipFun, Function.update_self, neg_neg, Function.update_idem]
    ext q <;> simp [Function.update_apply] <;> split_ifs <;> simp_all

def flipEquiv (j : Fin (K n) ⊕ Fin (r n)) : Al n ≃ Al n := (flipFun_invol j).toPerm _

lemma Zc_flip (j : Fin (K n) ⊕ Fin (r n)) (a : Al n) : Zc j (flipEquiv j a) = -Zc j a := by
  rcases j with p | i
  · simp only [flipEquiv, Function.Involutive.coe_toPerm, flipFun, Zc, Function.update_self]
    split_ifs <;> push_cast <;> ring
  · simp only [flipEquiv, Function.Involutive.coe_toPerm, flipFun, Zc, Function.update_self]
    push_cast; ring

lemma Zc_fix (j k : Fin (K n) ⊕ Fin (r n)) (a : Al n) (h : k ≠ j) :
    Zc k (flipEquiv j a) = Zc k a := by
  rcases j with p | i <;> rcases k with q | i'
  · have : q ≠ p := fun e => h (by rw [e])
    simp [flipEquiv, flipFun, Zc, Function.update_of_ne this]
  · rfl
  · rfl
  · have : i' ≠ i := fun e => h (by rw [e])
    simp [flipEquiv, flipFun, Zc, Function.update_of_ne this]

lemma Zc_bd (j : Fin (K n) ⊕ Fin (r n)) (a : Al n) : |Zc j a| ≤ 2 := by
  rcases j with p | i
  · simp only [Zc]
    split_ifs
    · rcases Int.units_eq_one_or ((a.1 p).2) with h | h <;> simp [h]
    · simp
  · simp only [Zc]
    rcases Int.units_eq_one_or (a.2 i) with h | h <;> simp [h]

lemma Zc_inr_sq (i : Fin (r n)) (a : Al n) : Zc (Sum.inr i) a ^ 2 = 1 := by
  simp only [Zc]
  rcases Int.units_eq_one_or (a.2 i) with h | h <;> simp [h]

lemma Zc_ind (j k : Fin (K n) ⊕ Fin (r n)) (h : j ≠ k) :
    (Fintype.card (Al n) : ℝ) * ∑ a, Zc j a ^ 2 * Zc k a ^ 2
      = (∑ a, Zc j a ^ 2) * ∑ a, Zc k a ^ 2 := by
  have hN : (Fintype.card (Al n) : ℝ) = ∑ _a : Al n, (1 : ℝ) := by simp
  rcases k with q | i
  · rcases j with p | i
    · have hpq : p ≠ q := fun e => h (by rw [e])
      set f : Bool × ℤˣ → ℝ := fun w => (if w.1 then 2 * (((w.2 : ℤˣ) : ℤ) : ℝ) else 0) ^ 2
      have hs : ∀ G : (Fin (K n) → Bool × ℤˣ) → ℝ, ∑ a : Al n, G a.1
          = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) * ∑ y, G y := by
        intro G; rw [Fintype.sum_prod_type]; simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]; rw [Finset.mul_sum]
      have e1 : ∑ a : Al n, Zc (Sum.inl p) a ^ 2 * Zc (Sum.inl q) a ^ 2
          = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) * ∑ y : Fin (K n) → Bool × ℤˣ, f (y p) * f (y q) :=
        hs (fun y => f (y p) * f (y q))
      have e2 : ∑ a : Al n, Zc (Sum.inl p) a ^ 2
          = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) * ∑ y : Fin (K n) → Bool × ℤˣ, f (y p) := hs (fun y => f (y p))
      have e3 : ∑ a : Al n, Zc (Sum.inl q) a ^ 2
          = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) * ∑ y : Fin (K n) → Bool × ℤˣ, f (y q) := hs (fun y => f (y q))
      have e4 : (∑ _a : Al n, (1 : ℝ)) = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) *
          ∑ _y : Fin (K n) → Bool × ℤˣ, (1 : ℝ) := hs (fun _ => 1)
      rw [hN, e1, e2, e3, e4]
      have := pi_indep p q hpq f f
      linear_combination (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) ^ 2 * this
    · simp_rw [Zc_inr_sq, one_mul]; rw [hN]; try simp [mul_comm]
  · simp_rw [Zc_inr_sq, mul_one]; rw [hN]; try simp [mul_comm]


section FourthMoment

variable {Ωs J : Type*} [Fintype Ωs] [Fintype J] [DecidableEq J]
  (Z : J → Ωs → ℝ) (σ : J → Ωs ≃ Ωs)
  (hflip : ∀ j ω, Z j (σ j ω) = -Z j ω) (hfix : ∀ j k ω, k ≠ j → Z k (σ j ω) = Z k ω)
  (hbd : ∀ j ω, |Z j ω| ≤ 2)

include hflip hfix hbd in
/-- **Fourth-moment bound** for a product of two squared linear forms. -/
lemma sum_sq_sq_le (u v : J → ℝ) :
    ∑ ω, (∑ j, u j * Z j ω) ^ 2 * (∑ k, v k * Z k ω) ^ 2
      ≤ 48 * Fintype.card Ωs * (∑ j, u j ^ 2) * ∑ k, v k ^ 2 := by
  set N := (Fintype.card Ωs : ℝ)
  set S : J → J → J → J → ℝ := fun j k j' k' => ∑ ω, Z j ω * Z k ω * Z j' ω * Z k' ω
  have hS_abs : ∀ j k j' k', |S j k j' k'| ≤ 16 * N := by
    intro j k j' k'
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _ω : Ωs, (16 : ℝ) := Finset.sum_le_sum (fun ω _ => abs_four_le Z hbd _ _ _ _ ω)
      _ = 16 * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hpt : ∀ ω, (∑ j, u j * Z j ω) ^ 2 * (∑ k, v k * Z k ω) ^ 2
      = ∑ j, ∑ k, ∑ j', ∑ k', u j * u k * v j' * v k' * (Z j ω * Z k ω * Z j' ω * Z k' ω) := by
    intro ω
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k' _ => by ring)
  have hexp : ∑ ω, (∑ j, u j * Z j ω) ^ 2 * (∑ k, v k * Z k ω) ^ 2
      = ∑ j, ∑ k, ∑ j', ∑ k', u j * u k * v j' * v k' * S j k j' k' := by
    simp_rw [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [Finset.mul_sum]
  rw [hexp]
  -- each term is bounded by the three pairings
  have hterm : ∀ j k j' k', u j * u k * v j' * v k' * S j k j' k' ≤
      16 * N * ((if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0) +
        (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0) +
        (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0)) := by
    intro j k j' k'
    by_cases h : (j = k ∧ j' = k') ∨ (j = j' ∧ k = k') ∨ (j = k' ∧ k = j')
    · have hle : u j * u k * v j' * v k' * S j k j' k' ≤ |u j * u k * v j' * v k'| * (16 * N) := by
        calc _ ≤ |u j * u k * v j' * v k' * S j k j' k'| := le_abs_self _
          _ = |u j * u k * v j' * v k'| * |S j k j' k'| := abs_mul _ _
          _ ≤ _ := by gcongr; exact hS_abs j k j' k'
      have h0 : 0 ≤ |u j * u k * v j' * v k'| := abs_nonneg _
      rcases h with h | h | h
      · have : (if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0) = |u j * u k * v j' * v k'| :=
          if_pos h
        rw [this]
        have hX : 0 ≤ (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hY : 0 ≤ (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hN0 : 0 ≤ 16 * N := by positivity
        nlinarith [mul_nonneg hN0 hX, mul_nonneg hN0 hY]
      · have : (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0) = |u j * u k * v j' * v k'| :=
          if_pos h
        rw [this]
        have hX : 0 ≤ (if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hY : 0 ≤ (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hN0 : 0 ≤ 16 * N := by positivity
        nlinarith [mul_nonneg hN0 hX, mul_nonneg hN0 hY]
      · have : (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0) = |u j * u k * v j' * v k'| :=
          if_pos h
        rw [this]
        have hX : 0 ≤ (if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hY : 0 ≤ (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0) := by split_ifs <;> positivity
        have hN0 : 0 ≤ 16 * N := by positivity
        nlinarith [mul_nonneg hN0 hX, mul_nonneg hN0 hY]
    · push Not at h
      obtain ⟨h1, h2, h3⟩ := h
      have := sum_four_eq_zero Z σ hflip hfix j k j' k' (fun e => h1 e.1 e.2)
        (fun e => h2 e.1 e.2) (fun e => h3 e.1 e.2)
      simp only [S, this, mul_zero]
      have : 0 ≤ (if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0) +
        (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0) +
        (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0) := by
        split_ifs <;> simp [abs_nonneg] <;> positivity
      have : 0 ≤ N := Nat.cast_nonneg _
      positivity
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) =>
    Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset J)) =>
      Finset.sum_le_sum (fun j' (_ : j' ∈ (univ : Finset J)) =>
        Finset.sum_le_sum (fun k' (_ : k' ∈ (univ : Finset J)) => hterm j k j' k'))))
  refine hsum.trans ?_
  -- evaluate the three pairing sums
  have P1 : ∑ j, ∑ k, ∑ j', ∑ k', (if j = k ∧ j' = k' then |u j * u k * v j' * v k'| else 0)
      = (∑ j, u j ^ 2) * ∑ k, v k ^ 2 := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j (fun k _ hk => Finset.sum_eq_zero (fun j' _ =>
      Finset.sum_eq_zero (fun k' _ => by simp [Ne.symm hk]))) (by simp)]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.sum_eq_single j' (fun k' _ hk => by simp [Ne.symm hk]) (by simp)]
    simp only [and_self, ↓reduceIte]
    rw [abs_mul, abs_mul, abs_mul, ← sq_abs (u j), ← sq_abs (v j')]; ring
  have P2 : ∑ j, ∑ k, ∑ j', ∑ k', (if j = j' ∧ k = k' then |u j * u k * v j' * v k'| else 0)
      = (∑ j, |u j * v j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.sum_eq_single j (fun j' _ hj => Finset.sum_eq_zero (fun k' _ => by
      simp [Ne.symm hj])) (by simp)]
    rw [Finset.sum_eq_single k (fun k' _ hk => by simp [Ne.symm hk]) (by simp)]
    simp only [and_self, ↓reduceIte]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]; ring
  have P3 : ∑ j, ∑ k, ∑ j', ∑ k', (if j = k' ∧ k = j' then |u j * u k * v j' * v k'| else 0)
      = (∑ j, |u j * v j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.sum_eq_single k (fun j' _ hj => Finset.sum_eq_zero (fun k' _ => by
      simp [Ne.symm hj])) (by simp)]
    rw [Finset.sum_eq_single j (fun k' _ hk => by simp [Ne.symm hk]) (by simp)]
    simp only [and_self, ↓reduceIte]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]; ring
  have hCS : (∑ j, |u j * v j|) ^ 2 ≤ (∑ j, u j ^ 2) * ∑ k, v k ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => |u j|) (fun j => |v j|)
    simp only [sq_abs] at this
    simpa [abs_mul] using this
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [P1, P2, P3]
  have : 0 ≤ N := Nat.cast_nonneg _
  nlinarith

end FourthMoment


lemma sum_pi_one {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] (p : ι) (f : W → ℝ) :
    (Fintype.card W : ℝ) * ∑ y : ι → W, f (y p) = (∑ w, f w) * ∑ _y : ι → W, (1 : ℝ) := by
  have e2 : ∀ y : ι → W, f (y p) = ∏ i, (if i = p then f (y i) else 1) := by
    intro y; rw [Finset.prod_ite_eq']; simp
  simp_rw [e2]
  rw [show (∑ _y : ι → W, (1 : ℝ)) = ∑ y : ι → W, ∏ _i : ι, (1 : ℝ) by simp]
  rw [← Fintype.prod_sum (fun i (w : W) => (1 : ℝ)),
    ← Fintype.prod_sum (fun i (w : W) => if i = p then f w else 1)]
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase univ (fun i => ∑ _w : W, (1 : ℝ)) (Finset.mem_univ p)]
  have : ∏ i ∈ univ.erase p, (∑ w : W, if i = p then f w else 1)
      = ∏ i ∈ univ.erase p, (∑ _w : W, (1 : ℝ)) :=
    Finset.prod_congr rfl (fun i hi => by simp [Finset.ne_of_mem_erase hi])
  rw [this]
  simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Second moments of the coordinates. -/
def sv (j : Fin (K n) ⊕ Fin (r n)) : ℝ :=
  match j with
  | Sum.inl _ => 2
  | Sum.inr _ => 1

lemma sum_Zc_sq (j : Fin (K n) ⊕ Fin (r n)) :
    ∑ a : Al n, Zc j a ^ 2 = (Fintype.card (Al n) : ℝ) * sv j := by
  rcases j with p | i
  · set f : Bool × ℤˣ → ℝ := fun w => (if w.1 then 2 * (((w.2 : ℤˣ) : ℤ) : ℝ) else 0) ^ 2
    have hs : ∑ a : Al n, Zc (Sum.inl p) a ^ 2
        = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) * ∑ y : Fin (K n) → Bool × ℤˣ, f (y p) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have : ∀ c : Fin (r n) → ℤˣ, Zc (Sum.inl p) (y, c) ^ 2 = f (y p) := fun c => rfl
      simp_rw [this]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    have h1 := sum_pi_one (ι := Fin (K n)) p f
    have hf : ∑ w, f w = 8 := by
      simp only [f, Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
      rw [show (univ : Finset ℤˣ) = {1, -1} from by decide, Finset.sum_pair (by decide)]
      norm_num
    have hW : (Fintype.card (Bool × ℤˣ) : ℝ) = 4 := by
      simp [Fintype.card_prod, Fintype.card_units_int]; try norm_num
    rw [hf, hW] at h1
    have hN : (Fintype.card (Al n) : ℝ) = (∑ _c : Fin (r n) → ℤˣ, (1 : ℝ)) *
        ∑ _y : Fin (K n) → Bool × ℤˣ, (1 : ℝ) := by
      simp [Fintype.card_prod, mul_comm]
    rw [hs, hN]; simp only [sv]
    have : ∑ y : Fin (K n) → Bool × ℤˣ, f (y p) = 2 * ∑ _y : Fin (K n) → Bool × ℤˣ, (1 : ℝ) := by
      linarith
    rw [this]; ring
  · simp_rw [Zc_inr_sq]; simp [sv]

/-! ## Interface 2 (`HZ`): many separated zeros of `RRa` -/

/-- Number of test intervals. -/
def Mn (n : ℕ) : ℕ := K n / 12

/-- Left endpoints. -/
def αl (n l : ℕ) : ℝ := π / 8 + 4 * hstep n * l

/-- Right endpoints. -/
def βl (n l : ℕ) : ℝ := αl n l + hstep n

/-- The matrix of the quadratic form `W = Σ_l RRa(α_l) RRa(β_l)`. -/
def Amat (n : ℕ) (j k : Fin (K n) ⊕ Fin (r n)) : ℝ :=
  ∑ l ∈ Finset.range (Mn n), vc (αl n l) j * vc (βl n l) k

lemma W_eq (a : Al n) :
    ∑ l ∈ Finset.range (Mn n), RRa a (αl n l) * RRa a (βl n l) = Qf Zc (Amat n) a := by
  simp only [RRa_eq, Finset.sum_mul_sum]
  unfold Qf Amat
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))


lemma sin_ge_of_mem {x : ℝ} (h1 : π / 4 ≤ x) (h2 : x ≤ 3 * π / 4) : Real.sqrt 2 / 2 ≤ Real.sin x := by
  rw [← Real.sin_pi_div_four]
  by_cases hx : x ≤ π / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hx h1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)

lemma abs_Dc_le_sqrt2 (n : ℕ) {x : ℝ} (h1 : π / 4 ≤ x) (h2 : x ≤ 3 * π / 4) :
    |Dc n x| ≤ Real.sqrt 2 := by
  have hs := sin_ge_of_mem h1 h2
  have hs0 : 0 < Real.sin x := lt_of_lt_of_le (by positivity) hs
  refine (abs_Dc_le n x hs0.ne').trans ?_
  rw [abs_of_pos hs0, div_le_iff₀ hs0]
  have h22 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  nlinarith [Real.sqrt_nonneg 2]

lemma hstep_pos (n : ℕ) (hn : 1 ≤ n) : 0 < hstep n := by
  have : 0 < K n := by unfold K; omega
  unfold hstep; positivity

lemma Mn_hstep (n : ℕ) (hn : 1 ≤ n) : (Mn n : ℝ) * hstep n * 8 ≤ π / 2 := by
  have hK : (0 : ℝ) < K n := by have : 0 < K n := by unfold K; omega
                                exact_mod_cast this
  have hM : (Mn n : ℝ) * 12 ≤ K n := by
    have : Mn n * 12 ≤ K n := by unfold Mn; omega
    exact_mod_cast this
  unfold hstep
  rw [show (Mn n : ℝ) * (3 * π / (4 * K n)) * 8 = (Mn n * 12) * π / (2 * K n) by
    field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_pos]

lemma αβ_mem (n : ℕ) (hn : 1 ≤ n) (l : ℕ) (hl : l < Mn n) :
    π / 4 ≤ αl n l + βl n l ∧ αl n l + βl n l ≤ 3 * π / 4 := by
  have hh := hstep_pos n hn
  have hM := Mn_hstep n hn
  have hl' : (l : ℝ) + 1 ≤ Mn n := by exact_mod_cast hl
  unfold βl αl
  constructor
  · have : 0 ≤ 4 * hstep n * l := by positivity
    linarith
  · nlinarith

lemma two_cos_mul_cos (a b : ℝ) : 2 * Real.cos a * Real.cos b = Real.cos (b - a) + Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The mean of `W` (divided by `N`). -/
lemma mean_W_le (n : ℕ) (hn : 10 ≤ n) :
    ∑ j, Amat n j j * sv j ≤ (Mn n : ℝ) * (4 - 2 * K n / (3 * π)) := by
  have hn1 : 1 ≤ n := by omega
  have hdiag : ∀ l, ∑ j : Fin (K n) ⊕ Fin (r n), vc (αl n l) j * vc (βl n l) j * sv j
      = Dc n (hstep n) + Dc n (αl n l + βl n l) + r n := by
    intro l
    rw [Fintype.sum_sum_type]
    simp only [vc, sv, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold Dc
    rw [← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_comm _ (2 : ℝ), ← mul_assoc, two_cos_mul_cos]
    congr 2 <;> unfold βl <;> ring
  unfold Amat
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hdiag]
  have hbound : ∀ l ∈ Finset.range (Mn n),
      Dc n (hstep n) + Dc n (αl n l + βl n l) + r n ≤ 4 - 2 * K n / (3 * π) := by
    intro l hl
    rw [Finset.mem_range] at hl
    have h1 := Dc_hstep_le n hn
    obtain ⟨m1, m2⟩ := αβ_mem n hn1 l hl
    have h2 := abs_Dc_le_sqrt2 n m1 m2
    have h3 : (r n : ℝ) ≤ 1 := by exact_mod_cast r_le_one n
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hK : (0 : ℝ) < K n := by have : 0 < K n := by unfold K; omega
                                  exact_mod_cast this
    have e : -1 / (2 * hstep n) = -(2 * K n / (3 * π)) := by
      unfold hstep; field_simp; ring
    rw [abs_le] at h2
    linarith
  calc _ ≤ ∑ _l ∈ Finset.range (Mn n), (4 - 2 * (K n : ℝ) / (3 * π)) := Finset.sum_le_sum hbound
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- Inverse-square sums over one side. -/
lemma sum_inv_sq_side (M l : ℕ) :
    ∑ l' ∈ (Finset.range M).filter (· < l), (((l : ℝ) - l') ^ 2)⁻¹ ≤ 2 := by
  have hinj : Set.InjOn (fun l' : ℕ => l - l') ((Finset.range M).filter (· < l) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    simp only at hab; omega
  have e : ∑ l' ∈ (Finset.range M).filter (· < l), (((l : ℝ) - l') ^ 2)⁻¹
      = ∑ d ∈ ((Finset.range M).filter (· < l)).image (fun l' => l - l'), ((d : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun l' hl' => ?_)
    simp only [Finset.mem_filter] at hl'
    rw [Nat.cast_sub hl'.2.le]
  rw [e]
  have hsub : ((Finset.range M).filter (· < l)).image (fun l' => l - l') ⊆ Finset.Ioo 0 (l + 1) := by
    intro d hd
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨l', ⟨_, h2⟩, rfl⟩ := hd
    simp only [Finset.mem_Ioo]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
  have := sum_Ioo_inv_sq_le (α := ℝ) 0 (l + 1)
  simpa using this

lemma sum_inv_sq_other (M l : ℕ) :
    ∑ l' ∈ (Finset.range M).filter (· ≠ l), (((l' : ℝ) - l) ^ 2)⁻¹ ≤ 4 := by
  have hsplit : (Finset.range M).filter (· ≠ l)
      = (Finset.range M).filter (· < l) ∪ (Finset.range M).filter (l < ·) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]; omega
  have hdisj : Disjoint ((Finset.range M).filter (· < l)) ((Finset.range M).filter (l < ·)) := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have h1 := sum_inv_sq_side M l
  have h2 : ∑ l' ∈ (Finset.range M).filter (l < ·), (((l' : ℝ) - l) ^ 2)⁻¹ ≤ 2 := by
    have hinj : Set.InjOn (fun l' : ℕ => l' - l) ((Finset.range M).filter (l < ·) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
      simp only at hab; omega
    have e : ∑ l' ∈ (Finset.range M).filter (l < ·), (((l' : ℝ) - l) ^ 2)⁻¹
        = ∑ d ∈ ((Finset.range M).filter (l < ·)).image (fun l' => l' - l), ((d : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun l' hl' => ?_)
      simp only [Finset.mem_filter] at hl'
      rw [Nat.cast_sub hl'.2.le]
    rw [e]
    have hsub : ((Finset.range M).filter (l < ·)).image (fun l' => l' - l) ⊆ Finset.Ioo 0 M := by
      intro d hd
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨l', ⟨h1, h2⟩, rfl⟩ := hd
      simp only [Finset.mem_Ioo]; omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 M
    simpa using this
  have e1 : ∑ l' ∈ (Finset.range M).filter (· < l), (((l' : ℝ) - l) ^ 2)⁻¹
      = ∑ l' ∈ (Finset.range M).filter (· < l), (((l : ℝ) - l') ^ 2)⁻¹ :=
    Finset.sum_congr rfl (fun _ _ => by ring)
  rw [e1]; linarith

/-- The Gram kernel of the weights. -/
def Gk (n : ℕ) (x y : ℝ) : ℝ := ∑ j : Fin (K n) ⊕ Fin (r n), vc (n := n) x j * vc (n := n) y j

lemma Gk_eq (n : ℕ) (x y : ℝ) : Gk n x y = r n + (Dc n (y - x) + Dc n (x + y)) / 2 := by
  unfold Gk
  rw [Fintype.sum_sum_type]
  simp only [vc, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Dc
  rw [add_comm, ← Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc, two_cos_mul_cos]
  congr 2 <;> ring

lemma frob_eq (n : ℕ) :
    ∑ j, ∑ k, Amat n j k ^ 2 = ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n),
      Gk n (αl n l) (αl n l') * Gk n (βl n l) (βl n l') := by
  have hpt : ∀ j k : Fin (K n) ⊕ Fin (r n), Amat n j k ^ 2 =
      ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n),
        (vc (αl n l) j * vc (αl n l') j) * (vc (βl n l) k * vc (βl n l') k) := by
    intro j k; unfold Amat; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => by ring))
  simp_rw [hpt]
  calc _ = ∑ j : Fin (K n) ⊕ Fin (r n), ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n),
        ∑ k : Fin (K n) ⊕ Fin (r n),
          (vc (αl n l) j * vc (αl n l') j) * (vc (βl n l) k * vc (βl n l') k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
    _ = ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n), ∑ j : Fin (K n) ⊕ Fin (r n),
        ∑ k : Fin (K n) ⊕ Fin (r n),
          (vc (αl n l) j * vc (αl n l') j) * (vc (βl n l) k * vc (βl n l') k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
        unfold Gk; rw [Finset.sum_mul_sum]

lemma Dc_zero (n : ℕ) : Dc n 0 = K n := by simp [Dc]

lemma Dc_neg (n : ℕ) (x : ℝ) : Dc n (-x) = Dc n x := by simp [Dc]

/-- Off-diagonal decay of the cosine sum along the grid. -/
lemma abs_Dc_grid (n : ℕ) (hn : 1 ≤ n) (d : ℕ) (hd : 1 ≤ d) (hdM : d < Mn n) :
    |Dc n (4 * hstep n * d)| ≤ K n / (6 * d) := by
  have hh := hstep_pos n hn
  have hM := Mn_hstep n hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdM' : (d : ℝ) + 1 ≤ Mn n := by exact_mod_cast hdM
  set x := 4 * hstep n * d
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ π / 2 := by simp only [x]; nlinarith
  have hs := Real.mul_le_sin hx0.le hx1
  have hs0 : 0 < Real.sin x := lt_of_lt_of_le (by positivity) hs
  refine (abs_Dc_le n x hs0.ne').trans ?_
  rw [abs_of_pos hs0]
  have hK : (0 : ℝ) < K n := by have : 0 < K n := by unfold K; omega
                                exact_mod_cast this
  have hxK : x = 3 * π * d / K n := by simp only [x]; unfold hstep; field_simp; try ring
  calc 1 / Real.sin x ≤ 1 / (2 / π * x) := by
        apply one_div_le_one_div_of_le (by positivity) hs
    _ = K n / (6 * d) := by rw [hxK]; field_simp; ring

/-- **Frobenius bound** for the quadratic form. -/
lemma frob_le (n : ℕ) (hn : 4 ≤ n) :
    ∑ j, ∑ k, Amat n j k ^ 2 ≤ (Mn n : ℝ) * ((K n : ℝ) + 4) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hh := hstep_pos n hn1
  have hM := Mn_hstep n hn1
  have hK : (0 : ℝ) < K n := by have : 0 < K n := by unfold K; omega
                                exact_mod_cast this
  have hMK : (Mn n : ℝ) * 12 ≤ K n := by
    have : Mn n * 12 ≤ K n := by unfold Mn; omega
    exact_mod_cast this
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  -- a bound on the Gram kernel at grid pairs
  set g : ℕ → ℕ → ℝ := fun l l' => if l = l' then 2 + (K n : ℝ) / 2
    else 2 + (K n : ℝ) / 12 * (((l' : ℝ) - l) ^ 2)⁻¹ * |(l' : ℝ) - l| with hg
  have hGα : ∀ l ∈ Finset.range (Mn n), ∀ l' ∈ Finset.range (Mn n),
      |Gk n (αl n l) (αl n l')| ≤ 2 + |Dc n (4 * hstep n * ((l' : ℝ) - l))| / 2 := by
    intro l hl l' hl'
    rw [Finset.mem_range] at hl hl'
    rw [Gk_eq]
    have hl1 : (l : ℝ) + 1 ≤ Mn n := by exact_mod_cast hl
    have hl1' : (l' : ℝ) + 1 ≤ Mn n := by exact_mod_cast hl'
    have hsum1 : π / 4 ≤ αl n l + αl n l' := by
      unfold αl; have : 0 ≤ 4 * hstep n * l := by positivity
      have : 0 ≤ 4 * hstep n * l' := by positivity
      linarith
    have hsum2 : αl n l + αl n l' ≤ 3 * π / 4 := by unfold αl; nlinarith
    have h2 := abs_Dc_le_sqrt2 n hsum1 hsum2
    have hdiff : αl n l' - αl n l = 4 * hstep n * ((l' : ℝ) - l) := by unfold αl; ring
    rw [hdiff]
    have h3 : (r n : ℝ) ≤ 1 := by exact_mod_cast r_le_one n
    have h4 : (0 : ℝ) ≤ r n := Nat.cast_nonneg _
    rw [abs_le] at h2 ⊢
    constructor
    · have := neg_abs_le (Dc n (4 * hstep n * ((l' : ℝ) - l))); linarith
    · have := le_abs_self (Dc n (4 * hstep n * ((l' : ℝ) - l))); linarith
  have hGβ : ∀ l ∈ Finset.range (Mn n), ∀ l' ∈ Finset.range (Mn n),
      |Gk n (βl n l) (βl n l')| ≤ 2 + |Dc n (4 * hstep n * ((l' : ℝ) - l))| / 2 := by
    intro l hl l' hl'
    rw [Finset.mem_range] at hl hl'
    rw [Gk_eq]
    have hl1 : (l : ℝ) + 1 ≤ Mn n := by exact_mod_cast hl
    have hl1' : (l' : ℝ) + 1 ≤ Mn n := by exact_mod_cast hl'
    have hsum1 : π / 4 ≤ βl n l + βl n l' := by
      unfold βl αl; have : 0 ≤ 4 * hstep n * l := by positivity
      have : 0 ≤ 4 * hstep n * l' := by positivity
      linarith
    have hsum2 : βl n l + βl n l' ≤ 3 * π / 4 := by unfold βl αl; nlinarith
    have h2 := abs_Dc_le_sqrt2 n hsum1 hsum2
    have hdiff : βl n l' - βl n l = 4 * hstep n * ((l' : ℝ) - l) := by unfold βl αl; ring
    rw [hdiff]
    have h3 : (r n : ℝ) ≤ 1 := by exact_mod_cast r_le_one n
    have h4 : (0 : ℝ) ≤ r n := Nat.cast_nonneg _
    rw [abs_le] at h2 ⊢
    constructor
    · have := neg_abs_le (Dc n (4 * hstep n * ((l' : ℝ) - l))); linarith
    · have := le_abs_self (Dc n (4 * hstep n * ((l' : ℝ) - l))); linarith
  -- the scalar bound on |Dc| along the grid
  have hD : ∀ l ∈ Finset.range (Mn n), ∀ l' ∈ Finset.range (Mn n),
      (2 + |Dc n (4 * hstep n * ((l' : ℝ) - l))| / 2) ^ 2 ≤
        (if l = l' then ((K n : ℝ) + 4) ^ 2 / 4 else 8 + (K n : ℝ) ^ 2 / 72 * (((l' : ℝ) - l) ^ 2)⁻¹) := by
    intro l hl l' hl'
    rw [Finset.mem_range] at hl hl'
    split_ifs with he
    · subst he; simp only [sub_self, mul_zero, Dc_zero]
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · -- reduce to a positive distance
      have hb : |Dc n (4 * hstep n * ((l' : ℝ) - l))| ≤ K n / 6 * (|(l' : ℝ) - l|)⁻¹ := by
        rcases lt_or_gt_of_ne he with hlt | hlt
        · have := abs_Dc_grid n hn1 (l' - l) (by omega) (by omega)
          rw [Nat.cast_sub hlt.le] at this
          have hll : (l : ℝ) < l' := by exact_mod_cast hlt
          rw [abs_of_pos (by linarith : (0 : ℝ) < (l' : ℝ) - l)]
          rw [div_eq_mul_inv, mul_inv] at this
          rw [div_eq_mul_inv]
          linarith
        · have := abs_Dc_grid n hn1 (l - l') (by omega) (by omega)
          rw [Nat.cast_sub hlt.le] at this
          rw [show 4 * hstep n * ((l' : ℝ) - l) = -(4 * hstep n * ((l : ℝ) - l')) by ring, Dc_neg]
          have hll : (l' : ℝ) < l := by exact_mod_cast hlt
          rw [abs_of_neg (by linarith : (l' : ℝ) - l < 0), neg_sub]
          rw [div_eq_mul_inv, mul_inv] at this
          rw [div_eq_mul_inv]
          linarith
      have hpos : 0 < |(l' : ℝ) - l| := by
        rw [abs_pos, sub_ne_zero]; exact_mod_cast (Ne.symm he)
      have hsq : (|(l' : ℝ) - l|)⁻¹ ^ 2 = (((l' : ℝ) - l) ^ 2)⁻¹ := by
        rw [inv_pow, sq_abs]
      set u := (|(l' : ℝ) - l|)⁻¹
      have hu : 0 ≤ u := by positivity
      have h0 : 0 ≤ |Dc n (4 * hstep n * ((l' : ℝ) - l))| := abs_nonneg _
      rw [← hsq]
      nlinarith [sq_nonneg (|Dc n (4 * hstep n * ((l' : ℝ) - l))| - 4)]
  rw [frob_eq]
  calc ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n),
        Gk n (αl n l) (αl n l') * Gk n (βl n l) (βl n l')
      ≤ ∑ l ∈ Finset.range (Mn n), ∑ l' ∈ Finset.range (Mn n),
        (if l = l' then ((K n : ℝ) + 4) ^ 2 / 4 else 8 + (K n : ℝ) ^ 2 / 72 * (((l' : ℝ) - l) ^ 2)⁻¹) := by
        refine Finset.sum_le_sum (fun l hl => Finset.sum_le_sum (fun l' hl' => ?_))
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul]
        refine le_trans ?_ (hD l hl l' hl')
        rw [sq]
        exact mul_le_mul (hGα l hl l' hl') (hGβ l hl l' hl') (abs_nonneg _) (by positivity)
    _ ≤ ∑ l ∈ Finset.range (Mn n), (((K n : ℝ) + 4) ^ 2 / 4 + (8 * Mn n + (K n : ℝ) ^ 2 / 72 * 4)) := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        rw [Finset.sum_ite, Finset.filter_eq (s := Finset.range (Mn n)), if_pos hl]
        simp only [Finset.sum_singleton]
        gcongr
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        have hc : (((Finset.range (Mn n)).filter fun x => ¬ l = x).card : ℝ) ≤ Mn n := by
          have := Finset.card_filter_le (Finset.range (Mn n)) (fun x => ¬ l = x)
          rw [Finset.card_range] at this; exact_mod_cast this
        have hs := sum_inv_sq_other (Mn n) l
        have hfe : (Finset.range (Mn n)).filter (fun x => ¬ l = x)
            = (Finset.range (Mn n)).filter (· ≠ l) := by
          ext x; simp [eq_comm]
        rw [hfe] at hc ⊢
        have : (0 : ℝ) ≤ (K n : ℝ) ^ 2 / 72 := by positivity
        nlinarith
    _ = (Mn n : ℝ) * (((K n : ℝ) + 4) ^ 2 / 4 + (8 * Mn n + (K n : ℝ) ^ 2 / 72 * 4)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (Mn n : ℝ) * ((K n : ℝ) + 4) ^ 2 := by
        gcongr
        nlinarith


lemma RRa_continuous (a : Al n) : Continuous (fun θ => RRa a θ) := by
  unfold RRa; fun_prop

open scoped Classical in
/-- Indices of test intervals with a sign change. -/
def negSet (n : ℕ) (a : Al n) : Finset ℕ :=
  (Finset.range (Mn n)).filter (fun l => RRa a (αl n l) * RRa a (βl n l) < 0)

lemma exists_zero_of_neg (a : Al n) (hn : 1 ≤ n) (l : ℕ) (hl : l ∈ negSet n a) :
    ∃ ξ ∈ Set.Ioo (αl n l) (βl n l), RRa a ξ = 0 := by
  classical
  simp only [negSet, Finset.mem_filter] at hl
  have hab : αl n l ≤ βl n l := by unfold βl; linarith [hstep_pos n hn]
  have hc := (RRa_continuous a).continuousOn (s := Set.Icc (αl n l) (βl n l))
  rcases mul_neg_iff.mp hl.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨ξ, hξ, hz⟩ := intermediate_value_Ioo' hab hc ⟨h2, h1⟩
    exact ⟨ξ, hξ, hz⟩
  · obtain ⟨ξ, hξ, hz⟩ := intermediate_value_Ioo hab hc ⟨h1, h2⟩
    exact ⟨ξ, hξ, hz⟩

/-- A set of sign changes gives a structured set of zeros. -/
lemma structured_of_neg (a : Al n) (hn : 4 ≤ n) (c₀ : ℝ) (hc0 : 0 < c₀) (hc1 : c₀ ≤ 1)
    (hcount : c₀ * n ≤ (negSet n a).card) :
    ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧ ∀ ξ ∈ Ξ, RRa a ξ = 0 := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hh := hstep_pos n hn1
  have hM := Mn_hstep n hn1
  have hz := exists_zero_of_neg a hn1
  set ξf : ℕ → ℝ := fun l => if h : l ∈ negSet n a then Classical.choose (hz l h) else 0
  have hξf : ∀ l ∈ negSet n a, ξf l ∈ Set.Ioo (αl n l) (βl n l) ∧ RRa a (ξf l) = 0 := by
    intro l hl
    simp only [ξf, dif_pos hl]
    exact Classical.choose_spec (hz l hl)
  have hmemM : ∀ l ∈ negSet n a, l < Mn n := by
    intro l hl; simp only [negSet, Finset.mem_filter, Finset.mem_range] at hl; exact hl.1
  -- separation of points from different intervals
  have hsep : ∀ l ∈ negSet n a, ∀ l' ∈ negSet n a, l < l' → 3 * hstep n ≤ ξf l' - ξf l := by
    intro l hl l' hl' hlt
    have h1 := (hξf l hl).1
    have h2 := (hξf l' hl').1
    have : (l : ℝ) + 1 ≤ l' := by exact_mod_cast hlt
    simp only [Set.mem_Ioo, βl, αl] at h1 h2
    nlinarith
  have hinj : Set.InjOn ξf (negSet n a : Set ℕ) := by
    intro l hl l' hl' he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsep l hl l' hl' h; rw [he] at this; linarith
    · have := hsep l' hl' l hl h; rw [he] at this; linarith
  refine ⟨(negSet n a).image ξf, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro ξ hξ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hξ
    obtain ⟨l, hl, rfl⟩ := hξ
    have h1 := (hξf l hl).1
    have hlM : (l : ℝ) + 1 ≤ Mn n := by exact_mod_cast hmemM l hl
    simp only [Set.mem_Ioo, βl, αl] at h1
    have : 0 ≤ 4 * hstep n * (l : ℝ) := by positivity
    constructor
    · linarith
    · nlinarith
  · rw [Finset.card_image_of_injOn hinj]; exact hcount
  · intro ξ hξ ξ' hξ' hne
    simp only [Finset.mem_image] at hξ hξ'
    obtain ⟨l, hl, rfl⟩ := hξ
    obtain ⟨l', hl', rfl⟩ := hξ'
    have hll : l ≠ l' := fun e => hne (by rw [e])
    have hK : (K n : ℝ) ≤ n := by
      have : K n ≤ n := by unfold K; omega
      exact_mod_cast this
    have hK0 : (0 : ℝ) < K n := by have : 0 < K n := by unfold K; omega
                                   exact_mod_cast this
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h3 : c₀ / n ≤ 3 * hstep n := by
      have hh' : 3 * π / (4 * n) ≤ hstep n := by
        unfold hstep
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      rw [div_le_iff₀ hn0]
      have e : 3 * π / (4 * n) * n = 3 * π / 4 := by field_simp
      have : 3 * π / (4 * n) * n ≤ hstep n * n := by gcongr
      nlinarith [Real.pi_gt_three]
    rcases lt_or_gt_of_ne hll with h | h
    · have := hsep l hl l' hl' h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have := hsep l' hl' l hl h
      rw [abs_of_nonneg (by linarith)]; linarith
  · intro ξ hξ
    simp only [Finset.mem_image] at hξ
    obtain ⟨l, hl, rfl⟩ := hξ
    exact (hξf l hl).2


/-- The test products. -/
def Xl (n : ℕ) (a : Al n) (l : ℕ) : ℝ := RRa a (αl n l) * RRa a (βl n l)

lemma negSet_card_ge (a : Al n) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 < B)
    (hW : ∑ l ∈ Finset.range (Mn n), Xl n a l ≤ -T)
    (hQ : ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2 ≤ B) :
    T ^ 2 / B ≤ (negSet n a).card := by
  classical
  set neg := negSet n a
  have hsub : neg ⊆ Finset.range (Mn n) := Finset.filter_subset _ _
  have hrest : 0 ≤ ∑ l ∈ Finset.range (Mn n) \ neg, Xl n a l := by
    refine Finset.sum_nonneg (fun l hl => ?_)
    simp only [Finset.mem_sdiff, neg, negSet, Finset.mem_filter, not_and, not_lt] at hl
    exact hl.2 hl.1
  have hsplit := Finset.sum_sdiff hsub (f := fun l => Xl n a l)
  have hnegsum : T ≤ ∑ l ∈ neg, (-Xl n a l) := by
    rw [Finset.sum_neg_distrib]; linarith
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq neg (fun _ => (1 : ℝ)) (fun l => -Xl n a l)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, neg_sq] at hCS
  have hQneg : ∑ l ∈ neg, Xl n a l ^ 2 ≤ B :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans hQ
  have hT2 : T ^ 2 ≤ (∑ l ∈ neg, (-Xl n a l)) ^ 2 := pow_le_pow_left₀ hT hnegsum 2
  rw [div_le_iff₀ hB]
  have hc0 : (0 : ℝ) ≤ neg.card := Nat.cast_nonneg _
  nlinarith

lemma W_eq' (a : Al n) : ∑ l ∈ Finset.range (Mn n), Xl n a l = Qf Zc (Amat n) a := W_eq a

lemma vsq_le (n : ℕ) (x : ℝ) : ∑ j : Fin (K n) ⊕ Fin (r n), vc (n := n) x j ^ 2 ≤ (K n : ℝ) + 1 := by
  rw [Fintype.sum_sum_type]
  simp only [vc, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  have h1 : ∑ p : Fin (K n), Real.cos (kk n p * x) ^ 2 ≤ (K n : ℝ) := by
    calc _ ≤ ∑ _p : Fin (K n), (1 : ℝ) := Finset.sum_le_sum (fun p _ => Real.cos_sq_le_one _)
      _ = (K n : ℝ) := by simp
  have h2 : (r n : ℝ) ≤ 1 := by exact_mod_cast r_le_one n
  linarith

lemma sumX_sq_le (n : ℕ) (l : ℕ) :
    ∑ a : Al n, Xl n a l ^ 2 ≤ 48 * (Fintype.card (Al n) : ℝ) * ((K n : ℝ) + 1) * ((K n : ℝ) + 1) := by
  have h := sum_sq_sq_le (Zc (n := n)) flipEquiv Zc_flip (fun j k ω h => Zc_fix j k ω h)
    Zc_bd (vc (n := n) (αl n l)) (vc (n := n) (βl n l))
  have e : ∑ a : Al n, Xl n a l ^ 2 = ∑ a : Al n,
      (∑ j : Fin (K n) ⊕ Fin (r n), vc (αl n l) j * Zc j a) ^ 2 *
      (∑ k : Fin (K n) ⊕ Fin (r n), vc (βl n l) k * Zc k a) ^ 2 := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Xl, RRa_eq, RRa_eq]; ring
  rw [e]
  refine h.trans ?_
  have h1 := vsq_le n (αl n l)
  have h2 := vsq_le n (βl n l)
  have h3 : 0 ≤ ∑ j : Fin (K n) ⊕ Fin (r n), vc (n := n) (βl n l) j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h4 : 0 ≤ 48 * (Fintype.card (Al n) : ℝ) := by positivity
  have h5 := mul_le_mul_of_nonneg_left h1 h4
  have h6 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 48 * (Fintype.card (Al n) : ℝ) * ((K n : ℝ) + 1))
  nlinarith

lemma sumQ_le (n : ℕ) :
    ∑ a : Al n, ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2
      ≤ 48 * (Fintype.card (Al n) : ℝ) * (Mn n : ℝ) * ((K n : ℝ) + 1) ^ 2 := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _l ∈ Finset.range (Mn n),
        48 * (Fintype.card (Al n) : ℝ) * ((K n : ℝ) + 1) * ((K n : ℝ) + 1) :=
        Finset.sum_le_sum (fun l _ => sumX_sq_le n l)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

open scoped Classical in
/-- **Interface 2 holds.** -/
theorem hZ_holds : HZ := by
  intro η hη
  refine ⟨min (η / 10 ^ 7) 1, by positivity, ?_⟩
  set c₀ := min (η / 10 ^ 7) 1
  filter_upwards [Filter.eventually_ge_atTop (10 ^ 7 * (⌈1 / η⌉₊ + 1))] with n hn
  -- sizes
  have hnη : (10 : ℝ) ^ 7 * (1 / η) ≤ n := by
    have h1 : (1 / η) ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((10 ^ 7 * (⌈1 / η⌉₊ + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; nlinarith
  have hn7 : 10 ^ 7 ≤ n := le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) hn
  have hn7' : 10000000 ≤ n := by norm_num at hn7; exact hn7
  have hn4 : 4 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  set N := (Fintype.card (Al n) : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef, card_Al]; positivity
  set M := (Mn n : ℝ) with hMdef
  set Kr := (K n : ℝ) with hKdef
  have hK2 : (n : ℝ) ≤ 2 * Kr + 1 := by
    have : n ≤ 2 * K n + 1 := by unfold K; omega
    rw [hKdef]; exact_mod_cast this
  have hM12 : Kr ≤ 12 * M + 12 := by
    have : K n ≤ 12 * Mn n + 12 := by unfold Mn; omega
    rw [hKdef, hMdef]; exact_mod_cast this
  have hnr : (10 : ℝ) ^ 7 ≤ n := by exact_mod_cast hn7
  have hKbig : 1000 ≤ Kr := by linarith
  have hMn : (n : ℝ) / 30 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hMη : 300000 / η ≤ M := by
    have : (10 : ℝ) ^ 7 * (1 / η) / 30 ≤ M := by linarith
    have e : (10 : ℝ) ^ 7 * (1 / η) / 30 = 10 ^ 7 / 30 / η := by field_simp
    rw [e] at this
    calc 300000 / η ≤ 10 ^ 7 / 30 / η := by gcongr; norm_num
      _ ≤ M := this
  -- the mean
  set m := ∑ j, Amat n j j * sv j with hm
  have hmle : m ≤ M * (4 - 2 * Kr / (3 * π)) := mean_W_le n (by omega)
  set T := M * Kr / 16 with hT
  have hT0 : 0 < T := by positivity
  have hm2 : m ≤ -2 * T := by
    have hpi : 2 * Kr / (3 * π) ≥ 2 * Kr / 10 := by
      gcongr; linarith [Real.pi_lt_d2]
    have : M * (4 - 2 * Kr / (3 * π)) ≤ M * (4 - 2 * Kr / 10) := by
      gcongr
    have hMK : 0 ≤ M * (Kr - 1000) := mul_nonneg hMpos.le (by linarith)
    rw [hT]; nlinarith
  have hsumW : ∑ a : Al n, Qf Zc (Amat n) a = N * m := by
    rw [sum_Qf Zc flipEquiv Zc_flip (fun j k ω h => Zc_fix j k ω h)]
    simp_rw [sum_Zc_sq]; rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have hvar := var_Qf Zc flipEquiv Zc_flip (fun j k ω h => Zc_fix j k ω h) Zc_bd Zc_ind (Amat n)
  have hfrob := frob_le n hn4
  rw [← hNdef, hsumW] at hvar
  -- Chebyshev for bad1
  have hdev : ∑ a : Al n, (Qf Zc (Amat n) a - m) ^ 2 ≤ 32 * N * (M * (Kr + 4) ^ 2) := by
    have e : ∑ a : Al n, (Qf Zc (Amat n) a - m) ^ 2
        = ∑ a : Al n, Qf Zc (Amat n) a ^ 2 - (N * m) ^ 2 / N := by
      have : ∑ a : Al n, (Qf Zc (Amat n) a - m) ^ 2 = ∑ a : Al n, Qf Zc (Amat n) a ^ 2
          - 2 * m * ∑ a : Al n, Qf Zc (Amat n) a + N * m ^ 2 := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef]
        congr 1; congr 1; refine Finset.sum_congr rfl (fun a _ => by ring)
      rw [this, hsumW]; field_simp; ring
    rw [e]
    calc _ ≤ 32 * N * ∑ j, ∑ k, Amat n j k ^ 2 := hvar
      _ ≤ 32 * N * (M * (Kr + 4) ^ 2) := by gcongr
  have hbad1 : (∑ a : Al n, if -T < Qf Zc (Amat n) a then (1 : ℝ) else 0) ≤ η / 2 * N := by
    have hpt : ∀ a : Al n, (if -T < Qf Zc (Amat n) a then (1 : ℝ) else 0)
        ≤ (Qf Zc (Amat n) a - m) ^ 2 / T ^ 2 := by
      intro a
      split_ifs with h
      · rw [le_div_iff₀ (by positivity), one_mul]
        have : T ≤ Qf Zc (Amat n) a - m := by linarith
        nlinarith
      · positivity
    calc _ ≤ ∑ a : Al n, (Qf Zc (Amat n) a - m) ^ 2 / T ^ 2 := Finset.sum_le_sum (fun a _ => hpt a)
      _ = (∑ a : Al n, (Qf Zc (Amat n) a - m) ^ 2) / T ^ 2 := by rw [Finset.sum_div]
      _ ≤ 32 * N * (M * (Kr + 4) ^ 2) / T ^ 2 := by gcongr
      _ ≤ η / 2 * N := by
          rw [div_le_iff₀ (by positivity), hT]
          have hK4 : (Kr + 4) ^ 2 ≤ 2 * Kr ^ 2 := by nlinarith
          have : 32 * N * (M * (Kr + 4) ^ 2) ≤ 64 * N * M * Kr ^ 2 := by
            have := mul_le_mul_of_nonneg_left hK4 (by positivity : (0 : ℝ) ≤ 32 * N * M)
            linarith
          have hηM : 300000 ≤ η * M := by rw [div_le_iff₀ hη] at hMη; linarith
          have : 64 * N * M * Kr ^ 2 ≤ η / 2 * N * (M * Kr / 16) ^ 2 := by
            have e : η / 2 * N * (M * Kr / 16) ^ 2 = (η * M) * (N * M * Kr ^ 2) / 512 := by ring
            rw [e]
            have : 0 ≤ N * M * Kr ^ 2 := by positivity
            nlinarith
          linarith
  -- Markov for bad2
  set B := 96 * M * (Kr + 1) ^ 2 / η with hB
  have hB0 : 0 < B := by positivity
  have hQsum : ∑ a : Al n, ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2 ≤ 48 * N * M * (Kr + 1) ^ 2 :=
    sumQ_le n
  have hbad2 : (∑ a : Al n, if B < ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2 then (1 : ℝ) else 0)
      ≤ η / 2 * N := by
    have hpt : ∀ a : Al n, (if B < ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2 then (1 : ℝ) else 0)
        ≤ (∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2) / B := by
      intro a
      split_ifs with h
      · rw [le_div_iff₀ hB0, one_mul]; exact h.le
      · exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hB0.le
    calc _ ≤ ∑ a : Al n, (∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2) / B :=
          Finset.sum_le_sum (fun a _ => hpt a)
      _ = (∑ a : Al n, ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2) / B := by rw [Finset.sum_div]
      _ ≤ 48 * N * M * (Kr + 1) ^ 2 / B := by gcongr
      _ = η / 2 * N := by rw [hB]; field_simp; ring
  -- good points have a structured zero set
  have hgood : ∀ a : Al n, ¬ (-T < Qf Zc (Amat n) a) →
      ¬ (B < ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2) →
      ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧ ∀ ξ ∈ Ξ, RRa a ξ = 0 := by
    intro a h1 h2
    push Not at h1 h2
    rw [← W_eq'] at h1
    have hc := negSet_card_ge a T B hT0.le hB0 h1 h2
    apply structured_of_neg a hn4 c₀ (by positivity) (min_le_right _ _)
    refine le_trans ?_ hc
    -- c₀ n ≤ T² / B
    rw [le_div_iff₀ hB0, hT, hB]
    have hK1 : (Kr + 1) ^ 2 ≤ 2 * Kr ^ 2 := by nlinarith only [hKbig]
    have hc0 : c₀ ≤ η / 10 ^ 7 := min_le_left _ _
    have hnM : (n : ℝ) ≤ 30 * M := by linarith only [hMn]
    have e : (M * Kr / 16) ^ 2 = M * M * Kr ^ 2 / 256 := by ring
    rw [e]
    have hc0n : c₀ * n ≤ η / 10 ^ 7 * (30 * M) := by
      have : 0 ≤ c₀ := by positivity
      calc c₀ * n ≤ c₀ * (30 * M) := by gcongr
        _ ≤ η / 10 ^ 7 * (30 * M) := by gcongr
    calc c₀ * n * (96 * M * (Kr + 1) ^ 2 / η)
        ≤ η / 10 ^ 7 * (30 * M) * (96 * M * (2 * Kr ^ 2) / η) := by
          gcongr
      _ = M * M * Kr ^ 2 * (30 * 96 * 2 / 10 ^ 7) := by field_simp
      _ ≤ M * M * Kr ^ 2 / 256 := by
          have h0 : 0 ≤ M * M * Kr ^ 2 := by positivity
          nlinarith only [h0]
  -- count
  rw [card_filter_real]
  have hpt : ∀ a : Al n, (1 : ℝ) ≤ (if ∃ Ξ : Finset ℝ, Structured c₀ n Ξ ∧ ∀ ξ ∈ Ξ, RRa a ξ = 0
      then 1 else 0) + (if -T < Qf Zc (Amat n) a then (1 : ℝ) else 0) +
      (if B < ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2 then (1 : ℝ) else 0) := by
    intro a
    by_cases h1 : -T < Qf Zc (Amat n) a
    · rw [if_pos h1]; split_ifs <;> norm_num
    · by_cases h2 : B < ∑ l ∈ Finset.range (Mn n), Xl n a l ^ 2
      · rw [if_pos h2]; split_ifs <;> norm_num
      · rw [if_pos (hgood a h1 h2)]; split_ifs <;> norm_num
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Al n))) => hpt a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← hNdef] at hs
  linarith only [hs, hbad1, hbad2]


/-! ## Interface 3 (`HH`): toward the hitting estimate -/

open scoped Classical in
/-- **Paley–Zygmund by counting.** -/
lemma pz_count {β : Type*} [Fintype β] (N : β → ℝ) (hN : ∀ b, 0 ≤ N b) :
    (∑ b, N b) ^ 2 ≤ ((univ.filter fun b => 0 < N b).card : ℝ) * ∑ b, N b ^ 2 := by
  set S := univ.filter fun b => 0 < N b
  have h1 : ∑ b, N b = ∑ b ∈ S, N b := by
    rw [Finset.sum_filter_of_ne]; intro b _ hb; exact lt_of_le_of_ne (hN b) (Ne.symm hb)
  have h2 : ∑ b ∈ S, N b ^ 2 ≤ ∑ b, N b ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) N
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  rw [h1]
  have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  nlinarith


lemma fourier_integrable (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable

lemma integrable_exp_mul_fourier (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ) := by
  refine (fourier_integrable ψ).bdd_mul (c := 1) (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **Two-point smoothed identity.** -/
theorem avg_schwartz2 {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : SchwartzMap ℝ ℂ)
    (c d : ι → ℝ) :
    (∑ b : ι → ℤˣ, ψ (∑ i, ((b i : ℤ) : ℝ) * c i) * ψ (∑ i, ((b i : ℤ) : ℝ) * d i))
        / 2 ^ Fintype.card ι
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ : ℝ → ℂ) u * 𝓕 (ψ : ℝ → ℂ) v *
          ∏ i, (Real.cos (2 * π * (u * c i + v * d i)) : ℂ) := by
  set F := 𝓕 (ψ : ℝ → ℂ)
  -- pointwise product of two inversion integrals
  have hprod : ∀ x y : ℝ, ψ x * ψ y = ∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F u * F v) := by
    intro x y
    rw [schwartz_inv ψ x, schwartz_inv ψ y, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner : ∀ (x y u : ℝ), Integrable (fun v : ℝ =>
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F u * F v)) := by
    intro x y u
    have := (integrable_exp_mul_fourier ψ y).const_mul
      (Complex.exp (↑(2 * π * u * x) * Complex.I) * F u)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner_eval : ∀ (x y u : ℝ), ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F u * F v) = Complex.exp (↑(2 * π * u * x) * Complex.I) * F u * ψ y := by
    intro x y u
    rw [schwartz_inv ψ y, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have houter : ∀ x y : ℝ, Integrable (fun u : ℝ => ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F u * F v)) := by
    intro x y
    simp_rw [hinner_eval x y]
    exact (integrable_exp_mul_fourier ψ x).mul_const _
  simp_rw [hprod]
  rw [← integral_finsetSum _ (fun b _ => houter _ _)]
  rw [div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [← integral_finsetSum _ (fun b _ => hinner _ _ u)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  -- the character sum
  have hc : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * u * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I) *
      Complex.exp (↑(2 * π * v * ∑ i, ((b i : ℤ) : ℝ) * d i) * Complex.I)
      = Complex.exp (↑(2 * π * 1 * ∑ i, ((b i : ℤ) : ℝ) * (u * c i + v * d i)) * Complex.I) := by
    intro b
    rw [← Complex.exp_add]; congr 1
    push_cast
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [← add_mul]; congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [← mul_assoc, hc]
  have hs := sum_signs_exp (fun i => u * c i + v * d i) 1
  simp only [mul_one] at hs ⊢
  rw [← Finset.sum_mul, ← Finset.sum_mul, hs, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  field_simp


/-! ### Cosine products -/

lemma abs_cos_le_exp (x : ℝ) : |Real.cos x| ≤ Real.exp (-(Real.sin x ^ 2) / 2) := by
  have h1 : Real.cos x ^ 2 ≤ Real.exp (-(Real.sin x ^ 2)) := by
    have := Real.add_one_le_exp (-(Real.sin x ^ 2))
    have := Real.sin_sq_add_cos_sq x
    linarith
  have h2 : Real.exp (-(Real.sin x ^ 2)) = Real.exp (-(Real.sin x ^ 2) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2] at h1
  have hE := Real.exp_pos (-(Real.sin x ^ 2) / 2)
  have h3 : |Real.cos x| ^ 2 ≤ Real.exp (-(Real.sin x ^ 2) / 2) ^ 2 := by rw [sq_abs]; exact h1
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hE.le (by norm_num)).mp h3

lemma cos_le_exp_core {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.cos x ≤ Real.exp (-(x ^ 2) / 2 + x ^ 4) := by
  have hb := Real.cos_bound (x := x) (by linarith)
  rw [abs_le] at hb
  have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [h4] at hb
  have := Real.add_one_le_exp (-(x ^ 2) / 2 + x ^ 4)
  have : 0 ≤ x ^ 4 := by positivity
  linarith

lemma exp_le_cos_core {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.exp (-(x ^ 2) / 2 - 2 * x ^ 4) ≤ Real.cos x := by
  have hb := Real.cos_bound (x := x) (by linarith)
  rw [abs_le] at hb
  have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  rw [h4] at hb
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have := sq_abs x; nlinarith [abs_nonneg x]
  set z := -(x ^ 2) / 2 - 2 * x ^ 4 with hzdef
  have hx40 : 0 ≤ x ^ 4 := by positivity
  have hx41 : x ^ 4 ≤ 1 / 16 := by nlinarith
  have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
  have hz : |z| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have he := Real.abs_exp_sub_one_sub_id_le hz
  rw [abs_le] at he
  have : z ^ 2 ≤ x ^ 4 / 4 + 2 * x ^ 6 + 4 * x ^ 8 := by simp only [z]; nlinarith
  have hx6 : x ^ 6 ≤ x ^ 4 / 4 := by
    have : x ^ 6 = x ^ 4 * x ^ 2 := by ring
    rw [this]; have : 0 ≤ x ^ 4 := by positivity
    nlinarith
  have hx8 : x ^ 8 ≤ x ^ 4 / 16 := by
    have : x ^ 8 = x ^ 4 * (x ^ 2) ^ 2 := by ring
    rw [this]; have : 0 ≤ x ^ 4 := by positivity
    have : (x ^ 2) ^ 2 ≤ 1 / 16 := by nlinarith
    nlinarith
  linarith [he.2, hb.1]


/-! ### `HH` from four sub-interfaces -/

/-- The weights of `IIt`. -/
def wv (t : Fin (K n) → Bool) (ξ : ℝ) (p : Fin (K n)) : ℝ :=
  if t p then 0 else 2 * Real.sin (kk n p * ξ)

lemma IIt_eq (t : Fin (K n) → Bool) (b : Fin (K n) → ℤˣ) (ξ : ℝ) :
    IIt t b ξ = ∑ p, (((b p : ℤˣ) : ℤ) : ℝ) * wv t ξ p := by
  unfold IIt wv
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> ring

/-- The variance of `IIt`. -/
def Vv (t : Fin (K n) → Bool) (ξ : ℝ) : ℝ := ∑ p, wv t ξ p ^ 2

/-- Smoothed single-point probability. -/
def E1 (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ : ℝ) : ℝ :=
  (∑ b : Fin (K n) → ℤˣ, bumpR δ hδ (IIt t b ξ)) / 2 ^ K n

/-- Smoothed two-point probability. -/
def E2 (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ ξ' : ℝ) : ℝ :=
  (∑ b : Fin (K n) → ℤˣ, bumpR δ hδ (IIt t b ξ) * bumpR δ hδ (IIt t b ξ')) / 2 ^ K n

/-- The mass of the bump. -/
def Ad (δ : ℝ) (hδ : 0 < δ) : ℝ := ∫ x, bumpR δ hδ x

lemma Ad_pos (δ : ℝ) (hδ : 0 < δ) : 0 < Ad δ hδ := (bumpR δ hδ).integral_pos

/-- Resolution of the equidistribution. -/
def Dn (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 20 : ℝ)⌋₊

/-- Non-resonance threshold. -/
def εn (n : ℕ) : ℝ := (n : ℝ) ^ (-(3 / 4) : ℝ)

/-- Single-point non-resonance. -/
def NR1 (n : ℕ) (ξ : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ Dn n → εn n ≤ |Real.sin (m * ξ)|

/-- Two-point non-resonance and separation. -/
def NR2 (n : ℕ) (ξ ξ' : ℝ) : Prop :=
  (n : ℝ) ^ (-(3 / 5) : ℝ) ≤ |ξ - ξ'| ∧
    ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ Dn n → |m₂| ≤ Dn n →
      εn n ≤ |Real.sin (m₁ * ξ + m₂ * ξ')|

/-- S1: single-point local limit (smoothed). -/
def S1 : Prop :=
  ∀ δ (hδ : 0 < δ), ∀ ε₀ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∀ t : Fin (K n) → Bool, Typical n t → ∀ ξ ∈ Set.Icc (π / 8) (3 * π / 8), NR1 n ξ →
      |E1 δ hδ t ξ - Ad δ hδ / Real.sqrt (2 * π * Vv t ξ)|
        ≤ ε₀ * (Ad δ hδ / Real.sqrt (2 * π * Vv t ξ))

/-- S2: two-point upper bound (smoothed). -/
def S2 : Prop :=
  ∀ δ (hδ : 0 < δ), ∀ ε₀ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∀ t : Fin (K n) → Bool, Typical n t →
      ∀ ξ ∈ Set.Icc (π / 8) (3 * π / 8), ∀ ξ' ∈ Set.Icc (π / 8) (3 * π / 8),
        NR1 n ξ → NR1 n ξ' → NR2 n ξ ξ' →
          E2 δ hδ t ξ ξ' ≤ (1 + ε₀) * ((Ad δ hδ / Real.sqrt (2 * π * Vv t ξ)) *
            (Ad δ hδ / Real.sqrt (2 * π * Vv t ξ')))

open scoped Classical in
/-- S3: few resonant points and few bad partners. -/
def S3 : Prop :=
  ∀ c₀ > (0 : ℝ), ∀ ε₀ > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ Ξ : Finset ℝ, Structured c₀ n Ξ →
    (((Ξ.filter fun ξ => ¬ NR1 n ξ).card : ℝ) ≤ ε₀ * Ξ.card) ∧
    ∀ ξ ∈ Ξ, NR1 n ξ →
      (((Ξ.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ').card : ℝ) ≤ (n : ℝ) ^ (9 / 20 : ℝ))

/-- S4: the variance is close to `K`. -/
def S4 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ t : Fin (K n) → Bool, Typical n t →
    ∀ ξ ∈ Set.Icc (π / 8) (3 * π / 8), |Vv t ξ - K n| ≤ 5 * (n : ℝ) ^ (3 / 5 : ℝ)


lemma pz_ratio {s Q R ε₀ η : ℝ} (hs : 0 < s) (hη : η ≤ 1 / 2) (hη0 : 0 ≤ η)
    (hQ : Q ≤ s + R + (1 + ε₀) * s ^ 2 / (1 - ε₀) ^ 2) (h1 : 1 / s ≤ η / 8) (h2 : R / s ^ 2 ≤ η / 8)
    (h3 : (1 + ε₀) / (1 - ε₀) ^ 2 ≤ 1 + η / 8) (hε : ε₀ < 1) :
    (1 - η) * Q ≤ s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hQs : Q ≤ s ^ 2 * (1 + 3 * η / 8) := by
    have e1 : s = s ^ 2 * (1 / s) := by field_simp
    have e2 : R = s ^ 2 * (R / s ^ 2) := by field_simp
    have h1e : 0 < 1 - ε₀ := by linarith
    have h1e2 : (1 - ε₀) ^ 2 ≠ 0 := by positivity
    have e3 : (1 + ε₀) * s ^ 2 / (1 - ε₀) ^ 2 = s ^ 2 * ((1 + ε₀) / (1 - ε₀) ^ 2) := by
      field_simp
    have k1 := mul_le_mul_of_nonneg_left h1 hs2.le
    have k2 := mul_le_mul_of_nonneg_left h2 hs2.le
    have k3 := mul_le_mul_of_nonneg_left h3 hs2.le
    linarith
  have : (1 - η) * (1 + 3 * η / 8) ≤ 1 := by nlinarith
  have h1η : 0 ≤ 1 - η := by linarith
  calc (1 - η) * Q ≤ (1 - η) * (s ^ 2 * (1 + 3 * η / 8)) := mul_le_mul_of_nonneg_left hQs h1η
    _ = s ^ 2 * ((1 - η) * (1 + 3 * η / 8)) := by ring
    _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left this hs2.le
    _ = s ^ 2 := mul_one _


lemma E2_le_E1 (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ ξ' : ℝ) :
    E2 δ hδ t ξ ξ' ≤ E1 δ hδ t ξ := by
  unfold E2 E1
  gcongr with b
  have h1 := bumpR_nonneg δ hδ (IIt t b ξ)
  have h2 := bumpR_le_one δ hδ (IIt t b ξ')
  nlinarith

lemma E1_nonneg (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ : ℝ) : 0 ≤ E1 δ hδ t ξ := by
  unfold E1
  exact div_nonneg (Finset.sum_nonneg (fun b _ => bumpR_nonneg δ hδ _)) (by positivity)

open scoped Classical in
/-- **The second-moment comparison behind `HH`**, for one `n`. -/
lemma hh_core (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (Ξ : Finset ℝ) (ε₀ P : ℝ)
    (hε0 : 0 ≤ ε₀) (hε1 : ε₀ < 1) (hP : 0 ≤ P) (a : ℝ → ℝ) (ha : ∀ ξ ∈ Ξ, 0 ≤ a ξ)
    (hE1 : ∀ ξ ∈ Ξ, (1 - ε₀) * a ξ ≤ E1 δ hδ t ξ)
    (hE2 : ∀ ξ ∈ Ξ, ∀ ξ' ∈ Ξ, ξ' ≠ ξ → NR2 n ξ ξ' → E2 δ hδ t ξ ξ' ≤ (1 + ε₀) * (a ξ * a ξ'))
    (hbad : ∀ ξ ∈ Ξ, (((Ξ.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ').card : ℝ) ≤ P)) :
    (∑ b : Fin (K n) → ℤˣ, ∑ ξ ∈ Ξ, bumpR δ hδ (IIt t b ξ)) = 2 ^ K n * ∑ ξ ∈ Ξ, E1 δ hδ t ξ ∧
    (∑ b : Fin (K n) → ℤˣ, (∑ ξ ∈ Ξ, bumpR δ hδ (IIt t b ξ)) ^ 2)
      ≤ 2 ^ K n * ((∑ ξ ∈ Ξ, E1 δ hδ t ξ) + P * (∑ ξ ∈ Ξ, E1 δ hδ t ξ) +
          (1 + ε₀) * (∑ ξ ∈ Ξ, E1 δ hδ t ξ) ^ 2 / (1 - ε₀) ^ 2) := by
  have h2K : (0 : ℝ) < 2 ^ K n := by positivity
  set S := ∑ ξ ∈ Ξ, E1 δ hδ t ξ with hS
  constructor
  · rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    unfold E1; field_simp
  -- second moment
  have hsq : (∑ b : Fin (K n) → ℤˣ, (∑ ξ ∈ Ξ, bumpR δ hδ (IIt t b ξ)) ^ 2)
      = 2 ^ K n * ∑ ξ ∈ Ξ, ∑ ξ' ∈ Ξ, E2 δ hδ t ξ ξ' := by
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ' _ => ?_)
    unfold E2; field_simp
  rw [hsq]
  refine mul_le_mul_of_nonneg_left ?_ h2K.le
  -- bound each row
  have hrow : ∀ ξ ∈ Ξ, ∑ ξ' ∈ Ξ, E2 δ hδ t ξ ξ'
      ≤ E1 δ hδ t ξ + P * E1 δ hδ t ξ + (1 + ε₀) * a ξ * ∑ ξ' ∈ Ξ, a ξ' := by
    intro ξ hξ
    have hsplit : ∑ ξ' ∈ Ξ, E2 δ hδ t ξ ξ'
        = E2 δ hδ t ξ ξ + ∑ ξ' ∈ Ξ.erase ξ, E2 δ hδ t ξ ξ' := by
      rw [← Finset.add_sum_erase _ _ hξ]
    rw [hsplit]
    have hdiag := E2_le_E1 δ hδ t ξ ξ
    have hoff : ∑ ξ' ∈ Ξ.erase ξ, E2 δ hδ t ξ ξ'
        ≤ ∑ ξ' ∈ Ξ.erase ξ, ((if NR2 n ξ ξ' then 0 else E1 δ hδ t ξ) +
            (1 + ε₀) * (a ξ * a ξ')) := by
      refine Finset.sum_le_sum (fun ξ' hξ' => ?_)
      have hne := Finset.ne_of_mem_erase hξ'
      have hmem := Finset.mem_of_mem_erase hξ'
      have hpos : 0 ≤ (1 + ε₀) * (a ξ * a ξ') := by
        have := ha ξ hξ; have := ha ξ' hmem; positivity
      split_ifs with h
      · rw [zero_add]; exact hE2 ξ hξ ξ' hmem hne h
      · have := E2_le_E1 δ hδ t ξ ξ'; linarith
    have hcnt : ∑ ξ' ∈ Ξ.erase ξ, (if NR2 n ξ ξ' then 0 else E1 δ hδ t ξ) ≤ P * E1 δ hδ t ξ := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have h1 : ((Ξ.erase ξ).filter fun ξ' => ¬ NR2 n ξ ξ').card
          ≤ (Ξ.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ').card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_erase] at hx ⊢
        exact ⟨hx.1.2, hx.1.1, hx.2⟩
      have h2 : (((Ξ.erase ξ).filter fun ξ' => ¬ NR2 n ξ ξ').card : ℝ) ≤ P :=
        le_trans (by exact_mod_cast h1) (hbad ξ hξ)
      exact mul_le_mul_of_nonneg_right h2 (E1_nonneg δ hδ t ξ)
    have hgood : ∑ ξ' ∈ Ξ.erase ξ, (1 + ε₀) * (a ξ * a ξ') ≤ (1 + ε₀) * a ξ * ∑ ξ' ∈ Ξ, a ξ' := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by have := ha ξ hξ; positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x hx _ => ha x hx)
    rw [Finset.sum_add_distrib] at hoff
    linarith
  have hsum := Finset.sum_le_sum hrow
  have hA : ∑ ξ ∈ Ξ, a ξ ≤ S / (1 - ε₀) := by
    rw [le_div_iff₀ (by linarith), hS, Finset.sum_mul]
    refine Finset.sum_le_sum (fun ξ hξ => ?_)
    have := hE1 ξ hξ; linarith
  have hA0 : 0 ≤ ∑ ξ ∈ Ξ, a ξ := Finset.sum_nonneg ha
  calc ∑ ξ ∈ Ξ, ∑ ξ' ∈ Ξ, E2 δ hδ t ξ ξ'
      ≤ ∑ ξ ∈ Ξ, (E1 δ hδ t ξ + P * E1 δ hδ t ξ + (1 + ε₀) * a ξ * ∑ ξ' ∈ Ξ, a ξ') := hsum
    _ = S + P * S + (1 + ε₀) * (∑ ξ ∈ Ξ, a ξ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          ← Finset.mul_sum, hS]
        ring
    _ ≤ S + P * S + (1 + ε₀) * (S / (1 - ε₀)) ^ 2 := by
        gcongr
    _ = S + P * S + (1 + ε₀) * S ^ 2 / (1 - ε₀) ^ 2 := by rw [div_pow]; ring


lemma eventually_small_rpow (C e η : ℝ) (he : 0 < e) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, C * (n : ℝ) ^ (-e) ≤ η := by
  have h : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-e)) Filter.atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa using this
  exact (h.eventually (gt_mem_nhds hη)).mono (fun _ h => h.le)

lemma inv_one_sub_sq_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 4) :
    (1 + ε) / (1 - ε) ^ 2 ≤ 1 + 6 * ε := by
  have hpos : 0 < (1 - ε) ^ 2 := by have : 0 < 1 - ε := by linarith
                                    positivity
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

open scoped Classical in
/-- **`HH` from the four sub-interfaces.** -/
theorem hH_of (h1 : S1) (h2 : S2) (h3 : S3) (h4 : S4) : HH := by
  intro δ hδ η hη c₀ hc₀
  set η' := min η (1 / 2) with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set ε₀ := η' / 60 with hε₀
  have hε0 : 0 < ε₀ := by positivity
  have hε1 : ε₀ ≤ 1 / 4 := by rw [hε₀]; linarith
  set A := Ad δ hδ
  have hA := Ad_pos δ hδ
  -- the constant in the lower bound for `s`
  set C1 := 8 * Real.sqrt (2 * π) / (c₀ * A) with hC1
  filter_upwards [h1 δ hδ ε₀ hε0, h2 δ hδ ε₀ hε0, h3 c₀ hc₀ ε₀ hε0, h4,
    eventually_small_rpow C1 (1 / 2) (η' / 8) (by norm_num) (by positivity),
    eventually_small_rpow C1 (1 / 20) (η' / 8) (by norm_num) (by positivity),
    eventually_small_rpow 40 (2 / 5) 1 (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop 16] with n hS1 hS2 hS3 hS4 hsm1 hsm2 hsm3 hn16
  intro t ht Ξ hΞ
  obtain ⟨hΞsub, hΞcard, _⟩ := hΞ
  obtain ⟨hres, hbadc⟩ := hS3 Ξ ⟨hΞsub, hΞcard, ‹_›⟩
  set Ξ' := Ξ.filter fun ξ => NR1 n ξ with hΞ'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn16r : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  -- variance bounds
  have hK1 : (K n : ℝ) ≤ n / 2 + 1 / 2 := by
    have : 2 * K n ≤ n + 1 := by unfold K; omega
    have : (2 * K n : ℝ) ≤ n + 1 := by exact_mod_cast this
    linarith
  have hK2 : (n : ℝ) / 2 - 1 / 2 ≤ K n := by
    have : n ≤ 2 * K n + 1 := by unfold K; omega
    have : (n : ℝ) ≤ 2 * K n + 1 := by exact_mod_cast this
    linarith
  have hp35 : 5 * (n : ℝ) ^ (3 / 5 : ℝ) ≤ n / 8 := by
    have e : (n : ℝ) ^ (3 / 5 : ℝ) = (n : ℝ) ^ (-(2 / 5) : ℝ) * n := by
      rw [show (3 / 5 : ℝ) = -(2 / 5) + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]
    rw [e]
    have := hsm3
    nlinarith
  have hVlo : ∀ ξ ∈ Ξ, (n : ℝ) / 4 ≤ Vv t ξ := by
    intro ξ hξ
    have := hS4 t ht ξ (hΞsub hξ)
    obtain ⟨hl, hr⟩ := abs_le.mp this
    linarith
  have hVhi : ∀ ξ ∈ Ξ, Vv t ξ ≤ n := by
    intro ξ hξ
    have := hS4 t ht ξ (hΞsub hξ)
    obtain ⟨hl, hr⟩ := abs_le.mp this
    linarith
  -- the weights a ξ
  set a : ℝ → ℝ := fun ξ => A / Real.sqrt (2 * π * Vv t ξ) with ha
  have ha0 : ∀ ξ ∈ Ξ', 0 ≤ a ξ := fun ξ _ => div_nonneg hA.le (Real.sqrt_nonneg _)
  have haLo : ∀ ξ ∈ Ξ, A / Real.sqrt (2 * π * n) ≤ a ξ := by
    intro ξ hξ
    have hV := hVlo ξ hξ
    have hVpos : 0 < 2 * π * Vv t ξ := mul_pos (by positivity) (by linarith)
    apply div_le_div_of_nonneg_left hA.le (Real.sqrt_pos.mpr hVpos)
    exact Real.sqrt_le_sqrt (by have := hVhi ξ hξ; nlinarith [Real.pi_pos])
  have hE1lo : ∀ ξ ∈ Ξ', (1 - ε₀) * a ξ ≤ E1 δ hδ t ξ := by
    intro ξ hξ
    simp only [hΞ', Finset.mem_filter] at hξ
    have := hS1 t ht ξ (hΞsub hξ.1) hξ.2
    rw [abs_le] at this
    simp only [ha]; linarith
  have hE2' : ∀ ξ ∈ Ξ', ∀ ξ' ∈ Ξ', ξ' ≠ ξ → NR2 n ξ ξ' →
      E2 δ hδ t ξ ξ' ≤ (1 + ε₀) * (a ξ * a ξ') := by
    intro ξ hξ ξ' hξ' _ hnr
    simp only [hΞ', Finset.mem_filter] at hξ hξ'
    exact hS2 t ht ξ (hΞsub hξ.1) ξ' (hΞsub hξ'.1) hξ.2 hξ'.2 hnr
  set P := (n : ℝ) ^ (9 / 20 : ℝ)
  have hP : 0 ≤ P := by positivity
  have hbad' : ∀ ξ ∈ Ξ', (((Ξ'.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ').card : ℝ) ≤ P) := by
    intro ξ hξ
    simp only [hΞ', Finset.mem_filter] at hξ
    refine le_trans ?_ (hbadc ξ hξ.1 hξ.2)
    exact_mod_cast Finset.card_le_card (fun x hx => by
      simp only [hΞ', Finset.mem_filter] at hx ⊢; exact ⟨hx.1.1, hx.2⟩)
  obtain ⟨hsum1, hsum2⟩ := hh_core δ hδ t Ξ' ε₀ P hε0.le (by linarith) hP a ha0 hE1lo hE2' hbad'
  set s := ∑ ξ ∈ Ξ', E1 δ hδ t ξ with hs
  -- the size of Ξ'
  have hΞ'card : c₀ * n / 2 ≤ (Ξ'.card : ℝ) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := Ξ) (fun ξ => NR1 n ξ)
    have : (Ξ'.card : ℝ) + ((Ξ.filter fun ξ => ¬ NR1 n ξ).card : ℝ) = Ξ.card := by
      exact_mod_cast hsplit
    have hc : (Ξ.card : ℝ) * ε₀ ≤ Ξ.card / 2 := by
      have : (0 : ℝ) ≤ Ξ.card := Nat.cast_nonneg _
      nlinarith
    linarith
  -- lower bound on s
  have hslo : c₀ * n / 2 * ((1 - ε₀) * (A / Real.sqrt (2 * π * n))) ≤ s := by
    calc c₀ * n / 2 * ((1 - ε₀) * (A / Real.sqrt (2 * π * n)))
        ≤ (Ξ'.card : ℝ) * ((1 - ε₀) * (A / Real.sqrt (2 * π * n))) := by
          have h1e : 0 ≤ 1 - ε₀ := by linarith
          exact mul_le_mul_of_nonneg_right hΞ'card
            (mul_nonneg h1e (div_nonneg hA.le (Real.sqrt_nonneg _)))
      _ = ∑ _ξ ∈ Ξ', (1 - ε₀) * (A / Real.sqrt (2 * π * n)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ξ ∈ Ξ', E1 δ hδ t ξ := by
          refine Finset.sum_le_sum (fun ξ hξ => ?_)
          refine le_trans ?_ (hE1lo ξ hξ)
          have hξΞ : ξ ∈ Ξ := (Finset.mem_filter.mp hξ).1
          have h1e : 0 ≤ 1 - ε₀ := by linarith
          exact mul_le_mul_of_nonneg_left (haLo ξ hξΞ) h1e
  have hsqrt : Real.sqrt (2 * π * n) = Real.sqrt (2 * π) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (n : ℝ)]
  have hs_ge : (n : ℝ) ^ (1 / 2 : ℝ) / (C1 / 2) ≤ s := by
    refine le_trans ?_ hslo
    have hq : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hsp : 0 < Real.sqrt (2 * π) := by positivity
    have hn12 : (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hn0]; norm_num
    have e1 : (n : ℝ) ^ (1 / 2 : ℝ) / (C1 / 2)
        = (n : ℝ) ^ (1 / 2 : ℝ) * (c₀ * A / (4 * Real.sqrt (2 * π))) := by
      rw [hC1]; field_simp; ring
    have hnq : (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [div_eq_iff hq.ne']; exact hn12
    have e2 : c₀ * n / 2 * ((1 - ε₀) * (A / Real.sqrt (2 * π * n)))
        = (n : ℝ) ^ (1 / 2 : ℝ) * (c₀ * A * (1 - ε₀) / (2 * Real.sqrt (2 * π))) := by
      rw [hsqrt]
      calc c₀ * n / 2 * ((1 - ε₀) * (A / (Real.sqrt (2 * π) * (n : ℝ) ^ (1 / 2 : ℝ))))
          = c₀ * A * (1 - ε₀) / (2 * Real.sqrt (2 * π)) * ((n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) := by
            field_simp
        _ = _ := by rw [hnq]; ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ hq.le
    have hcA : 0 < c₀ * A := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 2 * Real.sqrt (2 * π) ≤ (1 - ε₀) * (4 * Real.sqrt (2 * π)) := by
      nlinarith only [hsp, hε1]
    have h5 := mul_le_mul_of_nonneg_left h4 hcA.le
    linarith only [h5]
  have hspos : 0 < s := lt_of_lt_of_le (by
    have : 0 < C1 := by positivity
    have : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    positivity) hs_ge
  -- the three conditions of `pz_ratio`
  have hinv : 1 / s ≤ C1 / 2 * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hq : 0 < (n : ℝ) ^ (1 / 2 : ℝ) / (C1 / 2) := by
      have : 0 < C1 := by positivity
      positivity
    have h := one_div_le_one_div_of_le hq hs_ge
    rw [one_div_div] at h
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]; exact h
  have hC1pos : 0 < C1 := by positivity
  have k1 : 1 / s ≤ η' / 8 := by
    have h' : C1 / 2 * (n : ℝ) ^ (-(1 / 2) : ℝ) ≤ C1 * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
      have : 0 ≤ C1 * (n : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
      linarith
    linarith
  have k2 : P * s / s ^ 2 ≤ η' / 8 := by
    have e1 : P * s / s ^ 2 = P * (1 / s) := by field_simp
    have e2 : P * (C1 / 2 * (n : ℝ) ^ (-(1 / 2) : ℝ)) = C1 / 2 * (n : ℝ) ^ (-(1 / 20) : ℝ) := by
      rw [show P = (n : ℝ) ^ (9 / 20 : ℝ) from rfl, mul_left_comm, ← Real.rpow_add hn0]; norm_num
    have h3 : P * (1 / s) ≤ P * (C1 / 2 * (n : ℝ) ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_left hinv hP
    have h' : C1 / 2 * (n : ℝ) ^ (-(1 / 20) : ℝ) ≤ C1 * (n : ℝ) ^ (-(1 / 20) : ℝ) := by
      have : 0 ≤ C1 * (n : ℝ) ^ (-(1 / 20) : ℝ) := by positivity
      linarith
    rw [e1]; linarith
  have k3 : (1 + ε₀) / (1 - ε₀) ^ 2 ≤ 1 + η' / 8 := by
    have := inv_one_sub_sq_le hε0.le hε1
    rw [hε₀] at this ⊢; linarith
  have hQ := pz_ratio hspos hη'1 hη'0.le (le_refl _) k1 k2 k3 (by linarith)
  -- Paley–Zygmund
  set Nf : (Fin (K n) → ℤˣ) → ℝ := fun b => ∑ ξ ∈ Ξ', bumpR δ hδ (IIt t b ξ)
  have hNf0 : ∀ b, 0 ≤ Nf b := fun b => Finset.sum_nonneg (fun _ _ => bumpR_nonneg δ hδ _)
  have hpz := pz_count Nf hNf0
  have h2K : (0 : ℝ) < 2 ^ K n := by positivity
  set Qs := s + P * s + (1 + ε₀) * s ^ 2 / (1 - ε₀) ^ 2
  have hQs0 : 0 < Qs := by
    have : 0 ≤ (1 + ε₀) * s ^ 2 / (1 - ε₀) ^ 2 := by
      have : 0 < 1 - ε₀ := by linarith
      positivity
    have : 0 ≤ P * s := by positivity
    linarith
  have hsub : (univ.filter fun b => 0 < Nf b) ⊆
      (univ.filter fun b : Fin (K n) → ℤˣ => ∃ ξ ∈ Ξ, |IIt t b ξ| < δ) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    by_contra hcon
    push Not at hcon
    have : Nf b = 0 := Finset.sum_eq_zero (fun ξ hξ => bumpR_eq_zero δ hδ (by
      have := hcon ξ (Finset.mem_filter.mp hξ).1; linarith))
    linarith
  have hc1 : ((univ.filter fun b => 0 < Nf b).card : ℝ)
      ≤ ((univ.filter fun b : Fin (K n) → ℤˣ => ∃ ξ ∈ Ξ, |IIt t b ξ| < δ).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  set c := ((univ.filter fun b => 0 < Nf b).card : ℝ)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hA1 : (2 ^ K n * s) ^ 2 ≤ c * (2 ^ K n * Qs) := by
    have e1 : ∑ b, Nf b = 2 ^ K n * s := hsum1
    have e2 : ∑ b, Nf b ^ 2 ≤ 2 ^ K n * Qs := hsum2
    calc (2 ^ K n * s) ^ 2 = (∑ b, Nf b) ^ 2 := by rw [e1]
      _ ≤ c * ∑ b, Nf b ^ 2 := hpz
      _ ≤ c * (2 ^ K n * Qs) := mul_le_mul_of_nonneg_left e2 hc0
  have hA2 : (1 - η') * 2 ^ K n * Qs ≤ c * Qs := by
    have : (1 - η') * 2 ^ K n * Qs = 2 ^ K n * ((1 - η') * Qs) := by ring
    rw [this]
    have h3 : 2 ^ K n * ((1 - η') * Qs) ≤ 2 ^ K n * s ^ 2 :=
      mul_le_mul_of_nonneg_left hQ h2K.le
    have h4 : 2 ^ K n * s ^ 2 ≤ c * Qs := by
      have : (2 ^ K n * s) ^ 2 = 2 ^ K n * (2 ^ K n * s ^ 2) := by ring
      rw [this] at hA1
      have h5 : 2 ^ K n * (2 ^ K n * s ^ 2) ≤ 2 ^ K n * (c * Qs) := by linarith
      exact le_of_mul_le_mul_left h5 h2K
    linarith
  have hA3 : (1 - η') * 2 ^ K n ≤ c := le_of_mul_le_mul_right hA2 hQs0
  have hfin : (1 - η) * 2 ^ K n ≤ (1 - η') * 2 ^ K n :=
    mul_le_mul_of_nonneg_right (by linarith only [hη'η]) h2K.le
  linarith only [hfin, hA3, hc1]


/-! ### S4: the variance -/

lemma re_Ssum (t : Fin (K n) → Bool) (x : ℝ) :
    (Ssum t x).re = ∑ p, sg (t p) * (Real.cos (kk n p * x) / 2) := by
  rw [Ssum_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero]

lemma abs_re_le_norm' (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z

lemma Vv_eq (t : Fin (K n) → Bool) (ξ : ℝ) :
    Vv t ξ = (K n : ℝ) + 2 * ∑ p, sg (t p) * (Real.cos (kk n p * 0) / 2)
      - Dc n (2 * ξ) - 2 * ∑ p, sg (t p) * (Real.cos (kk n p * (2 * ξ)) / 2) := by
  unfold Vv wv Dc
  have hpt : ∀ p : Fin (K n), (if t p then (0 : ℝ) else 2 * Real.sin (kk n p * ξ)) ^ 2
      = 1 + 2 * (sg (t p) * (Real.cos (kk n p * 0) / 2)) - Real.cos (kk n p * (2 * ξ))
        - 2 * (sg (t p) * (Real.cos (kk n p * (2 * ξ)) / 2)) := by
    intro p
    have hc : Real.cos (kk n p * (2 * ξ)) = 1 - 2 * Real.sin (kk n p * ξ) ^ 2 := by
      rw [show kk n p * (2 * ξ) = 2 * (kk n p * ξ) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    cases t p <;> simp [sg, hc] <;> ring
  simp_rw [hpt]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]

/-- **S4 holds.** -/
lemma rpow35_ge_two (n : ℕ) (hn : 4 ≤ n) : (2 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by
  by_contra h
  push Not at h
  have h0 : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have h5 := pow_lt_pow_left₀ h h0 (by norm_num : (5 : ℕ) ≠ 0)
  have e : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ (5 : ℕ) = (n : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_natCast]; norm_num
  rw [e] at h5
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h64 : (4 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
  norm_num at h5 h64
  linarith

theorem S4_holds : S4 := by
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  intro t ht ξ hξ
  have h0 := (abs_re_le_norm' (Ssum t 0)).trans (ht 0)
  have h1 := (abs_re_le_norm' (Ssum t (2 * ξ))).trans (ht (2 * ξ))
  rw [re_Ssum] at h0 h1
  have h2 := abs_Dc_le_sqrt2 n (x := 2 * ξ) (by linarith [hξ.1]) (by linarith [hξ.2])
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hn2 := rpow35_ge_two n hn
  rw [Vv_eq]
  obtain ⟨a0, b0⟩ := abs_le.mp h0
  obtain ⟨a1, b1⟩ := abs_le.mp h1
  obtain ⟨a2, b2⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith


/-! ### S3: counting resonant points -/

/-- Separated points in a half-open interval. -/
lemma card_sep (g ℓ a : ℝ) (hg : 0 < g) (hℓ : 0 ≤ ℓ) (Ξ : Finset ℝ)
    (hsep : ∀ x ∈ Ξ, ∀ y ∈ Ξ, x ≠ y → g ≤ |x - y|) (hsub : ∀ x ∈ Ξ, a ≤ x ∧ x < a + ℓ) :
    (Ξ.card : ℝ) ≤ ℓ / g + 1 := by
  set f : ℝ → ℕ := fun x => ⌊(x - a) / g⌋₊
  have hmaps : ∀ x ∈ Ξ, f x ∈ Finset.range (⌊ℓ / g⌋₊ + 1) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hsub x hx
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    rw [div_le_div_iff_of_pos_right hg]; linarith
  have hinj : Set.InjOn f Ξ := by
    intro x hx y hy hxy
    by_contra hne
    have := hsep x hx y hy hne
    have hx0 : 0 ≤ (x - a) / g := div_nonneg (by linarith [(hsub x hx).1]) hg.le
    have hy0 : 0 ≤ (y - a) / g := div_nonneg (by linarith [(hsub y hy).1]) hg.le
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one ((x - a) / g)
    have h3 := Nat.floor_le hy0
    have h4 := Nat.lt_floor_add_one ((y - a) / g)
    simp only [f] at hxy
    rw [hxy] at h1 h2
    have hd : |(x - a) / g - (y - a) / g| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hg, div_lt_one hg] at hd
    have : x - a - (y - a) = x - y := by ring
    rw [this] at hd
    linarith
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hc
  have : ((⌊ℓ / g⌋₊ + 1 : ℕ) : ℝ) ≤ ℓ / g + 1 := by
    push_cast; have := Nat.floor_le (div_nonneg hℓ hg.le); linarith
  exact le_trans (by exact_mod_cast hc) this

lemma abs_sin_ge (y : ℝ) : 2 / π * |y - round (y / π) * π| ≤ |Real.sin y| := by
  set k := round (y / π)
  have hpi := Real.pi_pos
  have hz : |y - k * π| ≤ π / 2 := by
    have := abs_sub_round (y / π)
    have e : y - k * π = π * (y / π - k) := by field_simp
    rw [e, abs_mul, abs_of_pos hpi]
    nlinarith
  have hs : |Real.sin y| = |Real.sin (y - k * π)| := by
    rw [Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [hs]
  set z := y - k * π
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by
      rw [abs_of_nonneg h] at hz; linarith))]
    exact Real.mul_le_sin h (by rw [abs_of_nonneg h] at hz; exact hz)
  · rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by
      rw [abs_of_nonpos h] at hz; linarith))]
    have := Real.mul_le_sin (x := -z) (by linarith) (by rw [abs_of_nonpos h] at hz; linarith)
    rw [Real.sin_neg] at this; linarith

/-- Points of a separated set where `|sin (m x + c)|` is small. -/
lemma card_sin_small (m : ℕ) (hm : 1 ≤ m) (c ε g : ℝ) (hε : 0 ≤ ε) (hg : 0 < g) (Ξ : Finset ℝ)
    (hsep : ∀ x ∈ Ξ, ∀ y ∈ Ξ, x ≠ y → g ≤ |x - y|) (hsub : ∀ x ∈ Ξ, 0 ≤ x ∧ x ≤ π) :
    ((Ξ.filter fun x => |Real.sin (m * x + c)| < ε).card : ℝ)
      ≤ (m + 3) * (π * ε / (m * g) + 1) := by
  classical
  have hpi := Real.pi_pos
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set k0 : ℤ := round (c / π) - 1
  set Kset : Finset ℤ := Finset.Icc k0 (k0 + m + 2)
  set I : ℤ → Finset ℝ := fun k => Ξ.filter fun x =>
    (k * π - c) / m - π * ε / (2 * m) ≤ x ∧ x < (k * π - c) / m - π * ε / (2 * m) + π * ε / m
  have hcover : (Ξ.filter fun x => |Real.sin (m * x + c)| < ε) ⊆ Kset.biUnion I := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨hxΞ, hsmall⟩ := hx
    set y := m * x + c
    set k := round (y / π)
    have hb := abs_sin_ge y
    have hd : |y - k * π| < π * ε / 2 := by
      have : 2 / π * |y - k * π| < ε := lt_of_le_of_lt hb hsmall
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at this; linarith
    rw [Finset.mem_biUnion]
    refine ⟨k, ?_, ?_⟩
    · -- k is in the window
      have hx1 := (hsub x hxΞ).1
      have hx2 := (hsub x hxΞ).2
      have hr1 := abs_sub_round (y / π)
      have hr2 := abs_sub_round (c / π)
      rw [abs_le] at hr1 hr2
      have hyl : c / π ≤ y / π := by
        apply div_le_div_of_nonneg_right _ hpi.le; simp only [y]; nlinarith
      have hyu : y / π ≤ c / π + m := by
        rw [div_add' _ _ _ hpi.ne', div_le_div_iff_of_pos_right hpi]; simp only [y]; nlinarith
      simp only [Kset, Finset.mem_Icc, k0]
      constructor
      · have : (round (c / π) : ℝ) - 1 ≤ round (y / π) := by linarith
        exact_mod_cast this
      · have : (round (y / π) : ℝ) ≤ round (c / π) - 1 + m + 2 := by linarith
        exact_mod_cast this
    · simp only [I, Finset.mem_filter]
      have hmpos : (0 : ℝ) < m := by linarith
      have e : x - (k * π - c) / m = (m * x + c - k * π) / m := by field_simp; ring
      have hxu : |x - (k * π - c) / m| < π * ε / (2 * m) := by
        rw [e, abs_div, abs_of_pos hmpos, show π * ε / (2 * m) = (π * ε / 2) / m by ring]
        exact div_lt_div_of_pos_right hd hmpos
      have hsum : π * ε / (2 * m) + π * ε / (2 * m) = π * ε / m := by field_simp; ring
      obtain ⟨hl, hr⟩ := abs_lt.mp hxu
      refine ⟨hxΞ, by linarith, by linarith⟩
  have hcard := Finset.card_le_card hcover
  have hbu := Finset.card_biUnion_le (s := Kset) (t := I)
  have hI : ∀ k ∈ Kset, ((I k).card : ℝ) ≤ π * ε / (m * g) + 1 := by
    intro k _
    have hmpos : (0 : ℝ) < m := by linarith
    have := card_sep g (π * ε / m) ((k * π - c) / m - π * ε / (2 * m)) hg (by positivity) (I k)
      (fun x hx y hy h => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 h)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [div_div] at this; exact this
  have hKcard : (Kset.card : ℝ) = m + 3 := by
    have : Kset.card = m + 3 := by simp only [Kset, Int.card_Icc]; omega
    rw [this]; push_cast; ring
  calc ((Ξ.filter fun x => |Real.sin (m * x + c)| < ε).card : ℝ)
      ≤ ((Kset.biUnion I).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ k ∈ Kset, ((I k).card : ℝ) := by exact_mod_cast hbu
    _ ≤ ∑ _k ∈ Kset, (π * ε / (m * g) + 1) := Finset.sum_le_sum hI
    _ = (m + 3) * (π * ε / (m * g) + 1) := by rw [Finset.sum_const, nsmul_eq_mul, hKcard]


lemma abs_sin_int_mul (m : ℤ) (x : ℝ) : |Real.sin (m * x)| = |Real.sin ((m.natAbs : ℝ) * x)| := by
  rw [Nat.cast_natAbs]
  rcases abs_cases (m : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [Int.cast_abs, h]
  · rw [Int.cast_abs, h, neg_mul, Real.sin_neg, abs_neg]

lemma abs_sin_two (m₁ m₂ : ℤ) (ξ ξ' : ℝ) :
    |Real.sin (m₁ * ξ + m₂ * ξ')| =
      |Real.sin ((m₂.natAbs : ℝ) * ξ' + (if 0 ≤ m₂ then (m₁ : ℝ) else -m₁) * ξ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]
  by_cases h0 : 0 ≤ m₂
  · rw [if_pos h0, abs_of_nonneg (by exact_mod_cast h0 : (0 : ℝ) ≤ m₂), add_comm]
  · rw [if_neg h0, abs_of_neg (by exact_mod_cast (lt_of_not_ge h0) : (m₂ : ℝ) < 0)]
    have e : (m₁ : ℝ) * ξ + m₂ * ξ' = -(-(m₂ : ℝ) * ξ' + -(m₁ : ℝ) * ξ) := by ring
    rw [e, Real.sin_neg, abs_neg]

/-- Count of near points. -/
lemma card_near (Ξ : Finset ℝ) (g d ξ : ℝ) (hg : 0 < g) (hd : 0 ≤ d)
    (hsep : ∀ x ∈ Ξ, ∀ y ∈ Ξ, x ≠ y → g ≤ |x - y|) :
    ((Ξ.filter fun ξ' => |ξ - ξ'| < d).card : ℝ) ≤ 2 * d / g + 1 := by
  have := card_sep g (2 * d) (ξ - d) hg (by linarith) (Ξ.filter fun ξ' => |ξ - ξ'| < d)
    (fun x hx y hy h => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 h)
    (fun x hx => by
      have := (Finset.mem_filter.mp hx).2
      rw [abs_lt] at this; constructor <;> linarith)
  exact this

open scoped Classical in
/-- **S3 holds.** -/
theorem S3_holds : S3 := by
  intro c₀ hc₀ ε₀ hε₀
  set C2 := 4 * (π / c₀ + 1) / (ε₀ * c₀)
  set C3 := 48 * (π / c₀ + 1)
  filter_upwards [eventually_small_rpow C2 (13 / 20) 1 (by norm_num) (by norm_num),
    eventually_small_rpow C3 (1 / 20) 1 (by norm_num) (by norm_num),
    eventually_small_rpow (4 / c₀ + 2) (1 / 20) 1 (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop 1] with n hC2 hC3 hC4 hn
  intro Ξ hΞ
  obtain ⟨hsub, hcard, hsep⟩ := hΞ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set g := c₀ / n with hg
  have hg0 : 0 < g := by positivity
  have hsub' : ∀ x ∈ Ξ, 0 ≤ x ∧ x ≤ π := by
    intro x hx; have := hsub hx; constructor <;> linarith [this.1, this.2, Real.pi_pos]
  set D := Dn n
  set ε := εn n
  have hε0 : 0 ≤ ε := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hD : (D : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (by positivity)
  have hεn : ε * n = (n : ℝ) ^ (1 / 4 : ℝ) := by
    simp only [ε, εn]
    rw [show (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (-(3 / 4) : ℝ) * (n : ℝ) ^ (1 : ℝ) by
      rw [← Real.rpow_add hn0]; norm_num, Real.rpow_one]
  have hn14 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hn120 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  -- per-frequency bound
  have hper : ∀ m : ℕ, 1 ≤ m → m ≤ D → ∀ c : ℝ,
      ((Ξ.filter fun x => |Real.sin (m * x + c)| < ε).card : ℝ)
        ≤ ((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ)) := by
    intro m hm hmD c
    refine (card_sin_small m hm c ε g hε0 hg0 Ξ hsep hsub').trans ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmD' : (m : ℝ) ≤ D := by exact_mod_cast hmD
    have h1 : π * ε / (m * g) ≤ π / c₀ * (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [hg, ← hεn]
      rw [div_le_iff₀ (by positivity)]
      have : π / c₀ * (ε * n) * (m * (c₀ / n)) = π * ε * m := by field_simp
      rw [this]
      have : 0 ≤ π * ε := by positivity
      nlinarith
    have h2 : π * ε / (m * g) + 1 ≤ (π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ) := by nlinarith
    have h3 : (0 : ℝ) ≤ π * ε / (m * g) + 1 := by positivity
    calc ((m : ℝ) + 3) * (π * ε / (m * g) + 1) ≤ ((D : ℝ) + 3) * (π * ε / (m * g) + 1) := by
          gcongr
      _ ≤ ((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
  set B1 := ((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ)) with hB1
  have hB1_0 : 0 ≤ B1 := by positivity
  have hD3 : (D : ℝ) + 3 ≤ 4 * (n : ℝ) ^ (1 / 20 : ℝ) := by linarith
  constructor
  · -- resonant single points
    have hcover : (Ξ.filter fun ξ => ¬ NR1 n ξ) ⊆ (Finset.Icc 1 D).biUnion
        (fun m => Ξ.filter fun x => |Real.sin (m * x + 0)| < ε) := by
      intro x hx
      simp only [Finset.mem_filter, NR1, not_forall, not_le] at hx
      obtain ⟨hxΞ, m, hm1, hmD, hlt⟩ := hx
      simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, add_zero]
      exact ⟨m, ⟨hm1, hmD⟩, hxΞ, hlt⟩
    have hc1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hc2 : ((Ξ.filter fun ξ => ¬ NR1 n ξ).card : ℝ) ≤ D * B1 := by
      calc _ ≤ ∑ m ∈ Finset.Icc 1 D, ((Ξ.filter fun x => |Real.sin (m * x + 0)| < ε).card : ℝ) := by
            exact_mod_cast hc1
        _ ≤ ∑ _m ∈ Finset.Icc 1 D, B1 := Finset.sum_le_sum (fun m hm => by
            rw [Finset.mem_Icc] at hm; exact hper m hm.1 hm.2 0)
        _ = D * B1 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    refine hc2.trans ?_
    -- D * B1 ≤ ε₀ * |Ξ|
    have hpow : (n : ℝ) ^ (1 / 20 : ℝ) * (4 * (n : ℝ) ^ (1 / 20 : ℝ)) * ((π / c₀ + 1) *
        (n : ℝ) ^ (1 / 4 : ℝ)) = 4 * (π / c₀ + 1) * (n : ℝ) ^ (7 / 20 : ℝ) := by
      have : (n : ℝ) ^ (7 / 20 : ℝ) = (n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) *
          (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
      rw [this]; ring
    have hDB : (D : ℝ) * B1 ≤ 4 * (π / c₀ + 1) * (n : ℝ) ^ (7 / 20 : ℝ) := by
      rw [← hpow, hB1]
      have : (0 : ℝ) ≤ (π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      calc (D : ℝ) * (((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ)))
          ≤ (n : ℝ) ^ (1 / 20 : ℝ) * (((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ))) := by
            gcongr
        _ ≤ (n : ℝ) ^ (1 / 20 : ℝ) * (4 * (n : ℝ) ^ (1 / 20 : ℝ) * ((π / c₀ + 1) *
            (n : ℝ) ^ (1 / 4 : ℝ))) := by gcongr
        _ = _ := by ring
    have hsplit : (n : ℝ) = (n : ℝ) ^ (7 / 20 : ℝ) * (n : ℝ) ^ (13 / 20 : ℝ) := by
      rw [← Real.rpow_add hn0]; norm_num
    have hneg : (n : ℝ) ^ (-(13 / 20) : ℝ) * (n : ℝ) ^ (13 / 20 : ℝ) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    have hp7 : 0 < (n : ℝ) ^ (7 / 20 : ℝ) := by positivity
    have hp13 : 0 < (n : ℝ) ^ (13 / 20 : ℝ) := by positivity
    -- from hC2: C2 * n^(-13/20) ≤ 1
    have key : 4 * (π / c₀ + 1) ≤ ε₀ * c₀ * (n : ℝ) ^ (13 / 20 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hC2 hp13.le
      rw [mul_assoc, hneg, mul_one, one_mul] at this
      simp only [C2] at this
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    calc (D : ℝ) * B1 ≤ 4 * (π / c₀ + 1) * (n : ℝ) ^ (7 / 20 : ℝ) := hDB
      _ ≤ ε₀ * c₀ * (n : ℝ) ^ (13 / 20 : ℝ) * (n : ℝ) ^ (7 / 20 : ℝ) := by gcongr
      _ = ε₀ * c₀ * ((n : ℝ) ^ (7 / 20 : ℝ) * (n : ℝ) ^ (13 / 20 : ℝ)) := by ring
      _ = ε₀ * (c₀ * n) := by rw [← hsplit]; ring
      _ ≤ ε₀ * Ξ.card := by gcongr
  · -- bad partners
    intro ξ hξ hnr
    set Pairs : Finset (ℤ × ℤ) := (Finset.Icc (-(D : ℤ)) D ×ˢ Finset.Icc (-(D : ℤ)) D).filter
      (fun q => q.2 ≠ 0)
    set bad : ℤ × ℤ → Finset ℝ := fun q => Ξ.filter fun x =>
      |Real.sin ((q.2.natAbs : ℝ) * x + (if 0 ≤ q.2 then (q.1 : ℝ) else -q.1) * ξ)| < ε
    set near := Ξ.filter fun ξ' => |ξ - ξ'| < (n : ℝ) ^ (-(3 / 5) : ℝ)
    have hcover : (Ξ.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ') ⊆ near ∪ Pairs.biUnion bad := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨hxΞ, _, hbad⟩ := hx
      simp only [NR2, not_and_or, not_le, not_forall] at hbad
      rw [Finset.mem_union]
      rcases hbad with h | h
      · left; simp only [near, Finset.mem_filter]; exact ⟨hxΞ, h⟩
      · right
        obtain ⟨m₁, m₂, hne, h1, h2, hlt⟩ := h
        by_cases hm2 : m₂ = 0
        · exfalso
          subst hm2
          have hm1 : m₁ ≠ 0 := by tauto
          have := hnr m₁.natAbs (by omega) (by
            have : (m₁.natAbs : ℤ) ≤ D := by rw [Int.natCast_natAbs]; exact h1
            exact_mod_cast this)
          simp only [Int.cast_zero, zero_mul, add_zero] at hlt
          rw [abs_sin_int_mul] at hlt
          linarith
        · rw [Finset.mem_biUnion]
          refine ⟨(m₁, m₂), ?_, ?_⟩
          · simp only [Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
            rw [abs_le] at h1 h2
            exact ⟨⟨h1, h2⟩, hm2⟩
          · simp only [bad, Finset.mem_filter]
            refine ⟨hxΞ, ?_⟩
            rw [← abs_sin_two]; exact hlt
    have hc1 := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hnear : (near.card : ℝ) ≤ 2 * (n : ℝ) ^ (-(3 / 5) : ℝ) / g + 1 :=
      card_near Ξ g _ ξ hg0 (by positivity) hsep
    have hbadc : ∀ q ∈ Pairs, ((bad q).card : ℝ) ≤ B1 := by
      intro q hq
      simp only [Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      have hq1 : 1 ≤ q.2.natAbs := by omega
      have hq2 : q.2.natAbs ≤ D := by omega
      exact hper q.2.natAbs hq1 hq2 _
    have hPairs : (Pairs.card : ℝ) ≤ (2 * D + 1) ^ 2 := by
      have := Finset.card_filter_le (Finset.Icc (-(D : ℤ)) D ×ˢ Finset.Icc (-(D : ℤ)) D)
        (fun q => q.2 ≠ 0)
      rw [Finset.card_product, Int.card_Icc] at this
      have e : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
      rw [e] at this
      have : (Pairs.card : ℝ) ≤ ((2 * D + 1) * (2 * D + 1) : ℕ) := by exact_mod_cast this
      push_cast at this; nlinarith
    have hbu : ((Pairs.biUnion bad).card : ℝ) ≤ (2 * D + 1) ^ 2 * B1 := by
      calc ((Pairs.biUnion bad).card : ℝ) ≤ ∑ q ∈ Pairs, ((bad q).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ Pairs, B1 := Finset.sum_le_sum hbadc
        _ = Pairs.card * B1 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * D + 1) ^ 2 * B1 := by gcongr
    -- final arithmetic
    have hnear' : 2 * (n : ℝ) ^ (-(3 / 5) : ℝ) / g + 1 ≤ (2 / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ) := by
      have e : 2 * (n : ℝ) ^ (-(3 / 5) : ℝ) / g = 2 / c₀ * (n : ℝ) ^ (2 / 5 : ℝ) := by
        rw [hg]
        have : (n : ℝ) ^ (2 / 5 : ℝ) = (n : ℝ) ^ (-(3 / 5) : ℝ) * n := by
          rw [show (2 / 5 : ℝ) = -(3 / 5) + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]
        rw [this]; field_simp
      have : (1 : ℝ) ≤ (n : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
      rw [e]; nlinarith
    have hpair' : (2 * D + 1 : ℝ) ^ 2 * B1 ≤ 36 * (π / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ) := by
      have h2D : (2 * D + 1 : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 20 : ℝ) := by linarith
      have e : (n : ℝ) ^ (2 / 5 : ℝ) = (n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) *
          (n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
      rw [e, hB1]
      have h0 : (0 : ℝ) ≤ (π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
      have h2D0 : (0 : ℝ) ≤ 2 * D + 1 := by positivity
      calc (2 * D + 1 : ℝ) ^ 2 * (((D : ℝ) + 3) * ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ)))
          ≤ (3 * (n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 * ((4 * (n : ℝ) ^ (1 / 20 : ℝ)) *
            ((π / c₀ + 1) * (n : ℝ) ^ (1 / 4 : ℝ))) := by gcongr
        _ = _ := by ring
    have hfin : (2 / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ) + 36 * (π / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ)
        ≤ (n : ℝ) ^ (9 / 20 : ℝ) := by
      have e : (n : ℝ) ^ (2 / 5 : ℝ) = (n : ℝ) ^ (-(1 / 20) : ℝ) * (n : ℝ) ^ (9 / 20 : ℝ) := by
        rw [← Real.rpow_add hn0]; norm_num
      rw [e]
      have h9 : 0 < (n : ℝ) ^ (9 / 20 : ℝ) := by positivity
      have hc : 2 / c₀ + 1 + 36 * (π / c₀ + 1) ≤ C3 := by
        simp only [C3]
        have : 2 / c₀ ≤ π / c₀ := by gcongr; linarith [Real.pi_gt_three]
        have : 0 ≤ π / c₀ := by positivity
        linarith
      have hq : 0 < (n : ℝ) ^ (-(1 / 20) : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hc hq.le
      have h3 : (2 / c₀ + 1 + 36 * (π / c₀ + 1)) * (n : ℝ) ^ (-(1 / 20) : ℝ) ≤ 1 := by
        linarith only [hC3, this]
      have h4 := mul_le_mul_of_nonneg_right h3 h9.le
      linarith only [h4]
    calc ((Ξ.filter fun ξ' => ξ' ≠ ξ ∧ ¬ NR2 n ξ ξ').card : ℝ)
        ≤ (near.card : ℝ) + ((Pairs.biUnion bad).card : ℝ) := by exact_mod_cast hc1
      _ ≤ (2 / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ) + 36 * (π / c₀ + 1) * (n : ℝ) ^ (2 / 5 : ℝ) := by
          linarith only [hnear, hnear', hbu, hpair']
      _ ≤ (n : ℝ) ^ (9 / 20 : ℝ) := hfin


/-! ### Toward S1/S2: the torus average of `sin²` -/

lemma sin_le_099 {x : ℝ} (h1 : 1 / 3 ≤ x) : |Real.sin x| ≤ 99 / 100 * x := by
  by_cases h2 : x ≤ 1
  · have hb := Real.sin_bound (x := x) (by rw [abs_le]; constructor <;> linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hb
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_gt_three])
    rw [abs_of_nonneg hs0]
    have hx0 : 0 ≤ x := by linarith
    have hx2 : 1 / 9 ≤ x ^ 2 := by nlinarith
    have hx34 : x ^ 4 ≤ x ^ 3 := by
      have : x ^ 4 = x ^ 3 * x := by ring
      rw [this]; have : 0 ≤ x ^ 3 := by positivity
      nlinarith
    have hx3 : x / 9 ≤ x ^ 3 := by
      have : x ^ 3 = x * x ^ 2 := by ring
      rw [this]; nlinarith
    have hx53 : x ^ 5 ≤ x ^ 3 := by
      have : x ^ 5 = x ^ 3 * x ^ 2 := by ring
      rw [this]; have : 0 ≤ x ^ 3 := by positivity
      have : x ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  · push Not at h2
    by_cases h3 : x ≤ 102 / 100
    · have hb := Real.sin_bound (x := 1) (by norm_num)
      norm_num at hb
      rw [abs_le] at hb
      have hlip := Real.abs_sin_sub_sin_le x 1
      have hs0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_gt_three])
      rw [abs_of_nonneg hs0]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1)] at hlip
      obtain ⟨hl1, hl2⟩ := abs_le.mp hlip
      linarith
    · push Not at h3
      have := Real.abs_sin_le_one x
      linarith

/-- `∫₀¹ sin²(s x + a) dx` is bounded below when `|s| ≥ 1/3`. -/
lemma integral_sin_sq_lower (s a : ℝ) (hs : 1 / 3 ≤ |s|) :
    1 / 200 ≤ ∫ x in (0 : ℝ)..1, Real.sin (s * x + a) ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hs; linarith
  rw [intervalIntegral.integral_comp_mul_add (fun y => Real.sin y ^ 2) hs0, integral_sin_sq]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
  -- |sin a cos a - sin (s + a) cos (s + a)| ≤ |sin s|
  have key : |Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a)| ≤ |Real.sin s| := by
    have e : Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a)
        = -(Real.sin s * Real.cos (s + 2 * a)) := by
      have h2a : Real.sin a * Real.cos a = Real.sin (2 * a) / 2 := by rw [Real.sin_two_mul]; ring
      have h2b : Real.sin (s + a) * Real.cos (s + a) = Real.sin (2 * (s + a)) / 2 := by
        rw [Real.sin_two_mul]; ring
      rw [h2a, h2b, ← sub_div, Real.sin_sub_sin]
      rw [show (2 * a - 2 * (s + a)) / 2 = -s by ring, show (2 * a + 2 * (s + a)) / 2 = s + 2 * a by ring,
        Real.sin_neg]
      ring
    rw [e, abs_neg, abs_mul]
    have := Real.abs_cos_le_one (s + 2 * a)
    nlinarith [abs_nonneg (Real.sin s)]
  have hsin : |Real.sin s| ≤ 99 / 100 * |s| := by
    rcases le_or_gt 0 s with h | h
    · rw [abs_of_nonneg h] at hs ⊢; exact sin_le_099 hs
    · rw [abs_of_neg h] at hs ⊢
      have := sin_le_099 hs
      rwa [Real.sin_neg, abs_neg] at this
  have hpos : 0 < |s| := abs_pos.mpr hs0
  obtain ⟨key1, key2⟩ := abs_le.mp key
  -- s⁻¹ * ((sin a cos a - sin(s+a) cos(s+a) + s) / 2) ≥ 1/2 - 0.99/2
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hpos hsin
    have hs' : 0 < s := hpos
    rw [show s⁻¹ * ((Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a) + (s + a) - a) / 2)
      = ((Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a)) / s + 1) / 2 by
      field_simp; ring]
    have : -(99 / 100) ≤ (Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a)) / s := by
      rw [le_div_iff₀ hs']; linarith
    linarith
  · rw [abs_of_neg h] at hpos hsin
    have hs' : 0 < -s := hpos
    rw [show s⁻¹ * ((Real.sin a * Real.cos a - Real.sin (s + a) * Real.cos (s + a) + (s + a) - a) / 2)
      = ((Real.sin (s + a) * Real.cos (s + a) - Real.sin a * Real.cos a) / (-s) + 1) / 2 by
      field_simp; ring]
    have : -(99 / 100) ≤ (Real.sin (s + a) * Real.cos (s + a) - Real.sin a * Real.cos a) / (-s) := by
      rw [le_div_iff₀ hs']; linarith
    linarith


/-- The quarter-period average: `∫₀^{π/2} sin²(s sin θ + a) dθ ≥ 1/200` when `|s| ≥ 1/3`. -/
lemma quarter_mean (s a : ℝ) (hs : 1 / 3 ≤ |s|) :
    1 / 200 ≤ ∫ θ in (0 : ℝ)..(π / 2), Real.sin (s * Real.sin θ + a) ^ 2 := by
  have hsub : (∫ θ in (0 : ℝ)..(π / 2), ((fun x => Real.sin (s * x + a) ^ 2) ∘ Real.sin) θ
      * Real.cos θ) = ∫ x in Real.sin 0..Real.sin (π / 2), Real.sin (s * x + a) ^ 2 :=
    intervalIntegral.integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_sin x)
      Real.continuous_cos.continuousOn (by fun_prop)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  have hlow := integral_sin_sq_lower s a hs
  rw [← hsub] at hlow
  refine hlow.trans ?_
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
  · exact (by fun_prop : Continuous fun θ => ((fun x => Real.sin (s * x + a) ^ 2) ∘ Real.sin) θ
      * Real.cos θ).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ => Real.sin (s * Real.sin θ + a) ^ 2).intervalIntegrable _ _
  · intro θ hθ
    simp only [Function.comp_apply]
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
      hθ.2⟩
    have := sq_nonneg (Real.sin (s * Real.sin θ + a))
    nlinarith


/-! ### Fejér smoothing on the circle -/

/-- The Dirichlet-type sum `Σ_{j ≤ D} e^{ijx}`. -/
def dsum (D : ℕ) (x : ℝ) : ℂ := ∑ j ∈ Finset.range (D + 1), Complex.exp (↑((j : ℝ) * x) * Complex.I)

/-- The Fejér kernel `|Σ_{j ≤ D} e^{ijx}|² / (D+1)`. -/
def fej (D : ℕ) (x : ℝ) : ℝ := ‖dsum D x‖ ^ 2 / (D + 1)

lemma fej_nonneg (D : ℕ) (x : ℝ) : 0 ≤ fej D x := by unfold fej; positivity

lemma fej_expand (D : ℕ) (x : ℝ) :
    (fej D x : ℂ) = (1 / ((D : ℂ) + 1)) * ∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1),
      Complex.exp (↑(((j : ℝ) - k) * x) * Complex.I) := by
  unfold fej
  rw [Complex.ofReal_div, Complex.ofReal_pow, ← Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  unfold dsum
  rw [map_sum, Finset.sum_mul_sum, div_eq_mul_inv, mul_comm, one_div]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma integral_exp_int (m : ℤ) (hm : m ≠ 0) (θ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), Complex.exp (↑((m : ℝ) * (θ - φ)) * Complex.I) = 0 := by
  have hc : ((-(m : ℂ)) * Complex.I) ≠ 0 := by
    apply mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hm)) Complex.I_ne_zero
  have e : ∀ φ : ℝ, Complex.exp (↑((m : ℝ) * (θ - φ)) * Complex.I)
      = Complex.exp (↑((m : ℝ) * θ) * Complex.I) * Complex.exp ((-(m : ℂ)) * Complex.I * φ) := by
    intro φ; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  have h1 : Complex.exp ((-(m : ℂ)) * Complex.I * ↑(2 * π)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-m)
    rw [← this]; congr 1; push_cast; ring
  rw [h1]; simp

/-- One exponential term of the Fejér kernel. -/
def Ejk (θ : ℝ) (j k : ℕ) (φ : ℝ) : ℂ := Complex.exp (↑(((j : ℝ) - k) * (θ - φ)) * Complex.I)

lemma Ejk_cont (θ : ℝ) (j k : ℕ) : Continuous (Ejk θ j k) := by unfold Ejk; fun_prop

lemma integral_Ejk (θ : ℝ) (j k : ℕ) :
    ∫ φ in (0 : ℝ)..(2 * π), Ejk θ j k φ = if j = k then (2 * π : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [Ejk]
  · have := integral_exp_int ((j : ℤ) - k) (by omega) θ
    unfold Ejk; push_cast at this ⊢; exact this

lemma fej_eq_Ejk (D : ℕ) (θ φ : ℝ) :
    (fej D (θ - φ) : ℂ) = (1 / ((D : ℂ) + 1)) *
      ∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1), Ejk θ j k φ := by
  rw [fej_expand]; rfl

lemma integral_fej (D : ℕ) (θ : ℝ) : ∫ φ in (0 : ℝ)..(2 * π), fej D (θ - φ) = 2 * π := by
  have hc : (∫ φ in (0 : ℝ)..(2 * π), (fej D (θ - φ) : ℂ)) = 2 * π := by
    simp_rw [fej_eq_Ejk]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (continuous_finsetSum _ (fun k _ => Ejk_cont θ j k)).intervalIntegrable _ _)]
    have hjk : ∀ j ∈ Finset.range (D + 1), (∫ φ in (0 : ℝ)..(2 * π),
        ∑ k ∈ Finset.range (D + 1), Ejk θ j k φ) = 2 * π := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum (fun k _ => (Ejk_cont θ j k).intervalIntegrable _ _)]
      simp_rw [integral_Ejk]
      rw [Finset.sum_ite_eq]; simp [hj]
    rw [Finset.sum_congr rfl hjk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  have : (∫ φ in (0 : ℝ)..(2 * π), (fej D (θ - φ) : ℂ))
      = ((∫ φ in (0 : ℝ)..(2 * π), fej D (θ - φ) : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  rw [this] at hc
  exact_mod_cast hc

/-- **Fejér sums over points with small exponential sums.** -/
lemma sum_fej_ge {ι : Type*} (T : Finset ι) (θ : ι → ℝ) (D : ℕ) (W : ℝ)
    (hW : ∀ m : ℤ, m ≠ 0 → |m| ≤ D →
      ‖∑ p ∈ T, Complex.exp (↑((m : ℝ) * θ p) * Complex.I)‖ ≤ W) (φ : ℝ) :
    (T.card : ℝ) - D * W ≤ ∑ p ∈ T, fej D (θ p - φ) := by
  have hexp : ((∑ p ∈ T, fej D (θ p - φ) : ℝ) : ℂ) = (1 / ((D : ℂ) + 1)) *
      ∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1),
        Complex.exp (↑(-(((j : ℝ) - k) * φ)) * Complex.I) *
          ∑ p ∈ T, Complex.exp (↑((((j : ℤ) - k : ℤ) : ℝ) * θ p) * Complex.I) := by
    push_cast
    simp_rw [fej_expand]
    rw [← Finset.mul_sum]; congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  -- split diagonal and off-diagonal
  set F : ℕ → ℕ → ℂ := fun j k => Complex.exp (↑(-(((j : ℝ) - k) * φ)) * Complex.I) *
      ∑ p ∈ T, Complex.exp (↑((((j : ℤ) - k : ℤ) : ℝ) * θ p) * Complex.I)
  have hdiag : ∀ j, F j j = T.card := by
    intro j; simp [F]
  have hoff : ∀ j k, j ≠ k → j ∈ Finset.range (D + 1) → k ∈ Finset.range (D + 1) → ‖F j k‖ ≤ W := by
    intro j k hjk hj hk
    simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [Finset.mem_range] at hj hk
    exact hW ((j : ℤ) - k) (by omega) (by rw [abs_le]; constructor <;> push_cast <;> omega)
  have hsplit : ∀ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1), F j k
      = T.card + ∑ k ∈ (Finset.range (D + 1)).erase j, F j k := by
    intro j hj; rw [← Finset.add_sum_erase _ _ hj, hdiag]
  have hbound : ‖∑ j ∈ Finset.range (D + 1), ∑ k ∈ (Finset.range (D + 1)).erase j, F j k‖
      ≤ (D + 1) * (D * W) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j ∈ Finset.range (D + 1), (D * W) := by
          refine Finset.sum_le_sum (fun j hj => (norm_sum_le _ _).trans ?_)
          calc _ ≤ ∑ _k ∈ (Finset.range (D + 1)).erase j, W := Finset.sum_le_sum (fun k hk =>
                hoff j k (Finset.ne_of_mem_erase hk).symm hj (Finset.mem_of_mem_erase hk))
            _ = D * W := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hj, Finset.card_range, nsmul_eq_mul]
                simp
      _ = (D + 1) * (D * W) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hexp
  set E := ∑ j ∈ Finset.range (D + 1), ∑ k ∈ (Finset.range (D + 1)).erase j, F j k
  have hD1 : ((D : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero D)
  have hre : (∑ p ∈ T, fej D (θ p - φ) : ℝ) = T.card + (E / ((D : ℂ) + 1)).re := by
    have h := congrArg Complex.re hexp
    rw [Complex.ofReal_re] at h
    rw [h]
    have e : (1 / ((D : ℂ) + 1)) * (((D + 1 : ℕ) : ℂ) * (T.card : ℂ) + E)
        = (T.card : ℂ) + E / ((D : ℂ) + 1) := by
      push_cast; field_simp
    rw [e, Complex.add_re, Complex.natCast_re]
  rw [hre]
  have : |(E / ((D : ℂ) + 1)).re| ≤ D * W := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div]
    have hn : ‖(D : ℂ) + 1‖ = (D : ℝ) + 1 := by
      rw [show ((D : ℂ) + 1) = ((D + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn, div_le_iff₀ (by positivity)]
    linarith [hbound]
  rw [abs_le] at this
  linarith


/-! ### The Fourier transform of the bump near `0` -/

lemma bumpR_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (fun x : ℝ => bumpR δ hδ x) :=
  (bumpR δ hδ).integrable

lemma fourier_psi_zero (δ : ℝ) (hδ : 0 < δ) : 𝓕 (psi δ hδ : ℝ → ℂ) 0 = (Ad δ hδ : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  rw [show (fun v => (psi δ hδ) v) = fun v => ((bumpR δ hδ v : ℝ) : ℂ) from rfl]
  rw [integral_complex_ofReal]; rfl

lemma abs_mul_bumpR_le (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : |x| * bumpR δ hδ x ≤ δ / 2 * bumpR δ hδ x := by
  by_cases h : |x| < δ / 2
  · exact mul_le_mul_of_nonneg_right h.le (bumpR_nonneg δ hδ x)
  · rw [bumpR_eq_zero δ hδ (not_lt.mp h)]; simp

/-- Lipschitz bound for `𝓕ψ` at `0`. -/
lemma fourier_psi_lip (δ : ℝ) (hδ : 0 < δ) (u : ℝ) :
    ‖𝓕 (psi δ hδ : ℝ → ℂ) u - 𝓕 (psi δ hδ : ℝ → ℂ) 0‖ ≤ π * δ * |u| * Ad δ hδ := by
  have hi : Integrable (fun x : ℝ => ((bumpR δ hδ x : ℝ) : ℂ)) := (bumpR_integrable δ hδ).ofReal
  have e : 𝓕 (psi δ hδ : ℝ → ℂ) u - 𝓕 (psi δ hδ : ℝ → ℂ) 0
      = ∫ x : ℝ, (Complex.exp (↑(-2 * π * x * u) * Complex.I) - 1) * ((bumpR δ hδ x : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      ← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [smul_eq_mul, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      rw [show (psi δ hδ) x = ((bumpR δ hδ x : ℝ) : ℂ) from rfl]; ring
    · refine hi.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall (fun x => ?_))
      rw [Complex.norm_exp_ofReal_mul_I]
    · refine hi.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall (fun x => ?_))
      simp
  rw [e]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ x : ℝ, ‖(Complex.exp (↑(-2 * π * x * u) * Complex.I) - 1) * ((bumpR δ hδ x : ℝ) : ℂ)‖
      ≤ π * δ * |u| * bumpR δ hδ x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpR_nonneg δ hδ x)]
    have h1 : ‖Complex.exp (↑(-2 * π * x * u) * Complex.I) - 1‖ ≤ 2 * π * |u| * |x| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * π * x * u)
      rw [mul_comm] at this
      refine this.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs]
      rw [show -2 * π * x * u = -((2 * π) * (x * u)) by ring, abs_neg, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul]
      ring
    have h2 := abs_mul_bumpR_le δ hδ x
    have h0 := bumpR_nonneg δ hδ x
    calc ‖Complex.exp (↑(-2 * π * x * u) * Complex.I) - 1‖ * bumpR δ hδ x
        ≤ 2 * π * |u| * |x| * bumpR δ hδ x := mul_le_mul_of_nonneg_right h1 h0
      _ = 2 * π * |u| * (|x| * bumpR δ hδ x) := by ring
      _ ≤ 2 * π * |u| * (δ / 2 * bumpR δ hδ x) := by gcongr
      _ = π * δ * |u| * bumpR δ hδ x := by ring
  calc ∫ x, ‖(Complex.exp (↑(-2 * π * x * u) * Complex.I) - 1) * ((bumpR δ hδ x : ℝ) : ℂ)‖
      ≤ ∫ x, π * δ * |u| * bumpR δ hδ x := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          ((bumpR_integrable δ hδ).const_mul _) (Filter.Eventually.of_forall hpt)
    _ = π * δ * |u| * Ad δ hδ := by rw [integral_const_mul]; rfl


lemma fej_continuous (D : ℕ) : Continuous (fej D) := by
  unfold fej dsum; fun_prop

/-- **Fejér smoothing, lower bound form.** The modulus `ω` is an explicit hypothesis. -/
lemma smooth_lower {ι : Type*} (T : Finset ι) (θ : ι → ℝ) (D : ℕ) (W : ℝ)
    (hW : ∀ m : ℤ, m ≠ 0 → |m| ≤ D →
      ‖∑ p ∈ T, Complex.exp (↑((m : ℝ) * θ p) * Complex.I)‖ ≤ W)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgc : Continuous g) (ω : ℝ)
    (hω : ∀ θ₀, ∫ φ in (0 : ℝ)..(2 * π), |g θ₀ - g φ| * fej D (θ₀ - φ) ≤ 2 * π * ω) :
    ((T.card : ℝ) - D * W) * ((∫ φ in (0 : ℝ)..(2 * π), g φ) / (2 * π)) - T.card * ω
      ≤ ∑ p ∈ T, g (θ p) := by
  have hpi : 0 < 2 * π := by positivity
  have hfc := fej_continuous D
  have hint : ∀ θ₀, IntervalIntegrable (fun φ => g φ * fej D (θ₀ - φ)) MeasureTheory.volume 0 (2 * π) :=
    fun θ₀ => (hgc.mul (hfc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  -- pointwise: 2π g(θ₀) ≥ ∫ g(φ) fej(θ₀ - φ) - 2π ω
  have hpt : ∀ θ₀, (∫ φ in (0 : ℝ)..(2 * π), g φ * fej D (θ₀ - φ)) - 2 * π * ω ≤ 2 * π * g θ₀ := by
    intro θ₀
    have h1 : (∫ φ in (0 : ℝ)..(2 * π), g θ₀ * fej D (θ₀ - φ)) = 2 * π * g θ₀ := by
      rw [intervalIntegral.integral_const_mul, integral_fej]; ring
    have h2 : (∫ φ in (0 : ℝ)..(2 * π), g φ * fej D (θ₀ - φ))
        ≤ (∫ φ in (0 : ℝ)..(2 * π), g θ₀ * fej D (θ₀ - φ)) +
          ∫ φ in (0 : ℝ)..(2 * π), |g θ₀ - g φ| * fej D (θ₀ - φ) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_mono_on hpi.le (hint θ₀)
        · exact ((continuous_const.mul (hfc.comp (continuous_const.sub continuous_id))).add
            (((continuous_const.sub hgc).abs).mul
              (hfc.comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
        · intro φ _
          have hf := fej_nonneg D (θ₀ - φ)
          have hgφ : g φ ≤ g θ₀ + |g θ₀ - g φ| := by
            have := neg_abs_le (g θ₀ - g φ); linarith
          have := mul_le_mul_of_nonneg_right hgφ hf
          linarith
      · exact (continuous_const.mul (hfc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
      · exact (((continuous_const.sub hgc).abs).mul
          (hfc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
    have h3 := hω θ₀
    linarith
  -- sum over the points
  have hsum : (∫ φ in (0 : ℝ)..(2 * π), g φ * ∑ p ∈ T, fej D (θ p - φ)) - T.card * (2 * π * ω)
      ≤ 2 * π * ∑ p ∈ T, g (θ p) := by
    have e : (∫ φ in (0 : ℝ)..(2 * π), g φ * ∑ p ∈ T, fej D (θ p - φ))
        = ∑ p ∈ T, ∫ φ in (0 : ℝ)..(2 * π), g φ * fej D (θ p - φ) := by
      simp_rw [Finset.mul_sum]
      exact intervalIntegral.integral_finsetSum (fun p _ => hint (θ p))
    rw [e, Finset.mul_sum]
    have := Finset.sum_le_sum (fun p (_ : p ∈ T) => hpt (θ p))
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at this
    linarith
  -- lower bound the smoothed integral
  have hlow : ((T.card : ℝ) - D * W) * ∫ φ in (0 : ℝ)..(2 * π), g φ
      ≤ ∫ φ in (0 : ℝ)..(2 * π), g φ * ∑ p ∈ T, fej D (θ p - φ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hpi.le
    · exact (continuous_const.mul hgc).intervalIntegrable _ _
    · exact (hgc.mul (continuous_finsetSum _ (fun p _ =>
        hfc.comp (continuous_const.sub continuous_id)))).intervalIntegrable _ _
    · intro φ _
      have := sum_fej_ge T θ D W hW φ
      have := hg0 φ
      nlinarith
  have : ((T.card : ℝ) - D * W) * ((∫ φ in (0 : ℝ)..(2 * π), g φ) / (2 * π))
      = (((T.card : ℝ) - D * W) * ∫ φ in (0 : ℝ)..(2 * π), g φ) / (2 * π) := by ring
  rw [this, sub_le_iff_le_add, div_le_iff₀ hpi]
  nlinarith


lemma norm_dsum_le (D : ℕ) (x : ℝ) : ‖dsum D x‖ ≤ D + 1 := by
  unfold dsum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j ∈ Finset.range (D + 1), ‖Complex.exp (↑((j : ℝ) * x) * Complex.I)‖ = 1 :=
    fun j _ => Complex.norm_exp_ofReal_mul_I _
  rw [Finset.sum_congr rfl this]; simp

lemma norm_dsum_le' (D : ℕ) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ π) : ‖dsum D x‖ ≤ π / |x| := by
  have hpi := Real.pi_pos
  set w := Complex.exp (↑x * Complex.I) with hw
  have hw1 : ‖w - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [hw, show (↑x * Complex.I) = Complex.I * ↑x by ring, Complex.norm_exp_I_mul_ofReal_sub_one,
      Real.norm_eq_abs, abs_mul, abs_two]
  have hs : |x| / π ≤ |Real.sin (x / 2)| := by
    have hx2 : |x / 2| ≤ π / 2 := by rw [abs_div, abs_two]; linarith
    rcases le_total 0 x with h | h
    · have h' : 0 ≤ x / 2 := by linarith
      have := Real.mul_le_sin h' (by rw [abs_of_nonneg h'] at hx2; exact hx2)
      rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h' (by
        rw [abs_of_nonneg h'] at hx2; linarith [Real.pi_pos]))]
      have e : 2 / π * (x / 2) = x / π := by field_simp
      linarith
    · have h' : 0 ≤ -(x / 2) := by linarith
      have := Real.mul_le_sin h' (by rw [abs_of_nonpos (by linarith)] at hx2; linarith)
      rw [Real.sin_neg] at this
      have hnn : 0 ≤ 2 / π * -(x / 2) := mul_nonneg (by positivity) h'
      rw [abs_of_nonpos h, abs_of_nonpos (by linarith : Real.sin (x / 2) ≤ 0)]
      have e : 2 / π * -(x / 2) = -x / π := by field_simp
      linarith
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have hwne : w ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hw1
    have : 0 < |Real.sin (x / 2)| := lt_of_lt_of_le (by positivity) hs
    linarith
  have hgeom : dsum D x = ∑ j ∈ Finset.range (D + 1), w ^ j := by
    unfold dsum
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hw, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hgeom, geom_sum_eq hwne, norm_div, hw1]
  have hnum : ‖w ^ (D + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hw, Complex.norm_exp_ofReal_mul_I, one_pow, norm_one]; norm_num
  have hden : 0 < 2 * |Real.sin (x / 2)| := by
    have : 0 < |Real.sin (x / 2)| := lt_of_lt_of_le (by positivity) hs
    positivity
  rw [div_le_div_iff₀ hden hxpos]
  have : 2 * |x| ≤ π * (2 * |Real.sin (x / 2)|) := by
    rw [div_le_iff₀ hpi] at hs; linarith
  nlinarith [norm_nonneg (w ^ (D + 1) - 1)]


lemma dsum_periodic (D : ℕ) : Function.Periodic (dsum D) (2 * π) := by
  intro x
  unfold dsum
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : Complex.exp (↑((j : ℝ) * (2 * π)) * Complex.I) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (j : ℤ)
    rw [← this]; congr 1; push_cast; ring
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add, this, mul_one]

lemma fej_periodic (D : ℕ) : Function.Periodic (fej D) (2 * π) := by
  intro x; unfold fej; rw [dsum_periodic D x]

lemma fej_le (D : ℕ) (x : ℝ) : fej D x ≤ D + 1 := by
  unfold fej
  have h := norm_dsum_le D x
  have h0 := norm_nonneg (dsum D x)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma abs_mul_fej_le (D : ℕ) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ π) :
    |x| * fej D x ≤ π ^ 2 / ((D + 1) * |x|) := by
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have h := norm_dsum_le' D hx0 hx
  have h0 := norm_nonneg (dsum D x)
  unfold fej
  have h2 : ‖dsum D x‖ ^ 2 ≤ (π / |x|) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [div_pow] at h2
  have hD : (0 : ℝ) < D + 1 := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
  calc |x| * ‖dsum D x‖ ^ 2 * ((D + 1) * |x|) = (|x| ^ 2 * ‖dsum D x‖ ^ 2) * (D + 1) := by ring
    _ ≤ (|x| ^ 2 * (π ^ 2 / |x| ^ 2)) * (D + 1) := by gcongr
    _ = π ^ 2 * (D + 1) := by field_simp

/-- **The Fejér modulus.** -/
lemma integral_abs_fej_le (D : ℕ) :
    ∫ x in (-π)..π, |x| * fej D x ≤ 2 / (D + 1) + 2 * π ^ 2 * Real.log (π * (D + 1)) / (D + 1) := by
  have hpi := Real.pi_pos
  have hD : (0 : ℝ) < D + 1 := by positivity
  set a := 1 / ((D : ℝ) + 1) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hD]; linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have haπ : a < π := lt_of_le_of_lt ha1 (by linarith [Real.pi_gt_three])
  have hc : Continuous fun x : ℝ => |x| * fej D x := continuous_abs.mul (fej_continuous D)
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun x : ℝ => |x| * fej D x) MeasureTheory.volume u v :=
    fun u v => hc.intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-π) (-a)) (hi (-a) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-a) a) (hi a π)]
  -- middle
  have hmid : ∫ x in (-a)..a, |x| * fej D x ≤ 2 / (D + 1) := by
    have : ∫ x in (-a)..a, |x| * fej D x ≤ ∫ _x in (-a)..a, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith) (hi _ _) (by simp)
      intro x hx
      have hxa : |x| ≤ a := abs_le.mpr ⟨hx.1, hx.2⟩
      have := fej_le D x
      have := fej_nonneg D x
      calc |x| * fej D x ≤ a * (D + 1) := by gcongr
        _ = 1 := by rw [ha]; field_simp
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    have e : a - -a = 2 / (D + 1) := by rw [ha]; ring
    linarith
  -- right piece
  have hright : ∫ x in a..π, |x| * fej D x ≤ π ^ 2 * Real.log (π * (D + 1)) / (D + 1) := by
    have : ∫ x in a..π, |x| * fej D x ≤ ∫ x in a..π, π ^ 2 / (D + 1) * x⁻¹ := by
      apply intervalIntegral.integral_mono_on haπ.le (hi _ _)
      · exact (continuousOn_const.mul (continuousOn_inv₀.mono (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1]))).intervalIntegrable_of_Icc haπ.le
      · intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
        have hb := abs_mul_fej_le D hx0.ne' (by rw [abs_of_pos hx0]; exact hx.2)
        rw [abs_of_pos hx0] at hb ⊢
        calc x * fej D x ≤ π ^ 2 / ((D + 1) * x) := hb
          _ = π ^ 2 / (D + 1) * x⁻¹ := by field_simp
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hpi] at this
    have e : π / a = π * (D + 1) := by rw [ha]; field_simp
    rw [e] at this
    calc _ ≤ π ^ 2 / (D + 1) * Real.log (π * (D + 1)) := this
      _ = _ := by ring
  -- left piece, by symmetry
  have hleft : ∫ x in (-π)..(-a), |x| * fej D x ≤ π ^ 2 * Real.log (π * (D + 1)) / (D + 1) := by
    have : ∫ x in (-π)..(-a), |x| * fej D x ≤ ∫ x in (-π)..(-a), π ^ 2 / (D + 1) * (-x)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) (hi _ _)
      · exact (continuousOn_const.mul ((continuousOn_inv₀.comp continuousOn_neg (fun x hx => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.2])))).intervalIntegrable_of_Icc
          (by linarith)
      · intro x hx
        have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
        have hb := abs_mul_fej_le D hx0.ne (by rw [abs_of_neg hx0]; linarith [hx.1])
        rw [abs_of_neg hx0] at hb ⊢
        calc -x * fej D x ≤ π ^ 2 / ((D + 1) * -x) := hb
          _ = π ^ 2 / (D + 1) * (-x)⁻¹ := by field_simp
    have hsym : ∫ x in (-π)..(-a), π ^ 2 / (D + 1) * (-x)⁻¹ = ∫ x in a..π, π ^ 2 / (D + 1) * x⁻¹ := by
      rw [intervalIntegral.integral_comp_neg (fun x => π ^ 2 / (D + 1) * x⁻¹)]
      simp
    rw [hsym, intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hpi] at this
    have e : π / a = π * (D + 1) := by rw [ha]; field_simp
    rw [e] at this
    calc _ ≤ π ^ 2 / (D + 1) * Real.log (π * (D + 1)) := this
      _ = _ := by ring
  have e2 : 2 * π ^ 2 * Real.log (π * (D + 1)) / (D + 1)
      = π ^ 2 * Real.log (π * (D + 1)) / (D + 1) + π ^ 2 * Real.log (π * (D + 1)) / (D + 1) := by ring
  rw [e2]
  linarith

/-- The Fejér modulus for a Lipschitz periodic function. -/
lemma fej_modulus (D : ℕ) (g : ℝ → ℝ) (hper : Function.Periodic g (2 * π)) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y, |g x - g y| ≤ L * |x - y|) (hgc : Continuous g) (θ₀ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), |g θ₀ - g φ| * fej D (θ₀ - φ)
      ≤ L * (2 / (D + 1) + 2 * π ^ 2 * Real.log (π * (D + 1)) / (D + 1)) := by
  set F : ℝ → ℝ := fun x => |g θ₀ - g (θ₀ - x)| * fej D x with hF
  have hFc : Continuous F := by
    simp only [hF]; exact ((continuous_const.sub (hgc.comp (continuous_const.sub continuous_id))).abs).mul
      (fej_continuous D)
  have hFper : Function.Periodic F (2 * π) := by
    intro x
    simp only [hF]
    rw [fej_periodic D x, show θ₀ - (x + 2 * π) = (θ₀ - x) - 2 * π by ring, hper.sub_eq]
  have e1 : ∫ φ in (0 : ℝ)..(2 * π), |g θ₀ - g φ| * fej D (θ₀ - φ)
      = ∫ φ in (0 : ℝ)..(2 * π), F (θ₀ - φ) := by
    refine intervalIntegral.integral_congr (fun φ _ => ?_)
    simp only [hF, sub_sub_cancel]
  rw [e1, intervalIntegral.integral_comp_sub_left F θ₀]
  have e2 : ∫ x in (θ₀ - 2 * π)..(θ₀ - 0), F x = ∫ x in (-π)..(-π + 2 * π), F x := by
    rw [show θ₀ - 0 = (θ₀ - 2 * π) + 2 * π by ring]
    exact hFper.intervalIntegral_add_eq _ _
  rw [e2, show -π + 2 * π = π by ring]
  calc ∫ x in (-π)..π, F x ≤ ∫ x in (-π)..π, L * (|x| * fej D x) := by
        apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) (hFc.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_abs.mul (fej_continuous D))).intervalIntegrable _ _)
        intro x _
        simp only [hF]
        have h1 := hL θ₀ (θ₀ - x)
        rw [show θ₀ - (θ₀ - x) = x by ring] at h1
        have := fej_nonneg D x
        calc |g θ₀ - g (θ₀ - x)| * fej D x ≤ L * |x| * fej D x := by gcongr
          _ = L * (|x| * fej D x) := by ring
    _ = L * ∫ x in (-π)..π, |x| * fej D x := intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_fej_le D) hL0


/-! ### The intermediate region, one point -/

lemma abs_sin_sq_sub (a b : ℝ) : |Real.sin a ^ 2 - Real.sin b ^ 2| ≤ |a - b| := by
  have e : Real.sin a ^ 2 - Real.sin b ^ 2 = (Real.sin a - Real.sin b) * (Real.sin a + Real.sin b) := by
    ring
  rw [e, abs_mul]
  have h1 := Real.abs_sin_sub_sin_le a b
  have h2 : |Real.sin a + Real.sin b| ≤ 2 := by
    refine (abs_add_le _ _).trans ?_
    linarith [Real.abs_sin_le_one a, Real.abs_sin_le_one b]
  -- |sin a - sin b| * |sin a + sin b| = |sin(a-b)| * |sin(a+b)| ≤ |a - b|
  have e2 : (Real.sin a - Real.sin b) * (Real.sin a + Real.sin b) = Real.sin (a - b) * Real.sin (a + b) := by
    rw [Real.sin_sub, Real.sin_add]
    have := Real.sin_sq_add_cos_sq a
    have := Real.sin_sq_add_cos_sq b
    nlinarith
  rw [← abs_mul, e2, abs_mul]
  have h3 : |Real.sin (a - b)| ≤ |a - b| := Real.abs_sin_le_abs
  have h4 := Real.abs_sin_le_one (a + b)
  have h5 := abs_nonneg (Real.sin (a - b))
  nlinarith

/-- The type-`B` exponential sums at multiples of `ξ`. -/
lemma weyl_B (t : Fin (K n) → Bool) (ht : Typical n t) (ξ : ℝ) (hnr : NR1 n ξ) (m : ℤ)
    (hm : m ≠ 0) (hmD : |m| ≤ Dn n) :
    ‖∑ p ∈ univ.filter (fun p => t p = false),
        Complex.exp (↑((m : ℝ) * (kk n p * ξ)) * Complex.I)‖
      ≤ 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ) := by
  set x := (m : ℝ) * ξ
  have hsplit : ∑ p ∈ univ.filter (fun p => t p = false),
      Complex.exp (↑((m : ℝ) * (kk n p * ξ)) * Complex.I)
      = (1 / 2 : ℂ) * ∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I) + Ssum t x := by
    rw [Finset.sum_filter]
    unfold Ssum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have e : Complex.exp (↑((m : ℝ) * (kk n p * ξ)) * Complex.I)
        = Complex.exp (↑(kk n p * x) * Complex.I) := by congr 2; simp only [x]; ring
    rw [e]
    cases t p <;> simp <;> ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (ht x))
  -- the Dirichlet part
  have hm1 : 1 ≤ m.natAbs := by omega
  have hmD' : m.natAbs ≤ Dn n := by
    have : (m.natAbs : ℤ) ≤ Dn n := by rw [Int.natCast_natAbs]; exact hmD
    omega
  have hs := hnr m.natAbs hm1 hmD'
  have hsx : εn n ≤ |Real.sin x| := by
    simp only [x]; rw [abs_sin_int_mul]; exact hs
  have hε : 0 < εn n := Real.rpow_pos_of_pos (by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [Dn] at hmD'; omega
    · exact_mod_cast h) _
  have hs0 : Real.sin x ≠ 0 := by
    intro h; rw [h, abs_zero] at hsx; linarith
  have hd := dirichlet n x hs0
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I)‖
      ≤ 1 / 2 * (1 / |Real.sin x|) := by gcongr
    _ ≤ 1 / 2 * (1 / εn n) := by gcongr
    _ = 1 / (2 * εn n) := by ring


/-- The Fejér modulus constant. -/
def Ωf (D : ℕ) : ℝ := 2 / (D + 1) + 2 * π ^ 2 * Real.log (π * (D + 1)) / (D + 1)

lemma sin_sq_sin_lip (s : ℝ) (x y : ℝ) :
    |Real.sin (s * Real.sin x) ^ 2 - Real.sin (s * Real.sin y) ^ 2| ≤ |s| * |x - y| := by
  refine (abs_sin_sq_sub _ _).trans ?_
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le x y) (abs_nonneg s)

open scoped Classical in
/-- **Intermediate region, one point.** -/
lemma inter1 (t : Fin (K n) → Bool) (ht : Typical n t) (ξ : ℝ) (hnr : NR1 n ξ) (s : ℝ)
    (hs : 1 / 3 ≤ |s|)
    (hBW : (Dn n : ℝ) * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ))
      ≤ ((univ.filter fun p => t p = false).card : ℝ)) :
    (((univ.filter fun p => t p = false).card : ℝ) -
        Dn n * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ))) * (1 / (400 * π))
      - ((univ.filter fun p => t p = false).card : ℝ) * (|s| * Ωf (Dn n) / (2 * π))
      ≤ ∑ p ∈ univ.filter (fun p => t p = false), Real.sin (s * Real.sin (kk n p * ξ)) ^ 2 := by
  set B := univ.filter fun p : Fin (K n) => t p = false
  set W := 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)
  set g : ℝ → ℝ := fun θ => Real.sin (s * Real.sin θ) ^ 2 with hg
  have hpi := Real.pi_pos
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hper : Function.Periodic g (2 * π) := by
    intro x; simp only [hg, Real.sin_add_two_pi]
  have hmod := fun θ₀ => fej_modulus (Dn n) g hper |s| (abs_nonneg s)
    (fun x y => sin_sq_sin_lip s x y) hgc θ₀
  have hsm := smooth_lower B (fun p => kk n p * ξ) (Dn n) W
    (fun m hm hmD => weyl_B t ht ξ hnr m hm hmD) g (fun x => sq_nonneg _) hgc
    (|s| * Ωf (Dn n) / (2 * π)) (fun θ₀ => by
      have := hmod θ₀
      unfold Ωf
      have e : 2 * π * (|s| * (2 / ((Dn n : ℝ) + 1) + 2 * π ^ 2 * Real.log (π * ((Dn n : ℝ) + 1)) /
          ((Dn n : ℝ) + 1)) / (2 * π)) = |s| * (2 / ((Dn n : ℝ) + 1) + 2 * π ^ 2 *
          Real.log (π * ((Dn n : ℝ) + 1)) / ((Dn n : ℝ) + 1)) := by field_simp
      rw [e]; exact this)
  -- the mean of g
  have hmean : 1 / (400 * π) ≤ (∫ φ in (0 : ℝ)..(2 * π), g φ) / (2 * π) := by
    have h1 := quarter_mean s 0 hs
    simp only [add_zero] at h1
    have h2 : ∫ θ in (0 : ℝ)..(π / 2), g θ ≤ ∫ θ in (0 : ℝ)..(2 * π), g θ :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) (hgc.intervalIntegrable _ _)
    rw [le_div_iff₀ (by positivity)]
    have e : 1 / (400 * π) * (2 * π) = 1 / 200 := by field_simp; ring
    rw [e]
    simp only [hg] at h2
    linarith
  have h0 : (0 : ℝ) ≤ (B.card : ℝ) - Dn n * W := by linarith
  have := mul_le_mul_of_nonneg_left hmean h0
  simp only [hg] at hsm
  linarith


/-! ### Core region: the cosine product is Gaussian -/

lemma prod_cos_upper {k : ℕ} (x : Fin k → ℝ) (hx : ∀ p, |x p| ≤ 1 / 2) :
    ∏ p, Real.cos (x p) ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + ∑ p, x p ^ 4) := by
  have h : ∀ p, Real.cos (x p) ≤ Real.exp (-(x p ^ 2) / 2 + x p ^ 4) := fun p => cos_le_exp_core (hx p)
  have h0 : ∀ p, 0 ≤ Real.cos (x p) := fun p => Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp (hx p)).1, Real.pi_gt_three], by linarith [(abs_le.mp (hx p)).2,
      Real.pi_gt_three]⟩
  calc ∏ p, Real.cos (x p) ≤ ∏ p, Real.exp (-(x p ^ 2) / 2 + x p ^ 4) :=
        Finset.prod_le_prod (fun p _ => h0 p) (fun p _ => h p)
    _ = Real.exp (∑ p, (-(x p ^ 2) / 2 + x p ^ 4)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ p, x p ^ 2) / 2 + ∑ p, x p ^ 4) := by
        congr 1
        rw [show (∑ p, (-(x p ^ 2) / 2 + x p ^ 4)) = (-1 / 2) * ∑ p, x p ^ 2 + ∑ p, x p ^ 4 by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun p _ => by ring)]
        ring

lemma prod_cos_lower {k : ℕ} (x : Fin k → ℝ) (hx : ∀ p, |x p| ≤ 1 / 2) :
    Real.exp (-(∑ p, x p ^ 2) / 2 - 2 * ∑ p, x p ^ 4) ≤ ∏ p, Real.cos (x p) := by
  have h : ∀ p, Real.exp (-(x p ^ 2) / 2 - 2 * x p ^ 4) ≤ Real.cos (x p) :=
    fun p => exp_le_cos_core (hx p)
  calc Real.exp (-(∑ p, x p ^ 2) / 2 - 2 * ∑ p, x p ^ 4)
      = ∏ p, Real.exp (-(x p ^ 2) / 2 - 2 * x p ^ 4) := by
        rw [← Real.exp_sum]; congr 1
        rw [show (∑ p, (-(x p ^ 2) / 2 - 2 * x p ^ 4)) = (-1 / 2) * ∑ p, x p ^ 2 - 2 * ∑ p, x p ^ 4 by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun p _ => by ring)]
        ring
    _ ≤ ∏ p, Real.cos (x p) :=
        Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) (fun p _ => h p)

end K525


namespace K525

variable {n : ℕ}

/-! ## S1: the single-point smoothed local limit -/

lemma fourier_psi_le (δ : ℝ) (hδ : 0 < δ) (u : ℝ) : ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ Ad δ hδ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold Ad
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [show (psi δ hδ) x = ((bumpR δ hδ x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bumpR_nonneg δ hδ x)]

open scoped Classical in
lemma card_B_ge (t : Fin (K n) → Bool) (ht : Typical n t) :
    (K n : ℝ) / 2 - (n : ℝ) ^ (3 / 5 : ℝ) ≤ ((univ.filter fun p => t p = false).card : ℝ) := by
  have h0 := (abs_re_le_norm' (Ssum t 0)).trans (ht 0)
  rw [re_Ssum] at h0
  have hs : ∑ p, sg (t p) * (Real.cos (kk n p * 0) / 2)
      = ((univ.filter fun p => t p = false).card : ℝ) - (K n : ℝ) / 2 := by
    have : ∀ p : Fin (K n), sg (t p) * (Real.cos (kk n p * 0) / 2)
        = (if t p = false then (1 : ℝ) else 0) - 1 / 2 := by
      intro p; cases t p <;> simp [sg] <;> norm_num
    rw [Finset.sum_congr rfl (fun p _ => this p), Finset.sum_sub_distrib, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hs] at h0
  have := (abs_le.mp h0).1
  linarith

/-- The cosine product. -/
def Pc (t : Fin (K n) → Bool) (ξ u : ℝ) : ℝ := ∏ p, Real.cos (2 * π * u * wv t ξ p)

lemma abs_wv_le (t : Fin (K n) → Bool) (ξ : ℝ) (p : Fin (K n)) : |wv t ξ p| ≤ 2 := by
  unfold wv
  split_ifs
  · simp
  · rw [abs_mul, abs_two]
    have := Real.abs_sin_le_one (kk n p * ξ)
    linarith

lemma abs_x_le (t : Fin (K n) → Bool) (ξ u : ℝ) (p : Fin (K n)) :
    |2 * π * u * wv t ξ p| ≤ 4 * π * |u| := by
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc 2 * π * |u| * |wv t ξ p| ≤ 2 * π * |u| * 2 :=
        mul_le_mul_of_nonneg_left (abs_wv_le t ξ p) (by positivity)
    _ = 4 * π * |u| := by ring

lemma sum_x_sq (t : Fin (K n) → Bool) (ξ u : ℝ) :
    ∑ p, (2 * π * u * wv t ξ p) ^ 2 = 4 * π ^ 2 * u ^ 2 * Vv t ξ := by
  unfold Vv
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by ring)

lemma abs_Pc_le_one (t : Fin (K n) → Bool) (ξ u : ℝ) : |Pc t ξ u| ≤ 1 := by
  unfold Pc
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun p _ => abs_nonneg _) (fun p _ => Real.abs_cos_le_one _)

lemma Pc_continuous (t : Fin (K n) → Bool) (ξ : ℝ) : Continuous (fun u => Pc t ξ u) := by
  unfold Pc
  exact continuous_finset_prod _ (fun p _ => by fun_prop)

lemma Pc_core (t : Fin (K n) → Bool) (ξ u τ : ℝ) (hu : |u| ≤ τ) (hτ : 4 * π * τ ≤ 1 / 2) :
    Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) * Real.exp (-(2 * ((K n : ℝ) * (4 * π * τ) ^ 4)))
        ≤ Pc t ξ u ∧
      Pc t ξ u ≤ Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) * Real.exp ((K n : ℝ) * (4 * π * τ) ^ 4) := by
  set x : Fin (K n) → ℝ := fun p => 2 * π * u * wv t ξ p with hx
  have hxb : ∀ p, |x p| ≤ 4 * π * τ := fun p =>
    (abs_x_le t ξ u p).trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have hx2 : ∀ p, |x p| ≤ 1 / 2 := fun p => (hxb p).trans hτ
  have hsq : ∑ p, x p ^ 2 = 4 * π ^ 2 * u ^ 2 * Vv t ξ := sum_x_sq t ξ u
  have h4 : ∑ p, x p ^ 4 ≤ (K n : ℝ) * (4 * π * τ) ^ 4 := by
    calc ∑ p, x p ^ 4 ≤ ∑ _p : Fin (K n), (4 * π * τ) ^ 4 := Finset.sum_le_sum (fun p _ => by
          have e : |x p| ^ 4 = x p ^ 4 := Even.pow_abs ⟨2, rfl⟩ _
          rw [← e]; exact pow_le_pow_left₀ (abs_nonneg _) (hxb p) 4)
      _ = (K n : ℝ) * (4 * π * τ) ^ 4 := by simp
  have h40 : 0 ≤ ∑ p, x p ^ 4 := Finset.sum_nonneg (fun p _ => by positivity)
  have hu' := prod_cos_upper x hx2
  have hl' := prod_cos_lower x hx2
  constructor
  · calc Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) * Real.exp (-(2 * ((K n : ℝ) * (4 * π * τ) ^ 4)))
        = Real.exp (-(∑ p, x p ^ 2) / 2 - 2 * ((K n : ℝ) * (4 * π * τ) ^ 4)) := by
          rw [← Real.exp_add, hsq]; congr 1; ring
      _ ≤ Real.exp (-(∑ p, x p ^ 2) / 2 - 2 * ∑ p, x p ^ 4) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Pc t ξ u := hl'
  · calc Pc t ξ u ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + ∑ p, x p ^ 4) := hu'
      _ ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + (K n : ℝ) * (4 * π * τ) ^ 4) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [← Real.exp_add, hsq]; congr 1; ring

lemma Pc_mid (t : Fin (K n) → Bool) (ξ u : ℝ) (hu : 4 * π * |u| ≤ 1 / 2) :
    0 ≤ Pc t ξ u ∧ Pc t ξ u ≤ Real.exp (-(π ^ 2 * Vv t ξ) * u ^ 2) := by
  set x : Fin (K n) → ℝ := fun p => 2 * π * u * wv t ξ p with hx
  have hx2 : ∀ p, |x p| ≤ 1 / 2 := fun p => (abs_x_le t ξ u p).trans hu
  have hsq : ∑ p, x p ^ 2 = 4 * π ^ 2 * u ^ 2 * Vv t ξ := sum_x_sq t ξ u
  have h4 : ∑ p, x p ^ 4 ≤ (∑ p, x p ^ 2) / 4 := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have h := hx2 p
    have h2 : x p ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (x p)]
    have e : x p ^ 4 = x p ^ 2 * x p ^ 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (x p)]
  have hcos : ∀ p, 0 ≤ Real.cos (x p) := fun p => Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp (hx2 p)).1, Real.pi_gt_three],
      by linarith [(abs_le.mp (hx2 p)).2, Real.pi_gt_three]⟩
  refine ⟨Finset.prod_nonneg (fun p _ => hcos p), ?_⟩
  calc Pc t ξ u ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + ∑ p, x p ^ 4) := prod_cos_upper x hx2
    _ ≤ Real.exp (-(∑ p, x p ^ 2) / 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [hsq]; congr 1; ring

open scoped Classical in
lemma abs_Pc_inter (t : Fin (K n) → Bool) (ξ u : ℝ) :
    |Pc t ξ u| ≤ Real.exp (-(∑ p ∈ univ.filter (fun p => t p = false),
      Real.sin ((4 * π * u) * Real.sin (kk n p * ξ)) ^ 2) / 2) := by
  have hs : ∑ p, Real.sin (2 * π * u * wv t ξ p) ^ 2 = ∑ p ∈ univ.filter (fun p => t p = false),
      Real.sin ((4 * π * u) * Real.sin (kk n p * ξ)) ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold wv
    cases t p
    · simp only [Bool.false_eq_true, if_false, if_true]
      ring_nf
    · simp
  unfold Pc
  rw [Finset.abs_prod, ← hs]
  calc ∏ p, |Real.cos (2 * π * u * wv t ξ p)|
      ≤ ∏ p, Real.exp (-(Real.sin (2 * π * u * wv t ξ p) ^ 2) / 2) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => abs_cos_le_exp _)
    _ = Real.exp (∑ p, (-(Real.sin (2 * π * u * wv t ξ p) ^ 2) / 2)) := (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [show (∑ p, (-(Real.sin (2 * π * u * wv t ξ p) ^ 2) / 2))
            = (-1 / 2) * ∑ p, Real.sin (2 * π * u * wv t ξ p) ^ 2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)]
        ring

/-- Far region: `𝓕ψ` is small beyond `N ^ (1/100)`. -/
lemma fourier_far (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ u : ℝ,
    N ^ (1 / 100 : ℝ) ≤ |u| → ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ 2 * C / N * (1 + u ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := fourier_psi_decay δ hδ 102
  refine ⟨C, hC0, fun N hN u hu => ?_⟩
  have hT1 : 1 ≤ N ^ (1 / 100 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hu1 : 1 ≤ |u| := hT1.trans hu
  have hu0 : 0 < |u| := by linarith
  have hN100 : N ≤ |u| ^ (100 : ℕ) := by
    calc N = (N ^ (1 / 100 : ℝ)) ^ (100 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ |u| ^ (100 : ℕ) := pow_le_pow_left₀ (by positivity) hu 100
  have hb := hC u
  have hu2 : 1 ≤ u ^ 2 := by rw [← sq_abs]; nlinarith
  have h1 : ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ C / (|u| ^ 100 * u ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have e : |u| ^ 102 = |u| ^ 100 * u ^ 2 := by
      rw [show (102 : ℕ) = 100 + 2 from rfl, pow_add, sq_abs]
    rw [← e, mul_comm]; exact hb
  have h2 : C / (|u| ^ 100 * u ^ 2) ≤ 2 * C / (N * (1 + u ^ 2)) := by
    have hA : N * (1 + u ^ 2) ≤ |u| ^ 100 * (2 * u ^ 2) :=
      mul_le_mul hN100 (by linarith) (by positivity) (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hA hC0]
  rw [← div_eq_mul_inv, div_div]
  exact h1.trans h2

lemma E1_eq (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ : ℝ) :
    ((E1 δ hδ t ξ : ℝ) : ℂ) = ∫ u : ℝ, 𝓕 (psi δ hδ : ℝ → ℂ) u * ((Pc t ξ u : ℝ) : ℂ) := by
  have h := avg_schwartz (psi δ hδ) (wv t ξ)
  rw [Fintype.card_fin] at h
  have hb : ∀ b : Fin (K n) → ℤˣ, psi δ hδ (∑ p, ((b p : ℤ) : ℝ) * wv t ξ p)
      = ((bumpR δ hδ (IIt t b ξ) : ℝ) : ℂ) := by
    intro b; rw [psi_apply, IIt_eq]
  simp_rw [hb] at h
  unfold E1
  push_cast
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Pc, Complex.ofReal_prod]

lemma gauss_int (A V : ℝ) (hV : 0 < V) :
    ∫ u : ℝ, A * Real.exp (-(2 * π ^ 2 * V) * u ^ 2) = A / Real.sqrt (2 * π * V) := by
  rw [integral_const_mul, integral_gaussian, div_eq_mul_inv A, ← Real.sqrt_inv]
  congr 1; congr 1
  have := Real.pi_pos.ne'
  field_simp

lemma sqrt_gauss_half (V : ℝ) (hV : 0 < V) :
    Real.sqrt (π / (π ^ 2 * V / 2)) = 2 / Real.sqrt (2 * π * V) := by
  have hpi := Real.pi_pos
  have h0 : 0 < Real.sqrt (2 * π * V) := Real.sqrt_pos.mpr (by positivity)
  rw [eq_div_iff h0.ne', ← Real.sqrt_mul (by positivity)]
  have e : π / (π ^ 2 * V / 2) * (2 * π * V) = 2 ^ 2 := by field_simp
  rw [e, Real.sqrt_sq (by norm_num)]

/-- The majorant and its integral. -/
lemma H_integrable (A κ E L C T V : ℝ) (hV : 0 < V) :
    Integrable (fun u : ℝ => A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2) +
      2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2) +
      (Set.Icc (-T) T).indicator (fun _ => L) u + C * (1 + u ^ 2)⁻¹) := by
  have hpi := Real.pi_pos
  have iH1 : Integrable (fun u : ℝ => A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have iH2 : Integrable (fun u : ℝ => 2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have iH3 : Integrable (fun u : ℝ => (Set.Icc (-T) T).indicator (fun _ => L) u) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have iH4 : Integrable (fun u : ℝ => C * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  exact ((iH1.add iH2).add iH3).add iH4

lemma H_integral (A κ E L C T V : ℝ) (hV : 0 < V) (hT : 0 ≤ T) :
    ∫ u : ℝ, (A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2) +
      2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2) +
      (Set.Icc (-T) T).indicator (fun _ => L) u + C * (1 + u ^ 2)⁻¹)
      = A / Real.sqrt (2 * π * V) * (κ + 4 * E) + L * (2 * T) + C * π := by
  have hpi := Real.pi_pos
  have iH1 : Integrable (fun u : ℝ => A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have iH2 : Integrable (fun u : ℝ => 2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have iH3 : Integrable (fun u : ℝ => (Set.Icc (-T) T).indicator (fun _ => L) u) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have iH4 : Integrable (fun u : ℝ => C * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  have i12 : Integrable (fun u : ℝ => A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2) +
      2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2)) := iH1.add iH2
  have i123 : Integrable (fun u : ℝ => A * κ * Real.exp (-(2 * π ^ 2 * V) * u ^ 2) +
      2 * A * E * Real.exp (-(π ^ 2 * V / 2) * u ^ 2) +
      (Set.Icc (-T) T).indicator (fun _ => L) u) := i12.add iH3
  rw [integral_add i123 iH4, integral_add i12 iH3, integral_add iH1 iH2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_indicator_const _ measurableSet_Icc,
    integral_univ_inv_one_add_sq, integral_gaussian, integral_gaussian, Real.volume_real_Icc_of_le
      (by linarith), smul_eq_mul, sqrt_gauss_half V hV]
  have e1 : Real.sqrt (π / (2 * π ^ 2 * V)) = 1 / Real.sqrt (2 * π * V) := by
    rw [← (Real.sqrt_inv _).trans (inv_eq_one_div _)]
    congr 1
    field_simp
  rw [e1]
  ring

/-- **S1, pointwise majorant (abstract form).** -/
lemma S1_pt (F : ℂ) (P g h A κ E L C τ T u : ℝ) (hA0 : 0 < A) (hFle : ‖F‖ ≤ A)
    (hP1 : |P| ≤ 1) (hκ0 : 0 ≤ κ) (hE0 : 0 ≤ E) (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hL0 : 0 ≤ L)
    (hC0 : 0 ≤ C)
    (hcore : |u| ≤ τ → ‖F * (P : ℂ) - ((A * g : ℝ) : ℂ)‖ ≤ A * κ * g)
    (hgE : τ < |u| → g ≤ E * h)
    (hmid : τ < |u| → 4 * π * |u| ≤ 1 / 2 → |P| ≤ E * h)
    (hinter : 1 / 2 < 4 * π * |u| → |u| ≤ T → |P| * A ≤ L)
    (hfar : T < |u| → ‖F‖ ≤ C * (1 + u ^ 2)⁻¹) :
    ‖F * (P : ℂ) - ((A * g : ℝ) : ℂ)‖ ≤
      A * κ * g + 2 * A * E * h + (Set.Icc (-T) T).indicator (fun _ => L) u + C * (1 + u ^ 2)⁻¹ := by
  have hind0 : 0 ≤ (Set.Icc (-T) T).indicator (fun _ => L) u :=
    Set.indicator_nonneg (fun _ _ => hL0) u
  have hfar0 : 0 ≤ C * (1 + u ^ 2)⁻¹ := by positivity
  have h3 : 0 ≤ A * κ * g := by positivity
  have h4 : 0 ≤ A * E * h := by positivity
  by_cases hc : |u| ≤ τ
  · have := hcore hc
    linarith
  · push Not at hc
    have hG1 : ‖F * (P : ℂ) - ((A * g : ℝ) : ℂ)‖ ≤ ‖F‖ * |P| + A * g := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ A * g)]
    have hAg : A * g ≤ A * E * h := by
      calc A * g ≤ A * (E * h) := mul_le_mul_of_nonneg_left (hgE hc) hA0.le
        _ = A * E * h := by ring
    by_cases hm : 4 * π * |u| ≤ 1 / 2
    · have : ‖F‖ * |P| ≤ A * E * h := by
        calc ‖F‖ * |P| ≤ A * (E * h) := mul_le_mul hFle (hmid hc hm) (abs_nonneg _) hA0.le
          _ = A * E * h := by ring
      linarith
    · push Not at hm
      by_cases hTu : |u| ≤ T
      · have hmem : u ∈ Set.Icc (-T) T := abs_le.mp hTu
        have hind : (Set.Icc (-T) T).indicator (fun _ => L) u = L := Set.indicator_of_mem hmem _
        have : ‖F‖ * |P| ≤ L := by
          calc ‖F‖ * |P| ≤ A * |P| := mul_le_mul_of_nonneg_right hFle (abs_nonneg _)
            _ = |P| * A := by ring
            _ ≤ L := hinter hm hTu
        rw [hind]
        linarith
      · push Not at hTu
        have : ‖F‖ * |P| ≤ C * (1 + u ^ 2)⁻¹ := by
          calc ‖F‖ * |P| ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hP1 (norm_nonneg _)
            _ ≤ C * (1 + u ^ 2)⁻¹ := by rw [mul_one]; exact hfar hTu
        linarith

/-- **S1, the core bound.** -/
lemma S1_core_pt (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ τ u : ℝ)
    (hτ : 4 * π * τ ≤ 1 / 2) (hX : (K n : ℝ) * (4 * π * τ) ^ 4 ≤ 1 / 4) (hu : |u| ≤ τ) :
    ‖𝓕 (psi δ hδ : ℝ → ℂ) u * ((Pc t ξ u : ℝ) : ℂ) -
        ((Ad δ hδ * Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) : ℝ) : ℂ)‖
      ≤ Ad δ hδ * (2 * π * δ * τ + 4 * ((K n : ℝ) * (4 * π * τ) ^ 4)) *
          Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) := by
  obtain ⟨hlo, hhi⟩ := Pc_core t ξ u τ hu hτ
  generalize hXg : (K n : ℝ) * (4 * π * τ) ^ 4 = X at hlo hhi hX ⊢
  generalize hgg : Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) = g at hlo hhi ⊢
  generalize hPg : Pc t ξ u = P at hlo hhi ⊢
  have hlip := fourier_psi_lip δ hδ u
  rw [fourier_psi_zero] at hlip
  generalize hFg : 𝓕 (psi δ hδ : ℝ → ℂ) u = F at hlip ⊢
  have hA0 := Ad_pos δ hδ
  generalize hAg : Ad δ hδ = A at hlip hA0 ⊢
  have hX0 : 0 ≤ X := by rw [← hXg]; positivity
  have hg0 : 0 ≤ g := by rw [← hgg]; positivity
  have hpi := Real.pi_pos
  have hexpX : Real.exp X - 1 ≤ 2 * X := by
    have := Real.abs_exp_sub_one_le (x := X) (by rw [abs_of_nonneg hX0]; linarith)
    rw [abs_of_nonneg hX0] at this
    linarith [(abs_le.mp this).2]
  have hexp2 : 1 - Real.exp (-(2 * X)) ≤ 4 * X := by
    have h2X : |-(2 * X)| = 2 * X := by rw [abs_neg, abs_of_nonneg (by linarith)]
    have := Real.abs_exp_sub_one_le (x := -(2 * X)) (by rw [h2X]; linarith)
    rw [h2X] at this
    linarith [(abs_le.mp this).1]
  have hP0 : 0 ≤ P := le_trans (by positivity) hlo
  have hPg : |P - g| ≤ 4 * X * g := by
    rw [abs_le]
    constructor
    · have : g * (1 - Real.exp (-(2 * X))) ≤ g * (4 * X) := mul_le_mul_of_nonneg_left hexp2 hg0
      nlinarith
    · have : g * (Real.exp X - 1) ≤ g * (2 * X) := mul_le_mul_of_nonneg_left hexpX hg0
      nlinarith
  have hP2 : P ≤ 2 * g := by
    have : g * (Real.exp X - 1) ≤ g * (2 * X) := mul_le_mul_of_nonneg_left hexpX hg0
    nlinarith
  have hsplit : F * (P : ℂ) - ((A * g : ℝ) : ℂ) = (F - (A : ℂ)) * (P : ℂ) +
      (A : ℂ) * ((P - g : ℝ) : ℂ) := by push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hP0, abs_of_pos hA0]
  have hu0 := abs_nonneg u
  calc ‖F - (A : ℂ)‖ * P + A * |P - g|
      ≤ (π * δ * |u| * A) * (2 * g) + A * (4 * X * g) := by gcongr
    _ ≤ (π * δ * τ * A) * (2 * g) + A * (4 * X * g) := by gcongr
    _ = A * (2 * π * δ * τ + 4 * X) * g := by ring

/-- **S1, deterministic form.** -/
lemma S1_det (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ : ℝ) (τ T lam C : ℝ)
    (hV : 0 < Vv t ξ) (hτ0 : 0 < τ) (hτ : 4 * π * τ ≤ 1 / 2)
    (hX : (K n : ℝ) * (4 * π * τ) ^ 4 ≤ 1 / 4) (hT : 0 ≤ T)
    (hinter : ∀ u, 1 / 2 < 4 * π * |u| → |u| ≤ T → |Pc t ξ u| ≤ Real.exp (-lam))
    (hC0 : 0 ≤ C) (hfar : ∀ u, T < |u| → ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ C * (1 + u ^ 2)⁻¹) :
    |E1 δ hδ t ξ - Ad δ hδ / Real.sqrt (2 * π * Vv t ξ)| ≤
      Ad δ hδ / Real.sqrt (2 * π * Vv t ξ) *
        ((2 * π * δ * τ + 4 * ((K n : ℝ) * (4 * π * τ) ^ 4)) +
          4 * Real.exp (-(π ^ 2 * τ ^ 2 * Vv t ξ / 2)))
      + Ad δ hδ * Real.exp (-lam) * (2 * T) + C * π := by
  have hpi := Real.pi_pos
  have hA0 := Ad_pos δ hδ
  have hb1 : 0 < 2 * π ^ 2 * Vv t ξ := by positivity
  have hI1 : Integrable (fun u => 𝓕 (psi δ hδ : ℝ → ℂ) u * ((Pc t ξ u : ℝ) : ℂ)) := by
    refine (fourier_integrable (psi δ hδ)).mul_bdd (c := 1) ?_ ?_
    · exact (Complex.continuous_ofReal.comp (Pc_continuous t ξ)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun u => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Pc_le_one t ξ u
  have hI2 : Integrable (fun u => ((Ad δ hδ * Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) : ℝ) : ℂ)) :=
    ((integrable_exp_neg_mul_sq hb1).const_mul _).ofReal
  have hEq : ((E1 δ hδ t ξ - Ad δ hδ / Real.sqrt (2 * π * Vv t ξ) : ℝ) : ℂ) =
      ∫ u, (𝓕 (psi δ hδ : ℝ → ℂ) u * ((Pc t ξ u : ℝ) : ℂ) -
        ((Ad δ hδ * Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sub, E1_eq, ← gauss_int _ _ hV, ← integral_complex_ofReal,
      ← integral_sub hI1 hI2]
  have hpt : ∀ u, ‖𝓕 (psi δ hδ : ℝ → ℂ) u * ((Pc t ξ u : ℝ) : ℂ) -
        ((Ad δ hδ * Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) : ℝ) : ℂ)‖ ≤
      Ad δ hδ * (2 * π * δ * τ + 4 * ((K n : ℝ) * (4 * π * τ) ^ 4)) *
          Real.exp (-(2 * π ^ 2 * Vv t ξ) * u ^ 2) +
        2 * Ad δ hδ * Real.exp (-(π ^ 2 * τ ^ 2 * Vv t ξ / 2)) *
          Real.exp (-(π ^ 2 * Vv t ξ / 2) * u ^ 2) +
        (Set.Icc (-T) T).indicator (fun _ => Ad δ hδ * Real.exp (-lam)) u + C * (1 + u ^ 2)⁻¹ := by
    intro u
    have hV0 : 0 ≤ π ^ 2 * Vv t ξ := by positivity
    refine S1_pt _ _ _ _ _ _ _ _ _ τ T u hA0 (fourier_psi_le δ hδ u) (abs_Pc_le_one t ξ u)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hC0
      (S1_core_pt δ hδ t ξ τ u hτ hX) ?_ ?_ ?_ (hfar u)
    · intro hu
      have hu2 : τ ^ 2 ≤ u ^ 2 := by
        have := pow_le_pow_left₀ hτ0.le hu.le 2; rwa [sq_abs] at this
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    · intro hu hm
      have hu2 : τ ^ 2 ≤ u ^ 2 := by
        have := pow_le_pow_left₀ hτ0.le hu.le 2; rwa [sq_abs] at this
      obtain ⟨hP0, hP1⟩ := Pc_mid t ξ u hm
      rw [abs_of_nonneg hP0]
      refine hP1.trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    · intro hm hTu
      exact mul_le_mul_of_nonneg_right (hinter u hm hTu) hA0.le |>.trans_eq (by ring)
  have hnorm := norm_integral_le_of_norm_le (H_integrable (Ad δ hδ)
    (2 * π * δ * τ + 4 * ((K n : ℝ) * (4 * π * τ) ^ 4))
    (Real.exp (-(π ^ 2 * τ ^ 2 * Vv t ξ / 2))) (Ad δ hδ * Real.exp (-lam)) C T (Vv t ξ) hV)
    (Filter.Eventually.of_forall hpt)
  rw [← hEq, H_integral _ _ _ _ _ _ _ hV hT, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

end K525


namespace K525

variable {n : ℕ}

lemma eventually_le_sqrt (c : ℝ) : ∀ᶠ n : ℕ in Filter.atTop, c ≤ Real.sqrt n := by
  filter_upwards [Filter.eventually_ge_atTop ⌈c ^ 2⌉₊] with n hn
  calc c ≤ |c| := le_abs_self c
    _ = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))

lemma Dn_add_one_ge (n : ℕ) : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (Dn n : ℝ) + 1 := by
  unfold Dn; exact (Nat.lt_floor_add_one _).le

lemma Dn_le (n : ℕ) : (Dn n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
  unfold Dn; exact Nat.floor_le (by positivity)

/-- The Fejér modulus is small at resolution `Dn n`, even after multiplying by `4π n^(1/100)`. -/
lemma Omega_small_gen (η : ℝ) (hη : 0 < η) : ∀ᶠ n : ℕ in Filter.atTop,
    4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n) ≤ η := by
  have hpi := Real.pi_pos
  set c : ℝ := 2 + 4 * π ^ 2 * Real.sqrt π with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [eventually_small_rpow (4 * π * c) (3 / 200) η (by norm_num) hη,
    Filter.eventually_ge_atTop 1] with n hsm hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  set N : ℝ := (n : ℝ) with hNdef
  set y : ℝ := (Dn n : ℝ) + 1 with hy
  have hy0 : 1 ≤ y := by simp only [hy]; have := Nat.cast_nonneg (α := ℝ) (Dn n); linarith
  have hyN : N ^ (1 / 20 : ℝ) ≤ y := Dn_add_one_ge n
  have hsy : N ^ (1 / 40 : ℝ) ≤ Real.sqrt y := by
    have e : N ^ (1 / 40 : ℝ) = Real.sqrt (N ^ (1 / 20 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; norm_num
    rw [e]; exact Real.sqrt_le_sqrt hyN
  have hsy1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hy0
  have hlog : Real.log (π * y) ≤ 2 * Real.sqrt π * Real.sqrt y := by
    have h := Real.log_le_rpow_div (x := π * y) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hpi.le] at h
    linarith
  have hΩ : Ωf (Dn n) ≤ c / Real.sqrt y := by
    have e : Ωf (Dn n) = (2 + 2 * π ^ 2 * Real.log (π * y)) / y := by
      unfold Ωf; simp only [hy]; ring
    rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 : 2 + 2 * π ^ 2 * Real.log (π * y) ≤ c * Real.sqrt y := by
      have : 2 * π ^ 2 * Real.log (π * y) ≤ 2 * π ^ 2 * (2 * Real.sqrt π * Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      simp only [hc]; nlinarith
    calc (2 + 2 * π ^ 2 * Real.log (π * y)) * Real.sqrt y ≤ c * Real.sqrt y * Real.sqrt y :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = c * y := by rw [mul_assoc, Real.mul_self_sqrt (by linarith)]
  have hT0 : 0 ≤ N ^ (1 / 100 : ℝ) := by positivity
  have hq : N ^ (1 / 100 : ℝ) / N ^ (1 / 40 : ℝ) = N ^ (-(3 / 200) : ℝ) := by
    rw [← Real.rpow_sub hN0]; norm_num
  calc 4 * π * N ^ (1 / 100 : ℝ) * Ωf (Dn n) ≤ 4 * π * N ^ (1 / 100 : ℝ) * (c / Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hΩ (by positivity)
    _ ≤ 4 * π * N ^ (1 / 100 : ℝ) * (c / N ^ (1 / 40 : ℝ)) := by
        gcongr
    _ = 4 * π * c * (N ^ (1 / 100 : ℝ) / N ^ (1 / 40 : ℝ)) := by ring
    _ = 4 * π * c * N ^ (-(3 / 200) : ℝ) := by rw [hq]
    _ ≤ η := hsm

lemma Omega_small : ∀ᶠ n : ℕ in Filter.atTop,
    4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n) ≤ 1 / 800 := Omega_small_gen _ (by norm_num)

lemma exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp (x := y) hy.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  norm_num at h
  linarith

lemma exp_neg_le_inv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  have h := Real.add_one_le_exp y
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hy]
  linarith

open scoped Classical in
/-- Sizes of the variance, of `B`, and of the Weyl error. -/
lemma S1_sizes (n : ℕ) (hn : 16 ≤ n) (hF1 : 40 * (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1)
    (t : Fin (K n) → Bool) (ht : Typical n t) (ξ : ℝ)
    (hS4 : |Vv t ξ - K n| ≤ 5 * (n : ℝ) ^ (3 / 5 : ℝ)) :
    (n : ℝ) / 4 ≤ Vv t ξ ∧ Vv t ξ ≤ n ∧
      (n : ℝ) / 5 ≤ ((univ.filter fun p => t p = false).card : ℝ) ∧
      (Dn n : ℝ) * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤
        ((univ.filter fun p => t p = false).card : ℝ) / 2 := by
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hK1 : (K n : ℝ) ≤ n / 2 + 1 / 2 := by
    have : 2 * K n ≤ n + 1 := by unfold K; omega
    have : (2 * K n : ℝ) ≤ n + 1 := by exact_mod_cast this
    linarith
  have hK2 : (n : ℝ) / 2 - 1 / 2 ≤ K n := by
    have : n ≤ 2 * K n + 1 := by unfold K; omega
    have : (n : ℝ) ≤ 2 * K n + 1 := by exact_mod_cast this
    linarith
  have h45 : (n : ℝ) ^ (4 / 5 : ℝ) ≤ n / 40 := by
    have e : (n : ℝ) ^ (4 / 5 : ℝ) = (n : ℝ) ^ (-(1 / 5) : ℝ) * n := by
      rw [← Real.rpow_add_one hN0.ne']; norm_num
    rw [e]; nlinarith
  have h35 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ n / 40 :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)).trans h45
  obtain ⟨hl, hr⟩ := abs_le.mp hS4
  have hB := card_B_ge t ht
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have hε : 1 / (2 * εn n) = (n : ℝ) ^ (3 / 4 : ℝ) / 2 := by
    unfold εn; rw [Real.rpow_neg hN0.le]; field_simp
  rw [hε]
  have h1 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h2 : (n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hD := Dn_le n
  have hD0 : (0 : ℝ) ≤ Dn n := Nat.cast_nonneg _
  have h3 : (Dn n : ℝ) * ((n : ℝ) ^ (3 / 4 : ℝ) / 2 + (n : ℝ) ^ (3 / 5 : ℝ))
      ≤ (n : ℝ) ^ (1 / 20 : ℝ) * (3 / 2 * (n : ℝ) ^ (3 / 4 : ℝ)) :=
    mul_le_mul hD (by linarith) (by positivity) (by positivity)
  have h4 : (n : ℝ) ^ (1 / 20 : ℝ) * (3 / 2 * (n : ℝ) ^ (3 / 4 : ℝ)) = 3 / 2 * (n : ℝ) ^ (4 / 5 : ℝ) := by
    rw [← h2]; ring
  linarith

open scoped Classical in
/-- The intermediate region bound, with `λ = B / (3200 π)`. -/
lemma S1_inter (n : ℕ) (hn : 16 ≤ n)
    (hΩ : 4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n) ≤ 1 / 800)
    (t : Fin (K n) → Bool) (ht : Typical n t) (ξ : ℝ) (hnr : NR1 n ξ)
    (hW : (Dn n : ℝ) * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤
        ((univ.filter fun p => t p = false).card : ℝ) / 2) :
    ∀ u, 1 / 2 < 4 * π * |u| → |u| ≤ (n : ℝ) ^ (1 / 100 : ℝ) →
      |Pc t ξ u| ≤ Real.exp (-(((univ.filter fun p => t p = false).card : ℝ) / (3200 * π))) := by
  intro u hu hTu
  have hpi := Real.pi_pos
  generalize hBg : ((univ.filter fun p => t p = false).card : ℝ) = B at hW
  have hB0 : 0 ≤ B := by rw [← hBg]; positivity
  have hs : 1 / 3 ≤ |4 * π * u| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]; linarith
  have hBW : (Dn n : ℝ) * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤
      ((univ.filter fun p => t p = false).card : ℝ) := by rw [hBg]; linarith
  have hi := inter1 t ht ξ hnr (4 * π * u) hs hBW
  rw [hBg] at hi
  have hΩ0 : 0 ≤ Ωf (Dn n) := by
    unfold Ωf
    have : (1 : ℝ) ≤ π * ((Dn n : ℝ) + 1) := by
      have := Nat.cast_nonneg (α := ℝ) (Dn n); nlinarith [Real.pi_gt_three]
    have := Real.log_nonneg this
    positivity
  have hsΩ : |4 * π * u| * Ωf (Dn n) ≤ 1 / 800 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
    calc 4 * π * |u| * Ωf (Dn n) ≤ 4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n) := by gcongr
      _ ≤ 1 / 800 := hΩ
  generalize hWg : (Dn n : ℝ) * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) = W at hW hi
  generalize hSg : ∑ p ∈ univ.filter (fun p => t p = false),
      Real.sin ((4 * π * u) * Real.sin (kk n p * ξ)) ^ 2 = S at hi
  have hkey : B / (1600 * π) ≤ (B - W) * (1 / (400 * π)) - B * (|4 * π * u| * Ωf (Dn n) / (2 * π)) := by
    calc B / (1600 * π) = (B / 2) * (1 / (400 * π)) - B * ((1 / 800) / (2 * π)) := by
          field_simp; ring
      _ ≤ _ := sub_le_sub (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsΩ (by positivity)) hB0)
  refine (abs_Pc_inter t ξ u).trans (Real.exp_le_exp.mpr ?_)
  rw [hSg]
  have e : B / (3200 * π) = (B / (1600 * π)) / 2 := by field_simp; ring
  rw [e]
  linarith

/-- The two tail estimates, in abstract form. -/
lemma S1_tails (A N T lam C₀ ε₀ : ℝ) (hA0 : 0 < A) (hN0 : 0 < N) (hT0 : 0 ≤ T) (hε₀ : 0 < ε₀)
    (hlam0 : N / (16000 * π) ≤ lam) (hTs : T * Real.sqrt N ≤ N)
    (hF7 : 48 * (16000 * π) ^ 2 * N ^ (-1 : ℝ) ≤ ε₀)
    (hF8 : 24 * π * C₀ / (ε₀ * A) ≤ Real.sqrt N) :
    A * Real.exp (-lam) * (2 * T) ≤ ε₀ / 4 * (A / (3 * Real.sqrt N)) ∧
      2 * C₀ / N * π ≤ ε₀ / 4 * (A / (3 * Real.sqrt N)) := by
  have hpi := Real.pi_pos
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  constructor
  · have hexp : Real.exp (-lam) ≤ 2 * (16000 * π) ^ 2 / N ^ 2 := by
      have hl0 : 0 < N / (16000 * π) := by positivity
      calc Real.exp (-lam) ≤ Real.exp (-(N / (16000 * π))) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 2 / (N / (16000 * π)) ^ 2 := exp_neg_le_two_div_sq hl0
        _ = 2 * (16000 * π) ^ 2 / N ^ 2 := by field_simp
    rw [Real.rpow_neg_one] at hF7
    have h7 : 48 * (16000 * π) ^ 2 ≤ ε₀ * N := by
      have := mul_le_mul_of_nonneg_right hF7 hN0.le
      rwa [mul_assoc, inv_mul_cancel₀ hN0.ne', mul_one] at this
    rw [show ε₀ / 4 * (A / (3 * Real.sqrt N)) = A * (ε₀ / (12 * Real.sqrt N)) by
      field_simp; ring]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA0.le
    rw [le_div_iff₀ (by positivity)]
    have hTs0 : 0 ≤ T * Real.sqrt N := by positivity
    have hE0 : 0 ≤ Real.exp (-lam) := (Real.exp_pos _).le
    calc Real.exp (-lam) * (2 * T) * (12 * Real.sqrt N)
        = Real.exp (-lam) * (24 * (T * Real.sqrt N)) := by ring
      _ ≤ 2 * (16000 * π) ^ 2 / N ^ 2 * (24 * (T * Real.sqrt N)) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ 2 * (16000 * π) ^ 2 / N ^ 2 * (24 * N) := by gcongr
      _ = 48 * (16000 * π) ^ 2 / N := by field_simp; ring
      _ ≤ ε₀ := by rw [div_le_iff₀ hN0]; linarith
  · have h8 : 24 * π * C₀ ≤ ε₀ * A * Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)] at hF8; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
    have e : ε₀ / 4 * (A / (3 * Real.sqrt N)) * N = ε₀ * A * (N / Real.sqrt N) / 12 := by ring
    rw [e, Real.div_sqrt]
    linarith

/-- Core parameters. -/
lemma S1_core_params (n : ℕ) (hn : 16 ≤ n) (V δ ε₀ : ℝ) (hVlo : (n : ℝ) / 4 ≤ V)
    (hF3 : (4 * π) ^ 4 * (n : ℝ) ^ (-(3 / 5) : ℝ) ≤ 1 / 4)
    (hF3' : (4 * π) ^ 4 * (n : ℝ) ^ (-(3 / 5) : ℝ) ≤ ε₀ / 32)
    (hF4 : 2 * π * δ * (n : ℝ) ^ (-(2 / 5) : ℝ) ≤ ε₀ / 8)
    (hF5 : 32 / π ^ 2 * (n : ℝ) ^ (-(1 / 5) : ℝ) ≤ ε₀ / 4) :
    (K n : ℝ) * (4 * π * (n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4 ≤ 1 / 4 ∧
      2 * π * δ * (n : ℝ) ^ (-(2 / 5) : ℝ) +
        4 * ((K n : ℝ) * (4 * π * (n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4) ≤ ε₀ / 4 ∧
      4 * Real.exp (-(π ^ 2 * ((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 2 * V / 2)) ≤ ε₀ / 4 := by
  have hpi := Real.pi_pos
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hK1 : (K n : ℝ) ≤ n := by
    have : K n ≤ n := by unfold K; omega
    exact_mod_cast this
  generalize hτg : (n : ℝ) ^ (-(2 / 5) : ℝ) = τ at hF4 ⊢
  have hτ4 : (K n : ℝ) * (4 * π * τ) ^ 4 ≤ (4 * π) ^ 4 * (n : ℝ) ^ (-(3 / 5) : ℝ) := by
    have e : τ ^ 4 * n = (n : ℝ) ^ (-(3 / 5) : ℝ) := by
      rw [← hτg, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add_one hN0.ne']
      norm_num
    calc (K n : ℝ) * (4 * π * τ) ^ 4 = (4 * π) ^ 4 * (τ ^ 4 * K n) := by ring
      _ ≤ (4 * π) ^ 4 * (τ ^ 4 * n) := by gcongr
      _ = _ := by rw [e]
  refine ⟨hτ4.trans hF3, by linarith, ?_⟩
  have e : τ ^ 2 * n = (n : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← hτg, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add_one hN0.ne']
    norm_num
  have hpos : 0 < (n : ℝ) ^ (1 / 5 : ℝ) := by positivity
  have hy : π ^ 2 * (n : ℝ) ^ (1 / 5 : ℝ) / 8 ≤ π ^ 2 * τ ^ 2 * V / 2 := by
    have h1 : τ ^ 2 * ((n : ℝ) / 4) ≤ τ ^ 2 * V := mul_le_mul_of_nonneg_left hVlo (by positivity)
    have h2 : π ^ 2 * (τ ^ 2 * ((n : ℝ) / 4)) ≤ π ^ 2 * (τ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : π ^ 2 * (τ ^ 2 * ((n : ℝ) / 4)) = π ^ 2 * (n : ℝ) ^ (1 / 5 : ℝ) / 4 := by
      rw [← e]; ring
    nlinarith
  have h1 := exp_neg_le_inv (y := π ^ 2 * (n : ℝ) ^ (1 / 5 : ℝ) / 8) (by positivity)
  have h2 : Real.exp (-(π ^ 2 * τ ^ 2 * V / 2)) ≤ Real.exp (-(π ^ 2 * (n : ℝ) ^ (1 / 5 : ℝ) / 8)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : 4 * (1 / (π ^ 2 * (n : ℝ) ^ (1 / 5 : ℝ) / 8)) = 32 / π ^ 2 * (n : ℝ) ^ (-(1 / 5) : ℝ) := by
    rw [Real.rpow_neg hN0.le]; field_simp; ring
  linarith

open scoped Classical in
/-- **S1 holds.** -/
theorem S1_holds : S1 := by
  intro δ hδ ε₀ hε₀
  obtain ⟨C₀, hC₀0, hC₀⟩ := fourier_far δ hδ
  have hpi := Real.pi_pos
  have hA0 := Ad_pos δ hδ
  filter_upwards [S4_holds, Omega_small,
    eventually_small_rpow 40 (1 / 5) 1 (by norm_num) (by norm_num),
    eventually_small_rpow (4 * π) (2 / 5) (1 / 2) (by norm_num) (by norm_num),
    eventually_small_rpow ((4 * π) ^ 4) (3 / 5) (1 / 4) (by norm_num) (by norm_num),
    eventually_small_rpow ((4 * π) ^ 4) (3 / 5) (ε₀ / 32) (by norm_num) (by positivity),
    eventually_small_rpow (2 * π * δ) (2 / 5) (ε₀ / 8) (by norm_num) (by positivity),
    eventually_small_rpow (32 / π ^ 2) (1 / 5) (ε₀ / 4) (by norm_num) (by positivity),
    eventually_small_rpow (48 * (16000 * π) ^ 2) 1 ε₀ (by norm_num) hε₀,
    eventually_le_sqrt (24 * π * C₀ / (ε₀ * Ad δ hδ)),
    Filter.eventually_ge_atTop 16] with n hS4 hΩ hF1 hF2 hF3 hF3' hF4 hF5 hF7 hF8 hn
  intro t ht ξ hξ hnr
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hN1 : (1 : ℝ) ≤ n := by linarith
  obtain ⟨hVlo, hVhi, hBlo, hW⟩ := S1_sizes n hn hF1 t ht ξ (hS4 t ht ξ hξ)
  have hV0 : 0 < Vv t ξ := by linarith
  obtain ⟨hX, hκ, hEb⟩ := S1_core_params n hn (Vv t ξ) δ ε₀ hVlo hF3 hF3' hF4 hF5
  have hinter := S1_inter n hn hΩ t ht ξ hnr hW
  have hfar : ∀ u, (n : ℝ) ^ (1 / 100 : ℝ) < |u| →
      ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ 2 * C₀ / n * (1 + u ^ 2)⁻¹ :=
    fun u hu => hC₀ n hN1 u hu.le
  have hdet := S1_det δ hδ t ξ ((n : ℝ) ^ (-(2 / 5) : ℝ)) ((n : ℝ) ^ (1 / 100 : ℝ))
    (((univ.filter fun p => t p = false).card : ℝ) / (3200 * π)) (2 * C₀ / n) hV0
    (by positivity) hF2 hX (by positivity) hinter (by positivity) hfar
  have hsq : Real.sqrt (2 * π * Vv t ξ) ≤ 3 * Real.sqrt n := by
    rw [show (3 : ℝ) * Real.sqrt n = Real.sqrt (9 * n) by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])
  have hplo : Ad δ hδ / (3 * Real.sqrt n) ≤ Ad δ hδ / Real.sqrt (2 * π * Vv t ξ) :=
    div_le_div_of_nonneg_left hA0.le (Real.sqrt_pos.mpr (by positivity)) hsq
  have hlam0 : (n : ℝ) / (16000 * π) ≤ ((univ.filter fun p => t p = false).card : ℝ) / (3200 * π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hTs : (n : ℝ) ^ (1 / 100 : ℝ) * Real.sqrt n ≤ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
    calc (n : ℝ) ^ (1 / 100 + 1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = n := Real.rpow_one _
  obtain ⟨hmid, hfarb⟩ := S1_tails (Ad δ hδ) n ((n : ℝ) ^ (1 / 100 : ℝ))
    (((univ.filter fun p => t p = false).card : ℝ) / (3200 * π)) C₀ ε₀ hA0 hN0 (by positivity) hε₀
    hlam0 hTs hF7 hF8
  generalize hpg : Ad δ hδ / Real.sqrt (2 * π * Vv t ξ) = p at hdet hplo ⊢
  have hp0 : 0 ≤ p := by rw [← hpg]; positivity
  calc |E1 δ hδ t ξ - p| ≤ _ := hdet
    _ ≤ p * (ε₀ / 4 + ε₀ / 4) + ε₀ / 4 * p + ε₀ / 4 * p := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hκ hEb) hp0)
          (hmid.trans (mul_le_mul_of_nonneg_left hplo (by positivity))))
          (hfarb.trans (mul_le_mul_of_nonneg_left hplo (by positivity)))
    _ = ε₀ * p := by ring

end K525


namespace K525

variable {n : ℕ}

/-! ## S2, part a: two-dimensional equidistribution -/

lemma cont_param (F : ℝ → ℝ → ℝ) (hF : Continuous (fun q : ℝ × ℝ => F q.1 q.2)) (a b : ℝ) :
    Continuous (fun x => ∫ t in a..b, F x t) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF a b

/-- **Weighted Fejér sums.** -/
lemma sum_fej_w {ι : Type*} (T : Finset ι) (θ c : ι → ℝ) (D : ℕ) (W : ℝ)
    (hW : ∀ m : ℤ, m ≠ 0 → |m| ≤ D →
      ‖∑ p ∈ T, (c p : ℂ) * Complex.exp (↑((m : ℝ) * θ p) * Complex.I)‖ ≤ W) (φ : ℝ) :
    (∑ p ∈ T, c p) - D * W ≤ ∑ p ∈ T, c p * fej D (θ p - φ) := by
  have hexp : ((∑ p ∈ T, c p * fej D (θ p - φ) : ℝ) : ℂ) = (1 / ((D : ℂ) + 1)) *
      ∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1),
        Complex.exp (↑(-(((j : ℝ) - k) * φ)) * Complex.I) *
          ∑ p ∈ T, (c p : ℂ) * Complex.exp (↑((((j : ℤ) - k : ℤ) : ℝ) * θ p) * Complex.I) := by
    push_cast
    simp_rw [fej_expand]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have e : Complex.exp (↑(((j : ℝ) - k) * (θ p - φ)) * Complex.I)
        = Complex.exp (↑(-(((j : ℝ) - k) * φ)) * Complex.I) *
          Complex.exp (↑((((j : ℤ) - k : ℤ) : ℝ) * θ p) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    push_cast at e ⊢
    rw [e]; ring
  set F : ℕ → ℕ → ℂ := fun j k => Complex.exp (↑(-(((j : ℝ) - k) * φ)) * Complex.I) *
      ∑ p ∈ T, (c p : ℂ) * Complex.exp (↑((((j : ℤ) - k : ℤ) : ℝ) * θ p) * Complex.I)
  have hdiag : ∀ j, F j j = ((∑ p ∈ T, c p : ℝ) : ℂ) := by
    intro j; simp [F]
  have hoff : ∀ j k, j ≠ k → j ∈ Finset.range (D + 1) → k ∈ Finset.range (D + 1) → ‖F j k‖ ≤ W := by
    intro j k hjk hj hk
    simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [Finset.mem_range] at hj hk
    exact hW ((j : ℤ) - k) (by omega) (by rw [abs_le]; constructor <;> push_cast <;> omega)
  have hsplit : ∀ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1), F j k
      = ((∑ p ∈ T, c p : ℝ) : ℂ) + ∑ k ∈ (Finset.range (D + 1)).erase j, F j k := by
    intro j hj; rw [← Finset.add_sum_erase _ _ hj, hdiag]
  have hbound : ‖∑ j ∈ Finset.range (D + 1), ∑ k ∈ (Finset.range (D + 1)).erase j, F j k‖
      ≤ (D + 1) * (D * W) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j ∈ Finset.range (D + 1), (D * W) := by
          refine Finset.sum_le_sum (fun j hj => (norm_sum_le _ _).trans ?_)
          calc _ ≤ ∑ _k ∈ (Finset.range (D + 1)).erase j, W := Finset.sum_le_sum (fun k hk =>
                hoff j k (Finset.ne_of_mem_erase hk).symm hj (Finset.mem_of_mem_erase hk))
            _ = D * W := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hj, Finset.card_range, nsmul_eq_mul]
                simp
      _ = (D + 1) * (D * W) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hexp
  set E := ∑ j ∈ Finset.range (D + 1), ∑ k ∈ (Finset.range (D + 1)).erase j, F j k
  have hD1 : ((D : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero D)
  have hre : (∑ p ∈ T, c p * fej D (θ p - φ) : ℝ) = (∑ p ∈ T, c p) + (E / ((D : ℂ) + 1)).re := by
    have h := congrArg Complex.re hexp
    rw [Complex.ofReal_re] at h
    rw [h]
    have e : (1 / ((D : ℂ) + 1)) * (((D + 1 : ℕ) : ℂ) * ((∑ p ∈ T, c p : ℝ) : ℂ) + E)
        = ((∑ p ∈ T, c p : ℝ) : ℂ) + E / ((D : ℂ) + 1) := by
      push_cast; field_simp
    rw [e, Complex.add_re, Complex.ofReal_re]
  rw [hre]
  have : |(E / ((D : ℂ) + 1)).re| ≤ D * W := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div]
    have hn : ‖(D : ℂ) + 1‖ = (D : ℝ) + 1 := by
      rw [show ((D : ℂ) + 1) = ((D + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn, div_le_iff₀ (by positivity)]
    linarith [hbound]
  rw [abs_le] at this
  linarith

/-- Fejér weights against characters: the weights are expanded too. -/
lemma weyl_fej {ι : Type*} (T : Finset ι) (θ θ' : ι → ℝ) (D : ℕ) (W : ℝ)
    (hW2 : ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ D → |m₂| ≤ D →
      ‖∑ p ∈ T, Complex.exp (↑((m₁ : ℝ) * θ p + (m₂ : ℝ) * θ' p) * Complex.I)‖ ≤ W)
    (φ' : ℝ) (m : ℤ) (hm : m ≠ 0) (hmD : |m| ≤ D) :
    ‖∑ p ∈ T, ((fej D (θ' p - φ') : ℝ) : ℂ) * Complex.exp (↑((m : ℝ) * θ p) * Complex.I)‖
      ≤ (D + 1) * W := by
  have hexp : ∑ p ∈ T, ((fej D (θ' p - φ') : ℝ) : ℂ) * Complex.exp (↑((m : ℝ) * θ p) * Complex.I)
      = (1 / ((D : ℂ) + 1)) * ∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1),
        Complex.exp (↑(-(((j : ℝ) - k) * φ')) * Complex.I) *
          ∑ p ∈ T, Complex.exp (↑((m : ℝ) * θ p + ((((j : ℤ) - k : ℤ) : ℝ)) * θ' p) * Complex.I) := by
    simp_rw [fej_expand]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have e : Complex.exp (↑(((j : ℝ) - k) * (θ' p - φ')) * Complex.I) *
          Complex.exp (↑((m : ℝ) * θ p) * Complex.I)
        = Complex.exp (↑(-(((j : ℝ) - k) * φ')) * Complex.I) *
          Complex.exp (↑((m : ℝ) * θ p + ((((j : ℤ) - k : ℤ) : ℝ)) * θ' p) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc 1 / ((D : ℂ) + 1) * Complex.exp (↑(((j : ℝ) - k) * (θ' p - φ')) * Complex.I) *
          Complex.exp (↑((m : ℝ) * θ p) * Complex.I)
        = 1 / ((D : ℂ) + 1) * (Complex.exp (↑(((j : ℝ) - k) * (θ' p - φ')) * Complex.I) *
          Complex.exp (↑((m : ℝ) * θ p) * Complex.I)) := by ring
      _ = _ := by rw [e]
  rw [hexp, norm_mul]
  have hn : ‖1 / ((D : ℂ) + 1)‖ = 1 / ((D : ℝ) + 1) := by
    rw [norm_div, norm_one, show ((D : ℂ) + 1) = ((D + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn]
  have hb : ‖∑ j ∈ Finset.range (D + 1), ∑ k ∈ Finset.range (D + 1),
        Complex.exp (↑(-(((j : ℝ) - k) * φ')) * Complex.I) *
          ∑ p ∈ T, Complex.exp (↑((m : ℝ) * θ p + ((((j : ℤ) - k : ℤ) : ℝ)) * θ' p) * Complex.I)‖
      ≤ (D + 1) * ((D + 1) * W) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _j ∈ Finset.range (D + 1), ((D + 1) * W) := by
          refine Finset.sum_le_sum (fun j hj => (norm_sum_le _ _).trans ?_)
          calc _ ≤ ∑ _k ∈ Finset.range (D + 1), W := Finset.sum_le_sum (fun k hk => by
                rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
                rw [Finset.mem_range] at hj hk
                exact hW2 m ((j : ℤ) - k) (Or.inl hm) hmD
                  (by rw [abs_le]; constructor <;> push_cast <;> omega))
            _ = (D + 1) * W := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ = (D + 1) * ((D + 1) * W) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  calc 1 / ((D : ℝ) + 1) * _ ≤ 1 / ((D : ℝ) + 1) * ((D + 1) * ((D + 1) * W)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (D + 1) * W := by field_simp

/-- **Two-dimensional Fejér sums.** -/
lemma sum2_fej {ι : Type*} (T : Finset ι) (θ θ' : ι → ℝ) (D : ℕ) (W : ℝ) (hW0 : 0 ≤ W)
    (hW2 : ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ D → |m₂| ≤ D →
      ‖∑ p ∈ T, Complex.exp (↑((m₁ : ℝ) * θ p + (m₂ : ℝ) * θ' p) * Complex.I)‖ ≤ W)
    (φ φ' : ℝ) :
    (T.card : ℝ) - (D + 1) ^ 2 * W ≤ ∑ p ∈ T, fej D (θ p - φ) * fej D (θ' p - φ') := by
  have h1 := sum_fej_w T θ (fun p => fej D (θ' p - φ')) D ((D + 1) * W)
    (fun m hm hmD => weyl_fej T θ θ' D W hW2 φ' m hm hmD) φ
  have h2 := sum_fej_ge T θ' D W (fun m hm hmD => by
    have := hW2 0 m (Or.inr hm) (by simp) hmD
    simpa using this) φ'
  have e : ∑ p ∈ T, fej D (θ p - φ) * fej D (θ' p - φ') =
      ∑ p ∈ T, (fun p => fej D (θ' p - φ')) p * fej D (θ p - φ) :=
    Finset.sum_congr rfl (fun p _ => by ring)
  rw [e]
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have : (D : ℝ) * W + D * ((D + 1) * W) ≤ (D + 1) ^ 2 * W := by nlinarith
  linarith

/-- The two-variable test function. -/
def G2 (s₁ s₂ x y : ℝ) : ℝ := Real.sin (s₁ * Real.sin x + s₂ * Real.sin y) ^ 2

lemma G2_lip1 (s₁ s₂ x x' y : ℝ) : |G2 s₁ s₂ x y - G2 s₁ s₂ x' y| ≤ |s₁| * |x - x'| := by
  unfold G2
  refine (abs_sin_sq_sub _ _).trans ?_
  rw [show s₁ * Real.sin x + s₂ * Real.sin y - (s₁ * Real.sin x' + s₂ * Real.sin y)
    = s₁ * (Real.sin x - Real.sin x') by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le x x') (abs_nonneg s₁)

lemma G2_lip2 (s₁ s₂ x y y' : ℝ) : |G2 s₁ s₂ x y - G2 s₁ s₂ x y'| ≤ |s₂| * |y - y'| := by
  unfold G2
  refine (abs_sin_sq_sub _ _).trans ?_
  rw [show s₁ * Real.sin x + s₂ * Real.sin y - (s₁ * Real.sin x + s₂ * Real.sin y')
    = s₂ * (Real.sin y - Real.sin y') by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le y y') (abs_nonneg s₂)

lemma G2_nonneg (s₁ s₂ x y : ℝ) : 0 ≤ G2 s₁ s₂ x y := by unfold G2; positivity

lemma G2_cont (s₁ s₂ : ℝ) : Continuous (fun q : ℝ × ℝ => G2 s₁ s₂ q.1 q.2) := by
  unfold G2; fun_prop

lemma Ωf_eq (D : ℕ) : Ωf D = 2 / (D + 1) + 2 * π ^ 2 * Real.log (π * (D + 1)) / (D + 1) := rfl

/-- **Pointwise smoothing, two variables.** -/
lemma smooth2_pt (D : ℕ) (s₁ s₂ θ₀ θ₀' : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π),
        G2 s₁ s₂ φ φ' * (fej D (θ₀ - φ) * fej D (θ₀' - φ')))
      ≤ 4 * π ^ 2 * G2 s₁ s₂ θ₀ θ₀' + 2 * π * ((|s₁| + |s₂|) * Ωf D) := by
  have hpi := Real.pi_pos
  have hfc := fej_continuous D
  have hK0 : ∀ x, 0 ≤ fej D x := fej_nonneg D
  -- the inner modulus
  have hmod2 : ∀ φ, ∫ φ' in (0 : ℝ)..(2 * π), |G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ φ φ'| * fej D (θ₀' - φ')
      ≤ |s₂| * Ωf D := by
    intro φ
    have := fej_modulus D (fun y => G2 s₁ s₂ φ y) (fun y => by simp [G2, Real.sin_add_two_pi])
      |s₂| (abs_nonneg _) (fun y y' => G2_lip2 s₁ s₂ φ y y') (by (try unfold G2); fun_prop) θ₀'
    rw [Ωf_eq]; exact this
  have hmod1 : ∫ φ in (0 : ℝ)..(2 * π), |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'| * fej D (θ₀ - φ)
      ≤ |s₁| * Ωf D := by
    have := fej_modulus D (fun x => G2 s₁ s₂ x θ₀') (fun x => by simp [G2, Real.sin_add_two_pi])
      |s₁| (abs_nonneg _) (fun x x' => G2_lip1 s₁ s₂ x x' θ₀') (by (try unfold G2); fun_prop) θ₀
    rw [Ωf_eq]; exact this
  -- inner bound
  have hin : ∀ φ, ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' * (fej D (θ₀ - φ) * fej D (θ₀' - φ'))
      ≤ fej D (θ₀ - φ) * ((G2 s₁ s₂ θ₀ θ₀' + |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'|) * (2 * π)
        + |s₂| * Ωf D) := by
    intro φ
    have hKφ := hK0 (θ₀ - φ)
    calc ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' * (fej D (θ₀ - φ) * fej D (θ₀' - φ'))
        ≤ ∫ φ' in (0 : ℝ)..(2 * π), fej D (θ₀ - φ) *
            ((G2 s₁ s₂ θ₀ θ₀' + |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'|) * fej D (θ₀' - φ') +
              |G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ φ φ'| * fej D (θ₀' - φ')) := by
          apply intervalIntegral.integral_mono_on (by linarith)
          · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
          · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
          · intro φ' _
            have hK' := hK0 (θ₀' - φ')
            have hg : G2 s₁ s₂ φ φ' ≤ G2 s₁ s₂ θ₀ θ₀' + |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'| +
                |G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ φ φ'| := by
              have := le_abs_self (G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ θ₀ θ₀')
              have := neg_abs_le (G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀')
              have := neg_abs_le (G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ φ φ')
              linarith
            have := mul_le_mul_of_nonneg_right hg (mul_nonneg hKφ hK')
            nlinarith
      _ = fej D (θ₀ - φ) * ((G2 s₁ s₂ θ₀ θ₀' + |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'|) *
            (∫ φ' in (0 : ℝ)..(2 * π), fej D (θ₀' - φ')) +
            ∫ φ' in (0 : ℝ)..(2 * π), |G2 s₁ s₂ φ θ₀' - G2 s₁ s₂ φ φ'| * fej D (θ₀' - φ')) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
            intervalIntegral.integral_const_mul]
          · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
          · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
      _ ≤ _ := by
          rw [integral_fej]
          gcongr
          exact hmod2 φ
  -- outer bound
  calc (∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π),
        G2 s₁ s₂ φ φ' * (fej D (θ₀ - φ) * fej D (θ₀' - φ')))
      ≤ ∫ φ in (0 : ℝ)..(2 * π), fej D (θ₀ - φ) * ((G2 s₁ s₂ θ₀ θ₀' +
          |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'|) * (2 * π) + |s₂| * Ωf D) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (cont_param (fun φ φ' => G2 s₁ s₂ φ φ' * (fej D (θ₀ - φ) * fej D (θ₀' - φ')))
            (by unfold G2; fun_prop) 0 (2 * π)).intervalIntegrable _ _
        · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
        · intro φ _; exact hin φ
    _ = 2 * π * G2 s₁ s₂ θ₀ θ₀' * (∫ φ in (0 : ℝ)..(2 * π), fej D (θ₀ - φ)) +
        2 * π * (∫ φ in (0 : ℝ)..(2 * π), |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'| * fej D (θ₀ - φ)) +
        |s₂| * Ωf D * (∫ φ in (0 : ℝ)..(2 * π), fej D (θ₀ - φ)) := by
        have e : ∀ φ, fej D (θ₀ - φ) * ((G2 s₁ s₂ θ₀ θ₀' +
            |G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'|) * (2 * π) + |s₂| * Ωf D)
            = 2 * π * G2 s₁ s₂ θ₀ θ₀' * fej D (θ₀ - φ) +
              2 * π * (|G2 s₁ s₂ θ₀ θ₀' - G2 s₁ s₂ φ θ₀'| * fej D (θ₀ - φ)) +
              |s₂| * Ωf D * fej D (θ₀ - φ) := fun φ => by ring
        simp_rw [e]
        rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        all_goals exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
    _ ≤ 4 * π ^ 2 * G2 s₁ s₂ θ₀ θ₀' + 2 * π * ((|s₁| + |s₂|) * Ωf D) := by
        rw [integral_fej]
        have := mul_le_mul_of_nonneg_left hmod1 (by positivity : (0 : ℝ) ≤ 2 * π)
        nlinarith

/-- The torus mean of `G2` when the inner coefficient is not small. -/
lemma mean_G2 (s₁ s₂ : ℝ) (hs : 1 / 3 ≤ |s₂|) :
    π / 100 ≤ ∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' := by
  have hpi := Real.pi_pos
  have hin : ∀ φ, 1 / 200 ≤ ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' := by
    intro φ
    have h1 := quarter_mean s₂ (s₁ * Real.sin φ) hs
    have h2 : ∫ θ in (0 : ℝ)..(π / 2), Real.sin (s₂ * Real.sin θ + s₁ * Real.sin φ) ^ 2
        ≤ ∫ θ in (0 : ℝ)..(2 * π), Real.sin (s₂ * Real.sin θ + s₁ * Real.sin φ) ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun x => sq_nonneg _)) (Continuous.intervalIntegrable (by fun_prop) _ _)
    have e : ∫ θ in (0 : ℝ)..(2 * π), Real.sin (s₂ * Real.sin θ + s₁ * Real.sin φ) ^ 2
        = ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' := by
      unfold G2; congr 1; ext θ; ring_nf
    linarith
  calc π / 100 = ∫ φ in (0 : ℝ)..(2 * π), (1 / 200 : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ _ := by
        apply intervalIntegral.integral_mono_on (by linarith) (by simp)
        · exact (cont_param (fun φ φ' => G2 s₁ s₂ φ φ') (G2_cont s₁ s₂) 0 (2 * π)).intervalIntegrable _ _
        · intro φ _; exact hin φ

/-- **Two-dimensional smoothing over a point set.** -/
lemma inter2_gen {ι : Type*} (T : Finset ι) (θ θ' : ι → ℝ) (D : ℕ) (W : ℝ) (hW0 : 0 ≤ W)
    (hW2 : ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ D → |m₂| ≤ D →
      ‖∑ p ∈ T, Complex.exp (↑((m₁ : ℝ) * θ p + (m₂ : ℝ) * θ' p) * Complex.I)‖ ≤ W)
    (s₁ s₂ : ℝ) (hs : 1 / 3 ≤ |s₂|) (hTW : (D + 1) ^ 2 * W ≤ T.card) :
    ((T.card : ℝ) - (D + 1) ^ 2 * W) * (1 / (400 * π)) - T.card * ((|s₁| + |s₂|) * Ωf D / (2 * π))
      ≤ ∑ p ∈ T, G2 s₁ s₂ (θ p) (θ' p) := by
  have hpi := Real.pi_pos
  have hfc : Continuous (fej D) := fej_continuous D
  set I2 := ∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' with hI2
  have hmean := mean_G2 s₁ s₂ hs
  have hpt := fun p => smooth2_pt D s₁ s₂ (θ p) (θ' p)
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ T) => hpt p)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  -- swap the sum and the integrals
  have hcont : ∀ p, Continuous (fun φ => ∫ φ' in (0 : ℝ)..(2 * π),
      G2 s₁ s₂ φ φ' * (fej D (θ p - φ) * fej D (θ' p - φ'))) := by
    intro p
    exact cont_param (fun φ φ' => G2 s₁ s₂ φ φ' * (fej D (θ p - φ) * fej D (θ' p - φ')))
      (by unfold G2; fun_prop) 0 (2 * π)
  have hswap : ∑ p ∈ T, (∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π),
        G2 s₁ s₂ φ φ' * (fej D (θ p - φ) * fej D (θ' p - φ')))
      = ∫ φ in (0 : ℝ)..(2 * π), ∫ φ' in (0 : ℝ)..(2 * π),
        G2 s₁ s₂ φ φ' * ∑ p ∈ T, fej D (θ p - φ) * fej D (θ' p - φ') := by
    rw [← intervalIntegral.integral_finsetSum (fun p _ => (hcont p).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun φ _ => ?_)
    rw [← intervalIntegral.integral_finsetSum (fun p _ =>
      (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _))]
    refine intervalIntegral.integral_congr (fun φ' _ => ?_)
    simp only [Finset.mul_sum]
  have hlow : ((T.card : ℝ) - (D + 1) ^ 2 * W) * I2 ≤ ∫ φ in (0 : ℝ)..(2 * π),
      ∫ φ' in (0 : ℝ)..(2 * π), G2 s₁ s₂ φ φ' * ∑ p ∈ T, fej D (θ p - φ) * fej D (θ' p - φ') := by
    rw [hI2, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_const.mul (cont_param (fun φ φ' => G2 s₁ s₂ φ φ') (G2_cont s₁ s₂) 0
        (2 * π))).intervalIntegrable _ _
    · exact (cont_param (fun φ φ' => G2 s₁ s₂ φ φ' * ∑ p ∈ T, fej D (θ p - φ) * fej D (θ' p - φ'))
        (by unfold G2; fun_prop) 0 (2 * π)).intervalIntegrable _ _
    · intro φ _
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
      · exact (Continuous.intervalIntegrable (by (try unfold G2); fun_prop) _ _)
      · intro φ' _
        have h1 := sum2_fej T θ θ' D W hW0 hW2 φ φ'
        have h2 := G2_nonneg s₁ s₂ φ φ'
        nlinarith
  have hc0 : 0 ≤ (T.card : ℝ) - (D + 1) ^ 2 * W := by linarith
  have h3 : ((T.card : ℝ) - (D + 1) ^ 2 * W) * (π / 100) ≤ ((T.card : ℝ) - (D + 1) ^ 2 * W) * I2 :=
    mul_le_mul_of_nonneg_left hmean hc0
  -- combine: 4π² Σ G ≥ (card - ..) I2 - card · 2π (|s₁|+|s₂|) Ω
  have hfin : ((T.card : ℝ) - (D + 1) ^ 2 * W) * (π / 100) - T.card * (2 * π * ((|s₁| + |s₂|) * Ωf D))
      ≤ 4 * π ^ 2 * ∑ p ∈ T, G2 s₁ s₂ (θ p) (θ' p) := by
    rw [hswap] at hsum; linarith
  have e : ((T.card : ℝ) - (D + 1) ^ 2 * W) * (1 / (400 * π)) -
      T.card * ((|s₁| + |s₂|) * Ωf D / (2 * π))
      = (((T.card : ℝ) - (D + 1) ^ 2 * W) * (π / 100) -
        T.card * (2 * π * ((|s₁| + |s₂|) * Ωf D))) / (4 * π ^ 2) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

end K525


namespace K525

variable {n : ℕ}

/-! ## S2, part b: the two-point cosine product -/

/-- The two-point cosine product. -/
def Pc2 (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) : ℝ :=
  ∏ p, Real.cos (2 * π * (u * wv t ξ p + v * wv t ξ' p))

/-- The covariance. -/
def Cv (t : Fin (K n) → Bool) (ξ ξ' : ℝ) : ℝ := ∑ p, wv t ξ p * wv t ξ' p

lemma abs_x2_le (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) (p : Fin (K n)) :
    |2 * π * (u * wv t ξ p + v * wv t ξ' p)| ≤ 4 * π * (|u| + |v|) := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 := abs_wv_le t ξ p
  have h2 := abs_wv_le t ξ' p
  have h3 : |u * wv t ξ p + v * wv t ξ' p| ≤ |u| * 2 + |v| * 2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg u))
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg v))
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

lemma sum_x2_sq (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) :
    ∑ p, (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 =
      4 * π ^ 2 * (u ^ 2 * Vv t ξ + 2 * u * v * Cv t ξ ξ' + v ^ 2 * Vv t ξ') := by
  unfold Vv Cv
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by ring)

lemma abs_Pc2_le_one (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) : |Pc2 t ξ ξ' u v| ≤ 1 := by
  unfold Pc2
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun p _ => abs_nonneg _) (fun p _ => Real.abs_cos_le_one _)

lemma Pc2_core (t : Fin (K n) → Bool) (ξ ξ' u v τ : ℝ) (hu : |u| ≤ τ) (hv : |v| ≤ τ)
    (hτ : 8 * π * τ ≤ 1 / 2) :
    0 ≤ Pc2 t ξ ξ' u v ∧ Pc2 t ξ ξ' u v ≤
      Real.exp (-(2 * π ^ 2) * (u ^ 2 * Vv t ξ + 2 * u * v * Cv t ξ ξ' + v ^ 2 * Vv t ξ')) *
        Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4) := by
  set x : Fin (K n) → ℝ := fun p => 2 * π * (u * wv t ξ p + v * wv t ξ' p) with hx
  have hxb : ∀ p, |x p| ≤ 8 * π * τ := fun p => (abs_x2_le t ξ ξ' u v p).trans (by
    have : |u| + |v| ≤ 2 * τ := by linarith
    nlinarith [Real.pi_pos])
  have hx2 : ∀ p, |x p| ≤ 1 / 2 := fun p => (hxb p).trans hτ
  have hsq : ∑ p, x p ^ 2 = 4 * π ^ 2 * (u ^ 2 * Vv t ξ + 2 * u * v * Cv t ξ ξ' + v ^ 2 * Vv t ξ') :=
    sum_x2_sq t ξ ξ' u v
  have h4 : ∑ p, x p ^ 4 ≤ (K n : ℝ) * (8 * π * τ) ^ 4 := by
    calc ∑ p, x p ^ 4 ≤ ∑ _p : Fin (K n), (8 * π * τ) ^ 4 := Finset.sum_le_sum (fun p _ => by
          have e : |x p| ^ 4 = x p ^ 4 := Even.pow_abs ⟨2, rfl⟩ _
          rw [← e]; exact pow_le_pow_left₀ (abs_nonneg _) (hxb p) 4)
      _ = (K n : ℝ) * (8 * π * τ) ^ 4 := by simp
  have hcos : ∀ p, 0 ≤ Real.cos (x p) := fun p => Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(abs_le.mp (hx2 p)).1, Real.pi_gt_three],
      by linarith [(abs_le.mp (hx2 p)).2, Real.pi_gt_three]⟩
  refine ⟨Finset.prod_nonneg (fun p _ => hcos p), ?_⟩
  calc Pc2 t ξ ξ' u v ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + ∑ p, x p ^ 4) := prod_cos_upper x hx2
    _ ≤ Real.exp (-(∑ p, x p ^ 2) / 2 + (K n : ℝ) * (8 * π * τ) ^ 4) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [← Real.exp_add, hsq]; congr 1; ring

lemma abs_cos_le_jordan {x : ℝ} (hx : |x| ≤ π / 2) : |Real.cos x| ≤ Real.exp (-(2 * x ^ 2 / π ^ 2)) := by
  have hpi := Real.pi_pos
  have hj : 2 / π * |x| ≤ |Real.sin x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at hx ⊢
      have := Real.mul_le_sin h hx
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h] at hx ⊢
      have := Real.mul_le_sin (by linarith : 0 ≤ -x) hx
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hsq : (2 / π * |x|) ^ 2 ≤ Real.sin x ^ 2 := by
    rw [← sq_abs (Real.sin x)]; exact pow_le_pow_left₀ (by positivity) hj 2
  refine (abs_cos_le_exp x).trans (Real.exp_le_exp.mpr ?_)
  have e : (2 / π * |x|) ^ 2 = 4 * x ^ 2 / π ^ 2 := by rw [mul_pow, sq_abs]; field_simp; ring
  rw [e] at hsq
  have : 2 * x ^ 2 / π ^ 2 = (4 * x ^ 2 / π ^ 2) / 2 := by ring
  linarith

lemma Pc2_mid (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) (h : 4 * π * (|u| + |v|) ≤ π / 2) :
    |Pc2 t ξ ξ' u v| ≤
      Real.exp (-(8 * (u ^ 2 * Vv t ξ + 2 * u * v * Cv t ξ ξ' + v ^ 2 * Vv t ξ'))) := by
  have hpi := Real.pi_pos
  unfold Pc2
  rw [Finset.abs_prod]
  calc ∏ p, |Real.cos (2 * π * (u * wv t ξ p + v * wv t ξ' p))|
      ≤ ∏ p, Real.exp (-(2 * (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 / π ^ 2)) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _)
          (fun p _ => abs_cos_le_jordan ((abs_x2_le t ξ ξ' u v p).trans h))
    _ = Real.exp (∑ p, (-(2 * (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 / π ^ 2))) :=
        (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [show (∑ p, (-(2 * (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 / π ^ 2)))
            = -(2 / π ^ 2) * ∑ p, (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring),
          sum_x2_sq]
        field_simp
        ring

open scoped Classical in
lemma abs_Pc2_inter (t : Fin (K n) → Bool) (ξ ξ' u v : ℝ) :
    |Pc2 t ξ ξ' u v| ≤ Real.exp (-(∑ p ∈ univ.filter (fun p => t p = false),
      G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ')) / 2) := by
  have hs : ∑ p, Real.sin (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 =
      ∑ p ∈ univ.filter (fun p => t p = false),
        G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ') := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold wv G2
    cases t p
    · simp only [Bool.false_eq_true, if_false, if_true]
      ring_nf
    · simp
  unfold Pc2
  rw [Finset.abs_prod, ← hs]
  calc ∏ p, |Real.cos (2 * π * (u * wv t ξ p + v * wv t ξ' p))|
      ≤ ∏ p, Real.exp (-(Real.sin (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2) / 2) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => abs_cos_le_exp _)
    _ = Real.exp (∑ p, (-(Real.sin (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2) / 2)) :=
        (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [show (∑ p, (-(Real.sin (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2) / 2))
            = (-1 / 2) * ∑ p, Real.sin (2 * π * (u * wv t ξ p + v * wv t ξ' p)) ^ 2 by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)]
        ring

lemma Pc2_continuous (t : Fin (K n) → Bool) (ξ ξ' : ℝ) :
    Continuous (fun q : ℝ × ℝ => Pc2 t ξ ξ' q.1 q.2) := by
  unfold Pc2
  exact continuous_finset_prod _ (fun p _ => by fun_prop)

lemma E2_eq (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ ξ' : ℝ) :
    ((E2 δ hδ t ξ ξ' : ℝ) : ℂ) = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (psi δ hδ : ℝ → ℂ) u * 𝓕 (psi δ hδ : ℝ → ℂ) v *
      ((Pc2 t ξ ξ' u v : ℝ) : ℂ) := by
  have h := avg_schwartz2 (psi δ hδ) (wv t ξ) (wv t ξ')
  rw [Fintype.card_fin] at h
  have hb : ∀ b : Fin (K n) → ℤˣ, psi δ hδ (∑ p, ((b p : ℤ) : ℝ) * wv t ξ p) *
      psi δ hδ (∑ p, ((b p : ℤ) : ℝ) * wv t ξ' p)
      = ((bumpR δ hδ (IIt t b ξ) : ℝ) : ℂ) * ((bumpR δ hδ (IIt t b ξ') : ℝ) : ℂ) := by
    intro b; rw [psi_apply, psi_apply, IIt_eq, IIt_eq]
  simp_rw [hb] at h
  unfold E2
  push_cast
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [Pc2, Complex.ofReal_prod]

lemma Cv_eq (t : Fin (K n) → Bool) (ξ ξ' : ℝ) :
    Cv t ξ ξ' = Dc n (ξ - ξ') - Dc n (ξ + ξ') + 2 * ∑ p, sg (t p) * (Real.cos (kk n p * (ξ - ξ')) / 2)
      - 2 * ∑ p, sg (t p) * (Real.cos (kk n p * (ξ + ξ')) / 2) := by
  unfold Cv Dc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have h1 : Real.cos (kk n p * (ξ - ξ')) = Real.cos (kk n p * ξ) * Real.cos (kk n p * ξ') +
      Real.sin (kk n p * ξ) * Real.sin (kk n p * ξ') := by
    rw [mul_sub, Real.cos_sub]
  have h2 : Real.cos (kk n p * (ξ + ξ')) = Real.cos (kk n p * ξ) * Real.cos (kk n p * ξ') -
      Real.sin (kk n p * ξ) * Real.sin (kk n p * ξ') := by
    rw [mul_add, Real.cos_add]
  unfold wv
  rw [h1, h2]
  cases t p <;> simp [sg] <;> ring

open scoped Classical in
lemma abs_Cv_le (t : Fin (K n) → Bool) (ht : Typical n t) (ξ ξ' : ℝ)
    (hξ : ξ ∈ Set.Icc (π / 8) (3 * π / 8)) (hξ' : ξ' ∈ Set.Icc (π / 8) (3 * π / 8))
    (hsep : (n : ℝ) ^ (-(3 / 5) : ℝ) ≤ |ξ - ξ'|) (hn : 1 ≤ n) :
    |Cv t ξ ξ'| ≤ 8 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have hpi := Real.pi_pos
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP1 : 1 ≤ (n : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have h0 := (abs_re_le_norm' (Ssum t (ξ - ξ'))).trans (ht (ξ - ξ'))
  have h1 := (abs_re_le_norm' (Ssum t (ξ + ξ'))).trans (ht (ξ + ξ'))
  rw [re_Ssum] at h0 h1
  have h2 := abs_Dc_le_sqrt2 n (x := ξ + ξ') (by linarith [hξ.1, hξ'.1]) (by linarith [hξ.2, hξ'.2])
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  -- the small difference
  have hd : |ξ - ξ'| ≤ π / 2 := by
    rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2, hξ'.1, hξ'.2]
  have hsin : 2 / π * (n : ℝ) ^ (-(3 / 5) : ℝ) ≤ |Real.sin (ξ - ξ')| := by
    have hj : 2 / π * |ξ - ξ'| ≤ |Real.sin (ξ - ξ')| := by
      rcases le_total 0 (ξ - ξ') with h | h
      · rw [abs_of_nonneg h] at hd ⊢
        exact (Real.mul_le_sin h hd).trans (le_abs_self _)
      · rw [abs_of_nonpos h] at hd ⊢
        have := Real.mul_le_sin (by linarith : 0 ≤ -(ξ - ξ')) hd
        rw [Real.sin_neg] at this
        exact this.trans (neg_le_abs _)
    exact le_trans (mul_le_mul_of_nonneg_left hsep (by positivity)) hj
  have hpos : 0 < 2 / π * (n : ℝ) ^ (-(3 / 5) : ℝ) := by positivity
  have hs0 : Real.sin (ξ - ξ') ≠ 0 := by
    intro h; rw [h, abs_zero] at hsin; linarith
  have h3 := abs_Dc_le n (ξ - ξ') hs0
  have h4 : 1 / |Real.sin (ξ - ξ')| ≤ π / 2 * (n : ℝ) ^ (3 / 5 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have e : π / 2 * (n : ℝ) ^ (3 / 5 : ℝ) * (2 / π * (n : ℝ) ^ (-(3 / 5) : ℝ)) = 1 := by
      rw [Real.rpow_neg hN0.le]; field_simp
    calc (1 : ℝ) = π / 2 * (n : ℝ) ^ (3 / 5 : ℝ) * (2 / π * (n : ℝ) ^ (-(3 / 5) : ℝ)) := e.symm
      _ ≤ π / 2 * (n : ℝ) ^ (3 / 5 : ℝ) * |Real.sin (ξ - ξ')| :=
          mul_le_mul_of_nonneg_left hsin (by positivity)
  rw [Cv_eq]
  obtain ⟨a0, b0⟩ := abs_le.mp h0
  obtain ⟨a1, b1⟩ := abs_le.mp h1
  obtain ⟨a2, b2⟩ := abs_le.mp h2
  obtain ⟨a3, b3⟩ := abs_le.mp (h3.trans h4)
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_lt_four]

/-- The quadratic form is nondegenerate. -/
lemma Q_lower (u v V V' C ρ N : ℝ) (hV : N / 4 ≤ V) (hV' : N / 4 ≤ V') (hρ : 0 ≤ ρ)
    (hC : |C| ≤ ρ * (N / 4)) :
    (1 - ρ) * (u ^ 2 * V + v ^ 2 * V') ≤ u ^ 2 * V + 2 * u * v * C + v ^ 2 * V' := by
  have h1 : |2 * u * v * C| ≤ (u ^ 2 + v ^ 2) * |C| := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    have : 2 * |u| * |v| ≤ u ^ 2 + v ^ 2 := by
      have := sq_nonneg (|u| - |v|); rw [sub_sq, sq_abs, sq_abs] at this; linarith
    nlinarith [abs_nonneg C]
  have h2 : (u ^ 2 + v ^ 2) * |C| ≤ (u ^ 2 + v ^ 2) * (ρ * (N / 4)) :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  have h3 : (u ^ 2 + v ^ 2) * (ρ * (N / 4)) ≤ ρ * (u ^ 2 * V + v ^ 2 * V') := by
    have := mul_le_mul_of_nonneg_left hV (sq_nonneg u)
    have := mul_le_mul_of_nonneg_left hV' (sq_nonneg v)
    nlinarith
  have := neg_abs_le (2 * u * v * C)
  nlinarith

/-- Far region with an `N²` gain. -/
lemma fourier_far2 (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ u : ℝ,
    N ^ (1 / 100 : ℝ) ≤ |u| → ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ 2 * C / N ^ 2 * (1 + u ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := fourier_psi_decay δ hδ 202
  refine ⟨C, hC0, fun N hN u hu => ?_⟩
  have hT1 : 1 ≤ N ^ (1 / 100 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hu1 : 1 ≤ |u| := hT1.trans hu
  have hu0 : 0 < |u| := by linarith
  have hN200 : N ^ 2 ≤ |u| ^ (200 : ℕ) := by
    calc N ^ 2 = (N ^ (1 / 100 : ℝ)) ^ (200 : ℕ) := by
          rw [← Real.rpow_natCast (N ^ (1 / 100 : ℝ)) 200, ← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ |u| ^ (200 : ℕ) := pow_le_pow_left₀ (by positivity) hu 200
  have hb := hC u
  have hu2 : 1 ≤ u ^ 2 := by rw [← sq_abs]; nlinarith
  have h1 : ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ C / (|u| ^ 200 * u ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have e : |u| ^ 202 = |u| ^ 200 * u ^ 2 := by
      rw [show (202 : ℕ) = 200 + 2 from rfl, pow_add, sq_abs]
    rw [← e, mul_comm]; exact hb
  have h2 : C / (|u| ^ 200 * u ^ 2) ≤ 2 * C / (N ^ 2 * (1 + u ^ 2)) := by
    have hA : N ^ 2 * (1 + u ^ 2) ≤ |u| ^ 200 * (2 * u ^ 2) :=
      mul_le_mul hN200 (by linarith) (by positivity) (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hA hC0]
  rw [← div_eq_mul_inv, div_div]
  exact h1.trans h2

/-- Iterated integrals against product majorants. -/
lemma norm_iter_le {k : ℕ} (f : ℝ → ℝ → ℂ) (a b : Fin k → ℝ → ℝ) (ha : ∀ i, Integrable (a i))
    (hb : ∀ i, Integrable (b i)) (h : ∀ u v, ‖f u v‖ ≤ ∑ i, a i u * b i v) :
    ‖∫ u, ∫ v, f u v‖ ≤ ∑ i, (∫ u, a i u) * (∫ v, b i v) := by
  have hin : ∀ u, ‖∫ v, f u v‖ ≤ ∑ i, a i u * ∫ v, b i v := by
    intro u
    refine (norm_integral_le_of_norm_le (g := fun v => ∑ i, a i u * b i v)
      (integrable_finsetSum _ (fun i _ => (hb i).const_mul _))
      (Filter.Eventually.of_forall (h u))).trans (le_of_eq ?_)
    rw [integral_finsetSum _ (fun i _ => (hb i).const_mul _)]
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  refine (norm_integral_le_of_norm_le (g := fun u => ∑ i, a i u * ∫ v, b i v)
    (integrable_finsetSum _ (fun i _ => (ha i).mul_const _))
    (Filter.Eventually.of_forall hin)).trans (le_of_eq ?_)
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)

/-- Weyl sums of the `B`-type set at a non-resonant frequency. -/
lemma weyl_x (t : Fin (K n) → Bool) (ht : Typical n t) (x : ℝ) (hε : 0 < εn n)
    (hsx : εn n ≤ |Real.sin x|) :
    ‖∑ p ∈ univ.filter (fun p => t p = false), Complex.exp (↑(kk n p * x) * Complex.I)‖
      ≤ 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ) := by
  have hsplit : ∑ p ∈ univ.filter (fun p => t p = false), Complex.exp (↑(kk n p * x) * Complex.I)
      = (1 / 2 : ℂ) * ∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I) + Ssum t x := by
    rw [Finset.sum_filter]
    unfold Ssum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    cases t p <;> simp <;> ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (ht x))
  have hs0 : Real.sin x ≠ 0 := by
    intro h; rw [h, abs_zero] at hsx; linarith
  have hd := dirichlet n x hs0
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖∑ p : Fin (K n), Complex.exp (↑(kk n p * x) * Complex.I)‖
      ≤ 1 / 2 * (1 / |Real.sin x|) := by gcongr
    _ ≤ 1 / 2 * (1 / εn n) := by gcongr
    _ = 1 / (2 * εn n) := by ring

lemma exp_neg_le_six_div_cube {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 6 / y ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (x := y) hy.le 3
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

end K525


namespace K525

variable {n : ℕ}

/-! ## S2, part c: the deterministic two-point bound -/

/-- **S2, pointwise majorant (abstract form).** -/
lemma S2_pt (nu nv P A κ E L Cf τ T u v g1 g2 φu φv iu iv : ℝ) (hA0 : 0 ≤ A)
    (hnu0 : 0 ≤ nu) (hnv0 : 0 ≤ nv) (hnu : nu ≤ A) (hnv : nv ≤ A) (hP1 : |P| ≤ 1)
    (h0 : 0 ≤ A ^ 2 * κ * g1 * g2) (hE0 : 0 ≤ E) (hφu : 0 ≤ φu) (hφv : 0 ≤ φv)
    (hiu0 : 0 ≤ iu) (hiv0 : 0 ≤ iv) (hCf : 0 ≤ Cf)
    (hcore : |u| ≤ τ → |v| ≤ τ → nu * nv * |P| ≤ A ^ 2 * κ * g1 * g2)
    (hmid : |u| ≤ 1 / 16 → |v| ≤ 1 / 16 → (τ < |u| ∨ τ < |v|) → |P| ≤ E * φu * φv)
    (hinter : |u| ≤ T → |v| ≤ T → ¬ (|u| ≤ 1 / 16 ∧ |v| ≤ 1 / 16) → |P| ≤ Real.exp (-L))
    (hiu : |u| ≤ T → iu = 1) (hiv : |v| ≤ T → iv = 1)
    (hfu : T < |u| → nu ≤ Cf * (1 + u ^ 2)⁻¹) (hfv : T < |v| → nv ≤ Cf * (1 + v ^ 2)⁻¹) :
    nu * nv * |P| ≤ A ^ 2 * κ * g1 * g2 + A ^ 2 * E * φu * φv +
      A ^ 2 * Real.exp (-L) * iu * iv + Cf * (1 + u ^ 2)⁻¹ * nv + nu * (Cf * (1 + v ^ 2)⁻¹) := by
  have hm1 : 0 ≤ A ^ 2 * E * φu * φv := by positivity
  have hm2 : 0 ≤ A ^ 2 * Real.exp (-L) * iu * iv := by positivity
  have hm3 : 0 ≤ Cf * (1 + u ^ 2)⁻¹ * nv := by positivity
  have hm4 : 0 ≤ nu * (Cf * (1 + v ^ 2)⁻¹) := by positivity
  have hP0 := abs_nonneg P
  have hnn : nu * nv ≤ A ^ 2 := by nlinarith
  by_cases hTu : T < |u|
  · have := hfu hTu
    have : nu * nv * |P| ≤ Cf * (1 + u ^ 2)⁻¹ * nv := by
      calc nu * nv * |P| ≤ nu * nv * 1 := mul_le_mul_of_nonneg_left hP1 (by positivity)
        _ = nu * nv := by ring
        _ ≤ Cf * (1 + u ^ 2)⁻¹ * nv := mul_le_mul_of_nonneg_right this hnv0
    linarith
  by_cases hTv : T < |v|
  · have := hfv hTv
    have : nu * nv * |P| ≤ nu * (Cf * (1 + v ^ 2)⁻¹) := by
      calc nu * nv * |P| ≤ nu * nv * 1 := mul_le_mul_of_nonneg_left hP1 (by positivity)
        _ = nu * nv := by ring
        _ ≤ nu * (Cf * (1 + v ^ 2)⁻¹) := mul_le_mul_of_nonneg_left this hnu0
    linarith
  push Not at hTu hTv
  by_cases hc : |u| ≤ τ ∧ |v| ≤ τ
  · have := hcore hc.1 hc.2; linarith
  by_cases hm : |u| ≤ 1 / 16 ∧ |v| ≤ 1 / 16
  · have hτ : τ < |u| ∨ τ < |v| := by
      by_contra h; push Not at h; exact hc ⟨h.1, h.2⟩
    have hb := hmid hm.1 hm.2 hτ
    have : nu * nv * |P| ≤ A ^ 2 * E * φu * φv := by
      calc nu * nv * |P| ≤ A ^ 2 * (E * φu * φv) := mul_le_mul hnn hb hP0 (by positivity)
        _ = _ := by ring
    linarith
  · have hb := hinter hTu hTv hm
    rw [hiu hTu, hiv hTv] at hm2 ⊢
    have : nu * nv * |P| ≤ A ^ 2 * Real.exp (-L) * 1 * 1 := by
      calc nu * nv * |P| ≤ A ^ 2 * Real.exp (-L) := mul_le_mul hnn hb hP0 (by positivity)
        _ = _ := by ring
    linarith

lemma S2_core_pt (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ ξ' N ρ τ u v : ℝ)
    (hV : N / 4 ≤ Vv t ξ) (hV' : N / 4 ≤ Vv t ξ') (hρ0 : 0 ≤ ρ)
    (hC : |Cv t ξ ξ'| ≤ ρ * (N / 4)) (hτ : 8 * π * τ ≤ 1 / 2) (hu : |u| ≤ τ) (hv : |v| ≤ τ) :
    ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ * ‖𝓕 (psi δ hδ : ℝ → ℂ) v‖ * |Pc2 t ξ ξ' u v| ≤
      Ad δ hδ ^ 2 * ((1 + π * δ * τ) ^ 2 * Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4)) *
        Real.exp (-(2 * π ^ 2 * ((1 - ρ) * Vv t ξ)) * u ^ 2) *
        Real.exp (-(2 * π ^ 2 * ((1 - ρ) * Vv t ξ')) * v ^ 2) := by
  obtain ⟨hP0, hP1⟩ := Pc2_core t ξ ξ' u v τ hu hv hτ
  have hA0 := Ad_pos δ hδ
  have hFc : ∀ w, |w| ≤ τ → ‖𝓕 (psi δ hδ : ℝ → ℂ) w‖ ≤ Ad δ hδ * (1 + π * δ * τ) := by
    intro w hw
    have hl := fourier_psi_lip δ hδ w
    rw [fourier_psi_zero] at hl
    have h1 : ‖𝓕 (psi δ hδ : ℝ → ℂ) w‖ ≤ ‖𝓕 (psi δ hδ : ℝ → ℂ) w - (Ad δ hδ : ℂ)‖ + ‖(Ad δ hδ : ℂ)‖ := by
      have := norm_add_le (𝓕 (psi δ hδ : ℝ → ℂ) w - (Ad δ hδ : ℂ)) (Ad δ hδ : ℂ)
      rwa [sub_add_cancel] at this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0] at h1
    have : π * δ * |w| * Ad δ hδ ≤ π * δ * τ * Ad δ hδ := by gcongr
    nlinarith
  have hQ := Q_lower u v (Vv t ξ) (Vv t ξ') (Cv t ξ ξ') ρ N hV hV' hρ0 hC
  generalize Vv t ξ = V at hQ hP1 ⊢
  generalize Vv t ξ' = V' at hQ hP1 ⊢
  generalize Cv t ξ ξ' = C at hQ hP1
  have hPg : Pc2 t ξ ξ' u v ≤ Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V)) * u ^ 2) *
      Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V')) * v ^ 2) *
      Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4) := by
    refine hP1.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hπ : 0 ≤ 2 * π ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hQ hπ
    nlinarith
  rw [abs_of_nonneg hP0]
  have hn1 := hFc u hu
  have hn2 := hFc v hv
  have hτ1 : 0 ≤ Ad δ hδ * (1 + π * δ * τ) := le_trans (norm_nonneg _) hn1
  calc ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ * ‖𝓕 (psi δ hδ : ℝ → ℂ) v‖ * Pc2 t ξ ξ' u v
      ≤ (Ad δ hδ * (1 + π * δ * τ)) * (Ad δ hδ * (1 + π * δ * τ)) *
          (Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V)) * u ^ 2) *
            Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V')) * v ^ 2) *
            Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4)) :=
        mul_le_mul (mul_le_mul hn1 hn2 (norm_nonneg _) hτ1) hPg hP0 (by positivity)
    _ = _ := by ring

lemma S2_mid_pt (t : Fin (K n) → Bool) (ξ ξ' N ρ τ u v : ℝ) (hN0 : 0 < N)
    (hV : N / 4 ≤ Vv t ξ) (hV' : N / 4 ≤ Vv t ξ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (hC : |Cv t ξ ξ'| ≤ ρ * (N / 4)) (hτ0 : 0 < τ) (hu : |u| ≤ 1 / 16) (hv : |v| ≤ 1 / 16)
    (hτ' : τ < |u| ∨ τ < |v|) :
    |Pc2 t ξ ξ' u v| ≤ Real.exp (-(N * τ ^ 2 / 2)) * Real.exp (-(N / 2) * u ^ 2) *
      Real.exp (-(N / 2) * v ^ 2) := by
  have hm : 4 * π * (|u| + |v|) ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hb := Pc2_mid t ξ ξ' u v hm
  have hQ := Q_lower u v (Vv t ξ) (Vv t ξ') (Cv t ξ ξ') ρ N hV hV' hρ0 hC
  generalize Vv t ξ = V at hQ hb hV
  generalize Vv t ξ' = V' at hQ hb hV'
  generalize Cv t ξ ξ' = C at hQ hb
  have huv : τ ^ 2 ≤ u ^ 2 + v ^ 2 := by
    rcases hτ' with h | h
    · have := pow_le_pow_left₀ hτ0.le h.le 2; rw [sq_abs] at this; nlinarith [sq_nonneg v]
    · have := pow_le_pow_left₀ hτ0.le h.le 2; rw [sq_abs] at this; nlinarith [sq_nonneg u]
  refine hb.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hS0 : 0 ≤ u ^ 2 * V + v ^ 2 * V' := by
    have : 0 ≤ V := by linarith
    have : 0 ≤ V' := by linarith
    positivity
  have h1 : (1 / 2) * (u ^ 2 * V + v ^ 2 * V') ≤ (1 - ρ) * (u ^ 2 * V + v ^ 2 * V') :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  have h2a := mul_le_mul_of_nonneg_left hV (sq_nonneg u)
  have h2b := mul_le_mul_of_nonneg_left hV' (sq_nonneg v)
  have h3 := mul_le_mul_of_nonneg_left huv hN0.le
  linarith

set_option maxHeartbeats 1000000 in
/-- **S2, deterministic form.** -/
lemma S2_det (δ : ℝ) (hδ : 0 < δ) (t : Fin (K n) → Bool) (ξ ξ' : ℝ) (N ρ τ T lam Cf : ℝ)
    (hN0 : 0 < N) (hV : N / 4 ≤ Vv t ξ) (hV' : N / 4 ≤ Vv t ξ') (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (hC : |Cv t ξ ξ'| ≤ ρ * (N / 4)) (hτ0 : 0 < τ) (hτ : 8 * π * τ ≤ 1 / 2) (hT : 0 ≤ T)
    (hinter : ∀ u v, |u| ≤ T → |v| ≤ T → ¬ (|u| ≤ 1 / 16 ∧ |v| ≤ 1 / 16) →
      |Pc2 t ξ ξ' u v| ≤ Real.exp (-lam))
    (hCf : 0 ≤ Cf) (hfar : ∀ u, T < |u| → ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ Cf * (1 + u ^ 2)⁻¹) :
    E2 δ hδ t ξ ξ' ≤
      Ad δ hδ ^ 2 * ((1 + π * δ * τ) ^ 2 * Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4)) /
          Real.sqrt (2 * π * ((1 - ρ) * Vv t ξ)) * (1 / Real.sqrt (2 * π * ((1 - ρ) * Vv t ξ'))) +
        Ad δ hδ ^ 2 * Real.exp (-(N * τ ^ 2 / 2)) * (π / (N / 2)) +
        Ad δ hδ ^ 2 * Real.exp (-lam) * (2 * T) * (2 * T) +
        2 * (Cf * π * ∫ v, ‖𝓕 (psi δ hδ : ℝ → ℂ) v‖) := by
  have hpi := Real.pi_pos
  have hA0 := Ad_pos δ hδ
  set A := Ad δ hδ with hA
  set F := 𝓕 (psi δ hδ : ℝ → ℂ) with hF
  set V := Vv t ξ with hVdef
  set V' := Vv t ξ' with hV'def
  set C := Cv t ξ ξ' with hCdef
  set κ := (1 + π * δ * τ) ^ 2 * Real.exp ((K n : ℝ) * (8 * π * τ) ^ 4) with hκ
  set E := Real.exp (-(N * τ ^ 2 / 2)) with hE
  set Φ := ∫ v, ‖F v‖ with hΦ
  have hVp : 0 < V := by linarith
  have hV'p : 0 < V' := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  set g1 : ℝ → ℝ := fun u => Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V)) * u ^ 2) with hg1
  set g2 : ℝ → ℝ := fun u => Real.exp (-(2 * π ^ 2 * ((1 - ρ) * V')) * u ^ 2) with hg2
  set φ : ℝ → ℝ := fun u => Real.exp (-(N / 2) * u ^ 2) with hφ
  set ind : ℝ → ℝ := fun u => (Set.Icc (-T) T).indicator (fun _ => (1 : ℝ)) u with hind
  set a : Fin 5 → ℝ → ℝ := ![fun u => A ^ 2 * κ * g1 u, fun u => A ^ 2 * E * φ u,
    fun u => A ^ 2 * Real.exp (-lam) * ind u, fun u => Cf * (1 + u ^ 2)⁻¹, fun u => ‖F u‖] with ha
  set b : Fin 5 → ℝ → ℝ := ![g2, φ, ind, fun v => ‖F v‖, fun v => Cf * (1 + v ^ 2)⁻¹] with hb
  have ig1 : Integrable g1 := integrable_exp_neg_mul_sq (by positivity)
  have ig2 : Integrable g2 := integrable_exp_neg_mul_sq (by positivity)
  have iφ : Integrable φ := integrable_exp_neg_mul_sq (by positivity)
  have iind : Integrable ind :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have iF : Integrable (fun v => ‖F v‖) := (fourier_integrable (psi δ hδ)).norm
  have iC : Integrable (fun u : ℝ => Cf * (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  have hia : ∀ i, Integrable (a i) := by
    intro i; fin_cases i
    · exact ig1.const_mul _
    · exact iφ.const_mul _
    · exact iind.const_mul _
    · exact iC
    · exact iF
  have hib : ∀ i, Integrable (b i) := by
    intro i; fin_cases i
    · exact ig2
    · exact iφ
    · exact iind
    · exact iF
    · exact iC
  -- pointwise
  have hpt : ∀ u v, ‖F u * F v * ((Pc2 t ξ ξ' u v : ℝ) : ℂ)‖ ≤ ∑ i, a i u * b i v := by
    intro u v
    rw [Fin.sum_univ_five, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hFl : ∀ w, ‖F w‖ ≤ A := fun w => fourier_psi_le δ hδ w
    refine S2_pt ‖F u‖ ‖F v‖ (Pc2 t ξ ξ' u v) A κ E lam Cf τ T u v (g1 u) (g2 v) (φ u) (φ v)
      (ind u) (ind v) hA0.le (norm_nonneg _) (norm_nonneg _) (hFl u) (hFl v)
      (abs_Pc2_le_one t ξ ξ' u v) (by positivity) (by positivity) (by positivity) (by positivity)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) u)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) v) hCf ?_ ?_ (hinter u v) ?_ ?_
      (hfar u) (hfar v)
    · exact S2_core_pt δ hδ t ξ ξ' N ρ τ u v hV hV' hρ0 hC hτ
    · intro hu hv hτ'
      exact (S2_mid_pt t ξ ξ' N ρ τ u v hN0 hV hV' hρ0 hρ1 hC hτ0 hu hv hτ').trans (le_of_eq rfl)
    · intro hu
      exact Set.indicator_of_mem (show u ∈ Set.Icc (-T) T from abs_le.mp hu) (fun _ => (1 : ℝ))
    · intro hv
      exact Set.indicator_of_mem (show v ∈ Set.Icc (-T) T from abs_le.mp hv) (fun _ => (1 : ℝ))
  have hbound := norm_iter_le (fun u v => F u * F v * ((Pc2 t ξ ξ' u v : ℝ) : ℂ)) a b hia hib hpt
  have hE2 : E2 δ hδ t ξ ξ' ≤ ‖((E2 δ hδ t ξ ξ' : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  rw [E2_eq] at hE2
  have e0 : ∫ u, a 0 u = A ^ 2 * κ / Real.sqrt (2 * π * ((1 - ρ) * V)) := by
    show ∫ u, A ^ 2 * κ * g1 u = _
    exact gauss_int _ _ (by positivity)
  have e0' : ∫ v, b 0 v = 1 / Real.sqrt (2 * π * ((1 - ρ) * V')) := by
    show ∫ v, g2 v = _
    have := gauss_int 1 ((1 - ρ) * V') (by positivity)
    simp only [one_mul] at this; exact this
  have e1 : ∫ u, a 1 u = A ^ 2 * E * Real.sqrt (π / (N / 2)) := by
    show ∫ u, A ^ 2 * E * φ u = _
    rw [integral_const_mul, integral_gaussian]
  have e1' : ∫ v, b 1 v = Real.sqrt (π / (N / 2)) := by
    show ∫ v, φ v = _
    exact integral_gaussian _
  have e2 : ∫ u, a 2 u = A ^ 2 * Real.exp (-lam) * (2 * T) := by
    show ∫ u, A ^ 2 * Real.exp (-lam) * ind u = _
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have e2' : ∫ v, b 2 v = 2 * T := by
    show ∫ v, ind v = _
    rw [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have e3 : ∫ u, a 3 u = Cf * π := by
    show ∫ u, Cf * (1 + u ^ 2)⁻¹ = _
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have e3' : ∫ v, b 3 v = Φ := rfl
  have e4 : ∫ u, a 4 u = Φ := rfl
  have e4' : ∫ v, b 4 v = Cf * π := by
    show ∫ v, Cf * (1 + v ^ 2)⁻¹ = _
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [Fin.sum_univ_five, e0, e0', e1, e1', e2, e2', e3, e3', e4, e4'] at hbound
  have hsq : Real.sqrt (π / (N / 2)) * Real.sqrt (π / (N / 2)) = π / (N / 2) :=
    Real.mul_self_sqrt (by positivity)
  calc E2 δ hδ t ξ ξ' ≤ _ := hE2.trans hbound
    _ = _ := by
        rw [mul_assoc (A ^ 2 * E), hsq]
        ring

end K525


namespace K525

variable {n : ℕ}

/-! ## S2, part d: parameters -/

lemma S2_weyl_size (n : ℕ) (hn : 16 ≤ n) (hF : 60 * (n : ℝ) ^ (-(3 / 20 : ℝ)) ≤ 1) (B : ℝ)
    (hB : (n : ℝ) / 5 ≤ B) :
    ((Dn n : ℝ) + 1) ^ 2 * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤ B / 2 := by
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hN1 : (1 : ℝ) ≤ n := by linarith
  have hε : 1 / (2 * εn n) = (n : ℝ) ^ (3 / 4 : ℝ) / 2 := by
    unfold εn; rw [Real.rpow_neg hN0.le]; field_simp
  rw [hε]
  have h1 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hD := Dn_le n
  have hD0 : (0 : ℝ) ≤ Dn n := Nat.cast_nonneg _
  have hP1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hD1 : (Dn n : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 / 20 : ℝ) := by linarith
  have hD2 : ((Dn n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ (1 / 10 : ℝ) := by
    have e : (n : ℝ) ^ (1 / 10 : ℝ) = ((n : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [e]
    have := pow_le_pow_left₀ (by positivity) hD1 2
    nlinarith
  have e2 : (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ (-(3 / 20) : ℝ) * n := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add_one hN0.ne']; norm_num
  have h3 : ((Dn n : ℝ) + 1) ^ 2 * ((n : ℝ) ^ (3 / 4 : ℝ) / 2 + (n : ℝ) ^ (3 / 5 : ℝ))
      ≤ 4 * (n : ℝ) ^ (1 / 10 : ℝ) * (3 / 2 * (n : ℝ) ^ (3 / 4 : ℝ)) :=
    mul_le_mul hD2 (by linarith) (by positivity) (by positivity)
  have h4 : 4 * (n : ℝ) ^ (1 / 10 : ℝ) * (3 / 2 * (n : ℝ) ^ (3 / 4 : ℝ))
      = 6 * ((n : ℝ) ^ (-(3 / 20) : ℝ) * n) := by rw [← e2]; ring
  have h5 : 6 * ((n : ℝ) ^ (-(3 / 20) : ℝ) * n) ≤ (n : ℝ) / 10 := by nlinarith
  linarith

open scoped Classical in
/-- The two-point intermediate region. -/
lemma S2_inter (n : ℕ) (hn : 16 ≤ n)
    (hΩ : 4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n) ≤ 1 / 1600)
    (t : Fin (K n) → Bool) (ht : Typical n t) (ξ ξ' : ℝ) (hnr : NR2 n ξ ξ')
    (hW : ((Dn n : ℝ) + 1) ^ 2 * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤
        ((univ.filter fun p => t p = false).card : ℝ) / 2) :
    ∀ u v, |u| ≤ (n : ℝ) ^ (1 / 100 : ℝ) → |v| ≤ (n : ℝ) ^ (1 / 100 : ℝ) →
      ¬ (|u| ≤ 1 / 16 ∧ |v| ≤ 1 / 16) →
      |Pc2 t ξ ξ' u v| ≤ Real.exp (-(((univ.filter fun p => t p = false).card : ℝ) / (3200 * π))) := by
  intro u v hu hv huv
  have hpi := Real.pi_pos
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hε : 0 < εn n := Real.rpow_pos_of_pos hN0 _
  set B := univ.filter fun p : Fin (K n) => t p = false with hBdef
  have hW0 : 0 ≤ 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ) := by positivity
  -- Weyl sums, both orders
  have hWa : ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ Dn n → |m₂| ≤ Dn n →
      ‖∑ p ∈ B, Complex.exp (↑((m₁ : ℝ) * (kk n p * ξ) + (m₂ : ℝ) * (kk n p * ξ')) * Complex.I)‖
        ≤ 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ) := by
    intro m₁ m₂ hm h1 h2
    have e : ∑ p ∈ B, Complex.exp (↑((m₁ : ℝ) * (kk n p * ξ) + (m₂ : ℝ) * (kk n p * ξ')) * Complex.I)
        = ∑ p ∈ B, Complex.exp (↑(kk n p * ((m₁ : ℝ) * ξ + (m₂ : ℝ) * ξ')) * Complex.I) :=
      Finset.sum_congr rfl (fun p _ => by congr 3; ring)
    rw [e]
    exact weyl_x t ht _ hε (hnr.2 m₁ m₂ hm h1 h2)
  have hWb : ∀ m₁ m₂ : ℤ, (m₁ ≠ 0 ∨ m₂ ≠ 0) → |m₁| ≤ Dn n → |m₂| ≤ Dn n →
      ‖∑ p ∈ B, Complex.exp (↑((m₁ : ℝ) * (kk n p * ξ') + (m₂ : ℝ) * (kk n p * ξ)) * Complex.I)‖
        ≤ 1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ) := by
    intro m₁ m₂ hm h1 h2
    have e : ∑ p ∈ B, Complex.exp (↑((m₁ : ℝ) * (kk n p * ξ') + (m₂ : ℝ) * (kk n p * ξ)) * Complex.I)
        = ∑ p ∈ B, Complex.exp (↑(kk n p * ((m₂ : ℝ) * ξ + (m₁ : ℝ) * ξ')) * Complex.I) :=
      Finset.sum_congr rfl (fun p _ => by congr 3; ring)
    rw [e]
    exact weyl_x t ht _ hε (hnr.2 m₂ m₁ hm.symm h2 h1)
  have hTW : ((Dn n : ℝ) + 1) ^ 2 * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) ≤ (B.card : ℝ) := by
    have : 0 ≤ (B.card : ℝ) := by positivity
    linarith
  -- the lower bound on the sum of `G2`
  have hΩ0 : 0 ≤ Ωf (Dn n) := by
    unfold Ωf
    have : (1 : ℝ) ≤ π * ((Dn n : ℝ) + 1) := by
      have := Nat.cast_nonneg (α := ℝ) (Dn n); nlinarith [Real.pi_gt_three]
    have := Real.log_nonneg this
    positivity
  have hsΩ : (|4 * π * u| + |4 * π * v|) * Ωf (Dn n) ≤ 1 / 800 := by
    have h4u : |4 * π * u| = 4 * π * |u| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
    have h4v : |4 * π * v| = 4 * π * |v| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
    rw [h4u, h4v]
    calc (4 * π * |u| + 4 * π * |v|) * Ωf (Dn n) ≤
          (4 * π * (n : ℝ) ^ (1 / 100 : ℝ) + 4 * π * (n : ℝ) ^ (1 / 100 : ℝ)) * Ωf (Dn n) := by
          gcongr
      _ = 2 * (4 * π * (n : ℝ) ^ (1 / 100 : ℝ) * Ωf (Dn n)) := by ring
      _ ≤ 1 / 800 := by linarith
  have hsum : (B.card : ℝ) / (1600 * π) ≤
      ∑ p ∈ B, G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ') := by
    have hgen : ((B.card : ℝ) - ((Dn n : ℝ) + 1) ^ 2 * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ))) *
          (1 / (400 * π)) - B.card * ((|4 * π * u| + |4 * π * v|) * Ωf (Dn n) / (2 * π))
        ≤ ∑ p ∈ B, G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ') := by
      by_cases hv16 : 1 / 16 < |v|
      · have hs : 1 / 3 ≤ |4 * π * v| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]; nlinarith [Real.pi_gt_three]
        exact inter2_gen B (fun p => kk n p * ξ) (fun p => kk n p * ξ') (Dn n) _ hW0 hWa
          (4 * π * u) (4 * π * v) hs hTW
      · push Not at hv16
        have hu16 : 1 / 16 < |u| := by
          by_contra h; push Not at h; exact huv ⟨h, hv16⟩
        have hs : 1 / 3 ≤ |4 * π * u| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]; nlinarith [Real.pi_gt_three]
        have h := inter2_gen B (fun p => kk n p * ξ') (fun p => kk n p * ξ) (Dn n) _ hW0 hWb
          (4 * π * v) (4 * π * u) hs hTW
        have e : ∑ p ∈ B, G2 (4 * π * v) (4 * π * u) (kk n p * ξ') (kk n p * ξ)
            = ∑ p ∈ B, G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ') :=
          Finset.sum_congr rfl (fun p _ => by unfold G2; ring_nf)
        rw [e, add_comm |4 * π * v|] at h
        exact h
    generalize hWg : ((Dn n : ℝ) + 1) ^ 2 * (1 / (2 * εn n) + (n : ℝ) ^ (3 / 5 : ℝ)) = W at hW hgen
    generalize hSg : ∑ p ∈ B, G2 (4 * π * u) (4 * π * v) (kk n p * ξ) (kk n p * ξ') = S at hgen ⊢
    generalize hBg : (B.card : ℝ) = Bc at hW hgen ⊢
    have hB0 : 0 ≤ Bc := by rw [← hBg]; positivity
    have hkey : Bc / (1600 * π) ≤ (Bc - W) * (1 / (400 * π)) -
        Bc * ((|4 * π * u| + |4 * π * v|) * Ωf (Dn n) / (2 * π)) := by
      calc Bc / (1600 * π) = (Bc / 2) * (1 / (400 * π)) - Bc * ((1 / 800) / (2 * π)) := by
            field_simp; ring
        _ ≤ _ := sub_le_sub (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
            (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsΩ (by positivity)) hB0)
    linarith
  refine (abs_Pc2_inter t ξ ξ' u v).trans (Real.exp_le_exp.mpr ?_)
  have e : (B.card : ℝ) / (3200 * π) = ((B.card : ℝ) / (1600 * π)) / 2 := by field_simp; ring
  rw [e]
  linarith

/-- The core factor. -/
lemma core_factor (a b ρ η ε₀ : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hρ0 : 0 ≤ ρ) (ha : a ≤ η)
    (hb : b ≤ η) (hρ : ρ ≤ η) (hη : η ≤ 1 / 40) (hηε : 40 * η ≤ ε₀) :
    (1 + a) ^ 2 * Real.exp b / (1 - ρ) ≤ 1 + ε₀ / 2 := by
  have hη0 : 0 ≤ η := le_trans ha0 ha
  have heb : Real.exp b ≤ 1 + 2 * b := by
    have := Real.abs_exp_sub_one_le (x := b) (by rw [abs_of_nonneg hb0]; linarith)
    rw [abs_of_nonneg hb0] at this
    linarith [(abs_le.mp this).2]
  have h1 : (1 + a) ^ 2 * Real.exp b ≤ (1 + 3 * η) * (1 + 2 * η) := by
    have : (1 + a) ^ 2 ≤ 1 + 3 * η := by nlinarith
    calc (1 + a) ^ 2 * Real.exp b ≤ (1 + 3 * η) * (1 + 2 * b) :=
          mul_le_mul this heb (Real.exp_pos _).le (by linarith)
      _ ≤ (1 + 3 * η) * (1 + 2 * η) := by gcongr
  have hρ1 : 0 < 1 - ρ := by linarith
  rw [div_le_iff₀ hρ1]
  nlinarith

lemma S2_core_eq (A κ ρ X Y : ℝ) (h1ρ : 0 < 1 - ρ) (hX : 0 < X) (hY : 0 < Y) :
    A ^ 2 * κ / Real.sqrt (2 * π * ((1 - ρ) * X)) * (1 / Real.sqrt (2 * π * ((1 - ρ) * Y))) =
      κ / (1 - ρ) * ((A / Real.sqrt (2 * π * X)) * (A / Real.sqrt (2 * π * Y))) := by
  have hpi := Real.pi_pos
  rw [show 2 * π * ((1 - ρ) * X) = (1 - ρ) * (2 * π * X) by ring,
    show 2 * π * ((1 - ρ) * Y) = (1 - ρ) * (2 * π * Y) by ring,
    Real.sqrt_mul h1ρ.le, Real.sqrt_mul h1ρ.le]
  have hs : Real.sqrt (1 - ρ) * Real.sqrt (1 - ρ) = 1 - ρ := Real.mul_self_sqrt h1ρ.le
  have hs0 : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr h1ρ
  have ha0 : 0 < Real.sqrt (2 * π * X) := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < Real.sqrt (2 * π * Y) := Real.sqrt_pos.mpr (by positivity)
  generalize Real.sqrt (1 - ρ) = s at hs hs0 ⊢
  generalize Real.sqrt (2 * π * X) = a at ha0 ⊢
  generalize Real.sqrt (2 * π * Y) = b at hb0 ⊢
  rw [← hs]
  field_simp

lemma S2_tails (A N P E L T C₀ Φ ε₀ : ℝ) (hA : 0 < A) (hN : 16 ≤ N) (hε₀ : 0 < ε₀)
    (hP : A ^ 2 / (9 * N) ≤ P) (hE : E ≤ 2 * N ^ (-(1 / 5) : ℝ))
    (hF7 : 216 * π * N ^ (-(1 / 5) : ℝ) ≤ ε₀) (hL : N / (16000 * π) ≤ L)
    (hT2 : (2 * T) * (2 * T) ≤ 4 * N) (hF8 : 1296 * (16000 * π) ^ 3 * N ^ (-1 : ℝ) ≤ ε₀)
    (hF9 : 216 * π * C₀ * Φ / (ε₀ * A ^ 2) * N ^ (-1 : ℝ) ≤ 1) (hC₀ : 0 ≤ C₀) (hΦ : 0 ≤ Φ) :
    A ^ 2 * E * (π / (N / 2)) ≤ ε₀ / 6 * P ∧
      A ^ 2 * Real.exp (-L) * (2 * T) * (2 * T) ≤ ε₀ / 6 * P ∧
      2 * (2 * C₀ / N ^ 2 * π * Φ) ≤ ε₀ / 6 * P := by
  have hpi := Real.pi_pos
  have hN0 : 0 < N := by linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hPP : ε₀ / 6 * (A ^ 2 / (9 * N)) ≤ ε₀ / 6 * P := mul_le_mul_of_nonneg_left hP (by positivity)
  have e2 : ε₀ / 6 * (A ^ 2 / (9 * N)) = A ^ 2 * (ε₀ / (54 * N)) := by field_simp; ring
  rw [e2] at hPP
  refine ⟨le_trans ?_ hPP, le_trans ?_ hPP, le_trans ?_ hPP⟩
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA2.le
    have e3 : π / (N / 2) = 2 * π / N := by field_simp
    rw [e3]
    calc E * (2 * π / N) ≤ 2 * N ^ (-(1 / 5) : ℝ) * (2 * π / N) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ = (216 * π * N ^ (-(1 / 5) : ℝ)) / (54 * N) := by field_simp; ring
      _ ≤ ε₀ / (54 * N) := by gcongr
  · have hl0 : 0 < N / (16000 * π) := by positivity
    have hexp : Real.exp (-L) ≤ 6 * (16000 * π) ^ 3 / N ^ 3 := by
      calc Real.exp (-L) ≤ Real.exp (-(N / (16000 * π))) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 6 / (N / (16000 * π)) ^ 3 := exp_neg_le_six_div_cube hl0
        _ = 6 * (16000 * π) ^ 3 / N ^ 3 := by field_simp
    rw [Real.rpow_neg_one] at hF8
    have h8 : 1296 * (16000 * π) ^ 3 ≤ ε₀ * N := by
      have := mul_le_mul_of_nonneg_right hF8 hN0.le
      rwa [mul_assoc, inv_mul_cancel₀ hN0.ne', mul_one] at this
    rw [mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hA2.le
    have hT0 : 0 ≤ (2 * T) * (2 * T) := mul_self_nonneg _
    calc Real.exp (-L) * ((2 * T) * (2 * T)) ≤ 6 * (16000 * π) ^ 3 / N ^ 3 * (4 * N) :=
          mul_le_mul hexp hT2 hT0 (by positivity)
      _ = 24 * (16000 * π) ^ 3 / N ^ 2 := by field_simp; ring
      _ ≤ ε₀ / (54 * N) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  · rw [Real.rpow_neg_one] at hF9
    have h9 : 216 * π * C₀ * Φ ≤ ε₀ * A ^ 2 * N := by
      have := mul_le_mul_of_nonneg_right hF9 hN0.le
      rw [mul_assoc, inv_mul_cancel₀ hN0.ne', mul_one, div_le_iff₀ (by positivity)] at this
      linarith
    rw [show 2 * (2 * C₀ / N ^ 2 * π * Φ) = 4 * π * C₀ * Φ / N ^ 2 by ring,
      show A ^ 2 * (ε₀ / (54 * N)) = ε₀ * A ^ 2 / (54 * N) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

lemma sqrt_two_pi_le (V N : ℝ) (hV : V ≤ N) (hV0 : 0 ≤ V) (hN : 0 ≤ N) :
    Real.sqrt (2 * π * V) ≤ 3 * Real.sqrt N := by
  rw [show (3 : ℝ) * Real.sqrt N = Real.sqrt (9 * N) by
    rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])

lemma pp_lower (A V V' N : ℝ) (hA : 0 < A) (hN : 0 < N) (hV : N / 4 ≤ V) (hV' : N / 4 ≤ V')
    (hVh : V ≤ N) (hVh' : V' ≤ N) :
    A ^ 2 / (9 * N) ≤ (A / Real.sqrt (2 * π * V)) * (A / Real.sqrt (2 * π * V')) := by
  have hpi := Real.pi_pos
  have h1 : A / (3 * Real.sqrt N) ≤ A / Real.sqrt (2 * π * V) :=
    div_le_div_of_nonneg_left hA.le (Real.sqrt_pos.mpr (by nlinarith))
      (sqrt_two_pi_le V N hVh (by linarith) hN.le)
  have h2 : A / (3 * Real.sqrt N) ≤ A / Real.sqrt (2 * π * V') :=
    div_le_div_of_nonneg_left hA.le (Real.sqrt_pos.mpr (by nlinarith))
      (sqrt_two_pi_le V' N hVh' (by linarith) hN.le)
  have e : A ^ 2 / (9 * N) = (A / (3 * Real.sqrt N)) * (A / (3 * Real.sqrt N)) := by
    have hs := Real.sq_sqrt hN.le
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    field_simp
    rw [hs]; ring
  rw [e]
  exact mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **S2 holds.** -/
theorem S2_holds : S2 := by
  intro δ hδ ε₀ hε₀
  obtain ⟨C₀, hC₀0, hC₀⟩ := fourier_far2 δ hδ
  have hpi := Real.pi_pos
  have hA0 := Ad_pos δ hδ
  obtain ⟨η, hη0, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 40 ∧ 40 * η ≤ ε₀ :=
    ⟨min ε₀ 1 / 40, by positivity, by have := min_le_right ε₀ 1; linarith,
      by have := min_le_left ε₀ 1; linarith⟩
  obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ : ℝ, Φ = ∫ v, ‖𝓕 (psi δ hδ : ℝ → ℂ) v‖ ∧ 0 ≤ Φ :=
    ⟨_, rfl, integral_nonneg (fun _ => norm_nonneg _)⟩
  filter_upwards [S4_holds, Omega_small_gen (1 / 1600) (by norm_num),
    eventually_small_rpow 40 (1 / 5) 1 (by norm_num) (by norm_num),
    eventually_small_rpow 60 (3 / 20) 1 (by norm_num) (by norm_num),
    eventually_small_rpow (8 * π) (2 / 5) (1 / 2) (by norm_num) (by norm_num),
    eventually_small_rpow (π * δ) (2 / 5) η (by norm_num) hη0,
    eventually_small_rpow ((8 * π) ^ 4) (3 / 5) η (by norm_num) hη0,
    eventually_small_rpow 32 (2 / 5) η (by norm_num) hη0,
    eventually_small_rpow (216 * π) (1 / 5) ε₀ (by norm_num) hε₀,
    eventually_small_rpow (1296 * (16000 * π) ^ 3) 1 ε₀ (by norm_num) hε₀,
    eventually_small_rpow (216 * π * C₀ * Φ / (ε₀ * Ad δ hδ ^ 2)) 1 1 (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop 16] with n hS4 hΩ hF1 hF2 hF3 hF4 hF5 hF6 hF7 hF8 hF9 hn
  intro t ht ξ hξ ξ' hξ' _ _ hnr
  have hN16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hN1 : (1 : ℝ) ≤ n := by linarith
  obtain ⟨hVlo, hVhi, hBlo, -⟩ := S1_sizes n hn hF1 t ht ξ (hS4 t ht ξ hξ)
  obtain ⟨hVlo', hVhi', -, -⟩ := S1_sizes n hn hF1 t ht ξ' (hS4 t ht ξ' hξ')
  have hW2 := S2_weyl_size n hn hF2 _ hBlo
  have hinter := S2_inter n hn hΩ t ht ξ ξ' hnr hW2
  have hCv := abs_Cv_le t ht ξ ξ' hξ hξ' hnr.1 (by omega)
  have hρC : |Cv t ξ ξ'| ≤ 32 * (n : ℝ) ^ (-(2 / 5) : ℝ) * ((n : ℝ) / 4) := by
    have e : 32 * (n : ℝ) ^ (-(2 / 5) : ℝ) * ((n : ℝ) / 4) = 8 * (n : ℝ) ^ (3 / 5 : ℝ) := by
      have : (n : ℝ) ^ (-(2 / 5) : ℝ) * n = (n : ℝ) ^ (3 / 5 : ℝ) := by
        rw [← Real.rpow_add_one hN0.ne']; norm_num
      rw [← this]; ring
    rw [e]; exact hCv
  have hfar : ∀ u, (n : ℝ) ^ (1 / 100 : ℝ) < |u| →
      ‖𝓕 (psi δ hδ : ℝ → ℂ) u‖ ≤ 2 * C₀ / (n : ℝ) ^ 2 * (1 + u ^ 2)⁻¹ :=
    fun u hu => hC₀ n hN1 u hu.le
  have hρ0 : 0 ≤ 32 * (n : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
  have hdet := S2_det δ hδ t ξ ξ' n (32 * (n : ℝ) ^ (-(2 / 5) : ℝ)) ((n : ℝ) ^ (-(2 / 5) : ℝ))
    ((n : ℝ) ^ (1 / 100 : ℝ)) (((univ.filter fun p => t p = false).card : ℝ) / (3200 * π))
    (2 * C₀ / (n : ℝ) ^ 2) hN0 hVlo hVlo' hρ0 (by linarith) hρC (by positivity) hF3
    (by positivity) hinter (by positivity) hfar
  rw [← hΦ] at hdet
  have hτ4 : (K n : ℝ) * (8 * π * (n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4 ≤
      (8 * π) ^ 4 * (n : ℝ) ^ (-(3 / 5) : ℝ) := by
    have e : ((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4 * n = (n : ℝ) ^ (-(3 / 5) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add_one hN0.ne']
      norm_num
    have hKN : (K n : ℝ) ≤ n := by
      have : K n ≤ n := by unfold K; omega
      exact_mod_cast this
    calc (K n : ℝ) * (8 * π * (n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4
        = (8 * π) ^ 4 * (((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4 * K n) := by ring
      _ ≤ (8 * π) ^ 4 * (((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4 * n) := by gcongr
      _ = _ := by rw [e]
  have hcf := core_factor (π * δ * (n : ℝ) ^ (-(2 / 5) : ℝ))
    ((K n : ℝ) * (8 * π * (n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 4) (32 * (n : ℝ) ^ (-(2 / 5) : ℝ)) η ε₀
    (by positivity) (by positivity) hρ0 hF4 (hτ4.trans hF5) hF6 hη1 hηε
  have h1ρ : 0 < 1 - 32 * (n : ℝ) ^ (-(2 / 5) : ℝ) := by linarith
  rw [S2_core_eq _ _ _ _ _ h1ρ (by linarith) (by linarith)] at hdet
  have hpp := pp_lower (Ad δ hδ) (Vv t ξ) (Vv t ξ') n hA0 hN0 hVlo hVlo' hVhi hVhi'
  -- exponents
  have hE : Real.exp (-((n : ℝ) * ((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 2 / 2)) ≤
      2 * (n : ℝ) ^ (-(1 / 5) : ℝ) := by
    have e : (n : ℝ) * ((n : ℝ) ^ (-(2 / 5) : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm, ← Real.rpow_add_one hN0.ne']
      norm_num
    rw [e]
    have hy : 0 < (n : ℝ) ^ (1 / 5 : ℝ) / 2 := by positivity
    refine (exp_neg_le_inv hy).trans (le_of_eq ?_)
    rw [Real.rpow_neg hN0.le]; field_simp
  have hlam0 : (n : ℝ) / (16000 * π) ≤
      ((univ.filter fun p => t p = false).card : ℝ) / (3200 * π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hT2 : (2 * (n : ℝ) ^ (1 / 100 : ℝ)) * (2 * (n : ℝ) ^ (1 / 100 : ℝ)) ≤ 4 * n := by
    have : (n : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) ≤ n := by
      rw [← Real.rpow_add hN0]
      calc (n : ℝ) ^ (1 / 100 + 1 / 100 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = n := Real.rpow_one _
    nlinarith
  obtain ⟨hmid, hint, hfarb⟩ := S2_tails (Ad δ hδ) n _ _ _ ((n : ℝ) ^ (1 / 100 : ℝ)) C₀ Φ ε₀ hA0
    hN16 hε₀ hpp hE hF7 hlam0 hT2 hF8 hF9 hC₀0 hΦ0
  generalize hPg : Ad δ hδ / Real.sqrt (2 * π * Vv t ξ) * (Ad δ hδ / Real.sqrt (2 * π * Vv t ξ')) = P
    at hdet hmid hint hfarb hpp
  have hP0 : 0 ≤ P := le_trans (by positivity) hpp
  have hcore := mul_le_mul_of_nonneg_right hcf hP0
  calc E2 δ hδ t ξ ξ' ≤ _ := hdet
    _ ≤ (1 + ε₀ / 2) * P + ε₀ / 6 * P + ε₀ / 6 * P + ε₀ / 6 * P := by
        linarith
    _ = (1 + ε₀) * P := by ring

end K525


/-- The local copies of the Erdős 525 definitions agree with the real ones. -/
theorem K525.prob_eq (δ : ℝ) (n : ℕ) :
    Erdos525.prob n (fun f ↦ Erdos525.m f < δ) = K525.prob n (fun f ↦ K525.mm f < δ) := rfl

theorem OMA.solution : type_of% @Erdos525.erdos_525.variants.kashin := by
  intro δ hδ
  have h := K525.kashin_of K525.hT_holds K525.hZ_holds
    (K525.hH_of K525.S1_holds K525.S2_holds K525.S3_holds K525.S4_holds) δ hδ
  simp only [← K525.prob_eq] at h
  exact h
