import FormalConjectures.Other.SymbolLengthMilnorKTheory

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1
-- Credit: @hyprspacecoyote
--
-- Target: K_n(C(x_1, ..., x_m))/p = 0 for n > m. Proved here, with no hypothesis:
--   * propagation: K_n/l = 0 implies K_{n+1}/l = 0, so only n = m + 1 matters;
--   * m = 0: every unit of C is a p-th power;
--   * m = 1: K_2(C(x))/p = 0 (lemmas copied with credit from chris01-dev's merged
--     degree_two_isLeast.R1: Steinberg on (x - a)/(b - a) + (x - b)/(a - b) = 1);
--   * m = 2, p = 2: K_3(C(x, y))/2 = 0. C(x, y) has u-invariant 4 (Lang's degree count over
--     C[x, y], using Krull's height theorem and the Nullstellensatz), so <a, b, ab, 1, c> is
--     isotropic; this gives {a, b} = {e, f} with e = X^2 + c Z^2, hence {e, c} = 0 and
--     {a, b, c} = {f}{e, c} = 0.
-- Left as hypotheses (both only in degree m + 1):
--   H1  m = 2 and p odd: K_3(C(x, y))/p = 0 (needs Bass-Tate, or cd = 2 with Merkurjev-Suslin);
--   H2  m >= 3: K_{m+1}(C(x_1, ..., x_m))/p = 0.


namespace OMA.ZL.Artin2

open MvPolynomial

variable {k : Type*} [Field k]

theorem kill_succ_comp (N i : ℕ) :
    ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))).comp ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) = (aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, aeval_X]
  split_ifs with h1 h2 <;> simp_all
  omega

theorem ker_kill_le (N i : ℕ) :
    RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) ≤ RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← kill_succ_comp, AlgHom.comp_apply]
  erw [hf]
  simp

theorem height_ker_kill (N : ℕ) :
    ∀ i ≤ N, (i : ℕ∞) ≤ (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).height := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have : (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).IsPrime := RingHom.ker_isPrime _
    have : (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j)))).IsPrime := RingHom.ker_isPrime _
    have hlt : RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j))) < RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
      refine lt_of_le_of_ne (ker_kill_le N i) ?_
      intro h
      have hx : (X ⟨i, by omega⟩ : MvPolynomial (Fin N) k) ∈ RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < (i + 1) then (0 : MvPolynomial (Fin N) k) else X j))) := by
        rw [RingHom.mem_ker]; simp
      rw [← h, RingHom.mem_ker] at hx
      simp [X_ne_zero] at hx
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    calc ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < i then (0 : MvPolynomial (Fin N) k) else X j)))).height + 1 := by gcongr
      _ ≤ _ := this

theorem mem_ker_kill_N {N : ℕ} (f : MvPolynomial (Fin N) k) :
    f ∈ RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j))) ↔ constantCoeff f = 0 := by
  have : (aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j)) = aeval 0 := by
    apply MvPolynomial.algHom_ext; intro j; simp
  rw [RingHom.mem_ker, this, aeval_zero]
  simp

/-- Over an algebraically closed field, finitely many polynomials without constant term, fewer
than the number of variables, have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {N : ℕ} (s : Finset (MvPolynomial (Fin N) k))
    (hs : s.card < N) (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : Fin N → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin N) k) := Ideal.span (s : Set _)
  set M := RingHom.ker ((aeval (R := k) (fun j : Fin N ↦ if (j : ℕ) < N then (0 : MvPolynomial (Fin N) k) else X j)))
  have hM : M.IsPrime := RingHom.ker_isPrime _
  have hIM : I ≤ M := by
    rw [Ideal.span_le]
    intro f hf
    exact (mem_ker_kill_N f).mpr (h0 f hf)
  -- every common zero of `I` is `0`
  have hzero : ∀ v ∈ zeroLocus k I, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨f, hf, hfv⟩ := hcon v hv0
    apply hfv
    have := (mem_zeroLocus_iff.mp hv) f (Ideal.subset_span hf)
    simpa [aeval_eq_eval] using this
  have hMrad : M ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro f hf v hv
    rw [hzero v hv]
    have := (mem_ker_kill_N f).mp hf
    simpa [aeval_zero] using this
  have hmin : M ∈ I.minimalPrimes := by
    refine ⟨⟨hM, hIM⟩, fun q hq hqM ↦ ?_⟩
    exact hMrad.trans ((Ideal.IsPrime.radical_le_iff hq.1).mpr hq.2)
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 := height_ker_kill (k := k) N N le_rfl
  have : ((N : ℕ) : ℕ∞) ≤ s.card := h2.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hs)



theorem exists_common_zero' [IsAlgClosed k] {σ : Type*} [Fintype σ]
    (s : Finset (MvPolynomial σ k)) (hs : s.card < Fintype.card σ)
    (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : σ → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  classical
  set e := Fintype.equivFin σ
  obtain ⟨w, hw0, hw⟩ := exists_common_zero (s.image (rename e))
    (lt_of_le_of_lt Finset.card_image_le (by simpa using hs)) (by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      rw [constantCoeff_rename]; exact h0 g hg)
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h; apply hw0; funext j
    have := congrFun h (e.symm j); simpa using this
  · intro f hf
    have := hw (rename e f) (Finset.mem_image_of_mem _ hf)
    rwa [eval_rename] at this

@[simp] lemma mono_zero (j l : ℕ) : ((Finsupp.single (0 : Fin 2) (j : ℕ) + Finsupp.single (1 : Fin 2) (l : ℕ) : Fin 2 →₀ ℕ)) 0 = j := by simp
@[simp] lemma mono_one (j l : ℕ) : ((Finsupp.single (0 : Fin 2) (j : ℕ) + Finsupp.single (1 : Fin 2) (l : ℕ) : Fin 2 →₀ ℕ)) 1 = l := by simp
lemma eq_mono (m : Fin 2 →₀ ℕ) : m = ((Finsupp.single (0 : Fin 2) ((m 0) : ℕ) + Finsupp.single (1 : Fin 2) ((m 1) : ℕ) : Fin 2 →₀ ℕ)) := by
  ext i; fin_cases i <;> simp

lemma degreeOf_map_le' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (n : Fin 2) (p : MvPolynomial (Fin 2) R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro m hm
  exact monomial_le_degreeOf n (support_map_subset f p hm)

/-- Lang's count for `C(x, y)`: a diagonal quadratic form in `5` variables with polynomial
coefficients has a nonzero polynomial zero. -/
theorem lang_poly (P : Fin 5 → MvPolynomial (Fin 2) ℂ) :
    ∃ W : Fin 5 → MvPolynomial (Fin 2) ℂ, W ≠ 0 ∧ ∑ i, P i * W i ^ 2 = 0 := by
  classical
  set r := ∑ i, (degreeOf 0 (P i) + degreeOf 1 (P i)) with hr
  set S := 5 * r + 5 with hS
  set E := 11 * r + 9 with hE
  have hPr : ∀ i n, degreeOf n (P i) ≤ r := by
    intro i n
    have h1 : degreeOf 0 (P i) + degreeOf 1 (P i) ≤ r :=
      Finset.single_le_sum (f := fun i ↦ degreeOf 0 (P i) + degreeOf 1 (P i))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    fin_cases n <;> simp <;> omega
  let U := Fin 5 × Fin S × Fin S
  let V : Fin 5 → MvPolynomial (Fin 2) (MvPolynomial U ℂ) := fun i ↦
    ∑ jl : Fin S × Fin S, monomial (((Finsupp.single (0 : Fin 2) (jl.1 : ℕ) + Finsupp.single (1 : Fin 2) (jl.2 : ℕ) : Fin 2 →₀ ℕ))) (X (i, jl.1, jl.2))
  let Q : MvPolynomial (Fin 2) (MvPolynomial U ℂ) := ∑ i, map C (P i) * V i ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin E × Fin E)).image fun jl ↦ coeff (((Finsupp.single (0 : Fin 2) (jl.1 : ℕ) + Finsupp.single (1 : Fin 2) (jl.2 : ℕ) : Fin 2 →₀ ℕ))) Q
  have hV : ∀ i n, degreeOf n (V i) ≤ S - 1 := by
    intro i n
    rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨jl, -, hjl⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    have := support_monomial_subset hjl
    rw [Finset.mem_singleton] at this
    subst this
    have h1 := jl.1.isLt
    have h2 := jl.2.isLt
    fin_cases n <;> simp <;> omega
  have hQ : ∀ n, degreeOf n Q ≤ r + 2 * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans (add_le_add ((degreeOf_map_le' C n _).trans (hPr i n))
      ((degreeOf_pow_le n _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV i n)
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, E ≤ m 0 ∨ E ≤ m 1 → coeff m Q = 0 := by
    intro m hm
    by_contra hc
    have hsupp : m ∈ Q.support := mem_support_iff.mpr hc
    have h0 := (monomial_le_degreeOf 0 hsupp).trans (hQ 0)
    have h1 := (monomial_le_degreeOf 1 hsupp).trans (hQ 1)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ i, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V i) = 0 := by
      intro i
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, U]
    nlinarith
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨jl, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : Fin 5 → MvPolynomial (Fin 2) ℂ := fun i ↦ map (eval t) (V i)
  have hmapQ : map (eval t) Q = ∑ i, P i * W i ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext m
    rw [coeff_map, coeff_zero]
    by_cases hm : m 0 < E ∧ m 1 < E
    · apply ht
      refine Finset.mem_image.mpr ⟨(⟨m 0, hm.1⟩, ⟨m 1, hm.2⟩), Finset.mem_univ _, ?_⟩
      simp only
      rw [← eq_mono m]
    · rw [hcoeff m (by omega), map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨i, j, l⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWi : W i = 0 := congrFun hW i
  have key : coeff (((Finsupp.single (0 : Fin 2) (j : ℕ) + Finsupp.single (1 : Fin 2) (l : ℕ) : Fin 2 →₀ ℕ))) (W i) = t (i, j, l) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single (j, l)]
    · simp
    · rintro ⟨j', l'⟩ _ hne
      rw [if_neg]
      intro h
      apply hne
      have e0 := congrArg (fun m ↦ m 0) h
      have e1 := congrArg (fun m ↦ m 1) h
      simp only [mono_zero, mono_one] at e0 e1
      ext <;> simp [e0, e1]
    · simp
  rw [← key, hWi, coeff_zero]
  rfl




/-- `C(x, y)` has `u`-invariant at most `4`: every diagonal quadratic form in `5` variables is
isotropic. -/
theorem isotropic5 (q : Fin 5 → (MvRatFunc (Fin 2) ℂ)) : ∃ v : Fin 5 → (MvRatFunc (Fin 2) ℂ), v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0 := by
  classical
  have hex : ∀ i, ∃ nd : MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ, nd.2 ≠ 0 ∧
      q i = algebraMap _ (MvRatFunc (Fin 2) ℂ) nd.1 / algebraMap _ (MvRatFunc (Fin 2) ℂ) nd.2 := by
    intro i
    obtain ⟨n, d, hd, h⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 2) ℂ) (q i)
    exact ⟨(n, d), nonZeroDivisors.ne_zero hd, h.symm⟩
  choose nd hd hq using hex
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) ℂ) (MvRatFunc (Fin 2) ℂ)) :=
    IsFractionRing.injective _ _
  let P : Fin 5 → MvPolynomial (Fin 2) ℂ := fun i ↦
    (nd i).1 * ∏ j ∈ Finset.univ.erase i, (nd j).2
  obtain ⟨W, hW0, hW⟩ := lang_poly P
  set Dn := ∏ j, (nd j).2
  have hDn : algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hd j)
  have hP : ∀ i, algebraMap _ (MvRatFunc (Fin 2) ℂ) (P i) = q i * algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn := by
    intro i
    have hdi : algebraMap _ (MvRatFunc (Fin 2) ℂ) (nd i).2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hd i)
    simp only [P, Dn, map_mul, map_prod, hq i]
    rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ algebraMap _ (MvRatFunc (Fin 2) ℂ) (nd j).2)
      (Finset.mem_univ i)]
    field_simp
  refine ⟨fun i ↦ algebraMap _ (MvRatFunc (Fin 2) ℂ) (W i), ?_, ?_⟩
  · intro h
    apply hW0
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin 2) ℂ)) hW
    simp only [map_sum, map_mul, map_pow, map_zero, hP] at this
    have h2 : (∑ i, q i * algebraMap _ (MvRatFunc (Fin 2) ℂ) (W i) ^ 2) * algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn = 0 := by
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
    exact (mul_eq_zero.mp h2).resolve_right hDn

end OMA.ZL.Artin2


namespace OMA.ZL.Artin2K

open MilnorK

variable {F : Type*} [Field F]

theorem add_self_eq_zero (x : MilnorK F 2) : x + x = 0 := by
  have h2 : (2 : MilnorK F 2) = 0 := by exact_mod_cast natCast_eq_zero (F := F) 2
  rw [← two_mul, h2, zero_mul]

theorem neg_eq_self (x : MilnorK F 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem of_sq (u : Fˣ) : of 2 (u ^ 2) = 0 := by
  rw [of_pow, two_smul, add_self_eq_zero]

theorem of_neg_one (hi : ∃ i : F, i * i = -1) : of 2 (-1 : Fˣ) = 0 := by
  obtain ⟨i, hi⟩ := hi
  have hi0 : i ≠ 0 := by
    rintro rfl; simp at hi
  have : (-1 : Fˣ) = (Units.mk0 i hi0) ^ 2 := by
    ext; simp [sq, hi]
  rw [this, of_sq]

theorem of_neg (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 (-a) = of 2 a := by
  rw [show -a = (-1) * a by simp, of_mul, of_neg_one hi, zero_add]

theorem of_mul_self (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 a * of 2 a = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1; linear_combination -h
  have h2 : (1 : F) - (a⁻¹ : Fˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1
    have : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    simpa using congrArg (fun z : F ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of 2 a * of 2 b = 0 := of_mul_of_eq_zero 2 a b (by simp [b])
  have hc : of 2 a⁻¹ * of 2 c = 0 := of_mul_of_eq_zero 2 a⁻¹ c (by simp [c])
  have hc' : of 2 a * of 2 c = 0 := by
    rw [of_inv, neg_eq_self] at hc; exact hc
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  have : of 2 a * of 2 (-a) = 0 := by
    rw [hneg, of_mul, of_inv, neg_eq_self, mul_add, hb, hc', add_zero]
  rwa [of_neg hi] at this

theorem of_comm (hi : ∃ i : F, i * i = -1) (a b : Fˣ) : of 2 a * of 2 b = of 2 b * of 2 a := by
  have h := of_mul_self hi (a * b)
  rw [of_mul, add_mul, mul_add, mul_add, of_mul_self hi a, of_mul_self hi b, zero_add,
    add_zero] at h
  rw [← neg_eq_self (of 2 b * of 2 a)]
  exact eq_neg_of_add_eq_zero_left h

/-- `{s, t} = {e, s t}` when `s + t = e`. -/
theorem steinberg2 (hi : ∃ i : F, i * i = -1) (s t e : Fˣ) (h : (s : F) + t = e) :
    of 2 s * of 2 t = of 2 e * of 2 (s * t) := by
  have hst : of 2 (s * e⁻¹) * of 2 (t * e⁻¹) = 0 :=
    of_mul_of_eq_zero 2 _ _ (by
      have he : (e : F) ≠ 0 := e.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp; linear_combination h)
  simp only [of_mul, of_inv, neg_eq_self] at hst
  rw [add_mul, mul_add, mul_add, of_mul_self hi e, add_zero] at hst
  rw [of_mul, mul_add, of_comm hi e s]
  have h3 : of 2 s * of 2 t = -(of 2 s * of 2 e + of 2 e * of 2 t) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hst)
  rw [h3, neg_eq_self]

/-- If `e = a x² + b y²` then `{a, b} = {e, a b}`. -/
theorem slot2 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2) :
    of 2 a * of 2 b = of 2 e * of 2 (a * b) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by rintro rfl; subst hx; simp at h
    have he : e = b * (Units.mk0 y hy) ^ 2 := by ext; simp [h, hx]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, add_zero, of_comm hi]
  by_cases hy : y = 0
  · have he : e = a * (Units.mk0 x hx) ^ 2 := by ext; simp [h, hy]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, zero_add]
  set s := a * (Units.mk0 x hx) ^ 2
  set t := b * (Units.mk0 y hy) ^ 2
  have hst := steinberg2 hi s t e (by simp [s, t, h])
  have e1 : of 2 s = of 2 a := by simp only [s, of_mul, of_sq, add_zero]
  have e2 : of 2 t = of 2 b := by simp only [t, of_mul, of_sq, add_zero]
  have e3 : of 2 (s * t) = of 2 (a * b) := by
    simp only [s, t, of_mul, of_sq, add_zero]
  rw [e1, e2, e3] at hst
  exact hst

/-- If `u = x² + b z² ≠ 0` then `{u, b} = 0`. -/
theorem norm_slot (hi : ∃ i : F, i * i = -1) (b u : Fˣ) (x z : F) (h : (u : F) = x ^ 2 + b * z ^ 2) :
    of 2 u * of 2 b = 0 := by
  have := slot2 hi b 1 u z x (by rw [h]; simp; ring)
  rw [of_one, mul_zero, mul_one] at this
  exact this.symm

/-- If `e = a x² + b y² + a b z² ≠ 0` then `{a, b} = {e, f}` for some `f`. -/
theorem slot3 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y z : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2 + a * b * z ^ 2) :
    ∃ f : Fˣ, of 2 a * of 2 b = of 2 e * of 2 f := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · exact ⟨a * b, slot2 hi a b e 0 y (by rw [h]; linear_combination (a : F) * hu)⟩
  set u := Units.mk0 _ hu
  have hub := norm_slot hi b u x z rfl
  refine ⟨a * u * b, ?_⟩
  have h2 := slot2 hi (a * u) b e 1 y (by rw [h]; simp [u]; ring)
  rw [of_mul 2 a u, add_mul, hub, add_zero] at h2
  exact h2

/-- If `a x² + b y² + a b z² = 0` with `(x, y, z) ≠ 0` then `{a, b} = 0`. -/
theorem slot3_zero (hi : ∃ i : F, i * i = -1) (a b : Fˣ) (x y z : F) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h : (a : F) * x ^ 2 + b * y ^ 2 + a * b * z ^ 2 = 0) : of 2 a * of 2 b = 0 := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · have hy : (b : F) * y ^ 2 = 0 := by linear_combination h - (a : F) * hu
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hy with hb | hy
      · exact absurd hb b.ne_zero
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
    have hz : z ≠ 0 := by
      rintro rfl
      have : x = 0 := by simpa using hu
      rcases hne with h1 | h1 | h1 <;> contradiction
    have hx : x ≠ 0 := by
      rintro rfl
      have : (b : F) * z ^ 2 = 0 := by simpa using hu
      rcases mul_eq_zero.mp this with hb | hz'
      · exact b.ne_zero hb
      · exact hz (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz')
    have hb : b = -(Units.mk0 x hx * (Units.mk0 z hz)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hu
    rw [hb, of_neg hi, of_sq, mul_zero]
  · set u := Units.mk0 _ hu
    have hub := norm_slot hi b u x z rfl
    have hy : y ≠ 0 := by
      rintro rfl
      apply hu
      have : (a : F) * (x ^ 2 + b * z ^ 2) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left a.ne_zero
    -- a u = -b y², so a = -b y² u⁻¹
    have ha : a = -(b * (Units.mk0 y hy) ^ 2 * u⁻¹) := by
      ext
      have hu0 : (u : F) ≠ 0 := u.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      simp only [u, Units.val_mk0]
      linear_combination h
    rw [ha, of_neg hi, of_mul, of_mul, of_sq, add_zero, of_inv, neg_eq_self, add_mul,
      of_mul_self hi, hub, add_zero]

/-- Common slot: over a field where `-1` is a square and every diagonal quadratic form in `5`
variables is isotropic, the sum of two symbols mod `2` is a symbol. -/
theorem sum_two (hi : ∃ i : F, i * i = -1) (hu : ∀ q : Fin 5 → F, ∃ v : Fin 5 → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    (a b c d : Fˣ) : ∃ e f : Fˣ, of 2 a * of 2 b + of 2 c * of 2 d = of 2 e * of 2 f := by
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu ![a, b, a * b, c, d]
  replace hv : (a : F) * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 + c * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by
    simpa [Fin.sum_univ_five] using hv
  set E : F := a * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 with hE
  by_cases hE0 : E = 0
  · have hcd : (c : F) * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by linear_combination hv - hE0
    by_cases hx : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0
    · refine ⟨c, d, ?_⟩
      rw [slot3_zero ⟨i, hi'⟩ a b _ _ _ hx hE0, zero_add]
    · push Not at hx
      have hy : v 3 ≠ 0 ∨ v 4 ≠ 0 := by
        by_contra hy; push Not at hy
        apply hv0; funext j; fin_cases j <;> simp [hx, hy]
      refine ⟨a, b, ?_⟩
      have := slot3_zero ⟨i, hi'⟩ c d (v 3) (v 4) 0 (by tauto) (by simpa using hcd)
      rw [this, add_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨f, hf⟩ := slot3 ⟨i, hi'⟩ a b e (v 0) (v 1) (v 2) rfl
    have hcd := slot2 ⟨i, hi'⟩ c d e (i * v 3) (i * v 4) (by
      simp only [e, Units.val_mk0]
      linear_combination (-(c : F) * v 3 ^ 2 - d * v 4 ^ 2) * hi' + hv)
    refine ⟨e, f * (c * d), ?_⟩
    rw [hf, hcd, ← mul_add, ← of_mul]

end OMA.ZL.Artin2K

namespace OMA.ZL.Artin2K

open MilnorK

theorem exists_sqrt_neg_one : ∃ i : MvRatFunc (Fin 2) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin 2) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

theorem symbol_two {F : Type*} [Field F] (s : Fin 2 → Fˣ) :
    symbol 2 s = of 2 (s 0) * of 2 (s 1) := by
  simp [symbol_succ]

/-- Every class of `K^M_2(C(x, y))/2` is a single symbol. -/
theorem grade_two_single (x : MilnorK (MvRatFunc (Fin 2) ℂ) 2)
    (hx : x ∈ grade (MvRatFunc (Fin 2) ℂ) 2 2) :
    ∃ e f : (MvRatFunc (Fin 2) ℂ)ˣ, x = of 2 e * of 2 f := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s 0, s 1, symbol_two s⟩
  | zero => exact ⟨1, 1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact sum_two exists_sqrt_neg_one OMA.ZL.Artin2.isotropic5 a b c d
  | neg y _ hy =>
    obtain ⟨a, b, rfl⟩ := hy
    exact ⟨a⁻¹, b, by rw [of_inv, neg_eq_self, neg_eq_self]⟩

/-- Artin's theorem for `p = 2`: the symbol length of `K^M_2(C(x, y))/2` is at most `1`. -/
theorem one_mem : 1 ∈ symbolLengthBounds (MvRatFunc (Fin 2) ℂ) 2 2 := by
  intro x hx
  obtain ⟨e, f, rfl⟩ := grade_two_single x hx
  exact ⟨1, le_rfl, fun _ ↦ ![e, f], by simp [symbol_two]⟩

end OMA.ZL.Artin2K


namespace OMA.ZL.Artin2K

open MilnorK

/-- `K_3/2 = 0` over a field where `-1` is a square and `5`-dimensional diagonal forms are
isotropic: `<a, b, ab, 1, c>` is isotropic, so `{a, b} = {e, f}` with `e` a norm from
`F(√-c)`, hence `{e, c} = 0`. -/
theorem triple_zero {F : Type*} [Field F] (hi : ∃ i : F, i * i = -1)
    (hu : ∀ q : Fin 5 → F, ∃ v : Fin 5 → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    (a b c : Fˣ) : of 2 a * of 2 b * of 2 c = 0 := by
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu ![a, b, a * b, 1, c]
  replace hv : (a : F) * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 + v 3 ^ 2 + c * v 4 ^ 2 = 0 := by
    simpa [Fin.sum_univ_five] using hv
  set E : F := a * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 with hE
  by_cases hE0 : E = 0
  · by_cases hx : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0
    · rw [slot3_zero ⟨i, hi'⟩ a b _ _ _ hx hE0, zero_mul]
    · push Not at hx
      have h34 : v 3 ^ 2 + (c : F) * v 4 ^ 2 = 0 := by linear_combination hv - hE0
      have h4 : v 4 ≠ 0 := by
        intro h4
        apply hv0; funext j
        have h3 : v 3 = 0 := by simpa [h4] using h34
        fin_cases j <;> simp [hx, h3, h4]
      have hc : c = -(Units.mk0 (v 3) (by
          intro h3; apply h4
          have : (c : F) * v 4 ^ 2 = 0 := by simpa [h3] using h34
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
            ((mul_eq_zero.mp this).resolve_left c.ne_zero)) * (Units.mk0 (v 4) h4)⁻¹) ^ 2 := by
        ext
        simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val]
        field_simp
        linear_combination h34
      rw [hc, of_neg ⟨i, hi'⟩, of_sq, mul_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨f, hf⟩ := slot3 ⟨i, hi'⟩ a b e (v 0) (v 1) (v 2) rfl
    have hec : of 2 e * of 2 c = 0 :=
      norm_slot ⟨i, hi'⟩ c e (i * v 3) (i * v 4) (by
        simp only [e, Units.val_mk0]
        linear_combination (-(v 3) ^ 2 - (c : F) * v 4 ^ 2) * hi' + hv)
    rw [hf, of_comm ⟨i, hi'⟩ e f, mul_assoc, hec, mul_zero]

/-- If `K_n/ℓ = 0` then `K_{n+1}/ℓ = 0`. -/
theorem grade_succ_eq_bot {F : Type*} [Field F] (ℓ n : ℕ) (h : grade F ℓ n = ⊥) :
    grade F ℓ (n + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hs := symbol_mem_grade F ℓ (fun i ↦ s i.succ)
  rw [h, AddSubgroup.mem_bot] at hs
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, hs, mul_zero]

theorem grade_eq_bot_of_le {F : Type*} [Field F] (ℓ k : ℕ) (h : grade F ℓ k = ⊥) :
    ∀ n, k ≤ n → grade F ℓ n = ⊥ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact grade_succ_eq_bot ℓ n ih

/-- `K^M_n(C(x, y))/2 = 0` for `n ≥ 3`. -/
theorem grade_C2_two_eq_bot (n : ℕ) (hn : 3 ≤ n) :
    grade (MvRatFunc (Fin 2) ℂ) 2 n = ⊥ := by
  refine grade_eq_bot_of_le 2 3 ?_ n hn
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have : symbol 2 s = of 2 (s 0) * of 2 (s 1) * of 2 (s 2) := by
    simp [symbol_succ, mul_assoc]
  rw [this]
  exact triple_zero exists_sqrt_neg_one OMA.ZL.Artin2.isotropic5 _ _ _

end OMA.ZL.Artin2K


namespace OMA.ZL.SLKnown

open MilnorK MvPolynomial

/-- `C(x_1, ..., x_0) = C`: every element of `MvRatFunc (Fin 0) ℂ` is a constant. -/
theorem fin0_const (x : MvRatFunc (Fin 0) ℂ) :
    ∃ c : ℂ, x = algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) (C c) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 0) ℂ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set ca := coeff 0 a
  set cb := coeff 0 b
  have ha : a = C ca := eq_C_of_isEmpty a
  have hb' : b = C cb := eq_C_of_isEmpty b
  have hcb : cb ≠ 0 := by
    intro h; apply hb0; rw [hb', h, C_0]
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ)) :=
    IsFractionRing.injective _ _
  have hbm : algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hb0
  refine ⟨ca / cb, ?_⟩
  rw [div_eq_iff hbm, ← map_mul]
  congr 1
  rw [hb', ← C_mul, div_mul_cancel₀ ca hcb, ← ha]

/-- Row `m = 0`, `n ≥ 1`: `K^M_n(C)/p = 0`, so `0` bounds the symbol length. -/
theorem m_zero (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    0 ∈ symbolLengthBounds (MvRatFunc (Fin 0) ℂ) p n := by
  rw [zero_mem_symbolLengthBounds_iff]
  refine grade_eq_bot_of_forall_exists_pow_eq _ p (fun u ↦ ?_) hn.ne'
  obtain ⟨c, hc⟩ := fin0_const (u : MvRatFunc (Fin 0) ℂ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp.pos
  have hz0 : algebraMap (MvPolynomial (Fin 0) ℂ) (MvRatFunc (Fin 0) ℂ) (C z) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hc, ← hz, C_pow, map_pow, h, zero_pow hp.ne_zero]
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [hc, ← hz, C_pow, map_pow]

end OMA.ZL.SLKnown

/-! `K_2(C(x))/p = 0`: copied verbatim from the merged
`reductions/SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.lean`
(credit: chris01-dev). -/
namespace OMA.ZL.One

open MilnorK MvPolynomial

theorem kneg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    -A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, add_zero] at h3
  exact h3

theorem kmul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    A * -B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, add_zero] at h3
  exact h3

theorem kof_neg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : -A * B = 0) :
    A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, zero_add] at h3
  exact h3

theorem kof_mul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * -B = 0) :
    A * B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, zero_add] at h3
  exact h3

theorem units_gen (H : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ)
    (hc : ∀ (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) = algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c) →
        u ∈ H)
    (hx : ∀ (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) =
        algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a) → u ∈ H)
    (u : (MvRatFunc (Fin 1) ℂ)ˣ) : u ∈ H := by
  let M : Submonoid (MvRatFunc (Fin 1) ℂ) :=
    { carrier := {x | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, (v : MvRatFunc (Fin 1) ℂ) = x → v ∈ H}
      one_mem' := by
        intro v hv
        have : v = 1 := Units.ext hv
        rw [this]; exact H.one_mem
      mul_mem' := by
        intro x y hx' hy' v hv
        have hxy : x * y ≠ 0 := hv ▸ v.ne_zero
        have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy
        have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy
        have : v = Units.mk0 x hx0 * Units.mk0 y hy0 := Units.ext (by simp [hv])
        rw [this]
        exact H.mul_mem (hx' _ rfl) (hy' _ rfl) }
  have hpoly : ∀ q : MvPolynomial (Fin 1) ℂ,
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ∈ M := by
    intro q
    have hsurj : ∀ q : MvPolynomial (Fin 1) ℂ,
        ∃ r : Polynomial ℂ, Polynomial.eval₂RingHom MvPolynomial.C (X 0) r = q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => exact ⟨Polynomial.C a, by simp⟩
      | add f g hf hg =>
        obtain ⟨rf, rfl⟩ := hf
        obtain ⟨rg, rfl⟩ := hg
        exact ⟨rf + rg, map_add _ _ _⟩
      | mul_X f i hf =>
        obtain ⟨rf, rfl⟩ := hf
        refine ⟨rf * Polynomial.X, ?_⟩
        have : i = 0 := Subsingleton.elim _ _
        simp [this]
    obtain ⟨r, rfl⟩ := hsurj q
    rw [(IsAlgClosed.splits r).eq_prod_roots]
    rw [map_mul, map_mul, map_multiset_prod, map_multiset_prod]
    refine M.mul_mem ?_ (M.multiset_prod_mem _ ?_)
    · intro v hv
      refine hc r.leadingCoeff v ?_
      simpa using hv
    · intro x hx'
      simp only [Multiset.map_map, Multiset.mem_map] at hx'
      obtain ⟨a, -, rfl⟩ := hx'
      intro v hv
      refine hx a v ?_
      simpa using hv
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 1) ℂ)
    (u : MvRatFunc (Fin 1) ℂ)
  have hd0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) d ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, div_zero]
  have hn0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) n ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, zero_div]
  have : u = Units.mk0 _ hn0 * (Units.mk0 _ hd0)⁻¹ :=
    Units.ext (by simp [← hnd, div_eq_mul_inv])
  rw [this]
  exact H.mul_mem (hpoly n _ rfl) (H.inv_mem (hpoly d _ rfl))

theorem algMap_ne_zero {q : MvPolynomial (Fin 1) ℂ} (hq : q ≠ 0) :
    algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq

theorem of_const_eq_zero (p : ℕ) (hp : 0 < p) (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c)) :
    MilnorK.of p u = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp
  have hz0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C z) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hu, ← hz, map_pow, map_pow, h, zero_pow hp.ne']
  have : u = (Units.mk0 _ hz0) ^ p := Units.ext (by simp [hu, ← hz])
  rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_lin_mul_of_lin (p : ℕ) (hp : 0 < p) (a b : ℂ) (hab : a ≠ b)
    (u v : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a))
    (hv : (v : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C b)) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  have hα : (b - a) ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk1 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (b - a)⁻¹) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hk2 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (-(b - a)⁻¹)) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hpoly : (X 0 - C a) * C (b - a)⁻¹ + (X 0 - C b) * C (-(b - a)⁻¹) =
      (1 : MvPolynomial (Fin 1) ℂ) := by
    have h1 : (C ((b - a)⁻¹ * (b - a)) : MvPolynomial (Fin 1) ℂ) = 1 := by
      rw [inv_mul_cancel₀ hα, C_1]
    rw [← h1]
    simp only [map_mul, map_sub, map_neg]
    ring
  have hst : ((u * Units.mk0 _ hk1 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((v * Units.mk0 _ hk2 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, hu, hv]
    rw [← map_mul, ← map_mul, ← map_add, hpoly, map_one]
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_mul, of_const_eq_zero p hp _ (Units.mk0 _ hk1) rfl,
    of_const_eq_zero p hp _ (Units.mk0 _ hk2) rfl, add_zero, add_zero] at h
  exact h

theorem of_lin_mul_self (p : ℕ) (hp : 0 < p) (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a)) :
    MilnorK.of p u * MilnorK.of p u = 0 := by
  have hw0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) ≠ 0 := by
    refine algMap_ne_zero ?_
    intro h
    have := congrArg (MvPolynomial.eval (fun _ => a)) h
    simp at this
  have hw : (u : MvRatFunc (Fin 1) ℂ) - 1 =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) := by
    rw [hu, ← map_one (algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ)), ← map_sub]
    congr 1
    simp only [map_add, C_1]
    ring
  have hst : ((u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((Units.mk0 _ hw0 * u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, ← hw, Units.val_inv_eq_inv_val]
    have hu0 : (u : MvRatFunc (Fin 1) ℂ) ≠ 0 := u.ne_zero
    field_simp
    ring
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_inv] at h
  have h2 := of_lin_mul_of_lin p hp a (a + 1) (by simp) u (Units.mk0 _ hw0) hu rfl
  have h4 := kof_neg_mul _ _ h
  rw [mul_add, h2, zero_add] at h4
  exact kof_mul_neg _ _ h4

theorem of_mul_of_one_var (p : ℕ) (hp : 0 < p) (u v : (MvRatFunc (Fin 1) ℂ)ˣ) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  let K1 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
    { carrier := {u | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, MilnorK.of p u * MilnorK.of p v = 0}
      mul_mem' := by
        intro a b ha hb v
        rw [of_mul, add_mul, ha v, hb v, add_zero]
      one_mem' := by
        intro v
        rw [of_one, zero_mul]
      inv_mem' := by
        intro a ha v
        rw [of_inv]
        exact kneg_mul _ _ (ha v) }
  have hmem : u ∈ K1 := by
    refine units_gen K1 ?_ ?_ u
    · intro c u hu v
      rw [of_const_eq_zero p hp c u hu, zero_mul]
    · intro a u hu v
      let K2 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
        { carrier := {v | MilnorK.of p u * MilnorK.of p v = 0}
          mul_mem' := by
            intro x y hx hy
            show MilnorK.of p u * MilnorK.of p (x * y) = 0
            rw [of_mul, mul_add, hx, hy, add_zero]
          one_mem' := by
            show MilnorK.of p u * MilnorK.of p 1 = 0
            rw [of_one, mul_zero]
          inv_mem' := by
            intro x hx
            show MilnorK.of p u * MilnorK.of p x⁻¹ = 0
            rw [of_inv]
            exact kmul_neg _ _ hx }
      have hv : v ∈ K2 := by
        refine units_gen K2 ?_ ?_ v
        · intro c v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          rw [of_const_eq_zero p hp c v hv, mul_zero]
        · intro b v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          by_cases hab : a = b
          · subst hab
            have : u = v := Units.ext (hu.trans hv.symm)
            subst this
            exact of_lin_mul_self p hp a u hu
          · exact of_lin_mul_of_lin p hp a b hab u v hu hv
      exact hv
  exact hmem v

theorem grade_two_one_var (p : ℕ) (hp : 0 < p) : MilnorK.grade (MvRatFunc (Fin 1) ℂ) p 2 = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, symbol_succ]
  simp [of_mul_of_one_var p hp]

end OMA.ZL.One

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1

def H1 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) p 3

def H2 : Prop := ∀ m p : ℕ, 3 ≤ m → p.Prime →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p (m + 1)

theorem main : H1 → H2 → type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt := by
  intro h1 h2 m n p hmn hp
  rw [MilnorK.zero_mem_symbolLengthBounds_iff]
  refine OMA.ZL.Artin2K.grade_eq_bot_of_le p (m + 1) ?_ n hmn
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | rfl | rfl | hm
  · exact (MilnorK.zero_mem_symbolLengthBounds_iff _ _).mp (OMA.ZL.SLKnown.m_zero 1 p one_pos hp)
  · exact OMA.ZL.One.grade_two_one_var p hp.pos
  · by_cases hp2 : p = 2
    · subst hp2
      exact OMA.ZL.Artin2K.grade_C2_two_eq_bot 3 le_rfl
    · exact (MilnorK.zero_mem_symbolLengthBounds_iff _ _).mp (h1 p hp hp2)
  · exact (MilnorK.zero_mem_symbolLengthBounds_iff _ _).mp (h2 m p hm hp)

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1
