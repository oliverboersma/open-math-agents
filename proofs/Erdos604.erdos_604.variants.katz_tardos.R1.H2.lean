import OMAReductions.R_Erdos604_erdos_604_variants_katz_tardos_R1

-- Step Erdos604.erdos_604.variants.katz_tardos.R1.H2: hypothesis H2 of reduction Erdos604.erdos_604.variants.katz_tardos.R1
-- Credit: @JamesSlash. Proof: the distance-equality pattern is a polynomial system over Q with a complex
-- solution (z = x0 + i x1, w = x0 - i x1); by the Nullstellensatz it has a solution in the algebraic
-- closure of Q keeping all required inequalities; adjoin its coordinates and a square root of -1.

namespace OMA604KT

open MvPolynomial Finset

theorem kt_h2 (ι : Type) [Finite ι] (x : ι → EuclideanSpace ℝ (Fin 2))
    (hx : Function.Injective x) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
    ∃ (i : K) (u v : ι → K), i ^ 2 = -1 ∧ Function.Injective u ∧ Function.Injective v ∧
    ∀ a b c d, (u a - u b) * (v a - v b) = (u c - u d) * (v c - v d) ↔
      dist (x a) (x b) = dist (x c) (x d) := by
  classical
  haveI := Fintype.ofFinite ι
  -- squared distances
  let D : ι → ι → ℝ := fun a b => (x a 0 - x b 0) ^ 2 + (x a 1 - x b 1) ^ 2
  have hdist : ∀ a b, dist (x a) (x b) = Real.sqrt (D a b) := by
    intro a b
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  have hD0 : ∀ a b, 0 ≤ D a b := fun a b => by positivity
  have hdistiff : ∀ a b c d, dist (x a) (x b) = dist (x c) (x d) ↔ D a b = D c d := by
    intro a b c d
    rw [hdist, hdist, Real.sqrt_inj (hD0 a b) (hD0 c d)]
  -- the polynomial system over ℚ
  let U : ι → MvPolynomial (ι ⊕ ι) ℚ := fun a => X (Sum.inl a)
  let V : ι → MvPolynomial (ι ⊕ ι) ℚ := fun a => X (Sum.inr a)
  let P : ι × ι × ι × ι → MvPolynomial (ι ⊕ ι) ℚ := fun q =>
    (U q.1 - U q.2.1) * (V q.1 - V q.2.1) - (U q.2.2.1 - U q.2.2.2) * (V q.2.2.1 - V q.2.2.2)
  let Es : Finset (ι × ι × ι × ι) := univ.filter (fun q => D q.1 q.2.1 = D q.2.2.1 q.2.2.2)
  let Ns : Finset (ι × ι × ι × ι) := univ.filter (fun q => D q.1 q.2.1 ≠ D q.2.2.1 q.2.2.2)
  let Ps : Finset (ι × ι) := univ.filter (fun p => p.1 ≠ p.2)
  let Q : MvPolynomial (ι ⊕ ι) ℚ :=
    (∏ q ∈ Ns, P q) * ∏ p ∈ Ps, ((U p.1 - U p.2) * (V p.1 - V p.2))
  let I : Ideal (MvPolynomial (ι ⊕ ι) ℚ) := Ideal.span (P '' (Es : Set (ι × ι × ι × ι)))
  -- a complex solution: z = x0 + i x1, w = x0 - i x1
  let zc : ι ⊕ ι → ℂ := fun s =>
    Sum.elim (fun a => (⟨x a 0, x a 1⟩ : ℂ)) (fun a => (⟨x a 0, -x a 1⟩ : ℂ)) s
  have evP : ∀ q, aeval zc (P q) = ((D q.1 q.2.1 - D q.2.2.1 q.2.2.2 : ℝ) : ℂ) := by
    intro q
    simp only [P, U, V, map_sub, map_mul, aeval_X, zc, Sum.elim_inl, Sum.elim_inr]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.ofReal_re, D]
      ring
    · simp only [Complex.sub_re, Complex.mul_im, Complex.sub_im, Complex.ofReal_im]
      ring
  have evU : ∀ a b, a ≠ b → aeval zc (U a - U b) ≠ 0 ∧ aeval zc (V a - V b) ≠ 0 := by
    intro a b hab
    have hne : x a ≠ x b := hx.ne hab
    have hco : x a 0 ≠ x b 0 ∨ x a 1 ≠ x b 1 := by
      by_contra h
      push Not at h
      apply hne
      ext i
      fin_cases i
      · exact h.1
      · exact h.2
    simp only [U, V, map_sub, aeval_X, zc, Sum.elim_inl, Sum.elim_inr]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [sub_eq_zero] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only at h1 h2
      rcases hco with h' | h'
      · exact h' h1
      · exact h' h2
    · rw [sub_eq_zero] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [neg_inj] at h1 h2
      rcases hco with h' | h'
      · exact h' h1
      · exact h' h2
  have evQ : aeval zc Q ≠ 0 := by
    simp only [Q, map_mul, map_prod]
    refine mul_ne_zero (prod_ne_zero_iff.mpr ?_) (prod_ne_zero_iff.mpr ?_)
    · intro q hq
      rw [evP]
      have h := (mem_filter.mp hq).2
      exact_mod_cast sub_ne_zero.mpr h
    · intro p hp
      have h := evU p.1 p.2 (mem_filter.mp hp).2
      rw [← map_mul]
      rw [map_mul]
      exact mul_ne_zero h.1 h.2
  have hIker : ∀ f ∈ I, aeval zc f = 0 := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨q, hq, rfl⟩
      have h := (mem_filter.mp hq).2
      rw [evP, h, sub_self, Complex.ofReal_zero]
    · exact map_zero _
    · intro f g _ _ hf hg
      rw [map_add, hf, hg, add_zero]
    · intro r f _ hf
      rw [smul_eq_mul, map_mul, hf, mul_zero]
  -- an algebraic solution with the same pattern (Nullstellensatz)
  obtain ⟨p, hpI, hpQ⟩ : ∃ p ∈ zeroLocus (AlgebraicClosure ℚ) I, aeval p Q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem : Q ∈ vanishingIdeal ℚ (zeroLocus (AlgebraicClosure ℚ) I) := by
      rw [mem_vanishingIdeal_iff]
      exact hcon
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    obtain ⟨m, hm⟩ := hmem
    have h := hIker _ hm
    rw [map_pow] at h
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h
      exact one_ne_zero h
    exact evQ ((pow_eq_zero_iff hm0).mp h)
  have hP0 : ∀ q ∈ Es, aeval p (P q) = 0 := fun q hq =>
    (mem_zeroLocus_iff.mp hpI) _ (Ideal.subset_span ⟨q, hq, rfl⟩)
  have hQne : (∏ q ∈ Ns, aeval p (P q)) * ∏ r ∈ Ps, (aeval p (U r.1 - U r.2) * aeval p (V r.1 - V r.2)) ≠ 0 := by
    simpa only [Q, map_mul, map_prod] using hpQ
  have hPne : ∀ q ∈ Ns, aeval p (P q) ≠ 0 := prod_ne_zero_iff.mp (left_ne_zero_of_mul hQne)
  have hUne : ∀ r ∈ Ps, aeval p (U r.1 - U r.2) * aeval p (V r.1 - V r.2) ≠ 0 :=
    prod_ne_zero_iff.mp (right_ne_zero_of_mul hQne)
  -- the number field
  obtain ⟨j, hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos
  let S : Set (AlgebraicClosure ℚ) := insert j (Set.range p)
  have hSfin : Finite S := (Set.Finite.insert j (Set.finite_range p)).to_subtype
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ S
  have hfd : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin
      (fun y _ => ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral)
  have hNF : NumberField K := ⟨⟩
  have hjS : j ∈ K := IntermediateField.subset_adjoin ℚ S (Set.mem_insert j _)
  have hpS : ∀ s, p s ∈ K := fun s =>
    IntermediateField.subset_adjoin ℚ S (Set.mem_insert_of_mem _ ⟨s, rfl⟩)
  let u : ι → K := fun a => ⟨p (Sum.inl a), hpS _⟩
  let v : ι → K := fun a => ⟨p (Sum.inr a), hpS _⟩
  have hPeval : ∀ a b c d : ι, aeval p (P (a, b, c, d)) =
      (p (Sum.inl a) - p (Sum.inl b)) * (p (Sum.inr a) - p (Sum.inr b)) -
        (p (Sum.inl c) - p (Sum.inl d)) * (p (Sum.inr c) - p (Sum.inr d)) := by
    intro a b c d
    simp only [P, U, V, map_sub, map_mul, aeval_X]
  refine ⟨K, hNF, ⟨j, hjS⟩, u, v, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp [hj]
  · intro a b hab
    by_contra hne
    have h := hUne (a, b) (mem_filter.mpr ⟨mem_univ _, hne⟩)
    apply left_ne_zero_of_mul h
    simp only [U, map_sub, aeval_X]
    rw [sub_eq_zero]
    exact congrArg Subtype.val hab
  · intro a b hab
    by_contra hne
    have h := hUne (a, b) (mem_filter.mpr ⟨mem_univ _, hne⟩)
    apply right_ne_zero_of_mul h
    simp only [V, map_sub, aeval_X]
    rw [sub_eq_zero]
    exact congrArg Subtype.val hab
  · intro a b c d
    rw [hdistiff]
    have hK : (u a - u b) * (v a - v b) = (u c - u d) * (v c - v d) ↔
        aeval p (P (a, b, c, d)) = 0 := by
      rw [hPeval, sub_eq_zero, Subtype.ext_iff]
      simp [u, v]
    rw [hK]
    by_cases hD : D a b = D c d
    · exact ⟨fun _ => hD, fun _ => hP0 _ (mem_filter.mpr ⟨mem_univ _, hD⟩)⟩
    · exact ⟨fun h => absurd h (hPne _ (mem_filter.mpr ⟨mem_univ _, hD⟩)), fun h => absurd h hD⟩

end OMA604KT

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1.H2 := by
  intro ι _ x hx
  exact OMA604KT.kt_h2 ι x hx
