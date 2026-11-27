import OMAStatements.S_mse_2822876

/-!
A complete proof of the polynomial-ideal question catalogued as mse-2822876.
The argument first proves the more general UFD statement by finite prime avoidance.

Original question: Leonardo Schultz, Mathematics Stack Exchange, 17 June 2018:
https://math.stackexchange.com/questions/2822876/

Mathematical prior art: Will Sawin's UFD argument and tj_'s prime-avoidance
comment, MathOverflow, 13 December 2021:
https://mathoverflow.net/questions/410693/
https://mathoverflow.net/a/410694/

This is an independent Lean formalization of the established argument, not a
claim of a new mathematical theorem.
-/

namespace OMA.MSE2822876

open UniqueFactorizationMonoid

/-- In a UFD, pairwise nonzero nonunit common divisors in an ideal yield a global divisor. -/
theorem common_divisor_of_pairwise {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R)
    (hpair : ∀ a ∈ I, ∀ b ∈ I,
      ∃ d : R, d ≠ 0 ∧ ¬IsUnit d ∧ d ∣ a ∧ d ∣ b) :
    ∃ d : R, d ≠ 0 ∧ ¬IsUnit d ∧ ∀ a ∈ I, d ∣ a := by
  classical
  by_cases hz : ∀ a ∈ I, a = 0
  · obtain ⟨d, hd0, hdu, _, _⟩ := hpair 0 I.zero_mem 0 I.zero_mem
    refine ⟨d, hd0, hdu, ?_⟩
    intro a ha
    rw [hz a ha]
    exact dvd_zero d
  · push Not at hz
    obtain ⟨a, ha, ha0⟩ := hz
    let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
    let S : Finset R := (normalizedFactors a).toFinset
    have hprime : ∀ p ∈ S, Prime p := by
      intro p hp
      have hp' : p ∈ normalizedFactors a := Multiset.mem_toFinset.mp hp
      exact prime_of_normalized_factor p hp'
    have hcover : (I : Set R) ⊆
        ⋃ p ∈ (↑S : Set R), (Ideal.span ({p} : Set R) : Set R) := by
      intro b hb
      obtain ⟨d, hd0, hdu, hda, hdb⟩ := hpair a ha b hb
      obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
      obtain ⟨q, hq, hpq⟩ := exists_mem_normalizedFactors_of_dvd ha0 hp (hpd.trans hda)
      refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Multiset.mem_toFinset.mpr hq
      · exact Ideal.mem_span_singleton.mpr
          (hpq.dvd_iff_dvd_left.mp (hpd.trans hdb))
    obtain ⟨p, hp, hI⟩ :=
      (Ideal.subset_union_prime (s := S) (f := fun p => Ideal.span ({p} : Set R)) 0 0
        (fun p hp _ _ => Ideal.isPrime_span_singleton_of_prime (hprime p hp))).mp hcover
    refine ⟨p, (hprime p hp).ne_zero, (hprime p hp).not_isUnit, ?_⟩
    intro b hb
    exact Ideal.mem_span_singleton.mp (hI hb)

/-- The pairwise property is equivalent to containment in a nonzero principal prime ideal. -/
theorem pairwise_iff_exists_prime {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) :
    (∀ a ∈ I, ∀ b ∈ I,
      ∃ d : R, d ≠ 0 ∧ ¬IsUnit d ∧ d ∣ a ∧ d ∣ b) ↔
    ∃ p : R, Prime p ∧ ∀ a ∈ I, p ∣ a := by
  constructor
  · intro hpair
    obtain ⟨d, hd0, hdu, hdiv⟩ := common_divisor_of_pairwise I hpair
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
    exact ⟨p, irreducible_iff_prime.mp hp, fun a ha => hpd.trans (hdiv a ha)⟩
  · rintro ⟨p, hp, hdiv⟩ a ha b hb
    exact ⟨p, hp.ne_zero, hp.not_isUnit, hdiv a ha, hdiv b hb⟩

/-- Over a field, a polynomial is nonconstant exactly when it is nonzero and a nonunit. -/
theorem positive_totalDegree_iff {K σ : Type*} [Field K] (p : MvPolynomial σ K) :
    0 < p.totalDegree ↔ p ≠ 0 ∧ ¬IsUnit p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hp
      simp [hp] at h
    · intro hu
      have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
      omega
  · rintro ⟨hp, hnu⟩
    by_contra hn
    have hdeg : p.totalDegree = 0 := by omega
    have heq : p = MvPolynomial.C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
    have hc : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp
      simpa [hz] using heq
    apply hnu
    rw [heq]
    exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- The full source statement, including zero ideals and zero variables. -/
theorem polynomial_ideal_common_factor (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hpair : ∀ f ∈ I, ∀ g ∈ I,
      ∃ h : MvPolynomial (Fin n) ℂ, 0 < h.totalDegree ∧ h ∣ f ∧ h ∣ g) :
    ∃ h : MvPolynomial (Fin n) ℂ, 0 < h.totalDegree ∧ ∀ f ∈ I, h ∣ f := by
  have hg : ∀ f ∈ I, ∀ g ∈ I,
      ∃ h : MvPolynomial (Fin n) ℂ, h ≠ 0 ∧ ¬IsUnit h ∧ h ∣ f ∧ h ∣ g := by
    intro f hf g hg
    obtain ⟨h, hd, hdf, hdg⟩ := hpair f hf g hg
    exact ⟨h, (positive_totalDegree_iff h).mp hd |>.1,
      (positive_totalDegree_iff h).mp hd |>.2, hdf, hdg⟩
  obtain ⟨h, hn, hu, hdiv⟩ := common_divisor_of_pairwise I hg
  exact ⟨h, (positive_totalDegree_iff h).mpr ⟨hn, hu⟩, hdiv⟩

end OMA.MSE2822876

theorem OMA.solution : type_of% @OMA.S_mse_2822876.main := by
  intro n I hpair
  exact OMA.MSE2822876.polynomial_ideal_common_factor n I hpair
