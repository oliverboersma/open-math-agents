import OMAReductions.R_ABC_abc_variants_quality_R1

-- Step ABC.abc.variants.quality.R1.H1: hypothesis H1 of reduction ABC.abc.variants.quality.R1
-- Credit: @ptc-prover-bot

/-! For coprime `a + b = c`: the radical is multiplicative on coprime factors, so
`rad(abc) = rad(ab) · rad(c)` with `rad(c) ≥ 2` (as `c ≥ 2`). If `c` is squarefree, `rad(c) = c`;
if `ab` is squarefree, `rad(abc) = ab · rad(c) ≥ 2ab ≥ a + b`. (If `a = b`, coprimality of `a`
and `c = 2a` forces `a = b = 1`.) -/

namespace OMA.ABCQualityH1

lemma rad_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (h : Nat.Coprime x y) :
    ABC.radical (x * y) = ABC.radical x * ABC.radical y := by
  unfold ABC.radical
  rw [Nat.primeFactors_mul hx hy, Finset.prod_union h.disjoint_primeFactors]

lemma rad_pos (x : ℕ) : 0 < ABC.radical x :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_sq {x : ℕ} (hx : Squarefree x) : ABC.radical x = x := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_of_squarefree hx

lemma two_le_rad {c : ℕ} (hc : 2 ≤ c) : 2 ≤ ABC.radical c := by
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  have hmem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpc, by omega⟩
  have hd : p ∣ ABC.radical c := by
    unfold ABC.radical; exact Finset.dvd_prod_of_mem id hmem
  exact le_trans hp.two_le (Nat.le_of_dvd (rad_pos c) hd)

theorem H1_proof : OMA.R_ABC_abc_variants_quality_R1.H1 := by
  intro a b c ha hb hp habc
  have hac : a ≠ c := by omega
  have hbc : b ≠ c := by omega
  have cac : Nat.Coprime a c := hp (by simp) (by simp) hac
  have cbc : Nat.Coprime b c := hp (by simp) (by simp) hbc
  have cab : Nat.Coprime a b := by
    by_cases h : a = b
    · subst h
      have h2 : Nat.gcd a c = a := by
        rw [← habc]; exact Nat.gcd_eq_left (Dvd.intro 2 (by ring))
      have h1 : a = 1 := by rw [Nat.Coprime] at cac; omega
      subst h1; exact Nat.coprime_one_left 1
    · exact hp (by simp) (by simp) h
  have cabc : Nat.Coprime (a * b) c := Nat.Coprime.mul cac cbc
  have hab0 : a * b ≠ 0 := by positivity
  have hR : ABC.radical (a * b * c) = ABC.radical (a * b) * ABC.radical c :=
    rad_mul hab0 (by omega) cabc
  have r2 := two_le_rad (show 2 ≤ c by omega)
  have rp := rad_pos (a * b)
  refine ⟨?_, ?_⟩
  · rw [hR]; nlinarith
  · rintro (hc | hsq)
    · rw [hR, rad_sq hc]; nlinarith
    · rw [hR, rad_sq hsq]
      have h1 : a + b ≤ 2 * (a * b) := by nlinarith
      have h2 : 2 * (a * b) ≤ a * b * ABC.radical c := by
        rw [mul_comm 2]; exact Nat.mul_le_mul_left _ r2
      omega

end OMA.ABCQualityH1

theorem OMA.solution : OMA.R_ABC_abc_variants_quality_R1.H1 := OMA.ABCQualityH1.H1_proof
