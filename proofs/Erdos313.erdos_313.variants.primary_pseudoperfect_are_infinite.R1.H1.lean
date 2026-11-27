import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1

/-! Local divisibility conditions and a reciprocal bound give the cofactor identity. -/

open Finset

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1.H1 := by
  intro P _ hprime hlocal hrecip
  let cofactor (p : ℕ) := ∏ q ∈ P.erase p, q
  let product := ∏ p ∈ P, p
  let total := ∑ p ∈ P, cofactor p
  change product = 1 + total
  have hpos : 0 < product := prod_pos fun p hp => (hprime p hp).pos
  have hdiv (p : ℕ) (hp : p ∈ P) : p ∣ 1 + total := by
    have hrest : p ∣ ∑ q ∈ P.erase p, cofactor q := by
      apply dvd_sum
      intro q hq
      exact dvd_prod_of_mem id (mem_erase.mpr ⟨(mem_erase.mp hq).1.symm, hp⟩)
    rw [show total = cofactor p + ∑ q ∈ P.erase p, cofactor q from
      (add_sum_erase P cofactor hp).symm, ← add_assoc, add_comm 1]
    exact dvd_add (hlocal p hp) hrest
  have hproductDvd : product ∣ 1 + total :=
    prod_dvd_of_isRelPrime
      (fun _ hp _ hq hne => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hprime _ hp) (hprime _ hq)).mpr hne)) hdiv
  have hscaled : (∑ p ∈ P, (1 : ℚ) / p) * (product : ℚ) = (total : ℚ) := by
    rw [sum_mul]
    simp only [total, Nat.cast_sum]
    apply sum_congr rfl
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    rw [show product = cofactor p * p from (prod_erase_mul P id hp).symm, Nat.cast_mul]
    field_simp
  have hlt := mul_lt_mul_of_pos_right hrecip (show (0 : ℚ) < product by exact_mod_cast hpos)
  rw [hscaled, one_mul, Nat.cast_lt] at hlt
  exact le_antisymm (Nat.le_of_dvd (by omega) hproductDvd) (by omega)
