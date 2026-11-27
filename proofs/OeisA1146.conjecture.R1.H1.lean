import OMAReductions.R_OeisA1146_conjecture_R1

-- Step OeisA1146.conjecture.R1.H1: hypothesis H1 of reduction OeisA1146.conjecture.R1
-- Credit: @caa1982 (building on DONE note by @anmolspace)

theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1.H1 := by
  intro m
  rw [← pow_mul, OMA.Hasler.mersenneIff]
  constructor
  · intro h
    have hm : m ∣ 2 ^ m := (dvd_mul_right m 4).trans h
    obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
    refine ⟨t, ?_, rfl⟩
    by_contra! ht
    interval_cases t <;> norm_num at h
  · rintro ⟨t, ht, rfl⟩
    rw [show (2 : ℕ) ^ t * 4 = 2 ^ (t + 2) by norm_num [pow_add]]
    apply pow_dvd_pow
    induction t, ht using Nat.le_induction with
    | base => decide
    | succ t _ ih => rw [pow_succ]; omega
