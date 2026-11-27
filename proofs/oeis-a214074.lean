import OMAStatements.S_oeis_a214074

-- Counterexamples to Clark Kimberling's conjecture on OEIS A214074.
-- Credit: @anmolspace. The formal statement is due to @niclorusso.

namespace A214074Counterexample

-- Every exponent in this progression is 121 modulo 330. At each one,
-- subtracting three from either power produces a multiple of 487891.
theorem common_factor (t : ℕ) :
    (487891 : ℤ) ∣ (Int.gcd ((2 : ℤ) ^ (3438721 + 5366790 * t) - 3)
      ((3 : ℤ) ^ (3438721 + 5366790 * t) - 3) : ℤ) := by
  have propagate (b : ℤ) (base : b ^ 3438721 % 487891 = 3)
      (period : b ^ 5366790 % 487891 = 1) :
      b ^ (3438721 + 5366790 * t) % 487891 = 3 := by
    induction t with
    | zero => exact base
    | succ t ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, Int.pow_add, Int.mul_emod, ih, period]
      decide
  exact Int.dvd_coe_gcd
    (Int.dvd_self_sub_of_emod_eq (propagate 2 (by decide +kernel) (by decide +kernel)))
    (Int.dvd_self_sub_of_emod_eq (propagate 3 (by decide +kernel) (by decide +kernel)))

end A214074Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a214074.main) := by
  intro conjecture
  have least := (conjecture 3438721 (by decide)).2 ⟨10421, by decide, by decide⟩
  have coprime : Int.gcd ((2 : ℤ) ^ 3438721 - 3) ((3 : ℤ) ^ 3438721 - 3) = 1 :=
    least.1.2
  have factor : (487891 : ℤ) ∣ (Int.gcd ((2 : ℤ) ^ 3438721 - 3)
      ((3 : ℤ) ^ 3438721 - 3) : ℤ) := A214074Counterexample.common_factor 0
  rw [coprime] at factor
  exact (by decide : ¬ (487891 : ℤ) ∣ (1 : ℤ)) factor
