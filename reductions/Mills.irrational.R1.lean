import FormalConjectures.Wikipedia.Mills

/-!
The rational case of Saito's argument, using the exponential approximation for the least
Mills number (Lemma 3.9, equation (3.17)) and Mahler's rational separation theorem
(Theorem 2.5 in Saito, https://arxiv.org/abs/2404.19461).
-/

namespace OMA.R_Mills_irrational_R1

open Filter

/-- Powers of the least Mills number eventually approach integers exponentially closely. -/
def H1 : Prop := ∀ A : ℝ, Mills.IsMinMills A → ∃ γ : ℝ, 0 < γ ∧
  ∀ᶠ k : ℕ in atTop, ∃ z : ℤ,
    |A ^ (3 ^ k : ℕ) - (z : ℝ)| ≤ Real.exp (-γ * ((3 ^ k : ℕ) : ℝ))

/-- Powers of a rational noninteger greater than one eventually avoid every integer. -/
def H2 : Prop := ∀ q : ℚ, (1 : ℝ) < (q : ℝ) → (∀ z : ℤ, (q : ℝ) ≠ (z : ℝ)) →
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ z : ℤ,
    Real.exp (-ε * (n : ℝ)) < |(q : ℝ) ^ n - (z : ℝ)|

lemma mills_ne_int {A : ℝ} (hA : Mills.IsMinMills A) (z : ℤ) : A ≠ (z : ℝ) := by
  intro h
  have hA1 : 1 < A := hA.1.1
  have hz : 1 < z := by exact_mod_cast (show (1 : ℝ) < (z : ℝ) from h ▸ hA1)
  let a := z.toNat
  have haZ : (a : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have haR : (a : ℝ) = A := by rw [h, ← haZ, Int.cast_natCast]
  have hp : Nat.Prime ⌊A ^ (3 : ℕ)⌋₊ := by
    simpa only [Nat.prime_iff, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_one] using
      (hA.1.2 (1 : ℕ+))
  rw [← haR, ← Nat.cast_pow, Nat.floor_natCast] at hp
  exact Nat.Prime.not_prime_pow (by norm_num : 2 ≤ (3 : ℕ)) hp

theorem main : H1 → H2 → type_of% @Mills.irrational := by
  intro close separate A hA hrat
  obtain ⟨q, hq⟩ := hrat
  have hq1 : (1 : ℝ) < (q : ℝ) := by rw [hq]; exact hA.1.1
  have hq_ne_int (z : ℤ) : (q : ℝ) ≠ (z : ℝ) :=
    fun hz => mills_ne_int hA z (hq.symm.trans hz)
  obtain ⟨γ, hγ, hclose⟩ := close A hA
  have pow_tends : Tendsto (fun k : ℕ => (3 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hseparate := pow_tends.eventually (separate q hq1 hq_ne_int γ hγ)
  obtain ⟨k, ⟨z, hz⟩, hfar⟩ := (hclose.and hseparate).exists
  rw [← hq] at hz
  exact (not_lt_of_ge hz) (hfar z)

end OMA.R_Mills_irrational_R1
