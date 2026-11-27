import OMAStatements.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base

/-!
# Counting prime powers among palindromes

At the cutoff X = 2^(3t), bases of powers with exponent at least three
are below 2^t, and the exponent is below 3t. Removing those powers
leaves only primes and squares of primes.

The square estimate is deliberately weaker than the fixed-length bound
of Cilleruelo, Luca and Shparlinski, Power Values of Palindromes, §2.
The lower bound on palindromic prime powers is the open analytic input.

Credit: @Pixelstorm44
-/

namespace OMA.R_wp_are_there_infinitely_many_palindromic_primes_to_every_base_R1

-- The excess above the error budget is unbounded at arbitrarily large cutoffs.
def H1 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ B : ℕ, ∃ t ≥ B,
    (3 * t + 1) * 2 ^ t + B <
      ((Finset.range (2 ^ (3 * t))).filter fun n =>
        IsPrimePow n ∧ (Nat.digits b n).reverse = Nat.digits b n).card

-- There are eventually at most X^(1/3) palindromic squares below X.
def H2 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∃ T : ℕ, ∀ t ≥ T,
    ((Finset.range (2 ^ (3 * t))).filter fun n =>
      IsSquare n ∧ (Nat.digits b n).reverse = Nat.digits b n).card ≤ 2 ^ t

lemma higher_power_mem {p k t : ℕ} (hp : 2 ≤ p) (hk : 3 ≤ k)
    (hpk : p ^ k < 2 ^ (3 * t)) :
    p ^ k ∈ (((Finset.range (2 ^ t)).product (Finset.range (3 * t))).image
      fun z : ℕ × ℕ => z.1 ^ z.2) := by
  have hbase : p ^ 3 < (2 ^ t) ^ 3 := calc
    p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    _ < (2 ^ t) ^ 3 := by simpa [← pow_mul, Nat.mul_comm t 3] using hpk
  have hexp : (2 : ℕ) ^ k < 2 ^ (3 * t) :=
    (Nat.pow_le_pow_left hp k).trans_lt hpk
  apply Finset.mem_image.mpr
  refine ⟨(p, k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, rfl⟩
  · exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 3 ≠ 0)).mp hbase
  · exact (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hexp

theorem main : H1 → H2 → type_of% @OMA.S_wp_are_there_infinitely_many_palindromic_primes_to_every_base.main := by
  classical
  intro hlower hsquares b hb hfinite
  obtain ⟨T, hT⟩ := hsquares b hb
  let primes := hfinite.toFinset
  let B := max T primes.card
  obtain ⟨t, ht, hl⟩ := hlower b hb B
  let total := (Finset.range (2 ^ (3 * t))).filter fun n =>
    IsPrimePow n ∧ (Nat.digits b n).reverse = Nat.digits b n
  let squares := (Finset.range (2 ^ (3 * t))).filter fun n =>
    IsSquare n ∧ (Nat.digits b n).reverse = Nat.digits b n
  let pairs := (Finset.range (2 ^ t)).product (Finset.range (3 * t))
  let powers := pairs.image fun z : ℕ × ℕ => z.1 ^ z.2
  have cover : total ⊆ primes ∪ squares ∪ powers := by
    intro n hn
    obtain ⟨hbound, hpow, hpal⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    rcases eq_or_ne k 1 with rfl | hne
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply hfinite.mem_toFinset.mpr
      exact ⟨by simpa using hp, hpal⟩
    rcases eq_or_ne k 2 with rfl | hne'
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hbound, ⟨p, pow_two p⟩, hpal⟩
    · exact Finset.mem_union_right _ (higher_power_mem hp.two_le (by omega) (Finset.mem_range.mp hbound))
  have hpc : powers.card ≤ 2 ^ t * (3 * t) := calc
    powers.card ≤ pairs.card := Finset.card_image_le
    _ = _ := by simp [pairs]
  have hsc : squares.card ≤ 2 ^ t := hT t ((le_max_left _ _).trans ht)
  have hbc : primes.card ≤ B := le_max_right _ _
  have hc : total.card ≤ (primes.card + squares.card) + powers.card :=
    (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change (3 * t + 1) * 2 ^ t + B < total.card at hl
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (3 * t) (2 ^ t)] at hl
  omega

end OMA.R_wp_are_there_infinitely_many_palindromic_primes_to_every_base_R1
