import OMAStatements.S_oeis_a134347

-- Problem: A134347: A007318^(-1) * A134346.
-- Upstream: formal-conjectures statements/oeis-a134347.lean:0 (declaration OMA.S_oeis_a134347.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a134347

open OMA.S_oeis_a134347

lemma reduce (n k : ℕ) (hk : k ≤ n) : T n k = (n.choose k : ℤ) *
    ∑ t ∈ Finset.range (n - k + 1), (-1) ^ (n - k - t) * ((n - k).choose t : ℤ) *
      (2 ^ (k + t + 1) - 1) := by
  unfold T A134346
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ n + 1 by omega)]
  have h0 : ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (n - j) * (n.choose j : ℤ) *
      ((2 ^ (j + 1) - 1) * (j.choose k : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt hj]
    simp
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range, show n + 1 - k = n - k + 1 by omega,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  have hc : n.choose (k + t) * (k + t).choose k = n.choose k * (n - k).choose t := by
    have := Nat.choose_mul (n := n) (k := k + t) (s := k) (by omega)
    rw [this, show k + t - k = t by omega]
  have hc' : (n.choose (k + t) : ℤ) * ((k + t).choose k : ℤ) =
      (n.choose k : ℤ) * ((n - k).choose t : ℤ) := by exact_mod_cast hc
  rw [show n - (k + t) = n - k - t by omega, show k + t + 1 = k + t + 1 from rfl]
  linear_combination ((-1 : ℤ) ^ (n - k - t) * (2 ^ (k + t + 1) - 1)) * hc'

lemma alt_two (m : ℕ) : ∑ t ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - t) * (m.choose t : ℤ) * 2 ^ t
    = 1 := by
  calc ∑ t ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - t) * (m.choose t : ℤ) * 2 ^ t
      = ∑ t ∈ Finset.range (m + 1), (2 : ℤ) ^ t * (-1) ^ (m - t) * (m.choose t : ℤ) := by
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ = ((2 : ℤ) + -1) ^ m := (add_pow (2 : ℤ) (-1) m).symm
    _ = 1 := by norm_num

lemma alt_one (m : ℕ) : ∑ t ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - t) * (m.choose t : ℤ)
    = if m = 0 then 1 else 0 := by
  calc ∑ t ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - t) * (m.choose t : ℤ)
      = ∑ t ∈ Finset.range (m + 1), (1 : ℤ) ^ t * (-1) ^ (m - t) * (m.choose t : ℤ) := by
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ = ((1 : ℤ) + -1) ^ m := (add_pow (1 : ℤ) (-1) m).symm
    _ = if m = 0 then 1 else 0 := by
        split_ifs with h
        · subst h
          simp
        · norm_num [zero_pow h]

lemma solve : ∀ n k : ℕ, k ≤ n →
    T n k = if k < n then 2 ^ (k + 1) * (n.choose k : ℤ) else 2 ^ (n + 1) - 1 := by
  intro n k hk
  rw [reduce n k hk]
  have hsplit : ∑ t ∈ Finset.range (n - k + 1), (-1 : ℤ) ^ (n - k - t) *
      ((n - k).choose t : ℤ) * (2 ^ (k + t + 1) - 1) =
      2 ^ (k + 1) * ∑ t ∈ Finset.range (n - k + 1), (-1 : ℤ) ^ (n - k - t) *
        ((n - k).choose t : ℤ) * 2 ^ t -
      ∑ t ∈ Finset.range (n - k + 1), (-1 : ℤ) ^ (n - k - t) * ((n - k).choose t : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hsplit, alt_two, alt_one]
  split_ifs with h1 h2 h2
  · omega
  · obtain rfl : k = n := by omega
    simp
  · ring
  · omega

end OMA.P_oeis_a134347

theorem OMA.solution : type_of% @OMA.S_oeis_a134347.main := OMA.P_oeis_a134347.solve
