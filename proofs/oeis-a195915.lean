import OMAStatements.S_oeis_a195915

-- Problem: A195915: Table with T(n,1) = n, otherwise T(n,k) = xor(T(n-1,k-1), T(n-1,k)).
-- Upstream: statements/oeis-a195915.lean (declaration OMA.S_oeis_a195915.main)
-- Credit: @Ksungwon09

open OMA.S_oeis_a195915

private lemma entry_eq_zero_of_le : ∀ n k : ℕ, n ≤ k → entry n k = 0
  | 0, _, _ => rfl
  | n + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    change entry n k ^^^ entry n (k + 1) = 0
    rw [entry_eq_zero_of_le n k (by omega), entry_eq_zero_of_le n (k + 1) (by omega)]
    rfl

private lemma entry_shift_pow_two : ∀ j m c : ℕ,
    entry (m + 2 ^ j) (c + 2 ^ j) = entry m c ^^^ entry m (c + 2 ^ j)
  | 0, m, c => rfl
  | j + 1, m, c => by
    have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
    rw [hpow, ← Nat.add_assoc, ← Nat.add_assoc]
    rw [entry_shift_pow_two j (m + 2 ^ j) (c + 2 ^ j)]
    rw [entry_shift_pow_two j m c, entry_shift_pow_two j m (c + 2 ^ j)]
    rw [Nat.xor_assoc, ← Nat.xor_assoc (entry m (c + 2 ^ j)), Nat.xor_self, Nat.zero_xor]

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k _ hn
  rw [Nat.add_comm (2 ^ j) n, Nat.add_comm (2 ^ j) k, entry_shift_pow_two j n k]
  rw [entry_eq_zero_of_le n (k + 2 ^ j) (by omega), Nat.xor_zero]
