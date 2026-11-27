import OMAReductions.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1

/-! Key step: if M is at least the N-th prime and M ≤ s^2, then there is a prime q with
M < q < M + s. Indeed let n + 1 be the number of primes up to M, p the n-th prime and q the
next one; then n ≥ N, p ≤ M < q, and q - p < sqrt p ≤ sqrt M ≤ s. Apply it with
M = x (x - 1) and with M = x^2, both with s = x. -/

namespace OMAOppermann

lemma next_prime (N : ℕ)
    (hN : ∀ n ≥ N, ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ) <
      Real.sqrt (n.nth Nat.Prime))
    (M s : ℕ) (hM : N.nth Nat.Prime ≤ M) (hs : M ≤ s ^ 2) :
    ∃ q, q.Prime ∧ M < q ∧ q < M + s := by
  have hinf := Nat.infinite_setOfPred_prime
  have hNc : N < Nat.count Nat.Prime (M + 1) :=
    (Nat.lt_nth_iff_count_lt (p := Nat.Prime) hinf).2 (Nat.lt_succ_of_le hM)
  obtain ⟨n, hn⟩ : ∃ n, Nat.count Nat.Prime (M + 1) = n + 1 :=
    ⟨Nat.count Nat.Prime (M + 1) - 1, by omega⟩
  have hnN : N ≤ n := by omega
  have hp : Nat.nth Nat.Prime n < M + 1 :=
    (Nat.lt_nth_iff_count_lt (p := Nat.Prime) hinf).1 (by rw [hn]; exact Nat.lt_succ_self n)
  have hq : M + 1 ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.count_le_iff_le_nth (p := Nat.Prime) hinf).1 (le_of_eq hn)
  have hA := hN n hnN
  refine ⟨Nat.nth Nat.Prime (n + 1), Nat.prime_nth_prime _, by omega, ?_⟩
  have hpM : (Nat.nth Nat.Prime n : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hp
  have h1 : Real.sqrt (Nat.nth Nat.Prime n) ≤ (s : ℝ) := by
    rw [Real.sqrt_le_left (Nat.cast_nonneg s)]
    exact le_trans hpM (by exact_mod_cast hs)
  have h2 : (Nat.nth Nat.Prime (n + 1) : ℝ) < (M : ℝ) + (s : ℝ) := by linarith
  exact_mod_cast h2

end OMAOppermann

theorem OMA.solution : OMA.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1.H2 := by
  intro N hN x hx
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hx
    · exact h
  have e1 : x * (x - 1) + x = x ^ 2 := by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hle : x * (x - 1) ≤ x ^ 2 := by omega
  constructor
  · obtain ⟨q, hq, h1, h2⟩ := OMAOppermann.next_prime N hN (x * (x - 1)) x hx.le hle
    exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by omega⟩, hq⟩
  · obtain ⟨q, hq, h1, h2⟩ := OMAOppermann.next_prime N hN (x ^ 2) x (by omega) le_rfl
    exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by rw [Nat.mul_add, mul_one, ← pow_two]; exact h2⟩, hq⟩
