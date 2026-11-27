import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step OeisA182126.conjecture3.R1.H2: hypothesis H2 of reduction OeisA182126.conjecture3.R1
-- Credit: @ivillar
-- Proof: a kernel-checked table of the first 63 primes (each entry is prime and is preceded by
-- exactly its index many primes, so Nat.nth_count identifies it), then a finite kernel check of
-- a(1), ..., a(61).

namespace OMA.W3OeisA182126

def L : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307]

theorem table_raw : ∀ k < 63, Nat.count Nat.Prime (L.getD k 0) = k ∧ Nat.Prime (L.getD k 0) := by
  decide +kernel

theorem table (k : ℕ) (hk : k < 63) : Nat.nth Nat.Prime k = L.getD k 0 := by
  obtain ⟨hc, hp⟩ := table_raw k hk
  conv_lhs => rw [← hc]
  exact Nat.nth_count hp

theorem fin_check : ∀ n < 62, 0 < n →
    Nat.Prime ((L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0) →
    (L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0 ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  decide +kernel

theorem key : ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime →
    OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  intro n hn hle hp
  have ha : OeisA182126.a n = (L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0 := by
    unfold OeisA182126.a OeisA182126.prime
    rw [if_neg (by omega), table (n - 1) (by omega), show n + 1 - 1 = n by omega, table n (by omega),
      show n + 2 - 1 = n + 1 by omega, table (n + 1) (by omega)]
  rw [ha] at hp ⊢
  exact fin_check n (by omega) hn hp

end OMA.W3OeisA182126

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  unfold OMA.R_OeisA182126_conjecture3_R1.H2
  exact OMA.W3OeisA182126.key
