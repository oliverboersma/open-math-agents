import OMAReductions.R_OeisA238585_conjecture_2_R1
import Mathlib

/-! The twelve enumerated prime counts in A238585. -/
namespace A238585Short

private def primes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]

private theorem primeIndex (i p : ℕ) (hp : p.Prime)
    (hi : Nat.count Nat.Prime p = i) : Nat.nth Nat.Prime i = p :=
  hi ▸ Nat.nth_count hp

private theorem fastCount (i p : ℕ)
    (h : @Nat.count Nat.Prime Nat.decidablePrime' p = i) : Nat.count Nat.Prime p = i :=
  (congrArg (fun d : DecidablePred Nat.Prime => @Nat.count Nat.Prime d p)
    Nat.decidablePrime_csimp).trans h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem nth_eq (i : ℕ) (hi : i < 44) :
    Nat.nth Nat.Prime i = primes[i]! := by
  interval_cases i
  · exact primeIndex 0 2 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 1 3 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 2 5 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 3 7 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 4 11 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 5 13 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 6 17 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 7 19 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 8 23 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 9 29 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 10 31 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 11 37 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 12 41 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 13 43 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 14 47 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 15 53 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 16 59 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 17 61 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 18 67 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 19 71 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 20 73 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 21 79 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 22 83 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 23 89 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 24 97 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 25 101 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 26 103 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 27 107 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 28 109 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 29 113 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 30 127 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 31 131 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 32 137 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 33 139 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 34 149 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 35 151 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 36 157 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 37 163 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 38 167 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 39 173 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 40 179 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 41 181 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 42 191 (by norm_num) (by apply fastCount; decide +kernel)
  · exact primeIndex 43 193 (by norm_num) (by apply fastCount; decide +kernel)

private def count (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico 1 n,
    if (2 ≤ p ∧ p.minFac = p) ∧
      (2 ≤ primes[p - 1]! ^ 2 + (primes[n - 1]! - 1) ^ 2 ∧
        (primes[p - 1]! ^ 2 + (primes[n - 1]! - 1) ^ 2).minFac =
          primes[p - 1]! ^ 2 + (primes[n - 1]! - 1) ^ 2)
    then 1 else 0

private theorem a_eq (n : ℕ) (hn : n ≤ 44) : OeisA238585.a n = count n := by
  unfold OeisA238585.a count
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := (Finset.mem_Ico.mp hp).2
  rw [nth_eq (p - 1) (by omega), nth_eq (n - 1) (by omega)]
  simp only [Nat.prime_def_minFac]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem ones (n : ℕ)
    (hn : n ∈ ({4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44} : Set ℕ)) :
    OeisA238585.a n = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [a_eq _ (by decide)]
    unfold count
    decide +kernel

end A238585Short

theorem OMA.solution : OMA.R_OeisA238585_conjecture_2_R1.H1 := A238585Short.ones