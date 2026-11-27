import OMAStatements.S_oeis_a053922

namespace DecimalSixes
open OMA.S_oeis_a053922

/-- Decimal repunit with `n` ones, including the empty repunit at `n = 0`. -/
private def repunit : ℕ → ℕ
  | 0 => 0
  | n+1 => 1 + 10 * repunit n

private lemma power_ten (n : ℕ) : 10^n = 9 * repunit n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, repunit]; ring

private lemma repeat_value (n d : ℕ) : Nat.ofDigits 10 (List.replicate n d) = d * repunit n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih => rw [List.replicate_succ, Nat.ofDigits_cons, ih, repunit]; ring

/-- Least-significant digit first, following `Nat.digits`. -/
private def pattern (n : ℕ) := 4 :: (List.replicate n 2 ++ 6 :: List.replicate n 4)

private lemma pattern_value (n : ℕ) : sixesEight n ^ 2 = Nat.ofDigits 10 (pattern n) := by
  have hr : (10^n - 1) / 9 = repunit n := by rw [power_ten]; simp
  rw [sixesEight, hr]
  simp only [pattern, Nat.ofDigits_cons, Nat.ofDigits_append,
    List.length_replicate, repeat_value, power_ten]
  ring

private lemma pattern_mem {n d : ℕ} (h : d ∈ pattern n) : d = 2 ∨ d = 4 ∨ d = 6 := by
  simp only [pattern, List.mem_cons, List.mem_append, List.mem_replicate] at h
  tauto

lemma square_digits (n : ℕ) : Nat.digits 10 (sixesEight n ^ 2) = pattern n := by
  rw [pattern_value]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    rcases pattern_mem hd with rfl | rfl | rfl <;> decide
  · intro h
    rcases pattern_mem (List.getLast_mem h) with hv | hv | hv <;> omega

end DecimalSixes

/-- Harvey P. Dale's conjecture on OEIS A053922, using Zhao Hui Du's square pattern. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a053922.main := by
  intro n d hd
  rw [DecimalSixes.square_digits] at hd
  exact DecimalSixes.pattern_mem hd
