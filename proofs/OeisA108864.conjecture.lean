import FormalConjectures.OEIS.«108864»
import Mathlib.Tactic.NormNum.Prime

/-!
The odd number 815634435 has ordinary deficiency 6 (OEIS A141548).
Its proper divisors sum to less than the number, so the greedy subtraction
accepts every proper divisor and leaves exactly 6.
-/

open OeisA108864

private theorem greedy_subtraction_eq (n : ℕ) (ds : List ℕ) (r : ℕ)
    (h : (ds.filter fun d => decide (d ∣ n)).sum ≤ r) :
    ds.foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) r =
      r - (ds.filter fun d => decide (d ∣ n)).sum := by
  induction ds generalizing r with
  | nil => simp
  | cons d ds ih =>
    by_cases hd : d ∣ n
    · simp [hd] at h
      have hdr : d ≤ r := by omega
      have hrest : (ds.filter fun d => decide (d ∣ n)).sum ≤ r - d := by omega
      rw [List.foldl_cons, if_pos ⟨hd, hdr⟩, ih _ hrest]
      simp [hd]
      omega
    · simp [hd] at h ⊢
      exact ih _ h

private theorem sigma_prime (p : ℕ) (hp : p.Prime) :
    ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors]
  simp [Ne.symm hp.ne_one, add_comm]

private theorem sum_proper_divisors_list (n : ℕ) :
    ((List.range n).filter fun d => decide (d ∣ n)).sum = ∑ d ∈ n.properDivisors, d := by
  let ds := (List.range n).filter fun d => decide (d ∣ n)
  have hnodup : ds.Nodup := List.nodup_range.filter _
  have hset : ds.toFinset = n.properDivisors := by
    ext d
    simp [ds, Nat.mem_properDivisors, and_comm]
  change ds.sum = _
  rw [← hset]
  simpa using (List.sum_toFinset (id : ℕ → ℕ) hnodup).symm

private theorem perfect_deficiency_of_deficient (n : ℕ)
    (hpos : 0 < ∑ d ∈ n.properDivisors, d)
    (hbound : (∑ d ∈ n.properDivisors, d) ≤ n) :
    perfectDeficiency n = n - ∑ d ∈ n.properDivisors, d := by
  unfold perfectDeficiency
  have hfold := greedy_subtraction_eq n (List.range n) n (by
    rwa [sum_proper_divisors_list])
  rw [List.range_succ, List.foldl_append, hfold, sum_proper_divisors_list]
  have hlt : (n - ∑ d ∈ n.properDivisors, d) < n := by omega
  simp [not_le_of_gt hlt]

private theorem witness_properDivisor_sum :
    (∑ d ∈ (815634435 : ℕ).properDivisors, d) = 815634429 := by
  have hσ : ArithmeticFunction.sigma 1 815634435 = 1631268864 := by
    have hn : (815634435 : ℕ) = 3 * (5 * (7 * (11 * (547 * 1291)))) := by rfl
    rw [hn,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime 3 (5 * (7 * (11 * (547 * 1291))))),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime 5 (7 * (11 * (547 * 1291)))),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime 7 (11 * (547 * 1291))),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime 11 (547 * 1291)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (by decide : Nat.Coprime 547 1291)]
    norm_num [sigma_prime 3 (by norm_num), sigma_prime 5 (by norm_num),
      sigma_prime 7 (by norm_num), sigma_prime 11 (by norm_num),
      sigma_prime 547 (by norm_num), sigma_prime 1291 (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self] at hσ
  exact Nat.eq_sub_of_add_eq hσ

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1500000 in
theorem OMA.disproof : ¬ (type_of% @OeisA108864.conjecture) := by
  intro hall
  let n : ℕ := 815634435
  have hn : A n := by
    refine ⟨by decide, ?_⟩
    rw [perfect_deficiency_of_deficient _ (by rw [witness_properDivisor_sum]; decide)
      (by rw [witness_properDivisor_sum]; decide), witness_properDivisor_sum]
    decide
  let small : Finset ℕ :=
    {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24,
      26, 28, 30, 32, 40, 42, 44, 50, 52, 60, 64, 68, 72, 110, 120, 126, 128, 130,
      136, 144, 150, 152, 180, 184, 204, 228, 256, 315, 462, 496, 512, 528, 592,
      656, 750, 884, 1012, 1024, 1155}
  have hsmall : ∀ d ∈ small, d < n ∧ A d := by decide +kernel
  have hsub : small ⊆ (Finset.range n).filter A := by
    intro d hd
    obtain ⟨hlt, ha⟩ := hsmall d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ha⟩
  have hcount : 58 < Nat.count A n := by
    rw [Nat.count_eq_card_filter_range]
    exact lt_of_lt_of_le (show 58 < small.card by decide) (Finset.card_le_card hsub)
  have heven := hall (Nat.count A n) hcount
  rw [a, Nat.nth_count hn] at heven
  exact (by decide : ¬Even n) heven
