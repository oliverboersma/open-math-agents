import OMAStatements.S_oeis_a226224
import Mathlib

-- Problem: A226224: The largest value of k in base n for which the sum of digits of k = sqrt(k).
-- Upstream: formal-conjectures statements/oeis-a226224.lean:0 (declaration OMA.S_oeis_a226224.main)
-- Credit: @eskrishnaram-ai (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private theorem sum_le_length_of_le_one :
    ∀ L : List ℕ, (∀ d ∈ L, d ≤ 1) → L.sum ≤ L.length
  | [], _ => Nat.le_refl 0
  | d :: ds, h => by
    have hd : d ≤ 1 := h d List.mem_cons_self
    have hds : ds.sum ≤ ds.length :=
      sum_le_length_of_le_one ds (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [List.sum_cons, List.length_cons]
    omega

private theorem two_mul_sq_lt_two_pow : ∀ n : ℕ, 7 ≤ n → 2 * n ^ 2 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hk2 : 7 * k ≤ k * k := Nat.mul_le_mul_right k hk
    have h1 : 4 * k + 2 < 2 * (k * k) := by omega
    have h2 : 2 * (k + 1) ^ 2 = 2 * (k * k) + (4 * k + 2) := by ring
    have h3 : 2 * (2 * k ^ 2) = 2 * (k * k) + 2 * (k * k) := by ring
    have hsq : 2 * (k + 1) ^ 2 < 2 * (2 * k ^ 2) := by omega
    have htwice : 2 * (2 * k ^ 2) < 2 * 2 ^ k :=
      Nat.mul_lt_mul_of_pos_left ih Nat.two_pos
    have hexp : 2 * 2 ^ k = 2 ^ (k + 1) := by
      rw [Nat.pow_succ 2 k, Nat.mul_comm]
    calc
      2 * (k + 1) ^ 2 < 2 * (2 * k ^ 2) := hsq
      _ < 2 * 2 ^ k := htwice
      _ = 2 ^ (k + 1) := hexp

private theorem binary_sq_sum_eq_self (r : ℕ) (hr : 0 < r)
    (hsum : (Nat.digits 2 (r ^ 2)).sum = r) : r = 1 := by
  have hle : r ≤ (Nat.digits 2 (r ^ 2)).length := by
    calc
      r = (Nat.digits 2 (r ^ 2)).sum := hsum.symm
      _ ≤ (Nat.digits 2 (r ^ 2)).length :=
        sum_le_length_of_le_one (Nat.digits 2 (r ^ 2)) fun d hd => by
          have hlt := Nat.digits_lt_base (by decide : 1 < 2) hd
          omega
  have hr2 : r ^ 2 ≠ 0 := by
    have : 0 < r ^ 2 := Nat.pow_pos hr
    omega
  have hpow : 2 ^ r ≤ 2 * r ^ 2 := by
    have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have h2 := Nat.base_pow_length_digits_le 2 (r ^ 2) (by decide) hr2
    omega
  have hr7 : r < 7 := by
    by_contra hge
    have hge7 : 7 ≤ r := by omega
    have hlt := two_mul_sq_lt_two_pow r hge7
    omega
  rcases show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 by omega with
    rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hsum (by decide)
  · exact absurd hsum (by decide)
  · exact absurd hsum (by decide)
  · exact absurd hsum (by decide)
  · exact absurd hsum (by decide)

theorem OMA.solution : type_of% @OMA.S_oeis_a226224.main := by
  intro b hb
  constructor
  · intro h
    by_contra hb2
    obtain ⟨c, rfl⟩ : ∃ c : ℕ, b = c + 3 := ⟨b - 3, by omega⟩
    have hmem : (c + 2) ^ 2 ∈ OMA.S_oeis_a226224.solutions (c + 3) := by
      simp only [OMA.S_oeis_a226224.solutions, Set.mem_ofPred_eq]
      refine ⟨Nat.pow_pos (by omega), c + 2, rfl, ?_⟩
      have hdigits : Nat.digits (c + 3) ((c + 2) ^ 2) = [1, c + 1] := by
        rw [show (c + 2) ^ 2 = 1 + (c + 3) * (c + 1) by ring]
        rw [Nat.digits_add (c + 3) (by omega) 1 (c + 1) (by omega) (Or.inl (by decide))]
        rw [Nat.digits_of_lt (c + 3) (c + 1) (by omega) (by omega)]
      rw [hdigits]
      simp only [List.sum_cons, List.sum_nil]
      omega
    have hle : (c + 2) ^ 2 ≤ 1 := h.2 hmem
    have hge : 4 ≤ (c + 2) ^ 2 := by
      rw [show (c + 2) ^ 2 = c * c + 4 * c + 4 by ring]
      omega
    omega
  · rintro rfl
    refine ⟨?_, ?_⟩
    · simp only [OMA.S_oeis_a226224.solutions, Set.mem_ofPred_eq]
      refine ⟨by decide, 1, by norm_num, ?_⟩
      rw [Nat.digits_of_lt 2 1 (by decide) (by decide)]
      simp only [List.sum_cons, List.sum_nil, add_zero]
    · intro k hk
      simp only [OMA.S_oeis_a226224.solutions, Set.mem_ofPred_eq] at hk
      rcases hk with ⟨hk_pos, r, rfl, hsum⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · norm_num at hk_pos
      · have hr1 := binary_sq_sum_eq_self r hr_pos hsum
        rw [hr1]
        norm_num
