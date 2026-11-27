import OMAStatements.S_oeis_a075997

namespace OMA.S_oeis_a075997

lemma emod_helper (x b c : ℤ) (h0 : 0 ≤ x) (h1 : x < b) : (x + b * c) % b = x := by
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

lemma f_eq (n k : ℕ) (hk : 0 < k) :
    f ((n : ℤ) + k) ((n : ℤ) - k) = 1 - ((n / k % 2 : ℕ) : ℤ) := by
  have hdm := Nat.div_add_mod n k
  have hu := Nat.mod_lt n hk
  set t := n / k
  set u := n % k
  have hn : (n : ℤ) = k * t + u := by exact_mod_cast hdm.symm
  have hK : (0 : ℤ) < k := by exact_mod_cast hk
  have hu' : (u : ℤ) < k := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := by positivity
  have habs : |((n : ℤ) + k) - ((n : ℤ) - k)| = 2 * k := by
    rw [show ((n : ℤ) + k) - ((n : ℤ) - k) = 2 * k by ring]
    exact abs_of_pos (by linarith)
  unfold f
  rw [habs]
  rcases Nat.even_or_odd t with ⟨j, hj⟩ | ⟨j, hj⟩
  · have ht : t % 2 = 0 := by omega
    have hjz : (t : ℤ) = 2 * j := by exact_mod_cast (by omega : t = 2 * j)
    rw [show (n : ℤ) + k + ((n : ℤ) - k) = 2 * u + (2 * k) * (2 * j) by rw [hn, hjz]; ring,
      show (n : ℤ) + k = (k + u) + (2 * k) * j by rw [hn, hjz]; ring,
      show (n : ℤ) - k = (k + u) + (2 * k) * (j - 1) by rw [hn, hjz]; ring,
      emod_helper _ _ _ (by linarith) (by linarith), emod_helper _ _ _ (by linarith) (by linarith),
      emod_helper _ _ _ (by linarith) (by linarith), ht]
    rw [if_pos (by intro h; linarith)]
    norm_num
  · have ht : t % 2 = 1 := by omega
    have hjz : (t : ℤ) = 2 * j + 1 := by exact_mod_cast hj
    rw [show (n : ℤ) + k + ((n : ℤ) - k) = 2 * u + (2 * k) * (2 * j + 1) by rw [hn, hjz]; ring,
      show (n : ℤ) + k = u + (2 * k) * (j + 1) by rw [hn, hjz]; ring,
      show (n : ℤ) - k = u + (2 * k) * j by rw [hn, hjz]; ring,
      emod_helper _ _ _ (by linarith) (by linarith), emod_helper _ _ _ (by linarith) (by linarith),
      emod_helper _ _ _ (by linarith) (by linarith), ht]
    rw [if_neg (by intro h; apply h; ring)]
    norm_num

lemma alt_sum (m : ℕ) : ∑ k ∈ Finset.Icc 1 m, ((-1 : ℤ) ^ k) = -((m % 2 : ℕ) : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rcases Nat.even_or_odd m with h | h
    · rw [(h.add_one).neg_one_pow]
      obtain ⟨i, rfl⟩ := h
      push_cast
      omega
    · rw [(h.add_one).neg_one_pow]
      obtain ⟨i, rfl⟩ := h
      push_cast
      omega

lemma full_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ k * ((n / k : ℕ) : ℤ) =
      -∑ j ∈ Finset.Icc 1 n, ((n / j % 2 : ℕ) : ℤ) := by
  have h1 : ∀ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ k * ((n / k : ℕ) : ℤ) =
      ∑ _j ∈ Finset.Icc 1 (n / k), (-1 : ℤ) ^ k := by
    intro k _
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 n) (s' := fun j => Finset.Icc 1 (n / j))]
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => alt_sum (n / j)
  · intro k j
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hj1, hj⟩
      have hkj : j * k ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hj
      refine ⟨⟨hk1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩, hj1, ?_⟩
      nlinarith
    · rintro ⟨⟨hk1, hk⟩, hj1, hjn⟩
      have hkj : k * j ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hk
      refine ⟨⟨hk1, ?_⟩, hj1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩
      nlinarith

end OMA.S_oeis_a075997

open OMA.S_oeis_a075997 in
theorem OMA.solution : type_of% @OMA.S_oeis_a075997.main := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  have hsplit : ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ k * ((n / k : ℕ) : ℤ) = -(n : ℤ) + a n := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (show 1 ≤ n from hn), Finset.sum_insert (by simp)]
    simp [a]
  have ha : a n = ∑ j ∈ Finset.Icc 1 n, (1 - ((n / j % 2 : ℕ) : ℤ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have := full_sum n
    rw [hsplit] at this
    rw [Nat.add_sub_cancel]
    linarith
  rw [ha]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega), Nat.div_self (by omega), Nat.add_sub_cancel]
  simp only [Nat.one_mod, Nat.cast_one, sub_self, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [f_eq (m + 1) k (by simp at hk; omega)]
