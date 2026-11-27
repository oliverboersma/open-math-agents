import OMAStatements.S_oeis_a140472

namespace OMA.P_a140472

open OMA.S_oeis_a140472

def g (n : ℕ) : ℕ := if n = 0 then 0 else (n + 2 ^ padicValNat 2 n) / 2

lemma g_odd (k : ℕ) : g (2 * k + 1) = k + 1 := by
  have h : padicValNat 2 (2 * k + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  simp only [g, h, pow_zero]
  rw [if_neg (by omega)]
  omega

lemma g_even (k : ℕ) (hk : 0 < k) : g (2 * k) = 2 * g k := by
  have h : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    ring
  simp only [g, h]
  rw [if_neg (by omega), if_neg (by omega), pow_succ]
  have : 0 < 2 ^ padicValNat 2 k := by positivity
  have hd : 2 ∣ k + 2 ^ padicValNat 2 k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have : padicValNat 2 k ≠ 0 := by
        intro h0
        have := (padicValNat.eq_zero_iff.mp h0)
        omega
      obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [he, pow_succ]; omega
    · have : padicValNat 2 k = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      rw [this]; omega
  omega

lemma g_pos (n : ℕ) (hn : 0 < n) : 0 < g n := by
  simp only [g, if_neg (by omega : n ≠ 0)]
  have : 0 < 2 ^ padicValNat 2 n := by positivity
  omega

lemma g_le (n : ℕ) : g n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [g]
      · rw [g_even k hk]; have := ih k (by omega); omega
    · rw [g_odd]; omega

lemma g_rec (n : ℕ) (hn : 2 ≤ n) : g n = g (n - g (n - 1)) + g (n / 2) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · -- n = 2k, n - 1 = 2(k-1)+1
    have hk : 0 < k := by omega
    have h1 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    rw [h1, g_odd, g_even k hk]
    have : 2 * k - (k - 1 + 1) = k := by omega
    rw [this, show 2 * k / 2 = k by omega]
    ring
  · -- n = 2k+1, k ≥ 1
    have hk : 0 < k := by omega
    rw [show 2 * k + 1 - 1 = 2 * k by omega, g_even k hk, show (2 * k + 1) / 2 = k by omega,
      g_odd]
    have hle := g_le k
    have hpos := g_pos k hk
    rw [show 2 * k + 1 - 2 * g k = 2 * (k - g k) + 1 by omega, g_odd]
    omega

lemma g_isA : IsA140472 g := by
  refine ⟨by simp [g], ?_, g_rec⟩
  simp [g]

lemma eq_g (f : ℕ → ℕ) (hf : IsA140472 f) : ∀ n, f n = g n := by
  obtain ⟨h0, h1, hr⟩ := hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [h0, g]
      · rw [h1]; simp [g]
    · rw [hr n h, g_rec n h, ih (n - 1) (by omega)]
      have hp := g_pos (n - 1) (by omega)
      rw [ih (n - g (n - 1)) (by omega), ih (n / 2) (by omega)]

theorem main : (∃ f : ℕ → ℕ, IsA140472 f) ∧
    ∀ f : ℕ → ℕ, IsA140472 f → ∀ n : ℕ, 0 < n → f n = (n + 2 ^ padicValNat 2 n) / 2 := by
  refine ⟨⟨g, g_isA⟩, fun f hf n hn => ?_⟩
  rw [eq_g f hf n, g, if_neg (by omega)]

end OMA.P_a140472

theorem OMA.solution : type_of% @OMA.S_oeis_a140472.main := OMA.P_a140472.main
