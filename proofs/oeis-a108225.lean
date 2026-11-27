import OMAStatements.S_oeis_a108225

theorem OMA.solution : type_of% @OMA.S_oeis_a108225.main := by
  have key : ∀ n : ℕ, OMA.S_oeis_a108225.a (n + 1) = OMA.S_oeis_a108225.b (n + 1) + 1 ∧
      OMA.S_oeis_a108225.a (n + 2) = OMA.S_oeis_a108225.b (n + 2) + 1 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      show (OMA.S_oeis_a108225.a (n + 2) + OMA.S_oeis_a108225.a (n + 1)) *
        (OMA.S_oeis_a108225.a (n + 2) - OMA.S_oeis_a108225.a (n + 1) + 1) / 2 =
        OMA.S_oeis_a108225.b (n + 2 + 1) + 1
      have hb2 : OMA.S_oeis_a108225.b (n + 2) = OMA.S_oeis_a108225.b (n + 1) * (OMA.S_oeis_a108225.b (n + 1) + 1) / 2 + 1 := rfl
      have hb3 : OMA.S_oeis_a108225.b (n + 2 + 1) = OMA.S_oeis_a108225.b (n + 2) * (OMA.S_oeis_a108225.b (n + 2) + 1) / 2 + 1 := rfl
      rw [h1, h2, hb3]
      generalize OMA.S_oeis_a108225.b (n + 1) = x at hb2 ⊢
      generalize OMA.S_oeis_a108225.b (n + 2) = y at hb2 hb3 ⊢
      obtain ⟨k, hk⟩ := Nat.even_mul_succ_self x
      have hk2 : x * (x + 1) / 2 = k := by omega
      rw [hk2] at hb2
      subst hb2
      obtain ⟨l, hl⟩ := Nat.even_mul_succ_self (k + 1)
      have hl2 : (k + 1) * (k + 1 + 1) / 2 = l := by omega
      rw [hl2]
      have hxk : x ≤ k + 1 := by nlinarith
      obtain ⟨d, hd⟩ : ∃ d, k + 1 + 1 - (x + 1) + 1 = d := ⟨_, rfl⟩
      have hd2 : x + d = k + 2 := by omega
      have : (k + 1 + 1 + (x + 1)) * d = 2 * (l + 1 + 1) := by nlinarith
      rw [hd, this]
      omega
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1
