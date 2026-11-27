import OMAStatements.S_oeis_a230044

namespace OMA.S_oeis_a230044




lemma two_T (m : ℕ) : 2 * T m = m * (m + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd

lemma step {k s m : ℕ} (h : k + s ^ 2 = T m) :
    k + (2 * m + 3 * s + 1) ^ 2 = T (3 * m + 4 * s + 1) := by
  have h1 := two_T m
  have h2 := two_T (3 * m + 4 * s + 1)
  have hid : (3 * m + 4 * s + 1) * (3 * m + 4 * s + 1 + 1) + 2 * s ^ 2 =
      m * (m + 1) + 2 * (2 * m + 3 * s + 1) ^ 2 := by ring
  nlinarith

lemma iterate {k s m : ℕ} (h : k + s ^ 2 = T m) (j : ℕ) :
    ∃ m' s', k + s' ^ 2 = T m' ∧ j ≤ s' := by
  induction j with
  | zero => exact ⟨m, s, h, Nat.zero_le _⟩
  | succ j ih =>
    obtain ⟨m', s', h', hj⟩ := ih
    exact ⟨3 * m' + 4 * s' + 1, 2 * m' + 3 * s' + 1, step h', by omega⟩

/-- The conjecture: the set A230044 is the set of values of A064784 (n >= 1). -/
theorem conjecture : {k | InA230044 k} = {k | ∃ n, 1 ≤ n ∧ A064784 n = k} := by
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, m, h⟩
    obtain ⟨m', s', h', hs⟩ := iterate h (k + 1)
    have hsq : Nat.sqrt (T m') = s' := by
      symm
      rw [Nat.eq_sqrt]
      constructor <;> nlinarith
    refine ⟨m', ?_, ?_⟩
    · by_contra h0
      have : m' = 0 := by omega
      subst this
      simp [T] at h'
      omega
    · rw [A064784, hsq, ← h']
      omega
  · rintro ⟨n, -, rfl⟩
    refine ⟨Nat.sqrt (T n), n, ?_⟩
    have := Nat.sqrt_le' (T n)
    rw [A064784]
    omega

/-- Control: the listed terms of A064784 start 0, 2, 2, 1, 6, 5, 3, 0, 9, 6. -/
example : (List.range 10).map (fun n => A064784 (n + 1)) = [0, 2, 2, 1, 6, 5, 3, 0, 9, 6] := by
  decide +kernel

end OMA.S_oeis_a230044

theorem OMA.solution : type_of% @OMA.S_oeis_a230044.main :=
  OMA.S_oeis_a230044.conjecture
