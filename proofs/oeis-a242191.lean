import OMAStatements.S_oeis_a242191

theorem OMA_cnt (n k : ℕ) (hk : k ≤ 6) :
    (Finset.univ.filter (fun f : Fin n → Fin 6 => ∀ i, (f i : ℕ) < k)).card = k ^ n := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin n => Fin 6) (p := fun _ b => (b : ℕ) < k))]
  rw [Fintype.card_pi]
  have : Fintype.card {b : Fin 6 // (b : ℕ) < k} = k := by
    interval_cases k <;> decide
  simp [this]

theorem OMA_hi (n : ℕ) (f : Fin n → Fin 6) :
    OMA.S_oeis_a242191.highest f =
      ((Finset.range 6).filter (fun k => ¬ ∀ i, (f i : ℕ) < k)).card := by
  have hle : OMA.S_oeis_a242191.highest f ≤ 6 := by
    unfold OMA.S_oeis_a242191.highest
    apply Finset.sup_le
    intro i _
    have := (f i).2
    omega
  have : (Finset.range 6).filter (fun k => ¬ ∀ i, (f i : ℕ) < k) =
      (Finset.range 6).filter (fun k => k < OMA.S_oeis_a242191.highest f) := by
    apply Finset.filter_congr
    intro k _
    unfold OMA.S_oeis_a242191.highest
    constructor
    · intro h
      simp only [not_forall, not_lt] at h
      obtain ⟨i, hi⟩ := h
      exact lt_of_lt_of_le (by omega) (Finset.le_sup (f := fun i => (f i : ℕ) + 1) (Finset.mem_univ i))
    · intro h hall
      have : Finset.univ.sup (fun i => (f i : ℕ) + 1) ≤ k := by
        apply Finset.sup_le
        intro i _
        have := hall i
        omega
      omega
  rw [this]
  generalize OMA.S_oeis_a242191.highest f = h at hle ⊢
  interval_cases h <;> decide

theorem OMA.solution : type_of% @OMA.S_oeis_a242191.main := by
  intro n hn
  have h1 : OMA.S_oeis_a242191.a n =
      ∑ k ∈ Finset.range 6, (Finset.univ.filter (fun f : Fin n → Fin 6 => ¬ ∀ i, (f i : ℕ) < k)).card := by
    unfold OMA.S_oeis_a242191.a
    simp_rw [OMA_hi n, Finset.card_filter]
    rw [Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.range 6,
      (Finset.univ.filter (fun f : Fin n → Fin 6 => ¬ ∀ i, (f i : ℕ) < k)).card = 6 ^ n - k ^ n := by
    intro k hk
    have hk' : k ≤ 6 := by simp at hk; omega
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), OMA_cnt n k hk']
    simp
  rw [h1, Finset.sum_congr rfl h2]
  have hp : ∀ k ∈ Finset.range 6, k ^ n ≤ 6 ^ n := by
    intro k hk
    exact Nat.pow_le_pow_left (by simp at hk; omega) n
  have h0 : (0:ℕ) ^ n = 0 := zero_pow (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have a2 : 2 ^ n ≤ 6 ^ n := hp 2 (by simp)
  have a3 : 3 ^ n ≤ 6 ^ n := hp 3 (by simp)
  have a4 : 4 ^ n ≤ 6 ^ n := hp 4 (by simp)
  have a5 : 5 ^ n ≤ 6 ^ n := hp 5 (by simp)
  have a1 : 1 ≤ 6 ^ n := Nat.one_le_pow _ _ (by norm_num)
  rw [pow_succ]
  simp only [h0, one_pow, Nat.sub_zero]
  push_cast [Nat.cast_sub, a1, a2, a3, a4, a5]
  ring
