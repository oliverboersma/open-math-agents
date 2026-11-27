import FormalConjectures.ErdosProblems.«954»

open Erdos954

lemma OMA.rosenAux_succ_of_ne (k i : ℕ) (h : i ≠ k + 2) :
    rosenAux (k + 1) i = rosenAux k i := by
  show (if i = k + 2 then _ else rosenAux k i) = rosenAux k i
  rw [if_neg h]

lemma OMA.rosenAux_stable : ∀ k i : ℕ, i ≤ k + 1 → rosenAux k i = rosen i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl
    · rfl
    · show rosenAux 0 1 = rosenAux (0 + 1) 1
      rw [OMA.rosenAux_succ_of_ne 0 1 (by omega)]
  | succ k ih =>
    intro i hi
    by_cases h : i = k + 2
    · subst h
      show rosenAux (k + 1) (k + 2) = rosenAux (k + 1 + 1) (k + 2)
      rw [OMA.rosenAux_succ_of_ne (k + 1) (k + 2) (by omega)]
    · exact (OMA.rosenAux_succ_of_ne k i h).trans (ih i (by omega))

lemma OMA.rosen_add_two (k : ℕ) :
    rosen (k + 2) = sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} := by
  rw [← OMA.rosenAux_stable (k + 1) (k + 2) (by omega)]
  show (if k + 2 = k + 2 then _ else rosenAux k (k + 2)) = _
  rw [if_pos rfl]

-- The same pair persists when the index bound grows and all earlier terms are copied.
lemma OMA.pairCount_le {a b : ℕ → ℕ} {m m' : ℕ} (hm : m ≤ m')
    (eq : ∀ i, i ≤ m → a i = b i) (n : ℕ) : pairCount a m n ≤ pairCount b m' n := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  obtain ⟨⟨hi, hj⟩, horder, hpos, hsum⟩ := hp
  exact ⟨⟨by omega, by omega⟩, horder, hpos,
    by simpa only [eq p.1 (by omega), eq p.2 (by omega)] using hsum⟩

lemma OMA.le_pairCount (a : ℕ → ℕ) (x : ℕ) (h0 : a 0 = 0)
    (h : ∀ j, 1 ≤ j → j ≤ x → a j ≤ x) : x ≤ pairCount a x x := by
  unfold pairCount
  let f : ℕ ↪ ℕ × ℕ := ⟨fun j => (0, j), fun _ _ e => congrArg Prod.snd e⟩
  have included : (Finset.Icc 1 x).map f ⊆
      (Finset.range (x + 1) ×ˢ Finset.range (x + 1)).filter
        (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ a p.1 + a p.2 ≤ x) := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    change (0, j) ∈ _
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h0, Nat.zero_add]
    exact ⟨⟨by omega, by omega⟩, Nat.zero_le _, hj₁, h j hj₁ hj₂⟩
  simpa using Finset.card_le_card included

theorem OMA.solution : type_of% @Erdos954.erdos_954.variants.lower := by
  intro x
  change x ≤ pairCount rosen x x
  by_contra hlt
  have hx : pairCount rosen x x < x := Nat.lt_of_not_le hlt
  apply hlt
  apply OMA.le_pairCount rosen x rosen_zero
  intro j hj₁ hj₂
  by_cases hj : j = 1
  · simpa [hj, rosen_one] using hj₂
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    rw [OMA.rosen_add_two k]
    apply Nat.sInf_le
    exact lt_of_le_of_lt (OMA.pairCount_le (by omega : k + 1 ≤ x) (OMA.rosenAux_stable k) x) hx
