import OMAStatements.S_oeis_a393336

-- Problem: A393336, the sequence attains every integer.
-- Credit: @bnb9001

namespace OMA_A393336_Proof

open OMA.S_oeis_a393336

lemma weight_append (L₁ L₂ : List ℕ) (p : ℕ) :
    weight (L₁ ++ L₂) p = weight L₁ p + weight L₂ (p + L₁.length) := by
  induction L₁ generalizing p with
  | nil => simp [weight]
  | cons d L ih =>
    simp only [List.cons_append, weight, ih, List.length_cons]
    rw [show p + 1 + L.length = p + (L.length + 1) by ring]
    ring

def P (k : ℕ) : List ℕ := List.flatten (List.replicate k [0, 1])

def Q (k : ℕ) : List ℕ := List.flatten (List.replicate k [1, 0]) ++ [1, 0, 0, 1]

lemma weight_P (k p : ℕ) : weight (P k) p = k := by
  induction k generalizing p with
  | zero => simp [P, weight]
  | succ k ih =>
    unfold P at ih ⊢
    rw [List.replicate_succ, List.flatten_cons, weight_append, ih]
    simp [weight]
    ring

lemma weight_R (k p : ℕ) : weight (List.flatten (List.replicate k [1, 0])) p = -k := by
  induction k generalizing p with
  | zero => simp [weight]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, weight_append, ih]
    simp [weight]

lemma weight_Q (k p : ℕ) : weight (Q k) p = -k := by
  unfold Q
  rw [weight_append, weight_R]
  simp [weight]
  ring

lemma digits_ofDigits_eq (L : List ℕ) (h1 : ∀ l ∈ L, l < 2) (h2 : ∀ h : L ≠ [], L.getLast h ≠ 0)
    (hne : L ≠ []) : Nat.ofDigits 2 L ≠ 0 ∧ Nat.digits 2 (Nat.ofDigits 2 L) = L := by
  have hd := Nat.digits_ofDigits 2 (by norm_num) L h1 h2
  refine ⟨fun h0 => ?_, hd⟩
  rw [h0, Nat.digits_zero] at hd
  exact hne hd.symm

lemma P_digits (k : ℕ) : ∀ l ∈ P k, l < 2 := by
  intro l hl
  simp only [P, List.mem_flatten, List.mem_replicate] at hl
  obtain ⟨s, ⟨-, rfl⟩, hs⟩ := hl
  simp at hs
  omega

lemma Q_digits (k : ℕ) : ∀ l ∈ Q k, l < 2 := by
  intro l hl
  simp only [Q, List.mem_append, List.mem_flatten, List.mem_replicate] at hl
  rcases hl with ⟨s, ⟨-, rfl⟩, hs⟩ | hl
  · simp at hs; omega
  · simp at hl; omega

lemma P_last (k : ℕ) : ∀ h : P (k + 1) ≠ [], (P (k + 1)).getLast h ≠ 0 := by
  intro h
  have e : P (k + 1) = P k ++ [0, 1] := by
    unfold P
    rw [List.replicate_succ', List.flatten_append]
    simp
  simp [e]

lemma Q_last (k : ℕ) : ∀ h : Q k ≠ [], (Q k).getLast h ≠ 0 := by
  intro h
  simp [Q]

end OMA_A393336_Proof

open OMA_A393336_Proof OMA.S_oeis_a393336 in
theorem OMA.solution : type_of% @OMA.S_oeis_a393336.main := by
  intro z
  rcases lt_or_ge 0 z with hz | hz
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = (k + 1 : ℕ) := ⟨(z - 1).toNat, by omega⟩
    have hne : P (k + 1) ≠ [] := by
      unfold P; rw [List.replicate_succ, List.flatten_cons]; simp
    obtain ⟨h0, hd⟩ := digits_ofDigits_eq (P (k + 1)) (P_digits _) (P_last k) hne
    refine ⟨Nat.ofDigits 2 (P (k + 1)), ?_⟩
    unfold a
    rw [if_neg h0, hd, weight_P]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
    have hne : Q k ≠ [] := by simp [Q]
    obtain ⟨h0, hd⟩ := digits_ofDigits_eq (Q k) (Q_digits _) (Q_last k) hne
    refine ⟨Nat.ofDigits 2 (Q k), ?_⟩
    unfold a
    rw [if_neg h0, hd, weight_Q]
