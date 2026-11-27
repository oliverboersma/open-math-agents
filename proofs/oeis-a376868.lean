import OMAStatements.S_oeis_a376868

-- Problem: A376868: a(n) = n! * 4^binomial(n, 2).
-- Upstream: formal-conjectures statements/oeis-a376868.lean:0 (declaration OMA.S_oeis_a376868.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a376868

open OMA.S_oeis_a376868

lemma row_sum (n : ℕ) (c : Fin n) :
    ∑ r : Fin n → Fin 2, ∏ j, (if j = c then ((r j : Fin 2) : ℕ) else 1) = 2 ^ (n - 1) := by
  rw [← Fintype.prod_sum (fun j (x : Fin 2) => if j = c then (x : ℕ) else 1)]
  have h : ∀ j : Fin n, (∑ x : Fin 2, if j = c then (x : ℕ) else 1) = if j = c then 1 else 2 := by
    intro j
    split_ifs <;> simp [Fin.sum_univ_two]
  simp only [h]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' Finset.univ c, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin]

lemma fixed_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ M : Fin n → Fin n → Fin 2, ∏ i, ((M i (σ i) : Fin 2) : ℕ) = (2 ^ (n - 1)) ^ n := by
  have e : ∀ M : Fin n → Fin n → Fin 2, ∏ i, ((M i (σ i) : Fin 2) : ℕ) =
      ∏ i, ∏ j, (if j = σ i then ((M i j : Fin 2) : ℕ) else 1) := by
    intro M
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_ite_eq']
    simp
  simp only [e]
  rw [← Fintype.prod_sum (fun i (r : Fin n → Fin 2) =>
    ∏ j, (if j = σ i then ((r j : Fin 2) : ℕ) else 1))]
  simp only [row_sum]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma solve : ∀ n : ℕ,
    ∑ M : Matrix (Fin n) (Fin n) (Fin 2), (M.map (fun x => (x : ℕ))).permanent = a n := by
  intro n
  simp only [Matrix.permanent, Matrix.map_apply]
  rw [← Equiv.sum_comp Matrix.of]
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  have hs : ∀ σ : Equiv.Perm (Fin n),
      ∑ x : Fin n → Fin n → Fin 2, ∏ i, ((x (σ i) i : Fin 2) : ℕ) = (2 ^ (n - 1)) ^ n := by
    intro σ
    rw [← fixed_perm n σ, ← Equiv.sum_comp (Equiv.piComm (fun (_ : Fin n) (_ : Fin n) => Fin 2))]
    rfl
  simp only [hs]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
  unfold a
  congr 1
  rw [← pow_mul, Nat.choose_two_right, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  have h2 : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  rw [Nat.mul_div_cancel' h2, mul_comm]

end OMA.P_oeis_a376868

theorem OMA.solution : type_of% @OMA.S_oeis_a376868.main := OMA.P_oeis_a376868.solve
