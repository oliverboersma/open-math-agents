import FormalConjectures.ErdosProblems.«1114»

-- Problem: Erdős Problem 1114 — rolle
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1114.lean:86 (declaration Erdos1114.erdos_1114.variants.rolle)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P4

open scoped Polynomial

theorem rolle_core {N : ℕ} {a d : ℝ} (hd : 0 < d) {f : Polynomial ℝ}
    (hdegree : f.natDegree = N + 1)
    (hroots : ∀ j : ℕ, j ≤ N → f.eval (a + d * j) = 0) :
    (∀ k : ℕ, k < N →
      ∃! x : ℝ, x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)) ∧ f.derivative.eval x = 0) ∧
    (∀ x : ℝ, f.derivative.eval x = 0 →
      ∃ k : ℕ, k < N ∧ x ∈ Set.Ioo (a + d * k) (a + d * (k + 1))) := by
  have hex : ∀ k : ℕ, ∃ x : ℝ, k < N →
      (x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)) ∧ f.derivative.eval x = 0) := by
    intro k
    by_cases hk : k < N
    · have hlt : a + d * k < a + d * (k + 1) := by
        have : d * ((k : ℝ) + 1) = d * k + d := by ring
        linarith
      have h0 : f.eval (a + d * k) = f.eval (a + d * (k + 1)) := by
        rw [hroots k hk.le]
        have h1 := hroots (k + 1) (Nat.succ_le_of_lt hk)
        push_cast at h1
        rw [h1]
      obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt
        (f.continuous.continuousOn) h0 (fun x _ => f.hasDerivAt x)
      exact ⟨c, fun _ => ⟨hc, hc0⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hex
  have hc_mem : ∀ k, k < N → c k ∈ Set.Ioo (a + d * k) (a + d * (k + 1)) :=
    fun k hk => (hc k hk).1
  have hc_zero : ∀ k, k < N → f.derivative.eval (c k) = 0 :=
    fun k hk => (hc k hk).2
  have hcast : ∀ j k : ℕ, j < k → a + d * ((j : ℝ) + 1) ≤ a + d * (k : ℝ) := by
    intro j k hjk
    have h1 : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjk
    have h2 := mul_le_mul_of_nonneg_left h1 hd.le
    linarith
  have hmono : StrictMonoOn c (↑(Finset.range N) : Set ℕ) := by
    intro i _ j hj hij
    have hjN := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    linarith [(hc_mem i (lt_trans hij hjN)).2, (hc_mem j hjN).1, hcast i j hij]
  have hcard : (Finset.image c (Finset.range N)).card = N := by
    rw [Finset.card_image_of_injOn hmono.injOn, Finset.card_range]
  have hf'0 : f.derivative ≠ 0 := by
    intro h
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
    omega
  have hdeg : f.derivative.natDegree ≤ N := by
    have := Polynomial.natDegree_derivative_le f
    omega
  have hkey : ∀ y : ℝ, f.derivative.eval y = 0 → ∃ j, j < N ∧ y = c j := by
    intro y hy
    by_contra hne
    push_neg at hne
    have hnot : y ∉ Finset.image c (Finset.range N) := by
      intro hmem
      obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hmem
      exact hne j (Finset.mem_range.mp hj) hjy.symm
    have hsub : (insert y (Finset.image c (Finset.range N))).val ⊆ f.derivative.roots := by
      intro z hz
      rw [Finset.mem_val, Finset.mem_insert] at hz
      rw [Polynomial.mem_roots hf'0]
      rcases hz with rfl | hz
      · exact hy
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        exact hc_zero j (Finset.mem_range.mp hj)
    have hcardins : (insert y (Finset.image c (Finset.range N))).card = N + 1 := by
      rw [Finset.card_insert_eq_ite, if_neg hnot, hcard]
    have := Polynomial.card_le_degree_of_subset_roots hsub
    omega
  refine ⟨fun k hk => ⟨c k, ⟨hc_mem k hk, hc_zero k hk⟩, ?_⟩, fun x hx => ?_⟩
  · rintro y ⟨hy, hy0⟩
    obtain ⟨j, hj, rfl⟩ := hkey y hy0
    rcases lt_trichotomy j k with h | h | h
    · exact False.elim (not_lt_of_ge ((hcast j k h).trans hy.1.le) (hc_mem j hj).2)
    · rw [h]
    · exact False.elim (not_lt_of_ge ((hcast k j h).trans (hc_mem j hj).1.le) hy.2)
  · obtain ⟨j, hj, rfl⟩ := hkey x hx
    exact ⟨j, hj, hc_mem j hj⟩

end OMA.P4

theorem OMA.solution : type_of% @Erdos1114.erdos_1114.variants.rolle := by
  exact OMA.P4.rolle_core
