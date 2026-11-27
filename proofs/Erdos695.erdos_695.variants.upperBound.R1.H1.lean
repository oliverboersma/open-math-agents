import OMAReductions.R_Erdos695_erdos_695_variants_upperBound_R1
import Mathlib

-- Step Erdos695.erdos_695.variants.upperBound.R1.H1: hypothesis H1 of reduction Erdos695.erdos_695.variants.upperBound.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Compactness. The sequences bounded by cap form a compact subset of ℕ → ℕ (a product of
finite sets). For each N the bounded sequences that satisfy the conditions up to N form a closed,
nonempty and decreasing family, so their intersection is nonempty. -/

theorem OMA.solution : OMA.R_Erdos695_erdos_695_variants_upperBound_R1.H1 := by
  intro cap h
  let K : Set (ℕ → ℕ) := {q | ∀ k, q k ≤ cap k}
  have hKeq : K = Set.univ.pi (fun k => Set.Iic (cap k)) := by
    ext q; simp only [K, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Iic]
  have hK : IsCompact K := by
    rw [hKeq]; exact isCompact_univ_pi (fun k => (Set.finite_Iic (cap k)).isCompact)
  have hKc : IsClosed K := by
    rw [hKeq]; exact isClosed_set_pi (fun k _ => isClosed_discrete _)
  let t : ℕ → Set (ℕ → ℕ) := fun N => {q | (∀ k, q k ≤ cap k) ∧ (∀ k ≤ N, (q k).Prime) ∧
    ∀ k < N, q k < q (k + 1) ∧ q (k + 1) % q k = 1}
  have hclosed : ∀ N, IsClosed (t N) := by
    intro N
    have e : t N = K ∩ ((⋂ k, ⋂ (_ : k ≤ N), (fun q : ℕ → ℕ => q k) ⁻¹' {x : ℕ | x.Prime}) ∩
        (⋂ k, ⋂ (_ : k < N), (fun q : ℕ → ℕ => (q k, q (k + 1))) ⁻¹'
          {x : ℕ × ℕ | x.1 < x.2 ∧ x.2 % x.1 = 1})) := by
      ext q; simp [t, K]
    rw [e]
    refine hKc.inter (IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun _ => ?_)
      (isClosed_iInter fun k => isClosed_iInter fun _ => ?_))
    · exact IsClosed.preimage (continuous_apply k) (isClosed_discrete _)
    · exact IsClosed.preimage ((continuous_apply k).prodMk (continuous_apply (k + 1)))
        (isClosed_discrete _)
  have hmono : ∀ N, t (N + 1) ⊆ t N := by
    intro N q hq
    exact ⟨hq.1, fun k hk => hq.2.1 k (by omega), fun k hk => hq.2.2 k (by omega)⟩
  have hne : ∀ N, (t N).Nonempty := by
    intro N
    obtain ⟨q, h1, h2⟩ := h N
    refine ⟨fun k => if k ≤ N then q k else 0, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      split_ifs with hk
      · exact (h1 k hk).2
      · exact Nat.zero_le _
    · intro k hk
      dsimp only
      rw [if_pos hk]
      exact (h1 k hk).1
    · intro k hk
      dsimp only
      rw [if_pos (by omega), if_pos (by omega)]
      exact h2 k hk
  have ht0 : IsCompact (t 0) := hK.of_isClosed_subset (hclosed 0) (fun q hq => hq.1)
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hmono hne ht0
    hclosed
  rw [Set.mem_iInter] at hq
  have hstep : ∀ k, q k < q (k + 1) ∧ q (k + 1) % q k = 1 := fun k => (hq (k + 1)).2.2 k (by omega)
  exact ⟨q, strictMono_nat_of_lt_succ fun k => (hstep k).1, fun k => (hq k).2.1 k le_rfl,
    fun k => (hstep k).2, (hq 0).1⟩
