import OMAReductions.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1
import Mathlib

-- Step ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point.R1.H2: hypothesis H2 of reduction ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point.R1
-- Credit: @ivillar (original proof).
-- Strategy. Diagonal argument: otherwise pick H_j >= j and strictly increasing N_j >= H_j with
-- g H_j N_j >= eps; the step function H(N) = H_j for the largest j with N_j <= N tends to infinity,
-- satisfies H N <= N, and g (H N_j) N_j >= eps, contradicting the hypothesis.

open Filter Topology in
theorem OMA.solution :
    OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1.H2 := by
  intro g hg ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have h1 : ∀ A : ℕ, ∃ H ≥ A, ∀ B : ℕ, ∃ N ≥ B, ε ≤ g H N := by
    intro A
    obtain ⟨H, hHA, hH⟩ := (Filter.frequently_atTop.mp hcon) A
    refine ⟨H, hHA, fun B => ?_⟩
    rw [Filter.not_eventually] at hH
    obtain ⟨N, hNB, hN⟩ := (Filter.frequently_atTop.mp hH) B
    exact ⟨N, hNB, not_lt.mp hN⟩
  choose a ha hN using h1
  choose n hnB hnε using hN
  let Ns : ℕ → ℕ := fun j => Nat.rec (motive := fun _ => ℕ) (n 0 (a 0)) (fun j Nj => n (j + 1) (max (Nj + 1) (a (j + 1)))) j
  have hNsS : ∀ j, Ns (j + 1) = n (j + 1) (max (Ns j + 1) (a (j + 1))) := fun j => rfl
  have hmono : StrictMono Ns := strictMono_nat_of_lt_succ (fun j => by
    rw [hNsS]
    have := hnB (j + 1) (max (Ns j + 1) (a (j + 1)))
    omega)
  have haN : ∀ j, a j ≤ Ns j := by
    intro j
    cases j with
    | zero => exact hnB 0 (a 0)
    | succ j =>
      rw [hNsS]
      have := hnB (j + 1) (max (Ns j + 1) (a (j + 1)))
      omega
  have hgN : ∀ j, ε ≤ g (a j) (Ns j) := by
    intro j
    cases j with
    | zero => exact hnε 0 (a 0)
    | succ j =>
      rw [hNsS]
      exact hnε _ _
  have hjle : ∀ j, j ≤ Ns j := hmono.id_le
  let J : ℕ → ℕ := fun N : ℕ => @Nat.findGreatest (fun j : ℕ => Ns j ≤ N) (fun j => Nat.decLe (Ns j) N) N
  have hJge : ∀ j N : ℕ, Ns j ≤ N → j ≤ J N := fun j N h =>
    @Nat.le_findGreatest j (fun i : ℕ => Ns i ≤ N) (fun i => Nat.decLe (Ns i) N) N ((hjle j).trans h) h
  have hJspec : ∀ N : ℕ, Ns 0 ≤ N → Ns (J N) ≤ N := by
    intro N h
    exact @Nat.findGreatest_spec 0 (fun j : ℕ => Ns j ≤ N) (fun j => Nat.decLe (Ns j) N) N
      (Nat.zero_le N) h
  have hJeq : ∀ j, J (Ns j) = j := by
    intro j
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have h2 := hJspec (Ns j) (hmono.monotone (Nat.zero_le j))
      have h3 := hmono hlt
      omega
    · exact hJge j (Ns j) le_rfl
  have hHt : Tendsto (fun N => a (J N)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨Ns b, fun N hN => le_trans (hJge b N hN) (ha (J N))⟩
  have hHle : ∀ᶠ N in atTop, a (J N) ≤ N := by
    filter_upwards [eventually_ge_atTop (Ns 0)] with N hN
    exact (haN (J N)).trans (hJspec N hN)
  have hT := hg (fun N => a (J N)) hHt hHle
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  have h4 : g (a (J (Ns M))) (Ns M) < ε := hM (Ns M) (hjle M)
  rw [hJeq] at h4
  exact absurd (hgN M) (not_le.mpr h4)
