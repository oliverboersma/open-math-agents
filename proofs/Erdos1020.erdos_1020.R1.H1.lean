import OMAReductions.R_Erdos1020_erdos_1020_R1
import Mathlib

-- Step Erdos1020.erdos_1020.R1.H1: hypothesis H1 of reduction Erdos1020.erdos_1020.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The two classical constructions. All `r`-subsets of a fixed set of `r * k - 1` vertices
contain no `k` disjoint edges, since those would cover `r * k` vertices. All `r`-subsets
meeting a fixed set `T` of `k - 1` vertices contain no `k` disjoint edges either: the traces
of disjoint edges on `T` are disjoint and nonempty, so there are at most `k - 1` of them.
Both families are admissible in the extremal number `f n r k`. -/


namespace P4E1020

open Finset Erdos1020

theorem le_f {n r k : ℕ} (H : Finset (Finset (Fin n)))
    (hH : H ⊆ (univ : Finset (Fin n)).powersetCard r)
    (hM : ¬ H.HasHypergraphMatching k) : H.card ≤ f n r k := by
  unfold f Hypergraph.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))]
  exact ⟨mem_powerset.mpr hH, hM⟩

theorem part1 (n r k : ℕ) (hr : 1 ≤ r) (hk : 0 < k) (hn : r * k - 1 ≤ n) :
    (r * k - 1).choose r ≤ f n r k := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (n := r * k - 1) (by simpa using hn)
  have h := le_f (k := k) (S.powersetCard r) (powersetCard_mono (subset_univ S)) ?_
  · rwa [card_powersetCard, hS] at h
  · rintro ⟨M, hMH, hMc, hMd⟩
    have hsub : M.biUnion id ⊆ S := by
      intro x hx
      obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
      exact (mem_powersetCard.mp (hMH he)).1 hxe
    have hcard : (M.biUnion id).card = ∑ e ∈ M, e.card :=
      card_biUnion (fun x hx y hy hxy => hMd hx hy hxy)
    have hsum : ∑ e ∈ M, e.card = k * r := by
      rw [sum_congr rfl (fun e he => (mem_powersetCard.mp (hMH he)).2), sum_const, hMc,
        smul_eq_mul]
    have h1 := card_le_card hsub
    rw [hcard, hsum, hS] at h1
    have h2 : 1 ≤ r * k := Nat.mul_pos hr hk
    rw [mul_comm] at h1
    omega

theorem part2 (n r k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    n.choose r - (n - k + 1).choose r ≤ f n r k := by
  classical
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (n := k - 1) (by simp; omega)
  have hsub : (Tᶜ).powersetCard r ⊆ (univ : Finset (Fin n)).powersetCard r :=
    powersetCard_mono (subset_univ _)
  have h := le_f (k := k) ((univ : Finset (Fin n)).powersetCard r \ (Tᶜ).powersetCard r)
    sdiff_subset ?_
  · rw [card_sdiff_of_subset hsub, card_powersetCard, card_powersetCard, card_univ,
      Fintype.card_fin, card_compl, Fintype.card_fin, hT] at h
    have e : n - (k - 1) = n - k + 1 := by omega
    rwa [e] at h
  · rintro ⟨M, hMH, hMc, hMd⟩
    have hsub2 : M.biUnion (fun e => e ∩ T) ⊆ T := by
      intro x hx
      obtain ⟨e, -, hxe⟩ := mem_biUnion.mp hx
      exact (mem_inter.mp hxe).2
    have hcard : (M.biUnion (fun e => e ∩ T)).card = ∑ e ∈ M, (e ∩ T).card :=
      card_biUnion (fun x hx y hy hxy =>
        (hMd hx hy hxy).mono inter_subset_left inter_subset_left)
    have hge : ∀ e ∈ M, 1 ≤ (e ∩ T).card := by
      intro e he
      have h1 := hMH he
      rw [mem_sdiff, mem_powersetCard, mem_powersetCard] at h1
      have hne : ¬ e ⊆ Tᶜ := fun hs => h1.2 ⟨hs, h1.1.2⟩
      obtain ⟨x, hxe, hxT⟩ := not_subset.mp hne
      have hx : x ∈ T := by simpa using hxT
      exact card_pos.mpr ⟨x, mem_inter.mpr ⟨hxe, hx⟩⟩
    have hsum : k ≤ ∑ e ∈ M, (e ∩ T).card := by
      calc k = ∑ e ∈ M, 1 := by simp [hMc]
        _ ≤ _ := sum_le_sum hge
    have h3 := card_le_card hsub2
    rw [hcard, hT] at h3
    omega

end P4E1020

open P4E1020 in
theorem OMA.solution : OMA.R_Erdos1020_erdos_1020_R1.H1 := by
  intro r hr n k hk hn
  have hkr : 3 * k ≤ r * k := Nat.mul_le_mul_right k hr
  exact max_le (part1 n r k (by omega) hk hn) (part2 n r k hk (by omega))
