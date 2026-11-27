import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1
import Mathlib

/-! H2: if m + f m < B, the tuple for m sends each y-smooth d <= m with B < d y to a_d = d c in
(m, B) with c < y, which is y-smooth; distinct d give distinct a_d, contradicting the count.
H3: from the tuple for n, the entries at indices k, 2k, ..., mk divided by k form a tuple for m
in (m, m + (f n + 2n)/k). -/

open Finset Filter Real Erdos710

namespace OMA.P2b710H3

theorem f_mem (n : ℕ) : Erdos711.HasDivisibleDistinctTuple n n (f n) := by
  have h : {L : ℕ | Erdos711.HasDivisibleDistinctTuple n n L}.Nonempty :=
    ⟨n ^ 2 + 1, hasDivisibleDistinctTuple_sq n⟩
  exact Nat.sInf_mem h

theorem solH2 : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H2 := by
  unfold OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H2
  intro m y B h
  by_contra hlt
  have hlt' : m + f m < B := not_le.mp hlt
  obtain ⟨a, ha_inj, ha⟩ := f_mem m
  classical
  let g : ℕ → ℕ := fun d => if hd : 1 ≤ d ∧ d ≤ m then a ⟨d - 1, by omega⟩ else 0
  have hmaps : ∀ d ∈ (Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y),
      g d ∈ (Ioc m B).filter (· ∈ Nat.smoothNumbers y) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdm⟩, hsm, hBd⟩ := hd
    have hg : g d = a ⟨d - 1, by omega⟩ := by simp only [g]; rw [dif_pos ⟨hd1, hdm⟩]
    obtain ⟨h1, h2, h3⟩ := ha ⟨d - 1, by omega⟩
    simp only at h3
    rw [show d - 1 + 1 = d by omega] at h3
    rw [hg]
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨h1, by omega⟩, ?_⟩
    obtain ⟨c, hc⟩ := h3
    rw [hc]
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc; omega
      · exact h0
    have hcy : c < y := by
      by_contra hge
      have : d * y ≤ d * c := Nat.mul_le_mul_left d (not_lt.mp hge)
      omega
    exact Nat.mul_mem_smoothNumbers hsm (Nat.mem_smoothNumbers_of_lt hc0 hcy)
  have hinj : Set.InjOn g ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y) : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hd1 hd2
    simp only [g] at heq
    rw [dif_pos hd1.1, dif_pos hd2.1] at heq
    have := ha_inj heq
    simp only [Fin.mk.injEq] at this
    omega
  have := Finset.card_le_card_of_injOn g hmaps hinj
  omega

theorem solH3 : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H3 := by
  unfold OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H3
  intro n m k hm hk hkm
  obtain ⟨a, ha_inj, ha⟩ := f_mem n
  set L := (f n + 2 * n) / k with hL
  have hidx : ∀ j : Fin m, k * (j.val + 1) - 1 < n := by
    intro j
    have : k * (j.val + 1) ≤ k * m := Nat.mul_le_mul_left k (by omega)
    have : 1 ≤ k * (j.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  let idx : Fin m → Fin n := fun j => ⟨k * (j.val + 1) - 1, hidx j⟩
  have hdvd : ∀ j : Fin m, k * (j.val + 1) ∣ a (idx j) := by
    intro j
    have := (ha (idx j)).2.2
    simp only [idx] at this
    rwa [show k * (j.val + 1) - 1 + 1 = k * (j.val + 1) by
      have : 1 ≤ k * (j.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega] at this
  let b : Fin m → ℕ := fun j => a (idx j) / k
  have hkb : ∀ j, k * b j = a (idx j) := by
    intro j
    exact Nat.mul_div_cancel' ((Dvd.intro _ rfl).trans (hdvd j))
  have htuple : Erdos711.HasDivisibleDistinctTuple m m L := by
    refine ⟨b, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
    · intro j1 j2 hj
      have h1 : a (idx j1) = a (idx j2) := by rw [← hkb j1, ← hkb j2, hj]
      have h2 := ha_inj h1
      simp only [idx, Fin.mk.injEq] at h2
      apply Fin.ext
      have e1 : 1 ≤ k * (j1.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e2 : 1 ≤ k * (j2.val + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have : k * (j1.val + 1) = k * (j2.val + 1) := by omega
      have := Nat.eq_of_mul_eq_mul_left hk this
      omega
    · have h1 := (ha (idx j)).1
      have := hkb j
      by_contra hle
      have : k * b j ≤ k * m := Nat.mul_le_mul_left k (not_lt.mp hle)
      omega
    · have h2 := (ha (idx j)).2.1
      have := hkb j
      have hL1 : f n + 2 * n < k * L + k := by
        have := Nat.lt_mul_div_succ (f n + 2 * n) hk
        rw [hL]; linarith [this]
      have hkm1 : k ≤ k * m := Nat.le_mul_of_pos_right k hm
      by_contra hle
      have : k * (m + L) ≤ k * b j := Nat.mul_le_mul_left k (not_lt.mp hle)
      nlinarith
    · obtain ⟨t, ht⟩ := hdvd j
      refine ⟨t, ?_⟩
      have : k * b j = k * ((j.val + 1) * t) := by rw [hkb j, ht]; ring
      exact Nat.eq_of_mul_eq_mul_left hk this
  have hfm : f m ≤ L := f_le htuple
  calc k * f m ≤ k * L := Nat.mul_le_mul_left k hfm
    _ ≤ f n + 2 * n := Nat.mul_div_le (f n + 2 * n) k

end OMA.P2b710H3

theorem OMA.solution : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H3 := OMA.P2b710H3.solH3
