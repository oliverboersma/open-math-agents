import OMAStatements.S_oeis_a164011

-- Problem: A164011: Zero together with row 11 of the array in A163280.
-- Upstream: formal-conjectures statements/oeis-a164011.lean:0 (declaration OMA.S_oeis_a164011.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a164011

open OMA.S_oeis_a164011

lemma of_lowerDiv (j k : ℕ) (hj : 0 < j) (h : lowerDiv j = k) : k ∣ j ∧ k * k ≤ j := by
  unfold lowerDiv at h
  have hne : ((Nat.divisors j).filter (fun d => d * d ≤ j)).Nonempty :=
    ⟨1, by simp only [Finset.mem_filter, Nat.mem_divisors]; omega⟩
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [hsup] at h
  simp only [id] at h
  subst h
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  exact ⟨hd.1.1, hd.2⟩

lemma lowerDiv_eq (k r : ℕ) (hk : 0 < k)
    (H : ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    lowerDiv (k * (k + r)) = k := by
  unfold lowerDiv
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hsq⟩ := hd
    by_contra hlt
    obtain ⟨s, rfl⟩ : ∃ s, d = k + s := ⟨d - k, by simp only [id] at hlt; omega⟩
    have hs : 1 ≤ s := by simp only [id] at hlt; omega
    have hineq : 2 * k * s + s * s ≤ k * r := by nlinarith
    have hsr : 2 * s < r := by
      by_contra hc
      have hc' : r ≤ 2 * s := by omega
      have := Nat.mul_le_mul_left k hc'
      nlinarith
    have key : (k + s) ∣ s * (r - s) := by
      obtain ⟨t, rfl⟩ : ∃ t, r = s + t := ⟨r - s, by omega⟩
      have e : (k + s) * (k + t) = k * (k + (s + t)) + s * t := by ring
      have h1 : (k + s) ∣ k * (k + (s + t)) + s * t := e ▸ dvd_mul_right _ _
      rw [show s + t - s = t by omega]
      exact (Nat.dvd_add_right hdvd).mp h1
    have hpos : 0 < s * (r - s) := Nat.mul_pos (by omega) (by omega)
    have h1 := Nat.le_of_dvd hpos key
    have h2 := H s hs hineq
    omega
  · apply Finset.le_sup (f := id)
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨dvd_mul_right _ _, ?_⟩, ?_⟩
    · positivity
    · nlinarith

lemma count_eq (k R : ℕ) (hk : 0 < k)
    (H : ∀ r < R + 1, ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    Nat.count (fun j => lowerDiv j = k) (k * (k + R)) = R := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range (k * (k + R))).filter (fun j => lowerDiv j = k) =
      (Finset.range R).image (fun r => k * (k + r)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hl⟩
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h
          simp [lowerDiv] at hl
          omega
        · exact h
      obtain ⟨hd, hkk⟩ := of_lowerDiv j k hj0 hl
      obtain ⟨m, rfl⟩ := hd
      have hm1 : k ≤ m := Nat.le_of_mul_le_mul_left hkk hk
      have hm2 : m < k + R := Nat.lt_of_mul_lt_mul_left hj
      exact ⟨m - k, by omega, by rw [show k + (m - k) = m by omega]⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left (by omega) hk, lowerDiv_eq k r hk (H r (by omega))⟩
  rw [hset, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have := Nat.eq_of_mul_eq_mul_left hk hxy
    omega

lemma T_eq (k R : ℕ) (hk : 0 < k)
    (H : ∀ r < R + 1, ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    T (R + 1) k = k * (k + R) := by
  have hc := count_eq k R hk H
  have hp : lowerDiv (k * (k + R)) = k := lowerDiv_eq k R hk (H R (by omega))
  have h := Nat.nth_count (p := fun j => lowerDiv j = k) hp
  rw [hc] at h
  unfold T
  rw [Nat.add_sub_cancel]
  exact h

lemma solve : ∀ n : ℕ, 20 < n → a n = n * (n + 10) := by
  intro n hn
  unfold a
  rw [if_neg (by omega)]
  apply T_eq n 10 (by omega)
  intro r hr s hs h
  have h2 : 2 * s < r := by
    by_contra hc
    have hc' : r ≤ 2 * s := by omega
    have := Nat.mul_le_mul_left n hc'
    nlinarith
  have hs' : s < 7 := by omega
  interval_cases r <;> interval_cases s <;> omega

end OMA.P_oeis_a164011

theorem OMA.solution : type_of% @OMA.S_oeis_a164011.main := OMA.P_oeis_a164011.solve
