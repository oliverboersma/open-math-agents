import OMAStatements.S_oeis_a360070
import Mathlib

-- Problem: oeis-a360070, a partition whose mean part equals its mean multiplicity forces
-- n to be non-squarefree.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- With k parts and d distinct parts the condition reads n / k = k / d, so n d = k^2.
-- If n is squarefree, n divides k; as k <= n this gives k = n, so every part is 1 and d = 1,
-- hence n = n^2 and n = 1, contradicting n > 1.

namespace A360070

lemma all_one (s : Multiset ℕ) (h1 : ∀ x ∈ s, 1 ≤ x) (h2 : s.sum = Multiset.card s) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction_on with
  | empty => intro x hx; simp at hx
  | cons a t ih =>
    have ha : 1 ≤ a := h1 a (Multiset.mem_cons_self a t)
    have ht1 : ∀ x ∈ t, 1 ≤ x := fun x hx => h1 x (Multiset.mem_cons_of_mem hx)
    have hle : Multiset.card t ≤ t.sum := by
      have h3 := Multiset.card_nsmul_le_sum (s := t) (a := 1) ht1
      simpa using h3
    rw [Multiset.sum_cons, Multiset.card_cons] at h2
    have hta : t.sum = Multiset.card t := by omega
    have ha1 : a = 1 := by omega
    intro x hx
    rcases Multiset.mem_cons.mp hx with h | h
    · rw [h, ha1]
    · exact ih ht1 hta x h

end A360070

theorem OMA.solution : type_of% @OMA.S_oeis_a360070.main := by
  intro n hn hex hsq
  obtain ⟨P, hP⟩ := hex
  unfold OMA.S_oeis_a360070.SameMeans at hP
  rw [Multiset.toFinset_sum_count_eq, P.parts_sum] at hP
  obtain ⟨k, hk⟩ : ∃ k, k = Multiset.card P.parts := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = P.parts.toFinset.card := ⟨_, rfl⟩
  rw [← hk, ← hd] at hP
  have hpos1 : ∀ x ∈ P.parts, 1 ≤ x := fun x hx => P.parts_pos hx
  have hkn : k ≤ n := by
    have h := Multiset.card_nsmul_le_sum (s := P.parts) (a := 1) hpos1
    rw [P.parts_sum] at h
    rw [hk]
    simpa using h
  have hk0 : 0 < k := by
    rw [hk, Multiset.card_pos]
    intro h0
    have h1 := P.parts_sum
    rw [h0, Multiset.sum_zero] at h1
    omega
  have hd0 : 0 < d := by
    rw [hk] at hk0
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hk0
    rw [hd]
    exact Finset.card_pos.mpr ⟨x, Multiset.mem_toFinset.mpr hx⟩
  have heq : n * d = k * k := by
    have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    rw [div_eq_div_iff hkq hdq] at hP
    exact_mod_cast hP
  have hdvd : n ∣ k := by
    have h1 : n ∣ k ^ 2 := ⟨d, by rw [sq, ← heq]⟩
    exact (Squarefree.dvd_pow_iff_dvd hsq two_ne_zero).mp h1
  have hkeq : k = n := le_antisymm hkn (Nat.le_of_dvd hk0 hdvd)
  have hall : ∀ x ∈ P.parts, x = 1 :=
    A360070.all_one P.parts hpos1 (by rw [P.parts_sum, ← hk, hkeq])
  have hd1 : d ≤ 1 := by
    rw [hd]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Multiset.mem_toFinset] at ha hb
    rw [hall a ha, hall b hb]
  have hd_one : d = 1 := by omega
  rw [hd_one, hkeq] at heq
  have h3 : n = 1 := (Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) heq).symm
  omega
