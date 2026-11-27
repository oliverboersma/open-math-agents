import OMAStatements.S_oeis_a073759
import Mathlib

-- Problem: The largest unrelated number below a positive integer (OEIS A073759)
-- Upstream: formal-conjectures statements/oeis-a073759.lean:0 (declaration OMA.S_oeis_a073759.main)
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof. Let p be the least prime factor of n. A number n - j with 0 < j < p is coprime to n,
because a common prime factor would divide j < p. If n is prime the set is empty, so both sides
are 0. If n is composite, n - p is divisible by p, does not divide n (that would force n <= 2p,
against p^2 <= n and n >= 5), and is even (p = 2 forces n even; p odd forces n odd).
So the largest unrelated number is n - p = 2 * ((n - p) / 2).
-/

namespace OMA.A073759Proof
open OMA.S_oeis_a073759

/-- Below `n`, a number at distance less than the least prime factor is coprime to `n`. -/
theorem coprime_of_close (n m : ℕ) (hm : m < n) (hj : n - m < n.minFac) : m.Coprime n := by
  by_contra h
  obtain ⟨q, hq, hqm, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have h1 : q ∣ n - m := Nat.dvd_sub hqn hqm
  have h2 : n.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqn
  have h3 : q ≤ n - m := Nat.le_of_dvd (by omega) h1
  omega

theorem main_thm (n : ℕ) (hn : 5 ≤ n) : a n = 2 * halfGap n := by
  have hn1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn1
  set p := n.minFac with hpdef
  have hpn : p ∣ n := Nat.minFac_dvd n
  by_cases hprime : n.Prime
  · have hpe : p = n := hprime.minFac_eq
    have hhg : halfGap n = 0 := by
      unfold halfGap; rw [← hpdef, hpe]; simp
    rw [hhg]
    unfold a
    have : (Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ m.Coprime n) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro m hm
      rw [Finset.mem_Ico] at hm
      intro ⟨_, hc⟩
      exact hc (coprime_of_close n m hm.2 (by omega))
    rw [this]; simp
  · have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hprime
    have hp2 := hp.two_le
    have hpar : (n - p) % 2 = 0 := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · have : 2 ∣ n := h2 ▸ hpn
        omega
      · have hnodd : n % 2 = 1 := by
          by_contra hev
          have h2n : 2 ∣ n := by omega
          have := Nat.minFac_le_of_dvd (le_refl 2) h2n
          omega
        omega
    have hhg : 2 * halfGap n = n - p := by
      unfold halfGap; rw [← hpdef]; omega
    rw [hhg]
    unfold a
    apply le_antisymm
    · apply Finset.sup_le
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Ico] at hm
      obtain ⟨⟨_, hmn⟩, _, hc⟩ := hm
      by_contra hgt
      exact hc (coprime_of_close n m hmn (by simp only [id] at hgt; omega))
    · have hmem : n - p ∈ (Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ m.Coprime n) := by
        have hpp : p * p ≤ n := by nlinarith
        have hpp2 : 2 * p ≤ n := by nlinarith
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
        · intro hd
          have h1 : n - p ∣ n - (n - p) := Nat.dvd_sub hd (dvd_refl _)
          rw [show n - (n - p) = p by omega] at h1
          have h2 := Nat.le_of_dvd (by omega) h1
          have h3 : n ≤ 2 * p := by omega
          have h4 : p ≤ 2 := by nlinarith
          omega
        · intro hc
          have h1 : p ∣ n - p := Nat.dvd_sub hpn (dvd_refl p)
          have h2 : p ∣ Nat.gcd (n - p) n := Nat.dvd_gcd h1 hpn
          rw [hc] at h2
          exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
      exact Finset.le_sup (f := id) hmem

end OMA.A073759Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a073759.main :=
  fun n hn => OMA.A073759Proof.main_thm n hn
