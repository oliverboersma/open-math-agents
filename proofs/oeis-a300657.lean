import OMAStatements.S_oeis_a300657
import Mathlib

namespace OMAA300657Helpers
open ArithmeticFunction

theorem sigma_prime_mod (p : ℕ) (hp : p.Prime) : sigma 1 p % p = 1 := by
  rw [sigma_one_apply, Nat.Prime.sum_divisors hp, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt hp.one_lt

theorem proper_sum_zero_iff (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.properDivisors, sigma 1 d % d) = 0 ↔ (n = 1 ∨ Nat.Prime n) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, hp⟩ := hc
    have hq : (Nat.minFac n).Prime := Nat.minFac_prime h1
    have hmem : Nat.minFac n ∈ n.properDivisors := by
      rw [Nat.mem_properDivisors]
      refine ⟨Nat.minFac_dvd n, ?_⟩
      exact lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun he => hp (he ▸ hq))
    have := Finset.single_le_sum (f := fun d => sigma 1 d % d) (fun _ _ => Nat.zero_le _) hmem
    rw [sigma_prime_mod _ hq] at this
    omega
  · rintro (h | h)
    · subst h; simp
    · rw [Nat.Prime.properDivisors h]; simp
end OMAA300657Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a300657.main := by
  intro n hn
  unfold OMA.S_oeis_a300657.a OMA.S_oeis_a300657.b
  rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons, ← OMAA300657Helpers.proper_sum_zero_iff n hn]
  omega
