import FormalConjectures.ErdosProblems.«913»

/-!
For any fixed cutoff, ask for prime inputs whose quadratic values avoid
prime factors up to that cutoff. A uniform bound for the least surviving
input would bring its quadratic value below the square of the cutoff.
-/

namespace OMA.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1

def H1 : Prop :=
  ∀ B N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
    (∀ q : ℕ, q ≤ B → q.Prime → ¬ q ∣ 8 * p ^ 2 - 1)

def H2 : Prop :=
  ∀ N : ℕ, ∃ B : ℕ,
    3 * sInf {p : ℕ | N ≤ p ∧ p.Prime ∧
      (∀ q : ℕ, q ≤ B → q.Prime → ¬ q ∣ 8 * p ^ 2 - 1)} ≤ B

section Proof

theorem main : H1 → H2 →
    type_of% @Erdos913.erdos_913.variants.infinite_many_8p_sq_add_one_primes := by
  intro hSieve hLeast
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨B, hB⟩ := hLeast (N + 1)
  let U : Set ℕ := {p | N + 1 ≤ p ∧ p.Prime ∧
    (∀ q : ℕ, q ≤ B → q.Prime → ¬ q ∣ 8 * p ^ 2 - 1)}
  have hU : U.Nonempty := hSieve B (N + 1)
  let p := sInf U
  obtain ⟨hpN, hp, hdiv⟩ := (Nat.sInf_mem hU : p ∈ U)
  have hpB : 3 * p ≤ B := hB
  let n := 8 * p ^ 2 - 1
  have hn2 : 2 ≤ n := by
    have h := hp.two_le
    dsimp [n]
    have hp2 : 4 ≤ p ^ 2 := Nat.pow_le_pow_left h 2
    omega
  have hnB : n ≤ B ^ 2 := calc
    n ≤ 8 * p ^ 2 := Nat.sub_le .. 
    _ ≤ (3 * p) ^ 2 := by nlinarith
    _ ≤ B ^ 2 := Nat.pow_le_pow_left hpB 2
  have hprime : n.Prime := by
    by_contra hbad
    have hfac : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hbad
    have hfacB : n.minFac ≤ B := by
      rw [← Nat.sqrt_eq' B, Nat.le_sqrt']
      exact hfac.trans hnB
    exact hdiv n.minFac hfacB (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
  exact ⟨p, ⟨hp, hprime⟩, by omega⟩

end Proof

end OMA.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1
