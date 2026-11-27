import FormalConjectures.ErdosProblems.«779»

/-!
A short prime above the primorial gives both primes in Deaconescu's conjecture.
The offset criterion is Theorem 17 of Čejchan, Křížek, and Somer,
[On Remarkable Properties of Primes Near Factorials and Primorials](https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.pdf).
The offset has no prime factor among the primes in the primorial. If it is
less than the square of the next prime and greater than one, it is prime.
Bertrand's postulate bounds the square of the next prime by the primorial
starting at the fourth prime.
-/

open Finset Nat

namespace OMA.R_Erdos779_erdos_779_R1

/-- Starting with the fourth prime, any suitable short prime yields the pair. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    let P := ∏ i ∈ range (n + 1), nth Nat.Prime i
    ∀ q : ℕ, q.Prime → P + 1 < q → q - P < (nth Nat.Prime (n + 1)) ^ 2 →
      ∃ p : ℕ, p.Prime ∧ (P + p).Prime ∧ nth Nat.Prime n < p ∧ p < P

/-- Verify the prime pair at the first ten indices of the formal statement. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 10 →
    let P := ∏ i ∈ range (n + 1), nth Nat.Prime i
    ∃ p : ℕ, p.Prime ∧ (P + p).Prime ∧ nth Nat.Prime n < p ∧ p < P

/-- The remaining sufficient estimate only requires one prime in a specified interval. -/
def H3 : Prop :=
  ∀ n : ℕ, 11 ≤ n →
    let P := ∏ i ∈ range (n + 1), nth Nat.Prime i
    ∃ q : ℕ, q.Prime ∧ P + 1 < q ∧ q - P < (nth Nat.Prime (n + 1)) ^ 2

section Proof

theorem main : H1 → H2 → H3 → type_of% @Erdos779.erdos_779 := by
  intro short small large n hn
  by_cases h : n ≤ 10
  · exact small n hn h
  · obtain ⟨q, hq, hlo, hhi⟩ := large n (by omega)
    exact short n (by omega) q hq hlo hhi

end Proof

end OMA.R_Erdos779_erdos_779_R1
