import OMAStatements.S_oeis_a394454
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open OMA.S_oeis_a394454

private lemma infinite_indices {p : ℕ} (hp : p.Prime) :
    {n : ℕ | 1 ≤ n ∧ p ∣ n.centralBinom}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  let n := p*(B+1)-1
  have hle := Nat.mul_le_mul_right (B+1) hp.two_le
  have hsucc : n+1 = p*(B+1) := by dsimp [n]; omega
  have hB : B < n := by omega
  have hd : p ∣ n+1 := hsucc ▸ Nat.dvd_mul_right _ _
  exact ⟨n, ⟨by omega, hd.trans (Nat.succ_dvd_centralBinom n)⟩, hB⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a394454.main := by
  refine ⟨fun _ hp => infinite_indices hp, ?_⟩
  intro B N
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B+1)
  obtain ⟨n, ⟨_, hdiv⟩, hn⟩ := (infinite_indices hp).exists_gt N
  have hmem := hp.mem_primeFactors hdiv (Nat.centralBinom_pos n).ne'
  have hsum : p ≤ a n := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem
  exact ⟨n, hn, by omega⟩
