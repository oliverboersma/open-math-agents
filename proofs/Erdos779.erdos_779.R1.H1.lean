import OMAReductions.R_Erdos779_erdos_779_R1
import Mathlib

-- Step Erdos779.erdos_779.R1.H1: hypothesis H1 of reduction Erdos779.erdos_779.R1
-- Credit: @ivillar. The offset q - P has no prime factor among the first n + 1 primes and is below
-- the square of the next prime, so it is prime; Bertrand's postulate gives p_(n+1)^2 <= P for n >= 3.

/-! Short primes above the primorial yield Deaconescu's prime pair. -/

open Finset Nat

namespace P7E779H1


lemma nthp {k p : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) : nth Nat.Prime k = p :=
  hc ▸ Nat.nth_count hp

lemma c0 : nth Nat.Prime 0 = 2 := nthp (by norm_num) (by decide)
lemma c1 : nth Nat.Prime 1 = 3 := nthp (by norm_num) (by decide)
lemma c2 : nth Nat.Prime 2 = 5 := nthp (by norm_num) (by decide)
lemma c3 : nth Nat.Prime 3 = 7 := nthp (by norm_num) (by decide)
lemma c4 : nth Nat.Prime 4 = 11 := nthp (by norm_num) (by decide)

lemma mono : StrictMono (nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma idx (r : ℕ) (hr : r.Prime) : nth Nat.Prime (count Nat.Prime r) = r := Nat.nth_count hr

lemma succ_le_two_mul (k : ℕ) : nth Nat.Prime (k + 1) ≤ 2 * nth Nat.Prime k := by
  have hk := Nat.prime_nth_prime k
  obtain ⟨r, hr, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (nth Nat.Prime k) hk.ne_zero
  have hc : k < count Nat.Prime r := by
    by_contra h
    have := mono.monotone (not_lt.mp h)
    rw [idx r hr] at this
    omega
  calc nth Nat.Prime (k + 1) ≤ nth Nat.Prime (count Nat.Prime r) := mono.monotone hc
    _ = r := idx r hr
    _ ≤ _ := hle

lemma sq_le_prod (n : ℕ) (hn : 3 ≤ n) :
    nth Nat.Prime (n + 1) ^ 2 ≤ ∏ i ∈ range (n + 1), nth Nat.Prime i := by
  induction n, hn using Nat.le_induction with
  | base =>
    show nth Nat.Prime 4 ^ 2 ≤ ∏ i ∈ range 4, nth Nat.Prime i
    simp only [prod_range_succ, prod_range_zero, c0, c1, c2, c3, c4]
    norm_num
  | succ n hn ih =>
    rw [prod_range_succ]
    have h4 : 4 ≤ nth Nat.Prime (n + 1) := by
      have := mono.monotone (show 4 ≤ n + 1 by omega)
      rw [c4] at this
      omega
    have h2 := succ_le_two_mul (n + 1)
    calc nth Nat.Prime (n + 1 + 1) ^ 2 ≤ (2 * nth Nat.Prime (n + 1)) ^ 2 :=
          Nat.pow_le_pow_left h2 2
      _ = 4 * nth Nat.Prime (n + 1) * nth Nat.Prime (n + 1) := by ring
      _ ≤ nth Nat.Prime (n + 1) ^ 2 * nth Nat.Prime (n + 1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_right _ ih

lemma big_factor (n q : ℕ) (hq : q.Prime) (hPq : ∏ i ∈ range (n + 1), nth Nat.Prime i < q)
    (r : ℕ) (hr : r.Prime) (hrd : r ∣ q - ∏ i ∈ range (n + 1), nth Nat.Prime i) :
    nth Nat.Prime (n + 1) ≤ r := by
  have hc : n < count Nat.Prime r := by
    by_contra h
    have h := not_lt.mp h
    have hdvdP : r ∣ ∏ i ∈ range (n + 1), nth Nat.Prime i := by
      rw [← idx r hr]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
    have hdq : r ∣ q := by
      have : q = (q - ∏ i ∈ range (n + 1), nth Nat.Prime i) + ∏ i ∈ range (n + 1), nth Nat.Prime i := by
        omega
      rw [this]
      exact dvd_add hrd hdvdP
    have hrq := (Nat.prime_dvd_prime_iff_eq hr hq).mp hdq
    have hpos : 0 < ∏ i ∈ range (n + 1), nth Nat.Prime i :=
      Finset.prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)
    have := Nat.le_of_dvd hpos hdvdP
    omega
  calc nth Nat.Prime (n + 1) ≤ nth Nat.Prime (count Nat.Prime r) := mono.monotone hc
    _ = r := idx r hr

end P7E779H1

open P7E779H1

theorem OMA.solution : OMA.R_Erdos779_erdos_779_R1.H1 := by
  unfold OMA.R_Erdos779_erdos_779_R1.H1
  intro n hn
  dsimp only
  intro q hq hlo hhi
  have hbf := big_factor n q hq (by omega)
  have hprime : (q - ∏ i ∈ range (n + 1), nth Nat.Prime i).Prime := by
    by_contra hnp
    have hmf := Nat.minFac_sq_le_self (by omega) hnp
    have hge := hbf _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
    have := Nat.pow_le_pow_left hge 2
    omega
  refine ⟨_, hprime, ?_, ?_, ?_⟩
  · have : ∏ i ∈ range (n + 1), nth Nat.Prime i + (q - ∏ i ∈ range (n + 1), nth Nat.Prime i) = q := by
      omega
    rw [this]
    exact hq
  · have := hbf _ hprime dvd_rfl
    have := mono (show n < n + 1 by omega)
    omega
  · have := sq_le_prod n hn
    omega

