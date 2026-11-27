import OMAReductions.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Dirichlet's theorem supplies primes avoiding every prescribed finite set of factors. -/

open Finset

theorem prime_avoiding_factors :
    ∀ B N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
      (∀ q : ℕ, q ≤ B → q.Prime → ¬ q ∣ 8 * p ^ 2 - 1) := by
  intro B N
  let Q := (range (B + 1)).filter fun q => q.Prime ∧ q ≠ 7
  let M := ∏ q ∈ Q, q
  have hM : 0 < M := prod_pos fun q hq => (mem_filter.mp hq).2.1.pos
  have primeSeven : (7 : ℕ).Prime := by decide
  have hcop : Nat.Coprime 7 M := Nat.Coprime.prod_right fun q hq =>
    (primeSeven.coprime_iff_not_dvd.mpr fun hd =>
      (mem_filter.mp hq).2.2
        (((Nat.dvd_prime (mem_filter.mp hq).2.1).mp hd).resolve_left (by decide)).symm)
  obtain ⟨a, ha7, haM⟩ := Nat.chineseRemainder hcop 2 1
  have ca7 : a.Coprime 7 := ha7.gcd_eq.trans (by decide)
  have caM : a.Coprime M := haM.gcd_eq.trans (by simp)
  obtain ⟨p, hpN, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (Nat.mul_pos (by decide) hM).ne'
      (ca7.mul_right caM)
  have p7 : p ≡ 2 [MOD 7] := (hpa.of_dvd (dvd_mul_right 7 M)).trans ha7
  have pM : p ≡ 1 [MOD M] := (hpa.of_dvd (dvd_mul_left M 7)).trans haM
  have hp1 : 1 ≤ 8 * p ^ 2 := by
    have hpos : 0 < 8 * p ^ 2 := Nat.mul_pos (by decide) (pow_pos hp.pos _)
    omega
  refine ⟨p, hpN.le, hp, ?_⟩
  intro q hq hqp hd
  by_cases he : q = 7
  · subst q
    have h : 8 * p ^ 2 - 1 ≡ 31 [MOD 7] :=
      ((p7.pow 2).mul_left 8).sub hp1 (by decide) (Nat.ModEq.refl 1)
    exact (by decide : ¬ (7 : ℕ) ∣ 31) ((h.dvd_iff (dvd_refl 7)).mp hd)
  · have hqQ : q ∈ Q := mem_filter.mpr ⟨mem_range.mpr (by omega), hqp, he⟩
    have pq : p ≡ 1 [MOD q] := pM.of_dvd (dvd_prod_of_mem id hqQ)
    have h : 8 * p ^ 2 - 1 ≡ 7 [MOD q] :=
      ((pq.pow 2).mul_left 8).sub hp1 (by decide) (Nat.ModEq.refl 1)
    exact he (((Nat.dvd_prime primeSeven).mp ((h.dvd_iff (dvd_refl q)).mp hd)).resolve_left
      hqp.ne_one)

theorem OMA.solution : OMA.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1.H1 := prime_avoiding_factors