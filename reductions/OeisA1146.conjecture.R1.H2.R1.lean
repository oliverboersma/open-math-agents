import OMAReductions.R_OeisA1146_conjecture_R1

/-!
# Semiprime predecessors in Hasler's congruence

If k−1 = pq with p and q prime, q must divide 2^(p+1)−1: the local order
divides gcd(pq+1,q−1), which divides p+1. Factoring these explicit Mersenne
numbers and testing an obstruction for every remaining prime gives a
complete classification when one factor is at most 61.

The residual hypothesis excludes all these pairs. Lean proof by @Deldor14.
-/

namespace OMA.R_OeisA1146_conjecture_R1_H2_R1

open OMA.Hasler

/-- A prime-power predecessor forces k = 4. -/
theorem prime_power_pred {q t k : ℕ} (hq : q.Prime) (ht : 0 < t)
    (heq : k = q^t+1) (pass : k^4-1 ∣ 2^k-1) : k = 4 := by
  have hpow := pow_pos hq.pos t
  have hk : 1 < k := by omega
  have hd : q ∣ k-1 := by simpa [heq] using dvd_pow_self q ht.ne'
  have hf : k-1 ∣ k^4-1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow k 1 4
  have hlocal :=  (localIff hk).mp pass q 1 hq (by simpa using hd.trans hf)
  simp only [pow_one] at hlocal
  let g := k.gcd (q-1)
  have h₁ : g ∣ k := Nat.gcd_dvd_left _ _
  have h₂ : g ∣ q^t-1 := (Nat.gcd_dvd_right k (q-1)).trans (by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 t)
  have g2 := Nat.dvd_sub h₁ h₂
  rw [show k-(q^t-1) = 2 by omega] at g2
  have q3 : q ∣ 3 := hlocal.trans ((mersenneIff g 2).mpr g2)
  have eq3 := ((Nat.dvd_prime Nat.prime_three).mp q3).resolve_left hq.ne_one
  subst q
  by_cases h : t = 1
  · simpa [h] using heq
  · have t2 : 2 ≤ t := by omega
    have ds : 3^2 ∣ k-1 := by
      rw [heq, Nat.add_sub_cancel]
      exact pow_dvd_pow 3 t2
    exact False.elim (excludeSquares hk pass Nat.prime_three (by decide) (ds.trans hf))

/-- Only 16 can pass Hasler's divisibility test with a semiprime predecessor
having at least one prime factor at most 61. -/
def H1 : Prop := ∀ p q : ℕ, p.Prime → p ≤ 61 → q.Prime →
  (p*q+1)^4-1 ∣ 2^(p*q+1)-1 → p*q+1 = 16

/-- A local obstruction for mixed witnesses after excluding those predecessors. -/
def H2 : Prop :=
  ∀ e u : ℕ, 2 ≤ e → 1 < u → Odd u →
    let k := 2^e*u
    (∀ q : ℕ, q.Prime → q<1093 → ¬q^2 ∣ k^4-1) →
    (3∣k ∨ ∀ p ∈ ([7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199] : List ℕ),
      ¬p ∣ k^4-1) →
    (∀ q t : ℕ, q.Prime → 0 < t → k ≠ q^t+1) →
    (∀ p q : ℕ, p.Prime → p ≤ 61 → q.Prime → k ≠ p*q+1) →
    ∃ p j : ℕ, p.Prime ∧ 0<j ∧ p^j ∣ k^4-1 ∧ ¬p^j ∣ 2^(k.gcd (p-1))-1

theorem main : H1 → H2 → OMA.R_OeisA1146_conjecture_R1.H2 := by
  intro classify residual e u he hu odd
  dsimp only
  intro hs hc
  let k := 2^e*u
  have hk : 1 < k := by
    have hpow : 1 ≤ 2^e := Nat.one_le_two_pow
    dsimp [k]
    nlinarith
  by_contra! all
  have pass : k^4-1 ∣ 2^k-1 := (localIff hk).mpr (by
    intro p j hp hd
    cases j with
    | zero => simp
    | succ j => exact all p (j+1) hp (by omega) hd)
  have notSixteen : k ≠ 16 := by
    intro eq
    have ud : u ∣ 16 := eq ▸ (dvd_mul_left u (2^e) : u ∣ k)
    have hc16 : u.Coprime 16 := odd.coprime_two_right.pow_right 4
    change u.gcd 16 = 1 at hc16
    rw [Nat.gcd_eq_left ud] at hc16
    omega
  have excluded : ∀ p q : ℕ, p.Prime → p ≤ 61 → q.Prime → k ≠ p*q+1 := by
    intro p q hp hsmall hq heq
    apply notSixteen
    rw [heq] at pass ⊢
    exact classify p q hp hsmall hq pass
  have hMixed : 4 < k := by
    have h4 : 4 ≤ 2^e := (show 2^2 ≤ 2^e from Nat.pow_le_pow_right (by decide) he)
    dsimp [k]
    nlinarith
  have noPower : ∀ q t : ℕ, q.Prime → 0 < t → k ≠ q^t+1 := by
    intro q t hq ht eq
    have onlyFour := prime_power_pred hq ht eq pass
    omega
  obtain ⟨p,j,hp,hj,hd,hfail⟩ := residual e u he hu (by exact odd) hs hc noPower excluded
  exact hfail (all p j hp hj hd)

end OMA.R_OeisA1146_conjecture_R1_H2_R1
