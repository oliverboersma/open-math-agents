import FormalConjectures.ErdosProblems.«890»

/-! A restricted Dickson prime-tuple criterion for Erdős–Selfridge 890(a).
Write n = (k!)² t. For 0 < i < k, factoring out i leaves the primitive
linear form ((k!)²/i)t+1. The zeroth form is t. The removed cofactors are
k-smooth, so simultaneous prime values give a block with at most k large
prime divisors counted with the multiplicity of the block sum.
H1 is an open sufficient prime-tuple hypothesis. H2 is its finite local
sieve condition. The case k=1 follows directly from infinitude of primes. -/
-- Credit: @marcusbuffett

namespace OMA.R_Erdos890_erdos_890_parts_a_R1
open Filter Finset Erdos890

/-- The finite-sieve-to-primes implication for this particular primitive family. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k →
  (∀ B : ℕ, ∃ t ≥ B, ∀ p : ℕ, p.Prime → p ≤ B →
    ¬ p ∣ t ∧ ∀ i : ℕ, 0 < i → i < k → ¬ p ∣ (k.factorial^2/i)*t+1) →
  ∀ M : ℕ, ∃ t ≥ M, t.Prime ∧ ∀ i : ℕ, 0 < i → i < k → ((k.factorial^2/i)*t+1).Prime

/-- Every finite list of prime divisors can be avoided by the entire packet
throughout a nonconstant arithmetic progression. -/
def H2 : Prop := ∀ k : ℕ, 2 ≤ k → ∀ B : ℕ, ∃ a d : ℕ, 0 < d ∧
  ∀ j p : ℕ, p.Prime → p ≤ B → ¬ p ∣ a+d*j ∧
    ∀ i : ℕ, 0 < i → i < k → ¬ p ∣ (k.factorial^2/i)*(a+d*j)+1

private lemma single {k b q : ℕ} (hq : q.Prime) (hb : ∀ p : ℕ, p.Prime → p ∣ b → p ≤ k) :
    omegaGt k (b*q) ≤ 1 := by
  unfold omegaGt
  apply (card_le_card (t := {q}) ?_).trans (by simp)
  intro p hp
  obtain ⟨hm, hlarge⟩ := mem_filter.mp hp
  obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hm
  rcases hprime.dvd_mul.mp hd with h | h
  · exact False.elim ((not_le_of_gt hlarge) (hb p hprime h))
  · exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hprime hq).mp h)

theorem main : H1 → H2 → type_of% @Erdos890.erdos_890.parts.a := by
  intro packet sieve k hk
  apply liminf_le_of_frequently_le'
  apply frequently_atTop.2
  intro M
  by_cases he : k = 1
  · subst k
    obtain ⟨p,hM,hp⟩ := Nat.exists_infinite_primes M
    refine ⟨p,hM,?_⟩
    have h := single (k:=1) (b:=1) hp (fun q hq hd => Nat.le_of_dvd (by decide) hd)
    simpa using (show (omegaGt 1 (1*p) : EReal) ≤ (1:ℕ) by exact_mod_cast h)
  have hk2 : 2 ≤ k := by omega
  obtain ⟨t,hM,ht,hforms⟩ := packet k hk2 (by
    intro B
    obtain ⟨a,d,hd,h⟩ := sieve k hk2 B
    exact ⟨a+d*B, (Nat.le_mul_of_pos_left B hd).trans (Nat.le_add_left _ _),h B⟩) M
  let L := k.factorial^2
  have hL : 0 < L := pow_pos (Nat.factorial_pos k) _
  refine ⟨L*t,hM.trans (Nat.le_mul_of_pos_left _ hL),?_⟩
  calc
    ∑ i ∈ range k, (omegaGt k (L*t+i) : EReal) ≤ ∑ _i ∈ range k, (1:EReal) := by
      apply sum_le_sum
      intro i hi
      suffices h : omegaGt k (L*t+i) ≤ 1 by exact_mod_cast h
      by_cases h0 : i=0
      · subst i
        rw [Nat.add_zero]
        exact single ht fun p hp hd => hp.dvd_factorial.mp (hp.dvd_of_dvd_pow hd)
      have hi' := mem_range.mp hi
      have hd : i ∣ L := (Nat.dvd_factorial (by omega) hi'.le).trans (dvd_pow_self _ (by decide : 2 ≠ 0))
      have heq : i*(L/i*t+1) = L*t+i := by rw [mul_add,←mul_assoc,Nat.mul_div_cancel' hd,mul_one]
      rw [←heq]
      exact single (hforms i (by omega) hi') fun p _ hp => (Nat.le_of_dvd (by omega) hp).trans hi'.le
    _ = (k : EReal) := by simp

end OMA.R_Erdos890_erdos_890_parts_a_R1
