import FormalConjectures.ErdosProblems.«1053»
import Mathlib

/-!
For k ≥ 3 a k-perfect integer has a repeated prime factor. If both k and
the integer are odd, all prime exponents are even. These restrictions
give three disjoint finiteness problems.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OMA.R_Erdos1053_erdos_1053_variants_guy_R1

/-- Even multiperfect numbers with a repeated prime factor. -/
def H1 : Prop :=
  ∀ k ≥ 3, {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Even n ∧ ¬ Squarefree n}.Finite

/-- Odd multiperfect numbers of even multiplicity. -/
def H2 : Prop :=
  ∀ k ≥ 3, Even k →
    {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ ¬ Squarefree n}.Finite

/-- Odd multiperfect numbers of odd multiplicity are squares. -/
def H3 : Prop :=
  ∀ k ≥ 3, Odd k →
    {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ IsSquare n}.Finite

section Proof

private theorem perfect_eq {n k : ℕ} (h : Nat.IsPerfectFor n 1 k) : σ 1 n = k*n := by
  simpa [Nat.IsPerfectFor] using h.2

private theorem squarefree_perfect_divides_six {n k : ℕ}
    (h : Nat.IsPerfectFor n 1 k) (hs : Squarefree n) : n ∣ 6 := by
  classical
  have hn : n ≠ 0 := h.1.ne'
  have hSigma : σ 1 n = ∏ p ∈ n.primeFactors, (p+1) := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
    apply prod_congr rfl
    intro p hp
    have hPrime := Nat.prime_of_mem_primeFactors hp
    have hDvd := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.factorization_eq_one_of_squarefree hs hPrime hDvd]
    simp [Finset.sum_range_succ,add_comm]
  suffices hSubset : n.primeFactors ⊆ (6:ℕ).primeFactors by
    have hh := (Nat.prod_primeFactors_dvd_iff (by decide : (6:ℕ) ≠ 0)).mpr hSubset
    rwa [Nat.prod_primeFactors_of_squarefree hs] at hh
  by_cases hEmpty : n.primeFactors = ∅
  · intro r hr
    rw [hEmpty] at hr
    exact (notMem_empty r hr).elim
  have hS : n.primeFactors.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
  let p := n.primeFactors.max' hS
  have hp : p ∈ n.primeFactors := max'_mem _ _
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpS : p ∣ σ 1 n := by
    rw [perfect_eq h]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _
  rw [hSigma] at hpS
  obtain ⟨q,hq,hD⟩ := (hpP.prime.dvd_finsetProd_iff (fun q => q+1)).mp hpS
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hqp : q ≤ p := le_max' _ _ hq
  obtain ⟨j,hj⟩ := hD
  have hjPos : 0 < j := by
    by_contra! hn
    simp [show j = 0 by omega] at hj
  have hStep : j = 1 := by
    by_contra hne
    have hTwo : 2*p ≤ p*j := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left p (show 2 ≤ j by omega)
    have := hpP.two_le
    omega
  have heq : q+1 = p := by simpa [hStep] using hj
  have hq2 : q = 2 := by
    apply hqP.even_iff.mp
    have hqle := hqP.two_le
    have hp2 : p ≠ 2 := by omega
    simpa [show p-1=q by omega] using hpP.even_sub_one hp2
  have hp3 : p = 3 := by omega
  intro r hr
  have hrp : r ≤ p := le_max' _ _ hr
  have hr2 := (Nat.prime_of_mem_primeFactors hr).two_le
  have hr' : r = 2 ∨ r = 3 := by omega
  rcases hr' with rfl|rfl
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,by decide,by decide⟩
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three,by decide,by decide⟩

theorem not_squarefree_of_three_perfect {n k : ℕ}
    (h : Nat.IsPerfectFor n 1 k) (hk : 3 ≤ k) : ¬ Squarefree n := by
  intro hs
  have hn : n ≤ 6 := Nat.le_of_dvd (by decide) (squarefree_perfect_divides_six h hs)
  have hFinite : ∀ t : Fin 7, σ 1 t.val ≤ 2*t.val := by decide +kernel
  have hLow := hFinite ⟨n,by omega⟩
  rw [perfect_eq h] at hLow
  have hTwo : 2*n < k*n := Nat.mul_lt_mul_of_pos_right (by omega) h.1
  exact (not_lt_of_ge hLow) hTwo

private theorem odd_prime_power_sum_mod_two {p : ℕ} (hp : p%2=1) :
    ∀ t : ℕ, (∑ i ∈ range t, p^i)%2 = t%2 := by
  have hPow (i : ℕ) : p^i%2=1 := by
    rw [Nat.pow_mod, hp, one_pow]
    decide
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, Nat.add_mod, hPow,ih]
    omega

theorem square_of_odd_perfect {n k : ℕ}
    (h : Nat.IsPerfectFor n 1 k) (hn : Odd n) (hk : Odd k) : IsSquare n := by
  classical
  have hSigOdd : Odd (σ 1 n) := (perfect_eq h).symm ▸ hk.mul hn
  have hSigma :
      σ 1 n = ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p+1), p^i := by
    simpa using sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) h.1.ne'
  have hExpo (p : ℕ) (hp : p ∈ n.primeFactors) : n.factorization p % 2 = 0 := by
    have hpOdd : p%2=1 := by
      have hpD := Nat.dvd_of_mem_primeFactors hp
      have hnn : ¬2 ∣ n := by obtain ⟨t,ht⟩ := hn; omega
      have hp2 : ¬2 ∣ p := fun hh => hnn (hh.trans hpD)
      omega
    by_contra he
    have hSumEven : 2 ∣ ∑ i ∈ range (n.factorization p+1), p^i := by
      have hMod := odd_prime_power_sum_mod_two hpOdd (n.factorization p+1)
      omega
    have hProd : 2 ∣ σ 1 n := by
      rw [hSigma]
      exact hSumEven.trans (dvd_prod_of_mem _ hp)
    obtain ⟨t,ht⟩ := hSigOdd
    omega
  let m := ∏ p ∈ n.primeFactors, p^(n.factorization p/2)
  refine ⟨m,?_⟩
  have hProd : ∏ p ∈ n.primeFactors, p^(n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self h.1.ne'
  calc
    n = ∏ p ∈ n.primeFactors, p^(n.factorization p) := hProd.symm
    _ = ∏ p ∈ n.primeFactors, (p^(n.factorization p/2))^2 := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have := hExpo p hp
      omega
    _ = m*m := by rw [Finset.prod_pow]; exact pow_two m

theorem main : H1 → H2 → H3 → type_of% @Erdos1053.erdos_1053.variants.guy := by
  intro h1 h2 h3 k hk
  rcases Nat.even_or_odd k with he|ho
  · refine ((h1 k hk).union (h2 k hk he)).subset ?_
    intro n hn
    have hs := not_squarefree_of_three_perfect hn hk
    rcases Nat.even_or_odd n with hnE|hnO
    · exact Or.inl ⟨hn,hnE,hs⟩
    · exact Or.inr ⟨hn,hnO,hs⟩
  · refine ((h1 k hk).union (h3 k hk ho)).subset ?_
    intro n hn
    rcases Nat.even_or_odd n with hnE|hnO
    · exact Or.inl ⟨hn,hnE,not_squarefree_of_three_perfect hn hk⟩
    · exact Or.inr ⟨hn,hnO,square_of_odd_perfect hn hnO ho⟩

end Proof

end OMA.R_Erdos1053_erdos_1053_variants_guy_R1
