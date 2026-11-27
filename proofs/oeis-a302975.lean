import OMAStatements.S_oeis_a302975
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open OMA.S_oeis_a302975

namespace SquareDivisorDenominator

private lemma tau_pos {n : ℕ} (hn : 0 < n) : 0 < tau n :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩

private lemma den_formula {n : ℕ} (hn : 0 < n) :
    a n = (n ^ tau n) / (n ^ tau n).gcd (tau n ^ n) := by
  unfold a
  rw [← Nat.cast_pow, ← Nat.cast_pow, Rat.natCast_div_eq_divInt, Rat.divInt_ofNat, Rat.den_mkRat]
  simp [hn.ne']

/-- e(e+1) is already bounded by a single odd prime power p^e. -/
private lemma exponent_bound (e : ℕ) : e*(e+1) ≤ 3^e := by
  induction e with
  | zero => decide
  | succ e ih =>
    cases e with
    | zero => decide
    | succ e =>
      rw [pow_succ]
      nlinarith [sq_nonneg (e : ℤ), Nat.zero_le e]

private lemma odd_bound {n p : ℕ} (hn : 0 < n) (hodd : ¬Even n) :
    tau n * n.factorization p ≤ n := by
  by_cases hmem : p ∈ n.primeFactors
  · have h3 : 3 ≤ p := by
      have hp := Nat.prime_of_mem_primeFactors hmem
      have h2 : p ≠ 2 := by
        rintro rfl
        exact hodd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hmem))
      have := hp.two_le
      omega
    let v (q : ℕ) := n.factorization q
    have hc : tau n = (v p+1)*(∏ q ∈ n.primeFactors.erase p, (v q+1)) := by
      rw [tau, Nat.card_divisors hn.ne']
      exact (Finset.mul_prod_erase n.primeFactors (fun q => v q+1) hmem).symm
    have hf : n = p^(v p)*(∏ q ∈ n.primeFactors.erase p, q^(v q)) := by
      rw [Finset.mul_prod_erase n.primeFactors (fun q => q^(v q)) hmem]
      exact Nat.prod_primeFactors_pow_factorization hn.ne'
    have hsmall : (∏ q ∈ n.primeFactors.erase p, (v q+1)) ≤
        ∏ q ∈ n.primeFactors.erase p, q^(v q) := by
      apply Finset.prod_le_prod'
      intro q hq
      have hq2 := (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hq).2).two_le
      exact Nat.le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_left hq2 _)
    have hlocal : v p*(v p+1) ≤ p^(v p) :=
      (exponent_bound _).trans (Nat.pow_le_pow_left h3 _)
    calc
      tau n*n.factorization p = (v p*(v p+1)) * (∏ q ∈ n.primeFactors.erase p, (v q+1)) := by
        rw [hc]
        change _ * v p = _
        ring
      _ ≤ p^(v p)*(∏ q ∈ n.primeFactors.erase p, q^(v q)) := Nat.mul_le_mul hlocal hsmall
      _ = n := hf.symm
  · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hmem
    simp [hz]

private lemma base_even {n p : ℕ} (hn : 0 < n) : Even (tau n * n.factorization p) := by
  by_cases hmem : p ∈ n.primeFactors
  · have hd : n.factorization p+1 ∣ tau n := by
      rw [tau, Nat.card_divisors hn.ne']
      exact Finset.dvd_prod_of_mem _ hmem
    by_cases he : Even (n.factorization p)
    · exact he.mul_left _
    · have he' : Even (n.factorization p+1) := by simp [Nat.even_add_one, he]
      obtain ⟨k, hk⟩ := hd
      rw [hk]
      exact (he'.mul_right _).mul_right _
  · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hmem
    simp [hz]

private lemma valuation {n : ℕ} (hn : 0 < n) (p : ℕ) :
    (a n).factorization p = tau n * n.factorization p - n * (tau n).factorization p := by
  rw [den_formula hn, Nat.factorization_div (Nat.gcd_dvd_left _ _),
    Nat.factorization_gcd (pow_ne_zero _ hn.ne') (pow_ne_zero _ (tau_pos hn).ne')]
  simp only [Nat.factorization_pow, Finsupp.tsub_apply, Finsupp.inf_apply,
    Finsupp.smul_apply, smul_eq_mul]
  omega

private lemma den_even {n : ℕ} (hn : 0 < n) (p : ℕ) : Even ((a n).factorization p) := by
  rw [valuation hn]
  have he := base_even (p := p) hn
  by_cases hpar : Even n
  · exact he.tsub (hpar.mul_right _)
  · by_cases hz : (tau n).factorization p = 0
    · simpa [hz] using he
    · have hle : n ≤ n*((tau n).factorization p) := by
        simpa using Nat.mul_le_mul_left n (show 1 ≤ (tau n).factorization p by omega)
      have hbound := odd_bound (p := p) hn hpar
      rw [Nat.sub_eq_zero_of_le (hbound.trans hle)]
      simp

end SquareDivisorDenominator

theorem OMA.solution : type_of% @OMA.S_oeis_a302975.main := by
  intro n hn
  let d := a n
  let root := ∏ p ∈ d.primeFactors, p^(d.factorization p/2)
  refine ⟨root, ?_⟩
  change d = root^2
  have hd : d ≠ 0 := Rat.den_ne_zero _
  rw [Nat.prod_primeFactors_pow_factorization hd]
  dsimp [root]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul]
  have h := Nat.even_iff.mp (SquareDivisorDenominator.den_even hn p)
  change d.factorization p % 2 = 0 at h
  congr 1
  omega
