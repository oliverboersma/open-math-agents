import OMAStatements.S_oeis_a055210
import Mathlib

namespace OMAA055210Helpers
open ArithmeticFunction

def sqComp (f : ArithmeticFunction ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => f (n ^ 2), by simp⟩

theorem sqComp_apply (f : ArithmeticFunction ℕ) (n : ℕ) : sqComp f n = f (n ^ 2) := rfl

theorem sqComp_mult (f : ArithmeticFunction ℕ) (hf : f.IsMultiplicative) :
    (sqComp f).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [sqComp_apply, hf.map_one]
  · intro m n hmn
    simp only [sqComp_apply, mul_pow]
    exact hf.map_mul_of_coprime (Nat.Coprime.pow 2 2 hmn)

def phiF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

theorem phiF_apply (n : ℕ) : phiF n = Nat.totient n := rfl

theorem phiF_mult : phiF.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [phiF_apply]
  · intro m n hmn
    simp only [phiF_apply]
    exact Nat.totient_mul hmn

theorem geo (x q m : ℕ) (hx : x = q + 1) :
    (∑ i ∈ Finset.range m, x ^ i) * q + 1 = x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, pow_succ, hx]
    rw [hx] at ih
    nlinarith [ih]

theorem hA (q j : ℕ) (hp : (q + 1).Prime) :
    (q + 2) * (∑ i ∈ Finset.range (j + 1), Nat.totient ((q + 1) ^ (2 * i))) =
      (q + 1) ^ (2 * j + 1) + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, ih, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
      Nat.totient_prime_pow_succ hp]
    simp only [Nat.add_sub_cancel]
    ring

theorem pp (p j : ℕ) (hp : p.Prime) :
    (∑ i ∈ Finset.range (j + 1), Nat.totient (p ^ (2 * i))) *
        (∑ i ∈ Finset.range (2 * j + 1), p ^ (i * 1)) =
      ∑ i ∈ Finset.range (2 * j + 1), p ^ (2 * i) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have hq : 1 ≤ q := by have := hp.one_lt; omega
  have h1 := hA q j hp
  have h2 := geo (q + 1) q (2 * j + 1) rfl
  have h3 := geo ((q + 1) ^ 2) (q * (q + 2)) (2 * j + 1) (by ring)
  simp only [mul_one]
  have e : ∀ i, (q + 1) ^ (2 * i) = ((q + 1) ^ 2) ^ i := fun i => by rw [← pow_mul]
  simp only [e] at h1 ⊢
  set A := ∑ i ∈ Finset.range (j + 1), Nat.totient ((q + 1) ^ (2 * i))
  set B := ∑ i ∈ Finset.range (2 * j + 1), (q + 1) ^ i
  set C := ∑ i ∈ Finset.range (2 * j + 1), ((q + 1) ^ 2) ^ i
  set T := (q + 1) ^ (2 * j + 1)
  have hT : ((q + 1) ^ 2) ^ (2 * j + 1) = T * T := by rw [← pow_mul, ← pow_add]; ring_nf
  rw [hT] at h3
  have hpos : 0 < q * (q + 2) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  zify at h1 h2 h3 ⊢
  linear_combination (↑B * ↑q : ℤ) * h1 + ((↑T : ℤ) + 1) * h2 - h3
def rt (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

theorem rt_ne_zero (n : ℕ) : rt n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem rt_fact (n : ℕ) (q : ℕ) : (rt n).factorization q = n.factorization q / 2 := by
  have h : ∀ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)).factorization =
      Finsupp.single p (n.factorization p / 2) :=
    fun _ hp => (Nat.prime_of_mem_primeFactors hp).factorization_pow
  unfold rt
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Finset.sum_congr rfl h, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hq
  · rfl
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hq
    rw [hq]
    rfl

theorem sq_dvd_iff (n k : ℕ) (hn : n ≠ 0) : k ^ 2 ∣ n ↔ k ∣ rt n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hn, rt_ne_zero]
  · rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk.ne') hn,
      ← Nat.factorization_le_iff_dvd hk.ne' (rt_ne_zero n), Finsupp.le_def, Finsupp.le_def]
    simp only [Nat.factorization_pow, rt_fact, Finsupp.smul_apply, smul_eq_mul]
    exact forall_congr' (fun q => by omega)

theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    OMA.S_oeis_a055210.a n = ∑ k ∈ (rt n).divisors, Nat.totient (k ^ 2) := by
  unfold OMA.S_oeis_a055210.a
  rw [← Finset.sum_image (f := Nat.totient) (g := fun k => k ^ 2)
    (fun x _ y _ h => Nat.pow_left_injective two_ne_zero h)]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, r, rfl⟩
    exact ⟨r, ⟨(sq_dvd_iff n r hn).mp (by rw [sq]; exact hd), rt_ne_zero n⟩, by ring⟩
  · rintro ⟨k, ⟨hk, -⟩, rfl⟩
    exact ⟨⟨(sq_dvd_iff n k hn).mpr hk, hn⟩, k, by ring⟩

theorem sq_eq (n : ℕ) : OMA.S_oeis_a055210.squarePart n = (rt n) ^ 2 := by
  unfold OMA.S_oeis_a055210.squarePart rt
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [← pow_mul, mul_comm]

theorem mulzeta (f : ArithmeticFunction ℕ) (x : ℕ) :
    (f * zeta) x = ∑ d ∈ x.divisors, f d := by
  have := coe_mul_zeta_apply (f := f) (x := x)
  rwa [natCoe_nat] at this

theorem funEq : ((sqComp phiF * zeta).pmul (sqComp (sigma 1))) = sqComp (sigma 2) := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _
    (((sqComp_mult _ phiF_mult).mul isMultiplicative_zeta).pmul
      (sqComp_mult _ isMultiplicative_sigma)) _ (sqComp_mult _ isMultiplicative_sigma)]
  intro p i hp
  rw [pmul_apply, mulzeta, Nat.sum_divisors_prime_pow hp]
  simp only [sqComp_apply, phiF_apply, ← pow_mul]
  rw [sigma_apply_prime_pow hp, sigma_apply_prime_pow hp]
  have e : ∀ x, p ^ (x * 2) = p ^ (2 * x) := fun x => by rw [mul_comm]
  simp only [e]
  rw [show i * 2 = 2 * i by ring]
  exact pp p i hp

end OMAA055210Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a055210.main := by
  intro n hn
  rw [OMAA055210Helpers.a_eq n hn.ne', OMAA055210Helpers.sq_eq n]
  have h := congrArg (fun f => f (OMAA055210Helpers.rt n)) OMAA055210Helpers.funEq
  simp only [ArithmeticFunction.pmul_apply, OMAA055210Helpers.mulzeta] at h
  simpa only [OMAA055210Helpers.sqComp_apply, OMAA055210Helpers.phiF_apply] using h
