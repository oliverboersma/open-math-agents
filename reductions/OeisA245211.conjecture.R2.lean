import FormalConjectures.OEIS.«245211»
import Mathlib.Dynamics.PeriodicPts.Lemmas

namespace OMA.R_OeisA245211_conjecture_R2

open Finset

private theorem divisorSum_fixed_point {n : ℕ} (hn : n ≠ 0)
    (ha : OeisA245211.a n = n) :
    (∑ d ∈ n.divisors, d * d.divisors.card) = (n.divisors.card + 1) * n := by
  conv_lhs => rw [← Nat.insert_self_properDivisors hn, sum_insert Nat.self_notMem_properDivisors]
  change n * n.divisors.card + OeisA245211.a n = _
  rw [ha]
  ring

private theorem divisorSum_mul {m n : ℕ} (h : m.Coprime n) :
    (∑ d ∈ (m * n).divisors, d * d.divisors.card) =
      (∑ d ∈ m.divisors, d * d.divisors.card) * (∑ d ∈ n.divisors, d * d.divisors.card) := by
  rw [h.divisors_mul, sum_map]
  change (∑ x ∈ (m.divisors ×ˢ n.divisors).attach,
    x.val.1 * x.val.2 * (x.val.1 * x.val.2).divisors.card) = _
  rw [sum_attach (f := fun x : ℕ × ℕ => x.1 * x.2 * (x.1 * x.2).divisors.card),
    sum_product, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [((h.coprime_dvd_left (Nat.dvd_of_mem_divisors hi)).coprime_dvd_right
    (Nat.dvd_of_mem_divisors hj)).card_divisors_mul]
  ring

private theorem squarefree_product_data (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, d * d.divisors.card) = ∏ p ∈ P, (2 * p + 1) ∧
      (∏ p ∈ P, p).divisors.card = 2 ^ P.card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert p P hpP ih =>
    have hp' := hp p (mem_insert_self p P)
    have hP q (hq : q ∈ P) := hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ P, q) := by
      apply hp'.coprime_iff_not_dvd.mpr
      intro h
      obtain ⟨q, hq, hd⟩ := (hp'.prime.dvd_finsetProd_iff id).mp h
      exact hpP ((Nat.prime_dvd_prime_iff_eq hp' (hP q hq)).mp hd ▸ hq)
    have hdiv : p.divisors.card = 2 := by simp [hp'.divisors, Ne.symm hp'.ne_one]
    have hsum : (∑ d ∈ p.divisors, d * d.divisors.card) = 2 * p + 1 := by
      simp [hp'.divisors, Ne.symm hp'.ne_one, mul_comm, add_comm]
    obtain ⟨hs, hd⟩ := ih hP
    rw [prod_insert hpP, prod_insert hpP, card_insert_of_notMem hpP, divisorSum_mul hc,
      hc.card_divisors_mul, hdiv, hsum, hs, hd, pow_succ']
    exact ⟨rfl, rfl⟩

/-- Product equation for the distinct primes of a squarefree fixed point. -/
theorem squarefree_fixed_point_product {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n = n) :
    (∏ p ∈ n.primeFactors, (2 * p + 1)) =
      (2 ^ n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, p := by
  have hn := Nat.prod_primeFactors_of_squarefree hs
  obtain ⟨hsum, hcard⟩ := squarefree_product_data n.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rw [hn] at hsum hcard
  rw [← hsum, hn, divisorSum_fixed_point hs.ne_zero ha, hcard]

theorem baseProduct_lt {ι : Type*} (p : ι → ℕ) (s : Finset ι)
    (hs : s.Nonempty) (hp : ∀ i, (p i).Prime) :
    2 ^ s.card * (∏ i ∈ s, p i) < ∏ i ∈ s, (2 * p i + 1) := by
  rw [← prod_const, ← prod_mul_distrib]
  exact prod_lt_prod_of_nonempty (fun i _ => by have := (hp i).pos; positivity)
    (fun _ _ => Nat.lt_succ_self _) hs

theorem large_prime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hr : 2 ≤ Fintype.card ι)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    (i : ι) : 2 ^ (Fintype.card ι - 1) < p i := by
  let s : Finset ι := univ.erase i
  have hcard : s.card = Fintype.card ι - 1 := by simp [s]
  have hc : s.card + 1 = Fintype.card ι := by omega
  have hs : s.Nonempty := card_pos.mp (by omega)
  have hpos : 0 < ∏ j ∈ s, p j := prod_pos fun j _ => (hp j).pos
  have hp1 : (2 * p i + 1) * (∏ j ∈ s, (2 * p j + 1)) =
      (2 ^ Fintype.card ι + 1) * (p i * ∏ j ∈ s, p j) := by
    dsimp [s]
    rw [mul_prod_erase _ (fun j => 2 * p j + 1) (mem_univ i),
      mul_prod_erase _ p (mem_univ i)]
    exact hprod
  have hlt := Nat.mul_lt_mul_of_pos_left (baseProduct_lt p s hs hp) (by positivity : 0 < 2 * p i + 1)
  rw [hp1, ← hc, pow_succ] at hlt
  simp only [← mul_assoc] at hlt
  have := (Nat.mul_lt_mul_right hpos).mp hlt
  have hgoal : 2 ^ s.card < p i := by nlinarith only [this]
  simpa [hcard] using hgoal

private theorem small_prime_product (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hsmall : P.card ≤ 2)
    (he : (∏ p ∈ P, (2 * p + 1)) = (2 ^ P.card + 1) * ∏ p ∈ P, p) :
    (∏ p ∈ P, p) = 21 := by
  rcases (show P.card = 0 ∨ P.card = 1 ∨ P.card = 2 by omega) with h0 | h1 | h2
  · simp [card_eq_zero.mp h0] at he
  · obtain ⟨p, hpSet⟩ := card_eq_one.mp h1
    have hp2 := (hp p (by simp [hpSet])).two_le
    rw [hpSet] at he
    norm_num at he
    omega
  · obtain ⟨p, q, hpq, hpSet⟩ := card_eq_two.mp h2
    have hp2 := (hp p (by simp [hpSet])).two_le
    have hq2 := (hp q (by simp [hpSet])).two_le
    have hprod : (2 * p + 1) * (2 * q + 1) = 5 * (p * q) := by
      simpa [h2, hpSet, hpq] using he
    have hfactor : (p - 2) * (q - 2) = 5 := by
      rw [show p = p - 2 + 2 by omega, show q = q - 2 + 2 by omega] at hprod
      nlinarith only [hprod]
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp ⟨q - 2, hfactor.symm⟩ with h | h
    · rw [h] at hfactor
      have hp3 : p = 3 := by omega
      have hq7 : q = 7 := by omega
      norm_num [hpSet, hp3, hq7]
    · rw [h] at hfactor
      have hp7 : p = 7 := by omega
      have hq3 : q = 3 := by omega
      norm_num [hpSet, hp7, hq3]

private theorem even_prime_product_impossible (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hlarge : 3 ≤ P.card) (heven : Even P.card)
    (he : (∏ p ∈ P, (2 * p + 1)) = (2 ^ P.card + 1) * ∏ p ∈ P, p) : False := by
  have hc : Fintype.card P = P.card := by simp
  have htype : (∏ i : P, (2 * (i : ℕ) + 1)) =
      (2 ^ Fintype.card P + 1) * ∏ i : P, (i : ℕ) := by
    rw [hc]
    calc
      (∏ i : P, (2 * (i : ℕ) + 1)) = ∏ p ∈ P, (2 * p + 1) :=
        prod_coe_sort P (fun p => 2 * p + 1)
      _ = (2 ^ P.card + 1) * ∏ p ∈ P, p := he
      _ = (2 ^ P.card + 1) * ∏ i : P, (i : ℕ) :=
        congrArg (fun x : ℕ => (2 ^ P.card + 1) * x) (prod_coe_sort P (fun p => p)).symm
  have hpLarge (p : ℕ) (hm : p ∈ P) : 3 < p := by
    have hb := large_prime (fun i : P => (i : ℕ)) (fun i => hp i i.property)
      (by rw [hc]; omega) htype ⟨p, hm⟩
    change 2 ^ (Fintype.card P - 1) < p at hb
    rw [hc] at hb
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ P.card - 1 by omega)
    omega
  have hcast : (∏ p ∈ P, (2 * (p : ZMod 3) + 1)) =
        ((2 : ZMod 3) ^ P.card + 1) * ∏ p ∈ P, (p : ZMod 3) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_prod, Nat.cast_one, Nat.cast_ofNat]
      using congrArg (fun x : ℕ => (x : ZMod 3)) he
  have hpow : (2 : ZMod 3) ^ P.card = 1 := by
    rw [show (2 : ZMod 3) = -1 by decide, heven.neg_one_pow]
  have hnz (p : ℕ) (hm : p ∈ P) : (p : ZMod 3) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff p 3).mp hz
    have hp3 := (Nat.prime_dvd_prime_iff_eq (by decide) (hp p hm)).mp hd
    exact (hpLarge p hm).ne hp3
  have hright : ((2 : ZMod 3) ^ P.card + 1) * ∏ p ∈ P, (p : ZMod 3) ≠ 0 :=
    mul_ne_zero (by rw [hpow]; decide) (prod_ne_zero_iff.mpr hnz)
  have test : ∀ z : ZMod 3, z ≠ 0 → 2 * z + 1 ≠ 0 → z = 2 := by decide
  have ht (p : ℕ) (hm : p ∈ P) : (p : ZMod 3) = 2 := by
    apply test _ (hnz p hm)
    intro hz
    exact hright (hcast.symm.trans (prod_eq_zero hm hz))
  have hleft : (∏ p ∈ P, (2 * (p : ZMod 3) + 1)) = 1 := by
    calc
      (∏ p ∈ P, (2 * (p : ZMod 3) + 1)) = ∏ _p ∈ P, (2 : ZMod 3) :=
        prod_congr rfl fun p hm => by rw [ht p hm]; decide
      _ = 1 := by rw [prod_const, hpow]
  have hprod : (∏ p ∈ P, (p : ZMod 3)) = 1 := by
    rw [prod_congr rfl ht, prod_const, hpow]
  rw [hleft, hpow, hprod] at hcast
  exact (by decide : (1 : ZMod 3) ≠ (1 + 1) * 1) hcast

/-- Squarefree fixed points cannot have an odd prime-power number of prime factors. -/
def H1 : Prop :=
  ∀ n q k : ℕ, Squarefree n → q.Prime → Odd q → 0 < k →
    n.primeFactors.card = q ^ k → OeisA245211.a n ≠ n

/-- Exclude the remaining odd squarefree cases with fewer than 65 prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Squarefree n → 3 ≤ n.primeFactors.card → n.primeFactors.card < 65 →
    Odd n.primeFactors.card →
    (∀ q k : ℕ, q.Prime → 0 < k → n.primeFactors.card ≠ q ^ k) → OeisA245211.a n ≠ n

/-- Exclude squarefree cases with at least 65 factors and no prime-power count. -/
def H3 : Prop :=
  ∀ n : ℕ, Squarefree n → 65 ≤ n.primeFactors.card → Odd n.primeFactors.card →
    (∀ q k : ℕ, q.Prime → 0 < k → n.primeFactors.card ≠ q ^ k) → OeisA245211.a n ≠ n

/-- Exclude fixed points with repeated prime factors. -/
def H4 : Prop :=
  ∀ n : ℕ, 0 < n → ¬ Squarefree n → OeisA245211.a n ≠ n

theorem main : H1 → H2 → H3 → H4 → type_of% @OeisA245211.conjecture := by
  intro h1 h2 h3 h4 n hn
  constructor
  · intro ha
    by_cases hs : Squarefree n
    · let P := n.primeFactors
      have hp (p : ℕ) (hm : p ∈ P) : p.Prime := Nat.prime_of_mem_primeFactors hm
      have hprod_n : (∏ p ∈ P, p) = n := Nat.prod_primeFactors_of_squarefree hs
      have he : (∏ p ∈ P, (2 * p + 1)) = (2 ^ P.card + 1) * ∏ p ∈ P, p := by
        exact squarefree_fixed_point_product hs ha
      by_cases hsmall : P.card ≤ 2
      · exact hprod_n.symm.trans (small_prime_product P hp hsmall he)
      have hmin : 3 ≤ P.card := by omega
      rcases Nat.even_or_odd P.card with hEven | hOdd
      · exact (even_prime_product_impossible P hp hmin hEven he).elim
      by_cases hpower : ∃ q k : ℕ, q.Prime ∧ 0 < k ∧ P.card = q ^ k
      · obtain ⟨q, k, hq, hk, hr⟩ := hpower
        have hqo : Odd q := by
          rw [hr] at hOdd
          exact (Nat.odd_pow_iff hk.ne').mp hOdd
        exact (h1 n q k hs hq hqo hk hr ha).elim
      have hnot (q k : ℕ) (hq : q.Prime) (hk : 0 < k) : P.card ≠ q ^ k :=
        fun hr => hpower ⟨q, k, hq, hk, hr⟩
      by_cases hb : P.card < 65
      · exact (h2 n hs hmin hb hOdd hnot ha).elim
      · exact (h3 n hs (le_of_not_gt hb) hOdd hnot ha).elim
    · exact (h4 n hn hs ha).elim
  · rintro rfl
    decide

end OMA.R_OeisA245211_conjecture_R2
