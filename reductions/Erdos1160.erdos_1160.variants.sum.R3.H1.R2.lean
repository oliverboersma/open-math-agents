import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Separate the powers-of-two comparison from the cost of prescribing the Sylow
types. For an odd Sylow subgroup of order p^a, the elementary presentation
codebook has size p^(a.choose 2 + a.choose 3), proved by @gertjanvdgoot in
Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H1. Thus the usual uniform
prescribed-Sylow estimate of Blackburn--Neumann--Venkataraman, Theorem 16.20,
implies H2. The gap 2^11 ≤ 3^7 gives the coefficient 11 for odd orders
against 12 for the endpoint after raising counts to the same power 162.
This removes the need for a sharper, separate estimate for 3-groups.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2

/-- Relative cubic growth on powers of two with a uniform quadratic error. -/
def H1 : Prop := ∃ C : ℕ, ∀ a m : ℕ, 3 ≤ m → a ≤ m →
    2^(2*m^3) * g (2^a)^27 ≤ g (2^m)^27 * 2^(2*a^3+C*(m+1)^2)

/-- Count the Sylow two-subgroup by isomorphism type and the odd Sylow
subgroups by their elementary presentations. The cost of assembling the
types is at most an exponential with a quadratic exponent. -/
def H2 : Prop := ∃ E : ℕ, ∀ a q m : ℕ, Odd q → 2^a*q < 2^m →
    g (2^a*q) ≤ 2^(E*(m+1)^2) * g (2^a) *
      ∏ p ∈ q.primeFactors, p^((q.factorization p).choose 2 + (q.factorization p).choose 3)

theorem choose_arith (n : ℕ) : 6 * (n.choose 2 + n.choose 3) + n = n ^ 3 := by
  have h2 : ∀ m : ℕ, 2 * m.choose 2 + m = m ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  induction n with
  | zero => simp
  | succ m ih =>
    have := h2 m
    rw [Nat.choose_succ_succ m 2, Nat.choose_succ_succ m 1, Nat.choose_one_right]
    nlinarith

theorem odd_prime_code_bound {p a r : ℕ}
    (prime : p.Prime) (hp3 : 3 ≤ p) (hr : p^a ≤ 2^r) :
    (p^(a.choose 2 + a.choose 3))^162 ≤ (p^a)^(11*r^2) := by
  have hx : 11*a ≤ 7*r := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      (2:ℕ)^(11*a) = (2^11)^a := pow_mul ..
      _ ≤ (p^7)^a := Nat.pow_le_pow_left
        ((by decide : 2^11 ≤ 3^7).trans (Nat.pow_le_pow_left hp3 7)) _
      _ = (p^a)^7 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ (2^r)^7 := Nat.pow_le_pow_left hr _
      _ = 2^(7*r) := by rw [← pow_mul,Nat.mul_comm]
  have hs : 27*a^2 ≤ 11*r^2 := by
    nlinarith only [Nat.pow_le_pow_left hx 2, Nat.zero_le (r^2)]
  have hb : (p^(a.choose 2 + a.choose 3))^6 ≤ p^(a^3) := by
    rw [← pow_mul, Nat.mul_comm, ← choose_arith]
    exact Nat.pow_le_pow_right prime.pos (Nat.le_add_right _ _)
  calc
    (p^(a.choose 2 + a.choose 3))^162 = ((p^(a.choose 2 + a.choose 3))^6)^27 := pow_mul _ 6 27
    _ ≤ (p^(a^3))^27 := Nat.pow_le_pow_left hb _
    _ = (p^a)^(27*a^2) := by rw [← pow_mul,← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos prime.pos) hs

theorem odd_sylow_product_bound
    {q r : ℕ} (ho : Odd q) (hq : q < 2^r) :
    (∏ p ∈ q.primeFactors, (p^((q.factorization p).choose 2 + (q.factorization p).choose 3)))^162 ≤ 2^(11*r^3) := by
  classical
  have hn : 0 < q := by obtain ⟨u,hu⟩ := ho; omega
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) :
      (p^((q.factorization p).choose 2 + (q.factorization p).choose 3))^162 ≤ (p^q.factorization p)^(11*r^2) := by
    let a := q.factorization p
    have prime := Nat.prime_of_mem_primeFactors hp
    have hp3 : 3 ≤ p := by
      have hn2 : p ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
      have := prime.two_le
      omega
    have hr : p^a ≤ 2^r := (Nat.le_of_dvd hn (Nat.ordProj_dvd q p)).trans hq.le
    exact odd_prime_code_bound prime hp3 hr
  calc
    _ = ∏ p ∈ q.primeFactors, (p^((q.factorization p).choose 2 + (q.factorization p).choose 3))^162 := (Finset.prod_pow ..).symm
    _ ≤ ∏ p ∈ q.primeFactors, (p^q.factorization p)^(11*r^2) := Finset.prod_le_prod' hlocal
    _ = q^(11*r^2) := by
      have he : (∏ p ∈ q.primeFactors, p^q.factorization p) = q :=
        Nat.prod_factorization_pow_eq_self hn.ne'
      rw [Finset.prod_pow, he]
    _ ≤ (2^r)^(11*r^2) := Nat.pow_le_pow_left hq.le _
    _ = _ := by rw [← pow_mul]; congr 1; ring

theorem large_deficit_budget {a r C E : ℕ} (hr : 4*(6*C+162*E+162)+1 ≤ r) :
    162*(a+r) + 12*a^3 + 11*r^3 + (6*C+162*E)*(a+r+1)^2 ≤ 12*(a+r)^3 := by
  have hm : 1 ≤ a+r := by omega
  have hh := Nat.pow_le_pow_left (by omega : a+r+1 ≤ 2*(a+r)) 2
  have hs : a+r ≤ (a+r)^2 := by nlinarith only [Nat.mul_le_mul_left (a+r) hm]
  have hbig := Nat.mul_le_mul_right ((a+r)^2) hr
  nlinarith only [Nat.mul_le_mul_left (6*C+162*E) hh, Nat.mul_le_mul_left 162 hs,
    hbig, Nat.zero_le (a^2*r), Nat.zero_le (a*r^2), Nat.zero_le ((a+r)^2)]

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3.H1 := by
  rintro ⟨C,dyadic⟩ ⟨E,profiles⟩
  let R := 4*(6*C+162*E+162)+1
  refine ⟨R, by dsimp [R]; omega, eventually_atTop.mpr ⟨3, ?_⟩⟩
  intro k hk n hn hdiv
  obtain ⟨hnpos, hnlt⟩ := mem_Ico.mp hn
  obtain ⟨a,q,hodd,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have ha : a < k := by
    by_contra! h
    exact hdiv ((Nat.pow_dvd_pow 2 h).trans (dvd_mul_right _ _))
  let r := k+R-a
  have hsum : a+r = k+R := by dsimp [r]; omega
  have hr : R ≤ r := by dsimp [r]; omega
  rw [← hsum] at hnlt ⊢
  let m := a+r
  have hq : q < 2^r := by rw [pow_add] at hnlt; exact Nat.lt_of_mul_lt_mul_left hnlt
  let oddCodes := ∏ p ∈ q.primeFactors,
    p^((q.factorization p).choose 2 + (q.factorization p).choose 3)
  have hp : oddCodes^162 ≤ 2^(11*r^3) := odd_sylow_product_bound hodd hq
  have hd := Nat.pow_le_pow_left (dyadic a m (by dsimp [m]; omega) (by dsimp [m]; omega)) 6
  have hd' : 2^(12*m^3) * g (2^a)^162 ≤ g (2^m)^162 * 2^(12*a^3+6*C*(m+1)^2) := by
    convert hd using 1 <;> rw [mul_pow, ← pow_mul, ← pow_mul] <;> ring_nf
  have hb : 2^(12*m^3) * (2^m * g (2^a*q))^162 ≤ 2^(12*m^3) * g (2^m)^162 := calc
    _ ≤ 2^(12*m^3) * (2^m*(2^(E*(m+1)^2) * g (2^a) * oddCodes))^162 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (profiles a q m hodd hnlt)) _)
    _ = (2^(12*m^3)*g (2^a)^162) *
        oddCodes^162 * 2^(162*m+162*E*(m+1)^2) := by
      simp only [mul_pow, pow_add, ← pow_mul]; ring_nf
    _ ≤ (g (2^m)^162 * 2^(12*a^3+6*C*(m+1)^2)) * 2^(11*r^3) * 2^(162*m+162*E*(m+1)^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hd' hp)
    _ = g (2^m)^162 * 2^(162*m+12*a^3+11*r^3+(6*C+162*E)*(m+1)^2) := by
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]; congr 2; ring
    _ ≤ g (2^m)^162 * 2^(12*m^3) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (large_deficit_budget hr))
    _ = _ := Nat.mul_comm _ _
  exact (Nat.pow_le_pow_iff_left (by decide : 162 ≠ 0)).mp
    (Nat.le_of_mul_le_mul_left hb (Nat.two_pow_pos _))

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R2
