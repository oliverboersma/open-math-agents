import FormalConjectures.OEIS.«76495»
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin

/-! Prime factor restrictions on candidates of the divisor-sum congruence with remainder five. -/

open Finset ArithmeticFunction

namespace SigmaFive

private theorem two_prime_pow_of_two_le {a e q : ℕ} (ha : 1 ≤ a) (he : 2 ≤ e)
    (hq : q.Prime) (hq3 : 3 ≤ q) :
    sigma 1 (2 ^ a * q ^ e) % (2 ^ a * q ^ e) ≠ 5 := by
  intro h
  let P : ℕ := 2 ^ a
  let Q : ℕ := q ^ e
  let S : ℕ := ∑ i ∈ range e, q ^ i
  have hP : 2 ≤ P := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) ha
  have hQ : 9 ≤ Q := calc
    9 = 3 ^ 2 := by decide
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 _
    _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
  have hS : 1 + q ≤ S := by
    dsimp [S]
    have hel := sum_le_sum_of_subset_of_nonneg (range_mono he)
      (fun i _ _ => Nat.zero_le (q ^ i))
    simpa [sum_range_succ] using hel
  have hgeom : S * (q-1) + 1 = Q := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by omega), S, Q] using
      (geom_sum_mul_add (q-1) e)
  have hS2 : 2*S ≤ Q := by
    have hh := Nat.mul_le_mul_left S (show 2 ≤ q-1 by omega)
    omega
  have hc : Nat.Coprime P Q := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes Nat.prime_two hq).2 (by omega)
  have htwo : (∑ i ∈ range (a+1), 2 ^ i) = 2*P-1 := by
    have hh := geom_sum_mul_add (1 : ℕ) (a+1)
    norm_num [pow_succ, P] at hh ⊢
    omega
  have hs : sigma 1 (P*Q) = (2*P-1)*(S+Q) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc]
    change sigma 1 (2^a) * sigma 1 (q^e) = _
    rw [sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow hq,
      htwo, sum_range_succ]
  change sigma 1 (P*Q) % (P*Q) = 5 at h
  let k := ((2*P-1)*(S+Q)) / (P*Q)
  have heq := Nat.mod_add_div (sigma 1 (P*Q)) (P*Q)
  rw [h, hs] at heq
  change 5 + P*Q*k = (2*P-1)*(S+Q) at heq
  have hklo : 2 ≤ k := by
    by_contra! hr
    have hkmul := Nat.mul_le_mul_left (P*Q) (show k ≤ 1 by omega)
    have hlow : (P+1)*Q ≤ (2*P-1)*(S+Q) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [← heq] at hlow
    simp only [mul_one] at hkmul
    nlinarith
  have hkhi : k ≤ 2 := by
    by_contra! hr
    have hkprod := Nat.mul_le_mul_left (P*Q) hr
    have hsum : 2*(S+Q) ≤ 3*Q := by omega
    have hprod := Nat.mul_le_mul_left P hsum
    have hstrict : (2*P-1)*(S+Q) < (2*P)*(S+Q) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    nlinarith
  have hk : k = 2 := by omega
  rw [hk] at heq
  have key : 2*P*S = q*S+6 := by
    have hm : (q-1)+1=q := Nat.sub_add_cancel (by omega)
    have hp : (2*P-1)+1=2*P := Nat.sub_add_cancel (by omega)
    nlinarith only [heq, hgeom, congrArg (S * ·) hm, congrArg (· * (S+Q)) hp]
  have hgreater : q < 2*P := by
    by_contra! hh
    have := Nat.mul_le_mul_right S hh
    omega
  have hd : (2*P-q)*S = 6 := by
    rw [Nat.sub_mul, key, Nat.add_sub_cancel_left]
  have hle : S ≤ 6 := by
    have hp := Nat.mul_le_mul_right S (show 1 ≤ 2*P-q by omega)
    simpa [hd] using hp
  have hsmall : e = 2 := by
    by_contra hn
    have hem : 3 ≤ e := by omega
    have hc : 1+q+q^2 ≤ S := by
      dsimp [S]
      simpa [sum_range_succ] using (sum_le_sum_of_subset_of_nonneg (range_mono hem)
        (fun i _ _ => Nat.zero_le (q ^ i)))
    nlinarith
  have heval : S = 1+q := by simp [S,hsmall,sum_range_succ]
  have hqmax : q ≤ 5 := by omega
  interval_cases q
  · rw [heval] at hd
    omega
  · exact (by decide : ¬ Nat.Prime 4) hq
  · rw [heval] at hd
    have hp3 : P = 3 := by omega
    have : 2 ∣ P := by
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
      simp [P,pow_succ]
    omega

theorem two_prime_pow {a e q : ℕ} (ha : 1 ≤ a) (he : 1 ≤ e)
    (hq : q.Prime) (hq3 : 3 ≤ q) :
    sigma 1 (2 ^ a * q ^ e) % (2 ^ a * q ^ e) ≠ 5 := by
  by_cases hb : 2 ≤ e
  · exact two_prime_pow_of_two_le ha hb hq hq3
  have he1 : e = 1 := by omega
  subst e
  simp only [pow_one]
  intro h
  have hc : Nat.Coprime (2^a) q :=
    ((Nat.coprime_primes Nat.prime_two hq).2 (by omega)).pow_left a
  have hqeven : 2 ∣ q+1 := by
    obtain ⟨j,hj⟩ := hq.odd_of_ne_two (by omega)
    exact ⟨j+1, by omega⟩
  have hse : 2 ∣ sigma 1 (2^a*q) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, ← pow_one q,
      sigma_one_apply_prime_pow hq]
    simp only [show (1 : ℕ)+1=2 by decide, sum_range_succ, sum_range_zero, pow_zero,
      pow_one, zero_add]
    exact dvd_mul_of_dvd_right (by simpa [Nat.add_comm] using hqeven : 2 ∣ 1 + q) _
  have hne : 2 ∣ 2^a*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  have hm := Nat.mod_mod_of_dvd (sigma 1 (2^a*q)) hne
  rw [h, Nat.mod_eq_zero_of_dvd hse] at hm
  exact (by decide : 5 % 2 ≠ 0) hm

theorem prime_pow {q : ℕ} (hq : q.Prime) (e : ℕ) :
    sigma 1 (q^e) % (q^e) ≠ 5 := by
  let S := ∑ i ∈ range e, q^i
  have hg : S*(q-1)+1 = q^e := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by have := hq.two_le; omega), S] using
      (geom_sum_mul_add (q-1) e)
  have hl : S < q^e := by
    have := Nat.mul_le_mul_left S (show 1 ≤ q-1 by have := hq.two_le; omega)
    omega
  rw [sigma_one_apply_prime_pow hq, sum_range_succ, Nat.add_mod_right, Nat.mod_eq_of_lt hl]
  intro heq
  by_cases hlarge : 3 ≤ e
  · have hsum : 1+q+q^2 ≤ S := by
      dsimp [S]
      simpa [sum_range_succ] using (sum_le_sum_of_subset_of_nonneg (range_mono hlarge)
        (fun i _ _ => Nat.zero_le (q ^ i)))
    have hq2 := hq.two_le
    change S = 5 at heq
    nlinarith
  · have cases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · simp [S] at heq
    · simp [S, sum_range_succ] at heq
    · simp [S, sum_range_succ] at heq
      have hq4 : q = 4 := by omega
      exact (by decide : ¬ Nat.Prime 4) (hq4 ▸ hq)

private theorem sigma_bound {p d : ℕ} (hp : p.Prime) (e : ℕ) (hd : d ≤ p-1) :
    d * sigma 1 (p ^ e) ≤ (d+1)*p^e := by
  let S := ∑ i ∈ range e, p^i
  have hg : S*(p-1)+1 = p^e := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ p by have := hp.two_le; omega), S] using
      (geom_sum_mul_add (p-1) e)
  have hdS := Nat.mul_le_mul_left S hd
  rw [sigma_one_apply_prime_pow hp, sum_range_succ]
  change d*(S+p^e) ≤ _
  nlinarith

private theorem pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    p^e < sigma 1 (p^e) := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ]
  have hb : 1 ≤ ∑ i ∈ range e, p^i := by
    simpa using (single_le_sum (f := fun i => p^i) (fun i _ => Nat.zero_le _)
      (mem_range.mpr (show 0 < e by omega)))
  omega

theorem odd_two_prime_pow {p q a e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) (ha : 1 ≤ a) (he : 1 ≤ e) :
    sigma 1 (p^a*q^e) % (p^a*q^e) ≠ 5 := by
  let P := p^a
  let Q := q^e
  have hP : 3 ≤ P := hp3.trans (by
    simpa [P] using Nat.pow_le_pow_right hp.pos ha)
  have hQ : 5 ≤ Q := hq5.trans (by
    simpa [Q] using Nat.pow_le_pow_right hq.pos he)
  have hc : P.Coprime Q := ((Nat.coprime_primes hp hq).2 hne).pow _ _
  have hmul : sigma 1 (P*Q) = sigma 1 P * sigma 1 Q :=
    isMultiplicative_sigma.map_mul_of_coprime hc
  have high : sigma 1 (P*Q) < 2*(P*Q) := by
    rw [hmul]
    have h := Nat.mul_le_mul (sigma_bound hp a (d := 2) (by omega))
      (sigma_bound hq e (d := 4) (by omega))
    change (2*sigma 1 P)*(4*sigma 1 Q) ≤ (2+1)*P*((4+1)*Q) at h
    have hpos : 0 < P*Q := Nat.mul_pos (by omega) (by omega)
    nlinarith only [h, hpos]
  have low : P*Q+5 < sigma 1 (P*Q) := by
    rw [hmul]
    have hl := Nat.mul_le_mul (pow_lt_sigma hp ha) (pow_lt_sigma hq he)
    change (P+1)*(Q+1) ≤ sigma 1 P * sigma 1 Q at hl
    nlinarith only [hl, hP, hQ]
  change sigma 1 (P*Q) % (P*Q) ≠ 5
  intro h
  have hx := Nat.mod_add_div (sigma 1 (P*Q)) (P*Q)
  rw [h] at hx
  let k := sigma 1 (P*Q) / (P*Q)
  change 5 + (P*Q)*k = _ at hx
  by_cases hk : k ≤ 1
  · have hb := Nat.mul_le_mul_left (P*Q) hk
    omega
  · have hb := Nat.mul_le_mul_left (P*Q) (show 2 ≤ k by omega)
    omega

private theorem ordered_pair {p q a e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (ha : 1 ≤ a) (he : 1 ≤ e) :
    sigma 1 (p^a*q^e) % (p^a*q^e) ≠ 5 := by
  have hp2 := hp.two_le
  by_cases hp' : p = 2
  · subst p
    exact two_prime_pow ha he hq (by omega)
  have hq5 : 5 ≤ q := by
    by_contra! hh
    have hq4 : q = 4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (hq4 ▸ hq)
  exact odd_two_prime_pow hp hq (by omega) hq5 (by omega) ha he

theorem three_le_primeFactors_card {n : ℕ} (hn : 0 < n)
    (h : sigma 1 n % n = 5) : 3 ≤ n.primeFactors.card := by
  have hn0 := Nat.ne_of_gt hn
  have fac := Nat.prod_primeFactors_pow_factorization hn0
  by_contra! hs
  have cases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 := by omega
  rcases cases with hzero | hone | htwo
  · rw [Finset.card_eq_zero.mp hzero, Finset.prod_empty] at fac
    rw [fac] at h
    simp at h
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hone
    have hprime := (Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hp])).1
    rw [hp,Finset.prod_singleton] at fac
    exact (prime_pow hprime (n.factorization p)) (by simpa only [← fac] using h)
  · obtain ⟨p,q,hne,hpq⟩ := Finset.card_eq_two.mp htwo
    have hp := Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hpq])
    have hq := Nat.mem_primeFactors.mp (show q ∈ n.primeFactors by simp [hpq])
    have ha := hp.1.factorization_pos_of_dvd hn0 hp.2.1
    have he := hq.1.factorization_pos_of_dvd hn0 hq.2.1
    rw [hpq,Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at fac
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ordered_pair hp.1 hq.1 hlt ha he) (by simpa only [← fac] using h)
    · rw [mul_comm] at fac
      exact (ordered_pair hq.1 hp.1 hlt he ha) (by simpa only [← fac] using h)


end SigmaFive
open Finset ArithmeticFunction

namespace SigmaFive.Modular

private theorem sum_five_powers_mod_five (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, 5 ^ i) % 5 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hterm : 5 ^ n % 5 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_pow_self 5 (by omega)
      rw [Nat.add_mod, ih (by omega), hterm]


private theorem sum_three_powers_mod_three (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, 3 ^ i) % 3 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sum_range_succ]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hterm : 3 ^ n % 3 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact dvd_pow_self 3 (by omega)
      rw [Nat.add_mod, ih (by omega), hterm]

/-- Sigma of any power of 3 is one modulo 3. -/
theorem sigma_three_pow_mod_three (a : ℕ) :
    sigma 1 (3 ^ a) % 3 = 1 := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3), sum_range_succ]
  by_cases ha : a = 0
  · simp [ha]
  · have hs := sum_three_powers_mod_three a (by omega)
    have hp : 3 ^ a % 3 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self 3 (by omega)
    rw [Nat.add_mod, hs, hp]

private theorem pow_even_mod_three {p b : ℕ} (hp : p % 3 = 2) :
    p ^ (2*b) % 3 = 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show 2*(b+1) = 2*b+2 by omega, pow_add, Nat.mul_mod, Nat.mul_mod, ih]
    rw [Nat.pow_mod, hp]

private theorem sigma_prime_power_even_mod_three {p b : ℕ}
    (hp : p.Prime) (hpm : p % 3 = 2) (hpd : (p-1) % 3 = 1) :
    sigma 1 (p ^ (2*b)) % 3 = 1 := by
  rw [sigma_one_apply_prime_pow hp]
  rw [sum_range_succ]
  let S := ∑ i ∈ range (2*b), p ^ i
  have hm : p-1+1 = p := Nat.sub_add_cancel (by have := hp.two_le; omega)
  have hg : S * (p-1) + 1 = p ^ (2*b) := by
    convert geom_sum_mul_add (p-1) (2*b) using 1 <;> simp [S, hm]
  have hr := congrArg (fun x : ℕ => x % 3) hg
  rw [Nat.add_mod, Nat.mul_mod] at hr
  have hpow := @pow_even_mod_three p b hpm
  rw [hpow, hpd] at hr
  have hsum : S % 3 = 0 := by omega
  rw [Nat.add_mod, hsum, hpow]

/-- Sigma of a power of 5 with even exponent is one modulo 3. -/
theorem sigma_five_pow_mod_three (b : ℕ) :
    sigma 1 (5 ^ (2*b)) % 3 = 1 :=
  sigma_prime_power_even_mod_three (p := 5) (by decide) (by norm_num) (by norm_num)

/-- Sigma of a power of 11 with even exponent is one modulo 3. -/
theorem sigma_eleven_pow_mod_three (b : ℕ) :
    sigma 1 (11 ^ (2*b)) % 3 = 1 :=
  sigma_prime_power_even_mod_three (p := 11) (by decide) (by norm_num) (by norm_num)


/-- The geometric factor for every nonnegative even exponent of 5 is one modulo 5. -/
theorem sigma_five_pow_mod_five (b : ℕ) :
    sigma 1 (5 ^ (2*b)) % 5 = 1 := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
  rw [sum_range_succ]
  by_cases he : 2*b = 0
  · simp [he]
  · have hs := sum_five_powers_mod_five (2*b) (by omega)
    have hp : 5 ^ (2*b) % 5 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self 5 (by omega)
    rw [Nat.add_mod, hs, hp]

end SigmaFive.Modular

namespace SigmaFive

private theorem triple_sigma {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) :
    sigma 1 (p^a*q^b*r^c) = sigma 1 (p^a)*sigma 1 (q^b)*sigma 1 (r^c) := by
  have h1 : (p^a).Coprime (q^b) := ((Nat.coprime_primes hp hq).2 (by omega)).pow _ _
  have h2 : (p^a).Coprime (r^c) := ((Nat.coprime_primes hp hr).2 (by omega)).pow _ _
  have h3 : (q^b).Coprime (r^c) := ((Nat.coprime_primes hq hr).2 (by omega)).pow _ _
  rw [isMultiplicative_sigma.map_mul_of_coprime (h2.mul_left h3),
    isMultiplicative_sigma.map_mul_of_coprime h1]

private theorem triple_bound {p q r a b c d f g : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (hd : d ≤ p-1) (hf : f ≤ q-1) (hg : g ≤ r-1) :
    d*f*g*sigma 1 (p^a*q^b*r^c) ≤ (d+1)*(f+1)*(g+1)*(p^a*q^b*r^c) := by
  rw [triple_sigma hp hq hr hpq hqr]
  calc
    _ = (d*sigma 1 (p^a))*(f*sigma 1 (q^b))*(g*sigma 1 (r^c)) := by ring
    _ ≤ ((d+1)*p^a)*((f+1)*q^b)*((g+1)*r^c) := Nat.mul_le_mul
      (Nat.mul_le_mul (sigma_bound hp a hd) (sigma_bound hq b hf)) (sigma_bound hr c hg)
    _ = _ := by ring

private theorem sum_pow_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ i ∈ range e, p^i) % 2 = e % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

private theorem even_exp_of_odd_sigma {p e : ℕ} (hp : p.Prime)
    (hpodd : p % 2 = 1) (hs : Odd (sigma 1 (p^e))) : Even e := by
  rw [sigma_one_apply_prime_pow hp] at hs
  have hs' := Nat.odd_iff.mp hs
  rw [sum_pow_mod_two hpodd] at hs'
  exact Nat.even_iff.mpr (by omega)

theorem odd_triple_shape {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : sigma 1 (p^a*q^b*r^c) % (p^a*q^b*r^c) = 5) :
    p = 3 ∧ q = 5 ∧ (r = 7 ∨ r = 11 ∨ r = 13) ∧
      Even a ∧ Even b ∧ Even c ∧
      sigma 1 (p^a*q^b*r^c) = 2*(p^a*q^b*r^c)+5 := by
  have q5 : 5 ≤ q := by
    by_contra! hq'
    have : q = 4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (this ▸ hq)
  have r7 : 7 ≤ r := by
    by_contra! hr'
    have : r = 6 := by omega
    exact (by decide : ¬ Nat.Prime 6) (this ▸ hr)
  let P := p^a
  let Q := q^b
  let R := r^c
  let N := P*Q*R
  let F := sigma 1 N
  have P3 : 3 ≤ P := hp3.trans (by simpa [P] using Nat.pow_le_pow_right hp.pos ha)
  have Q5 : 5 ≤ Q := q5.trans (by simpa [Q] using Nat.pow_le_pow_right hq.pos hb)
  have R7 : 7 ≤ R := r7.trans (by simpa [R] using Nat.pow_le_pow_right hr.pos hc)
  have hn : 0 < N := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hbound := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
    (d := 2) (f := 4) (g := 6) (by omega) (by omega) (by omega)
  change 48*F ≤ 105*N at hbound
  have hl : N+5 < F := by
    have L : (P+1)*Q*R ≤ F := by
      dsimp only [F,N,P,Q,R]
      rw [triple_sigma hp hq hr hpq hqr]
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (pow_lt_sigma hp ha) (pow_lt_sigma hq hb).le)
        (pow_lt_sigma hr hc).le
    have hqr' : 5*7 ≤ Q*R := Nat.mul_le_mul Q5 R7
    dsimp only [N]
    nlinarith only [L, hqr']
  change F % N = 5 at h
  have heq := Nat.mod_add_div F N
  rw [h] at heq
  have hklo : 2 ≤ F/N := by
    by_contra! hh
    have := Nat.mul_le_mul_left N (show F/N ≤ 1 by omega)
    omega
  have hkhi : F/N ≤ 2 := by
    by_contra! hh
    have := Nat.mul_le_mul_left N hh
    omega
  have hk : F/N = 2 := by omega
  rw [hk] at heq
  have heq' : F = 2*N+5 := by omega
  have hp' : p = 3 := by
    by_contra hne
    have p5 : 5 ≤ p := by
      by_contra! hh
      have : p = 4 := by omega
      exact (by decide : ¬ Nat.Prime 4) (this ▸ hp)
    have q7 : 7 ≤ q := by
      by_contra! hh
      have : q = 6 := by omega
      exact (by decide : ¬ Nat.Prime 6) (this ▸ hq)
    have r11 : 11 ≤ r := by
      have r8 : 8 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> revert hr <;> decide
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 4) (f := 6) (g := 10) (by omega) (by omega) (by omega)
    change 240*F ≤ 385*N at H
    omega
  have hq' : q = 5 := by
    by_contra hne
    have q7 : 7 ≤ q := by
      by_contra! hh
      have : q = 6 := by omega
      exact (by decide : ¬ Nat.Prime 6) (this ▸ hq)
    have r11 : 11 ≤ r := by
      have r8 : 8 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> revert hr <;> decide
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 2) (f := 6) (g := 10) (by omega) (by omega) (by omega)
    change 120*F ≤ 231*N at H
    omega
  have r16 : r ≤ 16 := by
    by_contra! hh
    have H := triple_bound (a := a) (b := b) (c := c) hp hq hr hpq hqr
      (d := 2) (f := 4) (g := 16) (by omega) (by omega) (by omega)
    change 128*F ≤ 255*N at H
    omega
  have hrc : r = 7 ∨ r = 11 ∨ r = 13 := by
    interval_cases r <;> revert hr <;> decide
  have oddF : Odd F := ⟨N+2, by omega⟩
  change Odd (sigma 1 (p^a*q^b*r^c)) at oddF
  rw [triple_sigma hp hq hr hpq hqr, Nat.odd_mul, Nat.odd_mul] at oddF
  refine ⟨hp', hq', hrc, ?_, ?_, ?_, heq'⟩
  · exact even_exp_of_odd_sigma hp (by omega) oddF.1.1
  · exact even_exp_of_odd_sigma hq (by omega) oddF.1.2
  · exact even_exp_of_odd_sigma hr (by
      exact Nat.odd_iff.mp (hr.odd_of_ne_two (by omega))) oddF.2

end SigmaFive

namespace SigmaFive

private theorem sorted_card_three (S : Finset ℕ) (h : S.card = 3) :
    ∃ p q r, p < q ∧ q < r ∧ S = {p,q,r} := by
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hxy with hxy' | hyx
  · rcases lt_or_gt_of_ne hyz with hyz' | hzy
    · exact ⟨x,y,z,hxy',hyz',rfl⟩
    · rcases lt_or_gt_of_ne hxz with hxz' | hzx
      · refine ⟨x,z,y,hxz',hzy,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
      · refine ⟨z,x,y,hzx,hxy',?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
  · rcases lt_or_gt_of_ne hxz with hxz' | hzx
    · refine ⟨y,x,z,hyx,hxz',?_⟩
      ext t
      simp only [mem_insert,mem_singleton]
      tauto
    · rcases lt_or_gt_of_ne hyz with hyz' | hzy
      · refine ⟨y,z,x,hyz',hzx,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto
      · refine ⟨z,y,x,hzy,hyx,?_⟩
        ext t
        simp only [mem_insert,mem_singleton]
        tauto

theorem odd_four_support_of_modular
    (hexcl : ∀ a b c r : ℕ, 0 < a → 0 < b → Even a → Even b → Even c →
      (r = 7 ∨ r = 11 ∨ r = 13) →
      sigma 1 (3^a*5^b*r^c) ≠ 2*(3^a*5^b*r^c)+5)
    {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    4 ≤ n.primeFactors.card := by
  have hn' : 0 < n := by obtain ⟨j,hj⟩ := hn; omega
  have hge := three_le_primeFactors_card hn' h
  by_contra! hh
  obtain ⟨p,q,r,hpq,hqr,hset⟩ := sorted_card_three _ (by omega : n.primeFactors.card = 3)
  have hp := Nat.mem_primeFactors.mp (show p ∈ n.primeFactors by simp [hset])
  have hq := Nat.mem_primeFactors.mp (show q ∈ n.primeFactors by simp [hset])
  have hr := Nat.mem_primeFactors.mp (show r ∈ n.primeFactors by simp [hset])
  have hp3 : 3 ≤ p := by
    have := hp.1.two_le
    by_contra! hl
    have he : p = 2 := by omega
    exact (hn.not_two_dvd_nat) (he ▸ hp.2.1)
  have ha := hp.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hp.2.1
  have hb := hq.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hq.2.1
  have hc := hr.1.factorization_pos_of_dvd (Nat.ne_of_gt hn') hr.2.1
  have hnfac := Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn')
  rw [hset, prod_insert (by simp; omega), prod_insert (by simp; omega), prod_singleton] at hnfac
  rw [← mul_assoc] at hnfac
  obtain ⟨hp',hq',hR,ha',hb',hc',heq⟩ :=
    odd_triple_shape hp.1 hq.1 hr.1 hp3 hpq hqr ha hb hc (by simpa only [← hnfac] using h)
  subst p
  subst q
  exact hexcl _ _ _ _ ha hb ha' hb' hc' hR heq

end SigmaFive

namespace SigmaFive

theorem exclude_triple_from_residues
    (three_mod_three : ∀ a : ℕ, sigma 1 (3^a) % 3 = 1)
    (five_mod_three : ∀ b : ℕ, Even b → sigma 1 (5^b) % 3 = 1)
    (eleven_mod_three : ∀ c : ℕ, Even c → sigma 1 (11^c) % 3 = 1)
    (five_mod_five : ∀ b : ℕ, Even b → sigma 1 (5^b) % 5 = 1)
    (other_mod_five : ∀ p e : ℕ, (p = 3 ∨ p = 7 ∨ p = 13) → Even e →
      sigma 1 (p^e) % 5 ≠ 0)
    (a b c r : ℕ) (ha : 0<a) (hb : 0<b) (ha' : Even a) (hb' : Even b) (hc' : Even c)
    (hr : r=7 ∨ r=11 ∨ r=13) :
    sigma 1 (3^a*5^b*r^c) ≠ 2*(3^a*5^b*r^c)+5 := by
  intro heq
  have hp : Nat.Prime r := by rcases hr with rfl | rfl | rfl <;> decide
  have hgt : 5 < r := by omega
  rw [triple_sigma (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) hp (by decide) hgt] at heq
  by_cases hr11 : r = 11
  · subst r
    have hn0 : (2*(3^a*5^b*11^c)) % 3 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_pow_self 3 (by omega : a ≠ 0)) _) _) _
    have hh := congrArg (fun x : ℕ => x % 3) heq
    rw [Nat.add_mod, hn0, Nat.mul_mod, Nat.mul_mod (sigma 1 (3^a)) (sigma 1 (5^b)) 3, three_mod_three,
      five_mod_three b hb', eleven_mod_three c hc'] at hh
    norm_num at hh
  · have hn : 5 ∣ 2*(3^a*5^b*r^c)+5 := by
      apply dvd_add _ (dvd_refl _)
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega : b ≠ 0)) _) _) _
    rw [← heq] at hn
    have prime5 : Nat.Prime 5 := by decide
    rcases prime5.dvd_mul.mp hn with h | h
    · rcases prime5.dvd_mul.mp h with h3 | h5
      · exact (other_mod_five 3 a (Or.inl rfl) ha') (Nat.mod_eq_zero_of_dvd h3)
      · have hz := Nat.mod_eq_zero_of_dvd h5
        rw [five_mod_five b hb'] at hz
        omega
    · exact (other_mod_five r c (by omega) hc') (Nat.mod_eq_zero_of_dvd h)

end SigmaFive

namespace SigmaFive.Modular

private theorem geom_odd_ne_zero (x : ZMod 5) (hx : x ^ 2 = -1) (j : ℕ) :
    (∑ i ∈ range (2 * j + 1), x ^ i) ≠ 0 := by
  intro h
  have he := geom_sum_mul x (2 * j + 1)
  rw [h, zero_mul, eq_comm, sub_eq_zero] at he
  have hh := congrArg (fun y : ZMod 5 => y ^ 2) he
  rw [← pow_mul, mul_comm (2*j+1) 2, pow_mul, hx, one_pow] at hh
  have hodd : Odd (2*j+1) := ⟨j, rfl⟩
  rw [hodd.neg_pow, one_pow] at hh
  exact (by decide : (-1 : ZMod 5) ≠ 1) hh

theorem sigma_other_mod_five (p j : ℕ) (hp : p = 3 ∨ p = 7 ∨ p = 13) :
    sigma 1 (p ^ (2*j)) % 5 ≠ 0 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have hx : (p : ZMod 5) ^ 2 = -1 := by rcases hp with rfl | rfl | rfl <;> decide
  intro h
  have hc : ((sigma 1 (p ^ (2*j)) : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero h)
  rw [sigma_one_apply_prime_pow hprime, Nat.cast_sum] at hc
  push_cast at hc
  exact geom_odd_ne_zero p hx j hc

end SigmaFive.Modular

namespace SigmaFive

theorem odd_four_support {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    4 ≤ n.primeFactors.card := by
  apply odd_four_support_of_modular _ hn h
  apply exclude_triple_from_residues Modular.sigma_three_pow_mod_three
  · intro b hb
    obtain ⟨j, rfl⟩ := hb
    simpa [two_mul] using Modular.sigma_five_pow_mod_three j
  · intro c hc
    obtain ⟨j, rfl⟩ := hc
    simpa [two_mul] using Modular.sigma_eleven_pow_mod_three j
  · intro b hb
    obtain ⟨j, rfl⟩ := hb
    simpa [two_mul] using Modular.sigma_five_pow_mod_five j
  · intro p e hp he
    obtain ⟨j, rfl⟩ := he
    simpa [two_mul] using Modular.sigma_other_mod_five p j hp

end SigmaFive
open Finset ArithmeticFunction

open Finset ArithmeticFunction

namespace SigmaFive.FourBounds

private theorem sigma_bound {p d e : ℕ} (hp : p.Prime) (hd : d ≤ p-1) :
    d * sigma 1 (p ^ e) ≤ (d+1)*p^e := by
  let S := ∑ i ∈ range e, p^i
  have hg : S*(p-1)+1 = p^e := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ p by have := hp.two_le; omega), S] using
      (geom_sum_mul_add (p-1) e)
  have hdS := Nat.mul_le_mul_left S hd
  rw [sigma_one_apply_prime_pow hp, sum_range_succ]
  change d*(S+p^e) ≤ _
  nlinarith

theorem four_sigma {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    sigma 1 (p^a*q^b*r^c*s^d) =
      sigma 1 (p^a)*sigma 1 (q^b)*sigma 1 (r^c)*sigma 1 (s^d) := by
  have h1 : (p^a).Coprime (q^b) := ((Nat.coprime_primes hp hq).2 (by omega)).pow _ _
  have h2 : (p^a).Coprime (r^c) := ((Nat.coprime_primes hp hr).2 (by omega)).pow _ _
  have h3 : (q^b).Coprime (r^c) := ((Nat.coprime_primes hq hr).2 (by omega)).pow _ _
  have hps : (p^a).Coprime (s^d) := ((Nat.coprime_primes hp hs).2 (by omega)).pow _ _
  have hqs : (q^b).Coprime (s^d) := ((Nat.coprime_primes hq hs).2 (by omega)).pow _ _
  have hrs' : (r^c).Coprime (s^d) := ((Nat.coprime_primes hr hs).2 (by omega)).pow _ _
  have h4 : (p^a*q^b*r^c).Coprime (s^d) := by
    simpa only [mul_assoc] using hps.mul_left (hqs.mul_left hrs')

  rw [isMultiplicative_sigma.map_mul_of_coprime h4,
    isMultiplicative_sigma.map_mul_of_coprime (h2.mul_left h3),
    isMultiplicative_sigma.map_mul_of_coprime h1]

theorem four_bound {p q r s a b c d x y z w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hx : x ≤ p-1) (hy : y ≤ q-1) (hz : z ≤ r-1) (hw : w ≤ s-1) :
    x*y*z*w*sigma 1 (p^a*q^b*r^c*s^d) ≤
      (x+1)*(y+1)*(z+1)*(w+1)*(p^a*q^b*r^c*s^d) := by
  rw [four_sigma hp hq hr hs hpq hqr hrs]
  have h1 := sigma_bound (e := a) hp hx
  have h2 := sigma_bound (e := b) hq hy
  have h3 := sigma_bound (e := c) hr hz
  have h4 := sigma_bound (e := d) hs hw
  calc
    x*y*z*w*(sigma 1 (p^a)*sigma 1 (q^b)*sigma 1 (r^c)*sigma 1 (s^d))
      = (x*sigma 1 (p^a))*(y*sigma 1 (q^b))*(z*sigma 1 (r^c))*(w*sigma 1 (s^d)) := by ring
    _ ≤ ((x+1)*p^a)*((y+1)*q^b)*((z+1)*r^c)*((w+1)*s^d) := by
      gcongr
    _ = (x+1)*(y+1)*(z+1)*(w+1)*(p^a*q^b*r^c*s^d) := by ring


/-- The exact quotient equation forces the first three support primes into a short list. -/
theorem first_three_bounds {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hlarge : 3 ≤ p)
    (heq : sigma 1 (p^a*q^b*r^c*s^d) = 2*(p^a*q^b*r^c*s^d)+5) :
    p = 3 ∧ q ≤ 7 ∧ r ≤ 29 := by
  have hN : 0 < p^a*q^b*r^c*s^d := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) (pow_pos hr.pos _)) (pow_pos hs.pos _)
  have hp3 : p = 3 := by
    by_contra hne
    have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro he
        exact (by decide : ¬ Nat.Prime 4) (he ▸ hp)
      omega
    have hq7 : 7 ≤ q := by
      have hq6 : q ≠ 6 := by intro he; exact (by decide : ¬ Nat.Prime 6) (he ▸ hq)
      omega
    have hr11 : 11 ≤ r := by
      have hlo : 8 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> first
        | exact (by decide : ¬ Nat.Prime 8) hr
        | exact (by decide : ¬ Nat.Prime 9) hr
        | exact (by decide : ¬ Nat.Prime 10) hr
    have hs13 : 13 ≤ s := by
      have hlow : 12 ≤ s := by omega
      by_contra! hh
      interval_cases s <;> exact (by decide : ¬ Nat.Prime 12) hs
    have H := four_bound (a := a) (b := b) (c := c) (d := d) hp hq hr hs hpq hqr hrs (x := 4) (y := 6) (z := 10) (w := 12)
      (by omega) (by omega) (by omega) (by omega)
    have HH : 2880 * sigma 1 (p^a*q^b*r^c*s^d) ≤
        5005*(p^a*q^b*r^c*s^d) := by
      have h' := H
      norm_num at h'
      nlinarith [h']
    nlinarith [HH, heq, hN]
  have hq7 : q ≤ 7 := by
    by_contra hne
    have hq11 : 11 ≤ q := by
      have hlow : 8 ≤ q := by omega
      by_contra! hh
      interval_cases q <;> first
        | exact (by decide : ¬ Nat.Prime 8) hq
        | exact (by decide : ¬ Nat.Prime 9) hq
        | exact (by decide : ¬ Nat.Prime 10) hq
    have hr13 : 13 ≤ r := by
      have hlow : 12 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> exact (by decide : ¬ Nat.Prime 12) hr
    have hs15 : 15 ≤ s := by
      have hlow : 14 ≤ s := by omega
      by_contra! hh
      interval_cases s <;> exact (by decide : ¬ Nat.Prime 14) hs
    have H := four_bound (a := a) (b := b) (c := c) (d := d) hp hq hr hs hpq hqr hrs (x := 2) (y := 10) (z := 12) (w := 14)
      (by omega) (by omega) (by omega) (by omega)
    have HH : 3360 * sigma 1 (p^a*q^b*r^c*s^d) ≤
        6435*(p^a*q^b*r^c*s^d) := by
      have h' := H
      norm_num at h'
      nlinarith [h']
    nlinarith [HH, heq, hN]
  have hq5 : 5 ≤ q := by
    have hlow : 4 ≤ q := by omega
    by_contra! hh
    interval_cases q <;> exact (by decide : ¬ Nat.Prime 4) hq
  have hr29 : r ≤ 29 := by
    by_contra hne
    have hr31 : 31 ≤ r := by
      have hlow : 30 ≤ r := by omega
      by_contra! hh
      interval_cases r <;> exact (by decide : ¬ Nat.Prime 30) hr
    have hs33 : 33 ≤ s := by
      have hlow : 32 ≤ s := by omega
      by_contra! hh
      interval_cases s <;> exact (by decide : ¬ Nat.Prime 32) hs
    have H := four_bound (a := a) (b := b) (c := c) (d := d) hp hq hr hs hpq hqr hrs (x := 2) (y := 4) (z := 30) (w := 32)
      (by omega) (by omega) (by omega) (by omega)
    have HH : 7680 * sigma 1 (p^a*q^b*r^c*s^d) ≤
        15345*(p^a*q^b*r^c*s^d) := by
      have h' := H
      norm_num at h'
      nlinarith [h']
    nlinarith [HH, heq, hN]
  exact ⟨hp3,hq7,hr29⟩


private theorem special_four_bound {r b c d : ℕ}
    (hr : Nat.Prime r) (h11or13 : r = 11 ∨ r = 13)
    (hsprime : Nat.Prime sry) (hs257 : 257 ≤ sry) :
    9*4*(r-1)*256 * sigma 1 (3^2*5^b*r^c*sry^d) ≤
      13*5*r*257*(3^2*5^b*r^c*sry^d) := by
  have h1 : 9 * sigma 1 (3^2) ≤ 13*3^2 := by
    rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    norm_num [sum_range_succ]
  have h2 := sigma_bound (e := b) (p := 5) (d := 4) (by decide : Nat.Prime 5) (by decide)
  have h3 := sigma_bound (e := c) (p := r) (d := r-1) hr (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h3
  have h4 := sigma_bound (e := d) (p := sry) (d := 256) hsprime (by omega)
  have hmult :
      (9*sigma 1 (3^2))*(4*sigma 1 (5^b))*((r-1)*sigma 1 (r^c))*(256*sigma 1 (sry^d)) ≤
        (13*3^2)*(5*5^b)*(r*r^c)*(257*sry^d) := by
    have hleft := Nat.mul_le_mul h1 h2
    have hright := Nat.mul_le_mul h3 h4
    simpa [Nat.mul_assoc] using Nat.mul_le_mul hleft hright
  calc
    9*4*(r-1)*256 * sigma 1 (3^2*5^b*r^c*sry^d)
        = (9*sigma 1 (3^2))*(4*sigma 1 (5^b))*((r-1)*sigma 1 (r^c))*(256*sigma 1 (sry^d)) := by
          rw [four_sigma (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) hr hsprime
            (by omega) (by omega) (by omega)]
          ring
    _ ≤ (13*3^2)*(5*5^b)*(r*r^c)*(257*sry^d) := hmult
    _ = 13*5*r*257*(3^2*5^b*r^c*sry^d) := by ring

/-- A coarse upper-ratio estimate bounds the fourth support prime once the small
prefix cases are removed by the exact finite lower bounds. -/
theorem fourth_prime_bound {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (heq : sigma 1 (p^a*q^b*r^c*s^d) = 2*(p^a*q^b*r^c*s^d)+5)
    (hp3 : p = 3) (hqcase : q = 5 ∨ q = 7)
    (h5 : q = 5 → (r = 11 ∧ a = 2) ∨ (r = 13 ∧ a = 2) ∨ 17 ≤ r)
    (h7 : q = 7 → 11 ≤ r) : s ≤ 251 := by
  by_contra! hcap
  have hs257 : 257 ≤ s := by
    have hlow : 252 ≤ s := hcap
    by_contra! hs256
    have hsodd := hs.odd_of_ne_two (by omega)
    have hsne253 : s ≠ 253 := by
      intro hv
      have hdiv : 11 ∣ s := by rw [hv]; norm_num
      have heq := hs.eq_one_or_self_of_dvd 11 hdiv
      omega
    have hsne255 : s ≠ 255 := by
      intro hv
      have hdiv : 3 ∣ s := by rw [hv]; norm_num
      have heq := hs.eq_one_or_self_of_dvd 3 hdiv
      omega
    obtain ⟨k, hk⟩ := hsodd
    omega
  subst p
  rcases hqcase with hq5 | hq7
  · subst q
    rcases h5 rfl with ⟨r11, ha⟩ | ⟨r13, ha⟩ | hr17
    · subst r a
      have H := special_four_bound (r := 11) (b := b) (c := c) (d := d) (sry := s) (by simpa using hr) (Or.inl rfl) hs hs257
      have h' : 92160 * sigma 1 (3^2*5^b*11^c*s^d) ≤
          183755*(3^2*5^b*11^c*s^d) := by
        have := H
        norm_num at this ⊢
        exact this
      nlinarith [h', heq]
    · subst r a
      have H := special_four_bound (r := 13) (b := b) (c := c) (d := d) (sry := s) (by simpa using hr) (Or.inr rfl) hs hs257
      have h' : 110592 * sigma 1 (3^2*5^b*13^c*s^d) ≤
          217165*(3^2*5^b*13^c*s^d) := by
        have := H
        norm_num at this ⊢
        exact this
      nlinarith [h', heq]
    · have H := four_bound (a := a) (b := b) (c := c) (d := d)
        (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) hr hs
        (by norm_num : 3 < 5) (by omega : 5 < r) (by omega : r < s)
        (by omega) (by norm_num) (by omega) (by omega)
        (x := 2) (y := 4) (z := 16) (w := 256)
      have h' : 32768 * sigma 1 (3^a*5^b*r^c*s^d) ≤
          65535*(3^a*5^b*r^c*s^d) := by
        have := H
        norm_num at this ⊢
        exact this
      nlinarith [h', heq]
  · subst q
    have hr11 : 11 ≤ r := h7 rfl
    have H := four_bound (a := a) (b := b) (c := c) (d := d)
      (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) hr hs
      (by norm_num : 3 < 7) (by omega : 7 < r) (by omega : r < s)
      (by omega) (by omega) (by omega) (by omega)
      (x := 2) (y := 6) (z := 10) (w := 256)
    have h' : 30720 * sigma 1 (3^a*7^b*r^c*s^d) ≤
        59367*(3^a*7^b*r^c*s^d) := by
      have := H
      norm_num at this ⊢
      exact this
    nlinarith [h', heq]

end SigmaFive.FourBounds


namespace SigmaFive.FourBounds

theorem four_quotient_even {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : sigma 1 (p^a*q^b*r^c*s^d) % (p^a*q^b*r^c*s^d) = 5) :
    sigma 1 (p^a*q^b*r^c*s^d) = 2*(p^a*q^b*r^c*s^d)+5 ∧
      Even a ∧ Even b ∧ Even c ∧ Even d := by
  have hOdd {v : ℕ} (hv : v.Prime) (hv3 : 3 ≤ v) : Odd v :=
    hv.odd_of_ne_two (by omega)
  have q5 : 5 ≤ q := by have := Nat.odd_iff.mp (hOdd hq (by omega)); omega
  have r7 : 7 ≤ r := by have := Nat.odd_iff.mp (hOdd hr (by omega)); omega
  have s11 : 11 ≤ s := by
    have hsodd := Nat.odd_iff.mp (hOdd hs (by omega))
    by_contra! hh
    have he : s = 9 := by omega
    exact (by decide : ¬ Nat.Prime 9) (he ▸ hs)
  let P := p^a
  let Q := q^b
  let R := r^c
  let S := s^d
  let N := P*Q*R*S
  let F := sigma 1 N
  have hBound := four_bound (a := a) (b := b) (c := c) (d := d) hp hq hr hs hpq hqr hrs
    (x := 2) (y := 4) (z := 6) (w := 10) (by omega) (by omega) (by omega) (by omega)
  change 480*F ≤ 1155*N at hBound
  have hl : N+5 < F := by
    have L : (P+1)*Q*R*S ≤ F := by
      dsimp only [F,N,P,Q,R,S]
      rw [four_sigma hp hq hr hs hpq hqr hrs]
      have hP := SigmaFive.pow_lt_sigma hp ha
      have hQ := (SigmaFive.pow_lt_sigma hq hb).le
      have hR := (SigmaFive.pow_lt_sigma hr hc).le
      have hS := (SigmaFive.pow_lt_sigma hs hd).le
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hP hQ) hR) hS
    have Q5 : 5 ≤ Q := q5.trans (by simpa [Q] using Nat.pow_le_pow_right hq.pos hb)
    have R7 : 7 ≤ R := r7.trans (by simpa [R] using Nat.pow_le_pow_right hr.pos hc)
    have S11 : 11 ≤ S := s11.trans (by simpa [S] using Nat.pow_le_pow_right hs.pos hd)
    have hRest : 385 ≤ Q*R*S := Nat.mul_le_mul (Nat.mul_le_mul Q5 R7) S11
    dsimp only [N]
    nlinarith only [L, hRest]
  change F % N = 5 at h
  have hdiv := Nat.mod_add_div F N
  rw [h] at hdiv
  have hklo : 2 ≤ F/N := by
    by_contra! hh
    have := Nat.mul_le_mul_left N (show F/N ≤ 1 by omega)
    omega
  have hkhi : F/N ≤ 2 := by
    by_contra! hh
    have := Nat.mul_le_mul_left N hh
    omega
  have hk : F/N = 2 := by omega
  rw [hk] at hdiv
  have heq : F = 2*N+5 := by omega
  have hodd : Odd F := by
    rw [heq]
    exact ⟨N+2, by omega⟩
  change Odd (sigma 1 (p^a*q^b*r^c*s^d)) at hodd
  rw [four_sigma hp hq hr hs hpq hqr hrs, Nat.odd_mul, Nat.odd_mul, Nat.odd_mul] at hodd
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hodd
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · exact SigmaFive.even_exp_of_odd_sigma hp (Nat.odd_iff.mp (hOdd hp hp3)) hA
  · exact SigmaFive.even_exp_of_odd_sigma hq (Nat.odd_iff.mp (hOdd hq (by omega))) hB
  · exact SigmaFive.even_exp_of_odd_sigma hr (Nat.odd_iff.mp (hOdd hr (by omega))) hC
  · exact SigmaFive.even_exp_of_odd_sigma hs (Nat.odd_iff.mp (hOdd hs (by omega))) hD

end SigmaFive.FourBounds
open Finset ArithmeticFunction

namespace SigmaFive.Four

private def ratio (p e : ℕ) : ℚ := (sigma 1 (p^e) : ℚ) / (p : ℚ)^e

theorem ratio_eq {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ratio p e = ((p : ℚ) - ((p : ℚ)^e)⁻¹) / ((p : ℚ) - 1) := by
  let S := ∑ i ∈ range e, p^i
  have hgeom : S * (p-1) + 1 = p^e := by
    simpa only [Nat.sub_add_cancel (by have := hp.two_le; omega : 1 ≤ p), S] using
      geom_sum_mul_add (p-1) e
  have hS := congrArg (fun k : ℕ => (k : ℚ)) hgeom
  push_cast [Nat.cast_sub (by have := hp.two_le; omega : 1 ≤ p)] at hS
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p from hp.two_le)
  rw [ratio, sigma_one_apply_prime_pow hp, sum_range_succ]
  change ((S+p^e : ℕ) : ℚ) / (p : ℚ)^e = _
  push_cast
  field_simp [ne_of_gt (sub_pos.mpr hp1), ne_of_gt (pow_pos hp0 e)]
  nlinarith [hS]

theorem ratio_mono {p a b : ℕ} (hp : p.Prime) (hab : a ≤ b) :
    ratio p a ≤ ratio p b := by
  rw [ratio_eq hp, ratio_eq hp]
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p from hp.two_le)
  have hpow : (p : ℚ)^a ≤ (p : ℚ)^b := pow_le_pow_right₀ hp1.le hab
  have hpos : 0 < (p : ℚ)^a := pow_pos (by linarith) _
  exact div_le_div_of_nonneg_right (sub_le_sub_left (inv_anti₀ hpos hpow) _) (by linarith)

theorem ratio_upper {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ratio p e ≤ (p : ℚ) / ((p : ℚ)-1) := by
  rw [ratio_eq hp]
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p from hp.two_le)
  have hinv : 0 ≤ ((p : ℚ)^e)⁻¹ := by positivity
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem box_sound {ι : Type*} (I : Finset ι) (p e t : ι → ℕ)
    (hp : ∀ i ∈ I, (p i).Prime) (ht : ∀ i ∈ I, t i ≤ e i)
    (he : ∀ i ∈ I, t i < 10 → t i = e i)
    (hbox :
      (∏ i ∈ I, if t i < 10 then ratio (p i) (t i) else
        (p i : ℚ) / ((p i : ℚ) - 1)) ≤ 2 ∨
      2 + 5 / (∏ i ∈ I, (p i : ℚ) ^ t i) < ∏ i ∈ I, ratio (p i) (t i)) :
    (∏ i ∈ I, ratio (p i) (e i)) ≠ 2 + 5 / (∏ i ∈ I, (p i : ℚ) ^ e i) := by
  have hbase (i) (hi : i ∈ I) : (1 : ℚ) < p i := by
    exact_mod_cast (show 1 < p i from (hp i hi).two_le)
  have hpos (f : ι → ℕ) : 0 < ∏ i ∈ I, (p i : ℚ) ^ f i :=
    prod_pos fun i hi => pow_pos (by linarith [hbase i hi]) _
  have hnonneg (i : ι) (j : ℕ) : 0 ≤ ratio (p i) j := by unfold ratio; positivity
  intro heq
  rcases hbox with hU | hL
  · have hu : (∏ i ∈ I, ratio (p i) (e i)) ≤
          ∏ i ∈ I, if t i < 10 then ratio (p i) (t i) else
            (p i : ℚ) / ((p i : ℚ) - 1) := by
      apply prod_le_prod (fun i _ => hnonneg i (e i))
      intro i hi
      split_ifs with hi'
      · rw [he i hi hi']
      · exact ratio_upper (hp i hi) _
    have hf : 0 < (5 : ℚ) / (∏ i ∈ I, (p i : ℚ) ^ e i) := div_pos (by norm_num) (hpos e)
    linarith
  · have hl : (∏ i ∈ I, ratio (p i) (t i)) ≤ ∏ i ∈ I, ratio (p i) (e i) :=
      prod_le_prod (fun i _ => hnonneg i (t i)) fun i hi => ratio_mono (hp i hi) (ht i hi)
    have hn : (∏ i ∈ I, (p i : ℚ) ^ t i) ≤ ∏ i ∈ I, (p i : ℚ) ^ e i := by
      apply prod_le_prod (fun _ _ => by positivity)
      exact fun i hi => pow_le_pow_right₀ (hbase i hi).le (ht i hi)
    have hf : (5 : ℚ) / (∏ i ∈ I, (p i : ℚ) ^ e i) ≤ 5 / (∏ i ∈ I, (p i : ℚ) ^ t i) :=
      div_le_div_of_nonneg_left (by norm_num) (hpos t) hn
    linarith


theorem ratio_prod_of_factorization {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, ratio p (n.factorization p)) = ratio n 1 := by
  unfold ratio
  rw [prod_div_distrib, pow_one, pow_one]
  norm_cast
  have hσ : sigma 1 n = ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) :=
    isMultiplicative_sigma.multiplicative_factorization _ hn
  rw [← Nat.prod_primeFactors_pow_factorization hn, ← hσ]

theorem prod_of_ratio_eq {n : ℕ} (hn : n ≠ 0) (hs : sigma 1 n = 2*n+5) :
    (∏ p ∈ n.primeFactors, ratio p (n.factorization p)) =
      2 + 5 / (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) := by
  have hf : (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  rw [ratio_prod_of_factorization hn, hf, ratio, pow_one, pow_one, hs]
  push_cast
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp


theorem odd_four_product {n : ℕ} (hn : Odd n) (hc : n.primeFactors.card = 4) :
    ∃ (p q r s a b c d : ℕ),
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      3 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      n = p^a*q^b*r^c*s^d := by
  let f := n.primeFactors.orderEmbOfFin hc
  have hmem (i : Fin 4) : f i ∈ n.primeFactors :=
    Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 4) : (f i).Prime := Nat.prime_of_mem_primeFactors (hmem i)
  have hne : n ≠ 0 := by obtain ⟨k, hk⟩ := hn; omega
  have he (i : Fin 4) : 0 < n.factorization (f i) :=
    (hp i).factorization_pos_of_dvd hne (Nat.dvd_of_mem_primeFactors (hmem i))
  have h3 : 3 ≤ f 0 := by
    have h2 := (hp 0).two_le
    by_contra! hn3
    have heq : f 0 = 2 := by omega
    exact hn.not_two_dvd_nat (heq ▸ Nat.dvd_of_mem_primeFactors (hmem 0))
  have hprod := Nat.prod_primeFactors_pow_factorization hne
  rw [← Finset.map_orderEmbOfFin_univ _ hc, Finset.prod_map] at hprod
  change n = ∏ i : Fin 4, f i ^ n.factorization (f i) at hprod
  rw [Fin.prod_univ_four] at hprod
  refine ⟨f 0, f 1, f 2, f 3, _, _, _, _, hp 0, hp 1, hp 2, hp 3, h3,
    f.strictMono (by decide), f.strictMono (by decide), f.strictMono (by decide),
    he 0, he 1, he 2, he 3, ?_⟩
  simpa only [mul_assoc] using hprod


end SigmaFive.Four
namespace SigmaFive.Four

private def exponents : List ℕ := [2,4,6,8,10]

theorem min_mem_exponents {a : ℕ} (ha : 0 < a) (he : Even a) :
    min a 10 ∈ exponents := by
  obtain ⟨k, hk⟩ := he
  have hm : min a 10 = 2 ∨ min a 10 = 4 ∨ min a 10 = 6 ∨
      min a 10 = 8 ∨ min a 10 = 10 := by omega
  simpa [exponents] using hm

theorem eq_of_min_lt {a : ℕ} (ha : min a 10 < 10) :
    min a 10 = a := by omega

end SigmaFive.Four

namespace SigmaFive.Four

theorem explicit_box_sound {p q r s a b c d A B C D : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hA : A ≤ a) (hB : B ≤ b) (hC : C ≤ c) (hD : D ≤ d)
    (hAa : A < 10 → A = a) (hBb : B < 10 → B = b)
    (hCc : C < 10 → C = c) (hDd : D < 10 → D = d)
    (hbox :
      (if A < 10 then ratio p A else (p : ℚ) / ((p : ℚ) - 1)) *
      (if B < 10 then ratio q B else (q : ℚ) / ((q : ℚ) - 1)) *
      (if C < 10 then ratio r C else (r : ℚ) / ((r : ℚ) - 1)) *
      (if D < 10 then ratio s D else (s : ℚ) / ((s : ℚ) - 1)) ≤ 2 ∨
      2 + 5 / ((p : ℚ)^A*(q : ℚ)^B*(r : ℚ)^C*(s : ℚ)^D) <
      ratio p A * ratio q B * ratio r C * ratio s D) :
    sigma 1 (p^a*q^b*r^c*s^d) ≠ 2*(p^a*q^b*r^c*s^d)+5 := by
  let primes : Fin 4 → ℕ := ![p,q,r,s]
  let actual : Fin 4 → ℕ := ![a,b,c,d]
  let clipped : Fin 4 → ℕ := ![A,B,C,D]
  have noBox := box_sound (univ : Finset (Fin 4)) primes actual clipped
    (by intro i _; fin_cases i <;> assumption)
    (by intro i _; fin_cases i <;> assumption)
    (by intro i _; fin_cases i <;> assumption)
    (by
      simp only [Fin.prod_univ_four, primes, clipped, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      by_cases hA : A < 10 <;> by_cases hB : B < 10 <;> by_cases hC : C < 10 <;>
        by_cases hD : D < 10 <;> simpa only [hA, hB, hC, hD, if_true, if_false] using hbox)
  intro heq
  apply noBox
  simp [Fin.prod_univ_four, primes, actual]
  have hc : (sigma 1 (p^a*q^b*r^c*s^d) : ℚ) =
      2*((p : ℚ)^a*(q : ℚ)^b*(r : ℚ)^c*(s : ℚ)^d)+5 := by exact_mod_cast heq
  rw [FourBounds.four_sigma hp hq hr hs hpq hqr hrs] at hc
  push_cast at hc
  unfold ratio
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne_zero
  field_simp [hp0,hq0,hr0,hs0]
  nlinarith only [hc]


end SigmaFive.Four

namespace SigmaFive.Four

theorem no_small_prefix {r s a b c d A : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hqr : 5 < r) (hrs : r < s)
    (ha : A ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hbad : 2 + 5 / ((3 : ℚ)^A * (5 : ℚ)^2 * (r : ℚ)^2) <
      ratio 3 A * ratio 5 2 * ratio r 2) :
    sigma 1 (3^a*5^b*r^c*s^d) ≠ 2*(3^a*5^b*r^c*s^d)+5 := by
  intro heq
  let primes : Fin 4 → ℕ := ![3,5,r,s]
  let mins : Fin 4 → ℕ := ![A,2,2,0]
  let actual : Fin 4 → ℕ := ![a,b,c,d]
  have hp (i : Fin 4) : (primes i).Prime := by
    fin_cases i
    · exact (by decide : Nat.Prime 3)
    · exact (by decide : Nat.Prime 5)
    · exact hr
    · exact hs
  have he (i : Fin 4) : mins i ≤ actual i := by fin_cases i <;> first | assumption | exact Nat.zero_le _
  have hcl : ∏ i, ratio (primes i) (mins i) ≤ ∏ i, ratio (primes i) (actual i) :=
    prod_le_prod (fun _ _ => by unfold ratio; positivity)
      fun i _ => ratio_mono (hp i) (he i)
  have hden : (∏ i, (primes i : ℚ)^mins i) ≤ ∏ i, (primes i : ℚ)^actual i := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro i _
    have hh : (1 : ℚ) ≤ primes i := by exact_mod_cast (show 1 ≤ primes i from (hp i).two_le.trans' (by decide))
    exact pow_le_pow_right₀ hh (he i)
  have hn : 0 < ∏ i, (primes i : ℚ)^mins i := by
    apply prod_pos
    intro i _
    have hh : (0 : ℚ) < primes i := by exact_mod_cast (hp i).pos
    exact pow_pos hh _
  have hf : (5 : ℚ) / (∏ i, (primes i : ℚ)^actual i) ≤ 5 / (∏ i, (primes i : ℚ)^mins i) :=
    div_le_div_of_nonneg_left (by norm_num) hn hden
  have hq : (∏ i, ratio (primes i) (actual i)) = 2 + 5 / (∏ i, (primes i : ℚ)^actual i) := by
    simp [Fin.prod_univ_four, primes, actual]
    have hcast : (sigma 1 (3^a*5^b*r^c*s^d) : ℚ) =
      2*((3 : ℚ)^a*(5 : ℚ)^b*(r : ℚ)^c*(s : ℚ)^d)+5 := by exact_mod_cast heq
    rw [FourBounds.four_sigma (by decide) (by decide) hr hs (by decide) hqr hrs] at hcast
    push_cast at hcast
    unfold ratio
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne_zero
    norm_num only [Nat.cast_ofNat]
    field_simp [hr0,hs0, show (3 : ℚ) ≠ 0 by decide, show (5 : ℚ) ≠ 0 by decide]
    nlinarith only [hcast]
  have hb' : 2 + 5 / (∏ i, (primes i : ℚ)^mins i) < ∏ i, ratio (primes i) (mins i) := by
    have hS : ratio s 0 = 1 := by simp [ratio]
    simp only [Fin.prod_univ_four, primes, mins, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      pow_zero, mul_one, hS]
    simpa only [mul_assoc, Nat.cast_ofNat] using hbad
  linarith

theorem small_prefix_restrictions {r s a b c d : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hqr : 5 < r) (hrs : r < s)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hae : Even a)
    (heq : sigma 1 (3^a*5^b*r^c*s^d) = 2*(3^a*5^b*r^c*s^d)+5) :
    r ≠ 7 ∧ ((r = 11 ∨ r = 13) → a = 2) := by
  constructor
  · rintro rfl
    exact no_small_prefix hr hs hqr hrs ha hb hc (by decide +kernel) heq
  · intro hR
    by_contra! hA
    obtain ⟨k, hk⟩ := hae
    have h4 : 4 ≤ a := by omega
    rcases hR with rfl | rfl
    · exact no_small_prefix hr hs hqr hrs h4 hb hc (by decide +kernel) heq
    · exact no_small_prefix hr hs hqr hrs h4 hb hc (by decide +kernel) heq


end SigmaFive.Four

namespace SigmaFive.Four

theorem fourth_cap_inputs {q r s a b c d : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (hq3 : 3 < q) (hqr : q < r) (hrs : r < s)
    (hq7 : q ≤ 7) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hae : Even a)
    (heq : sigma 1 (3^a*q^b*r^c*s^d) = 2*(3^a*q^b*r^c*s^d)+5) :
    (q = 5 ∨ q = 7) ∧
    (q = 5 → (r = 11 ∧ a = 2) ∨ (r = 13 ∧ a = 2) ∨ 17 ≤ r) ∧
    (q = 7 → 11 ≤ r) := by
  have hq' : q = 5 ∨ q = 7 := by
    interval_cases q <;> first | omega | (exfalso; revert hq; decide)
  refine ⟨hq', ?_, ?_⟩
  · rintro rfl
    obtain ⟨hne, hexp⟩ := small_prefix_restrictions hr hs hqr hrs ha hb hc hae heq
    by_cases h11 : r = 11
    · exact Or.inl ⟨h11, hexp (Or.inl h11)⟩
    by_cases h13 : r = 13
    · exact Or.inr (Or.inl ⟨h13, hexp (Or.inr h13)⟩)
    right; right
    by_contra! h
    interval_cases r <;> first | omega | revert hr <;> decide
  · rintro rfl
    by_contra! h
    interval_cases r <;> revert hr <;> decide

end SigmaFive.Four

namespace SigmaFive.Four

private def upperRatio (p e : ℕ) : ℚ :=
  if e < 10 then ratio p e else (p : ℚ) / ((p : ℚ) - 1)

private def clipsSeparated (q r s A B C D : ℕ) : Prop :=
    upperRatio 3 A * upperRatio q B * upperRatio r C * upperRatio s D ≤ 2 ∨
    2 + 5 / ((3 : ℚ)^A*(q : ℚ)^B*(r : ℚ)^C*(s : ℚ)^D) <
      ratio 3 A * ratio q B * ratio r C * ratio s D

theorem odd_five_support_of_boxes
    (cert : ∀ q r s A B C D : ℕ,
      q.Prime → r.Prime → s.Prime → (q = 5 ∨ q = 7) → q < r → r < s →
      r ≤ 29 → s ≤ 251 → (q = 5 → r ≠ 7) →
      (q = 5 → (r = 11 ∨ r = 13) → A = 2) →
      A ∈ exponents → B ∈ exponents → C ∈ exponents → D ∈ exponents →
      clipsSeparated q r s A B C D)
    {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    5 ≤ n.primeFactors.card := by
  have h4 := SigmaFive.odd_four_support hn h
  by_contra! h5
  obtain ⟨p,q,r,s,a,b,c,d,hp,hq,hr,hs,hp3,hpq,hqr,hrs,ha,hb,hc,hd,rfl⟩ :=
    odd_four_product hn (show n.primeFactors.card = 4 by omega)
  obtain ⟨heq, hae, hbe, hce, hde⟩ :=
    FourBounds.four_quotient_even hp hq hr hs hp3 hpq hqr hrs ha hb hc hd h
  obtain ⟨rfl,hq7,hr29⟩ := FourBounds.first_three_bounds hp hq hr hs hpq hqr hrs hp3 heq
  have ha2 : 2 ≤ a := by obtain ⟨k,hk⟩ := hae; omega
  have hb2 : 2 ≤ b := by obtain ⟨k,hk⟩ := hbe; omega
  have hc2 : 2 ≤ c := by obtain ⟨k,hk⟩ := hce; omega
  obtain ⟨hqcase,hq5,hq7'⟩ := fourth_cap_inputs hq hr hs hpq hqr hrs hq7 ha2 hb2 hc2 hae heq
  have hs251 := FourBounds.fourth_prime_bound hp hq hr hs hpq hqr hrs heq rfl hqcase hq5 hq7'
  have hrne : q = 5 → r ≠ 7 := by
    intro hq' hr'
    have h := hq5 hq'
    omega
  have ha' : q = 5 → (r = 11 ∨ r = 13) → min a 10 = 2 := by
    intro hq' hr'
    have h := hq5 hq'
    omega
  have hbox := cert q r s (min a 10) (min b 10) (min c 10) (min d 10)
    hq hr hs hqcase hqr hrs hr29 hs251 hrne ha'
    (min_mem_exponents ha hae) (min_mem_exponents hb hbe)
    (min_mem_exponents hc hce) (min_mem_exponents hd hde)
  exact explicit_box_sound hp hq hr hs hpq hqr hrs
    (min_le_left _ _) (min_le_left _ _) (min_le_left _ _) (min_le_left _ _)
    eq_of_min_lt eq_of_min_lt eq_of_min_lt eq_of_min_lt hbox heq


end SigmaFive.Four

namespace SigmaFive.Four

theorem ratio_as_cross {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ratio p e = ((p^(e+1)-1 : ℕ) : ℚ) / (p^e*(p-1) : ℕ) := by
  rw [ratio_eq hp]
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (show 1 < p from hp.two_le)
  have hp0 : (0 : ℚ) < p := by linarith
  have hpow : 1 ≤ p^(e+1) := Nat.one_le_pow _ _ hp.pos
  have hm : 1 ≤ p := hp.pos
  rw [Nat.cast_sub hpow]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hm, Nat.cast_one, pow_succ]
  field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp1)]

theorem cross_lower {L M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (h : M*(2*N+5) < N*L) :
    2 + 5 / (N : ℚ) < (L : ℚ) / M := by
  have hm : (0 : ℚ) < M := by exact_mod_cast hM
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hh : (M : ℚ)*(2*N+5) < (N : ℚ)*L := by exact_mod_cast h
  apply (lt_div_iff₀ hm).2
  apply (lt_of_mul_lt_mul_right _ hn.le)
  calc
    ((2 + 5 / (N : ℚ)) * M) * N = (M : ℚ)*(2*N+5) := by field_simp
    _ < (N : ℚ)*L := hh
    _ = (L : ℚ)*N := mul_comm _ _

theorem cross_upper {U V : ℕ} (hV : 0 < V) (h : U ≤ 2*V) :
    (U : ℚ) / V ≤ 2 := by
  have hv : (0 : ℚ) < V := by exact_mod_cast hV
  exact (div_le_iff₀ hv).2 (by exact_mod_cast h)


end SigmaFive.Four
namespace FourSigmaCertificate

/-- One prime support with its four clipped even exponents. -/
private structure Box where
  primes : List Nat
  upperExp : List (Option Nat)
  minExp : List Nat
  deriving DecidableEq, Repr

private abbrev Support := Nat × Nat × Nat × Nat
private abbrev ExponentTuple := Nat × Nat × Nat × Nat

private def product (xs : List Nat) : Nat := xs.foldl (· * ·) 1

private def factorNum (p : Nat) (e : Option Nat) : Nat :=
  match e with
  | none => p
  | some k => p ^ (k + 1) - 1

private def factorDen (p : Nat) (e : Option Nat) : Nat :=
  match e with
  | none => p - 1
  | some k => p ^ k * (p - 1)

private def ratioNum (ps : List Nat) (es : List (Option Nat)) : Nat :=
  product (List.zipWith factorNum ps es)

private def ratioDen (ps : List Nat) (es : List (Option Nat)) : Nat :=
  product (List.zipWith factorDen ps es)

private def lowerSize (ps : List Nat) (es : List Nat) : Nat :=
  product (List.zipWith (fun p e => p ^ e) ps es)

/-- Cross multiplication checks H ≤ 2 or H > 2 + 5/n using natural numbers. -/
private def Box.check (b : Box) : Bool :=
  ratioNum b.primes b.upperExp <= 2 * ratioDen b.primes b.upperExp ||
    let n := lowerSize b.primes b.minExp
    n * ratioNum b.primes (b.minExp.map some) >
      ratioDen b.primes (b.minExp.map some) * (2 * n + 5)

private def primesUpTo251 : List Nat :=
  (List.range 252).filter (fun n => decide n.Prime)

private def firstExp (q r : Nat) : Option Nat :=
  if q == 5 && (r == 11 || r == 13) then some 2 else none

private def prefixNum (q r : Nat) : Nat := factorNum 3 (firstExp q r) * q * r

private def prefixDen (q r : Nat) : Nat := factorDen 3 (firstExp q r) * (q - 1) * (r - 1)

/-- The nested support filter from the screen, with the proved prime cap 251. -/
private def candidateSupports : List (Nat × Nat × Nat × Nat) :=
  [5, 7].flatMap fun q =>
    primesUpTo251.filter (fun r => q < r && r < 31 && !(q == 5 && r == 7)) |>.flatMap fun r =>
      primesUpTo251.filter (fun s =>
        r < s && prefixNum q r < 2 * prefixDen q r &&
          prefixNum q r * s > 2 * prefixDen q r * (s - 1)) |>.map fun s =>
            (3, q, r, s)

private def clippedExponents : List Nat := [2, 4, 6, 8, 10]

private def exponents (xs ys zs ws : List Nat) : List ExponentTuple :=
  xs.flatMap fun a => ys.flatMap fun b => zs.flatMap fun c => ws.map fun d => (a, b, c, d)

private def makeBox (support : Support) (es : ExponentTuple) : Box :=
  let (p, q, r, s) := support
  let (a, b, c, d) := es
  let fixed := firstExp q r
  let upper e := if e == 10 then none else some e
  { primes := [p, q, r, s]
    upperExp := [if fixed.isSome then some 2 else upper a, upper b, upper c, upper d]
    minExp := [a, b, c, d] }

private def exponentsForSupport (support : Support) : List ExponentTuple :=
  let (_, q, r, _) := support
  let first := if firstExp q r == some 2 then [2] else clippedExponents
  exponents first clippedExponents clippedExponents clippedExponents

private def boxesForSupport (support : Support) : List Box :=
  (exponentsForSupport support).map (makeBox support)

/-- All clipped exponent boxes, with the two special p₁ exponents fixed at 2. -/
private def boxes : List Box :=
  candidateSupports.flatMap boxesForSupport

theorem support_count : candidateSupports.length = 113 := by decide +kernel

theorem boxes_length : boxes.length = 52125 := by decide +kernel

private def supportRows : List Support := [
  (3, 5, 11, 13),
  (3, 5, 11, 17),
  (3, 5, 11, 19),
  (3, 5, 11, 23),
  (3, 5, 11, 29),
  (3, 5, 11, 31),
  (3, 5, 11, 37),
  (3, 5, 11, 41),
  (3, 5, 11, 43),
  (3, 5, 11, 47),
  (3, 5, 11, 53),
  (3, 5, 11, 59),
  (3, 5, 11, 61),
  (3, 5, 11, 67),
  (3, 5, 11, 71),
  (3, 5, 11, 73),
  (3, 5, 11, 79),
  (3, 5, 11, 83),
  (3, 5, 11, 89),
  (3, 5, 11, 97),
  (3, 5, 11, 101),
  (3, 5, 11, 103),
  (3, 5, 11, 107),
  (3, 5, 11, 109),
  (3, 5, 11, 113),
  (3, 5, 11, 127),
  (3, 5, 11, 131),
  (3, 5, 11, 137),
  (3, 5, 11, 139),
  (3, 5, 13, 17),
  (3, 5, 13, 19),
  (3, 5, 13, 23),
  (3, 5, 13, 29),
  (3, 5, 13, 31),
  (3, 5, 13, 37),
  (3, 5, 13, 41),
  (3, 5, 13, 43),
  (3, 5, 17, 19),
  (3, 5, 17, 23),
  (3, 5, 17, 29),
  (3, 5, 17, 31),
  (3, 5, 17, 37),
  (3, 5, 17, 41),
  (3, 5, 17, 43),
  (3, 5, 17, 47),
  (3, 5, 17, 53),
  (3, 5, 17, 59),
  (3, 5, 17, 61),
  (3, 5, 17, 67),
  (3, 5, 17, 71),
  (3, 5, 17, 73),
  (3, 5, 17, 79),
  (3, 5, 17, 83),
  (3, 5, 17, 89),
  (3, 5, 17, 97),
  (3, 5, 17, 101),
  (3, 5, 17, 103),
  (3, 5, 17, 107),
  (3, 5, 17, 109),
  (3, 5, 17, 113),
  (3, 5, 17, 127),
  (3, 5, 17, 131),
  (3, 5, 17, 137),
  (3, 5, 17, 139),
  (3, 5, 17, 149),
  (3, 5, 17, 151),
  (3, 5, 17, 157),
  (3, 5, 17, 163),
  (3, 5, 17, 167),
  (3, 5, 17, 173),
  (3, 5, 17, 179),
  (3, 5, 17, 181),
  (3, 5, 17, 191),
  (3, 5, 17, 193),
  (3, 5, 17, 197),
  (3, 5, 17, 199),
  (3, 5, 17, 211),
  (3, 5, 17, 223),
  (3, 5, 17, 227),
  (3, 5, 17, 229),
  (3, 5, 17, 233),
  (3, 5, 17, 239),
  (3, 5, 17, 241),
  (3, 5, 17, 251),
  (3, 5, 19, 23),
  (3, 5, 19, 29),
  (3, 5, 19, 31),
  (3, 5, 19, 37),
  (3, 5, 19, 41),
  (3, 5, 19, 43),
  (3, 5, 19, 47),
  (3, 5, 19, 53),
  (3, 5, 19, 59),
  (3, 5, 19, 61),
  (3, 5, 19, 67),
  (3, 5, 19, 71),
  (3, 5, 19, 73),
  (3, 5, 19, 79),
  (3, 5, 19, 83),
  (3, 5, 19, 89),
  (3, 5, 23, 29),
  (3, 5, 23, 31),
  (3, 5, 23, 37),
  (3, 5, 23, 41),
  (3, 5, 23, 43),
  (3, 5, 23, 47),
  (3, 5, 29, 31),
  (3, 7, 11, 13),
  (3, 7, 11, 17),
  (3, 7, 11, 19),
  (3, 7, 11, 23),
  (3, 7, 13, 17),
  (3, 7, 13, 19)
]

theorem supportCheck0 : (boxesForSupport (3, 5, 11, 13)).all Box.check = true := by decide +kernel

theorem supportCheck1 : (boxesForSupport (3, 5, 11, 17)).all Box.check = true := by decide +kernel

theorem supportCheck2 : (boxesForSupport (3, 5, 11, 19)).all Box.check = true := by decide +kernel

theorem supportCheck3 : (boxesForSupport (3, 5, 11, 23)).all Box.check = true := by decide +kernel

theorem supportCheck4 : (boxesForSupport (3, 5, 11, 29)).all Box.check = true := by decide +kernel

theorem supportCheck5 : (boxesForSupport (3, 5, 11, 31)).all Box.check = true := by decide +kernel

theorem supportCheck6 : (boxesForSupport (3, 5, 11, 37)).all Box.check = true := by decide +kernel

theorem supportCheck7 : (boxesForSupport (3, 5, 11, 41)).all Box.check = true := by decide +kernel

theorem supportCheck8 : (boxesForSupport (3, 5, 11, 43)).all Box.check = true := by decide +kernel

theorem supportCheck9 : (boxesForSupport (3, 5, 11, 47)).all Box.check = true := by decide +kernel

theorem supportCheck10 : (boxesForSupport (3, 5, 11, 53)).all Box.check = true := by decide +kernel

theorem supportCheck11 : (boxesForSupport (3, 5, 11, 59)).all Box.check = true := by decide +kernel

theorem supportCheck12 : (boxesForSupport (3, 5, 11, 61)).all Box.check = true := by decide +kernel

theorem supportCheck13 : (boxesForSupport (3, 5, 11, 67)).all Box.check = true := by decide +kernel

theorem supportCheck14 : (boxesForSupport (3, 5, 11, 71)).all Box.check = true := by decide +kernel

theorem supportCheck15 : (boxesForSupport (3, 5, 11, 73)).all Box.check = true := by decide +kernel

theorem supportCheck16 : (boxesForSupport (3, 5, 11, 79)).all Box.check = true := by decide +kernel

theorem supportCheck17 : (boxesForSupport (3, 5, 11, 83)).all Box.check = true := by decide +kernel

theorem supportCheck18 : (boxesForSupport (3, 5, 11, 89)).all Box.check = true := by decide +kernel

theorem supportCheck19 : (boxesForSupport (3, 5, 11, 97)).all Box.check = true := by decide +kernel

theorem supportCheck20 : (boxesForSupport (3, 5, 11, 101)).all Box.check = true := by decide +kernel

theorem supportCheck21 : (boxesForSupport (3, 5, 11, 103)).all Box.check = true := by decide +kernel

theorem supportCheck22 : (boxesForSupport (3, 5, 11, 107)).all Box.check = true := by decide +kernel

theorem supportCheck23 : (boxesForSupport (3, 5, 11, 109)).all Box.check = true := by decide +kernel

theorem supportCheck24 : (boxesForSupport (3, 5, 11, 113)).all Box.check = true := by decide +kernel

theorem supportCheck25 : (boxesForSupport (3, 5, 11, 127)).all Box.check = true := by decide +kernel

theorem supportCheck26 : (boxesForSupport (3, 5, 11, 131)).all Box.check = true := by decide +kernel

theorem supportCheck27 : (boxesForSupport (3, 5, 11, 137)).all Box.check = true := by decide +kernel

theorem supportCheck28 : (boxesForSupport (3, 5, 11, 139)).all Box.check = true := by decide +kernel

theorem supportCheck29 : (boxesForSupport (3, 5, 13, 17)).all Box.check = true := by decide +kernel

theorem supportCheck30 : (boxesForSupport (3, 5, 13, 19)).all Box.check = true := by decide +kernel

theorem supportCheck31 : (boxesForSupport (3, 5, 13, 23)).all Box.check = true := by decide +kernel

theorem supportCheck32 : (boxesForSupport (3, 5, 13, 29)).all Box.check = true := by decide +kernel

theorem supportCheck33 : (boxesForSupport (3, 5, 13, 31)).all Box.check = true := by decide +kernel

theorem supportCheck34 : (boxesForSupport (3, 5, 13, 37)).all Box.check = true := by decide +kernel

theorem supportCheck35 : (boxesForSupport (3, 5, 13, 41)).all Box.check = true := by decide +kernel

theorem supportCheck36 : (boxesForSupport (3, 5, 13, 43)).all Box.check = true := by decide +kernel

theorem supportCheck37 : (boxesForSupport (3, 5, 17, 19)).all Box.check = true := by decide +kernel

theorem supportCheck38 : (boxesForSupport (3, 5, 17, 23)).all Box.check = true := by decide +kernel

theorem supportCheck39 : (boxesForSupport (3, 5, 17, 29)).all Box.check = true := by decide +kernel

theorem supportCheck40 : (boxesForSupport (3, 5, 17, 31)).all Box.check = true := by decide +kernel

theorem supportCheck41 : (boxesForSupport (3, 5, 17, 37)).all Box.check = true := by decide +kernel

theorem supportCheck42 : (boxesForSupport (3, 5, 17, 41)).all Box.check = true := by decide +kernel

theorem supportCheck43 : (boxesForSupport (3, 5, 17, 43)).all Box.check = true := by decide +kernel

theorem supportCheck44 : (boxesForSupport (3, 5, 17, 47)).all Box.check = true := by decide +kernel

theorem supportCheck45 : (boxesForSupport (3, 5, 17, 53)).all Box.check = true := by decide +kernel

theorem supportCheck46 : (boxesForSupport (3, 5, 17, 59)).all Box.check = true := by decide +kernel

theorem supportCheck47 : (boxesForSupport (3, 5, 17, 61)).all Box.check = true := by decide +kernel

theorem supportCheck48 : (boxesForSupport (3, 5, 17, 67)).all Box.check = true := by decide +kernel

theorem supportCheck49 : (boxesForSupport (3, 5, 17, 71)).all Box.check = true := by decide +kernel

theorem supportCheck50 : (boxesForSupport (3, 5, 17, 73)).all Box.check = true := by decide +kernel

theorem supportCheck51 : (boxesForSupport (3, 5, 17, 79)).all Box.check = true := by decide +kernel

theorem supportCheck52 : (boxesForSupport (3, 5, 17, 83)).all Box.check = true := by decide +kernel

theorem supportCheck53 : (boxesForSupport (3, 5, 17, 89)).all Box.check = true := by decide +kernel

theorem supportCheck54 : (boxesForSupport (3, 5, 17, 97)).all Box.check = true := by decide +kernel

theorem supportCheck55 : (boxesForSupport (3, 5, 17, 101)).all Box.check = true := by decide +kernel

theorem supportCheck56 : (boxesForSupport (3, 5, 17, 103)).all Box.check = true := by decide +kernel

theorem supportCheck57 : (boxesForSupport (3, 5, 17, 107)).all Box.check = true := by decide +kernel

theorem supportCheck58 : (boxesForSupport (3, 5, 17, 109)).all Box.check = true := by decide +kernel

theorem supportCheck59 : (boxesForSupport (3, 5, 17, 113)).all Box.check = true := by decide +kernel

theorem supportCheck60 : (boxesForSupport (3, 5, 17, 127)).all Box.check = true := by decide +kernel

theorem supportCheck61 : (boxesForSupport (3, 5, 17, 131)).all Box.check = true := by decide +kernel

theorem supportCheck62 : (boxesForSupport (3, 5, 17, 137)).all Box.check = true := by decide +kernel

theorem supportCheck63 : (boxesForSupport (3, 5, 17, 139)).all Box.check = true := by decide +kernel

theorem supportCheck64 : (boxesForSupport (3, 5, 17, 149)).all Box.check = true := by decide +kernel

theorem supportCheck65 : (boxesForSupport (3, 5, 17, 151)).all Box.check = true := by decide +kernel

theorem supportCheck66 : (boxesForSupport (3, 5, 17, 157)).all Box.check = true := by decide +kernel

theorem supportCheck67 : (boxesForSupport (3, 5, 17, 163)).all Box.check = true := by decide +kernel

theorem supportCheck68 : (boxesForSupport (3, 5, 17, 167)).all Box.check = true := by decide +kernel

theorem supportCheck69 : (boxesForSupport (3, 5, 17, 173)).all Box.check = true := by decide +kernel

theorem supportCheck70 : (boxesForSupport (3, 5, 17, 179)).all Box.check = true := by decide +kernel

theorem supportCheck71 : (boxesForSupport (3, 5, 17, 181)).all Box.check = true := by decide +kernel

theorem supportCheck72 : (boxesForSupport (3, 5, 17, 191)).all Box.check = true := by decide +kernel

theorem supportCheck73 : (boxesForSupport (3, 5, 17, 193)).all Box.check = true := by decide +kernel

theorem supportCheck74 : (boxesForSupport (3, 5, 17, 197)).all Box.check = true := by decide +kernel

theorem supportCheck75 : (boxesForSupport (3, 5, 17, 199)).all Box.check = true := by decide +kernel

theorem supportCheck76 : (boxesForSupport (3, 5, 17, 211)).all Box.check = true := by decide +kernel

theorem supportCheck77 : (boxesForSupport (3, 5, 17, 223)).all Box.check = true := by decide +kernel

theorem supportCheck78 : (boxesForSupport (3, 5, 17, 227)).all Box.check = true := by decide +kernel

theorem supportCheck79 : (boxesForSupport (3, 5, 17, 229)).all Box.check = true := by decide +kernel

theorem supportCheck80 : (boxesForSupport (3, 5, 17, 233)).all Box.check = true := by decide +kernel

theorem supportCheck81 : (boxesForSupport (3, 5, 17, 239)).all Box.check = true := by decide +kernel

theorem supportCheck82 : (boxesForSupport (3, 5, 17, 241)).all Box.check = true := by decide +kernel

theorem supportCheck83 : (boxesForSupport (3, 5, 17, 251)).all Box.check = true := by decide +kernel

theorem supportCheck84 : (boxesForSupport (3, 5, 19, 23)).all Box.check = true := by decide +kernel

theorem supportCheck85 : (boxesForSupport (3, 5, 19, 29)).all Box.check = true := by decide +kernel

theorem supportCheck86 : (boxesForSupport (3, 5, 19, 31)).all Box.check = true := by decide +kernel

theorem supportCheck87 : (boxesForSupport (3, 5, 19, 37)).all Box.check = true := by decide +kernel

theorem supportCheck88 : (boxesForSupport (3, 5, 19, 41)).all Box.check = true := by decide +kernel

theorem supportCheck89 : (boxesForSupport (3, 5, 19, 43)).all Box.check = true := by decide +kernel

theorem supportCheck90 : (boxesForSupport (3, 5, 19, 47)).all Box.check = true := by decide +kernel

theorem supportCheck91 : (boxesForSupport (3, 5, 19, 53)).all Box.check = true := by decide +kernel

theorem supportCheck92 : (boxesForSupport (3, 5, 19, 59)).all Box.check = true := by decide +kernel

theorem supportCheck93 : (boxesForSupport (3, 5, 19, 61)).all Box.check = true := by decide +kernel

theorem supportCheck94 : (boxesForSupport (3, 5, 19, 67)).all Box.check = true := by decide +kernel

theorem supportCheck95 : (boxesForSupport (3, 5, 19, 71)).all Box.check = true := by decide +kernel

theorem supportCheck96 : (boxesForSupport (3, 5, 19, 73)).all Box.check = true := by decide +kernel

theorem supportCheck97 : (boxesForSupport (3, 5, 19, 79)).all Box.check = true := by decide +kernel

theorem supportCheck98 : (boxesForSupport (3, 5, 19, 83)).all Box.check = true := by decide +kernel

theorem supportCheck99 : (boxesForSupport (3, 5, 19, 89)).all Box.check = true := by decide +kernel

theorem supportCheck100 : (boxesForSupport (3, 5, 23, 29)).all Box.check = true := by decide +kernel

theorem supportCheck101 : (boxesForSupport (3, 5, 23, 31)).all Box.check = true := by decide +kernel

theorem supportCheck102 : (boxesForSupport (3, 5, 23, 37)).all Box.check = true := by decide +kernel

theorem supportCheck103 : (boxesForSupport (3, 5, 23, 41)).all Box.check = true := by decide +kernel

theorem supportCheck104 : (boxesForSupport (3, 5, 23, 43)).all Box.check = true := by decide +kernel

theorem supportCheck105 : (boxesForSupport (3, 5, 23, 47)).all Box.check = true := by decide +kernel

theorem supportCheck106 : (boxesForSupport (3, 5, 29, 31)).all Box.check = true := by decide +kernel

theorem supportCheck107 : (boxesForSupport (3, 7, 11, 13)).all Box.check = true := by decide +kernel

theorem supportCheck108 : (boxesForSupport (3, 7, 11, 17)).all Box.check = true := by decide +kernel

theorem supportCheck109 : (boxesForSupport (3, 7, 11, 19)).all Box.check = true := by decide +kernel

theorem supportCheck110 : (boxesForSupport (3, 7, 11, 23)).all Box.check = true := by decide +kernel

theorem supportCheck111 : (boxesForSupport (3, 7, 13, 17)).all Box.check = true := by decide +kernel

theorem supportCheck112 : (boxesForSupport (3, 7, 13, 19)).all Box.check = true := by decide +kernel

theorem supports_exact : candidateSupports = supportRows := by decide +kernel

theorem supportRows_check : supportRows.all (fun s => (boxesForSupport s).all Box.check) = true := by
  simp [supportRows, supportCheck0, supportCheck1, supportCheck2, supportCheck3, supportCheck4, supportCheck5, supportCheck6, supportCheck7, supportCheck8, supportCheck9, supportCheck10, supportCheck11, supportCheck12, supportCheck13, supportCheck14, supportCheck15, supportCheck16, supportCheck17, supportCheck18, supportCheck19, supportCheck20, supportCheck21, supportCheck22, supportCheck23, supportCheck24, supportCheck25, supportCheck26, supportCheck27, supportCheck28, supportCheck29, supportCheck30, supportCheck31, supportCheck32, supportCheck33, supportCheck34, supportCheck35, supportCheck36, supportCheck37, supportCheck38, supportCheck39, supportCheck40, supportCheck41, supportCheck42, supportCheck43, supportCheck44, supportCheck45, supportCheck46, supportCheck47, supportCheck48, supportCheck49, supportCheck50, supportCheck51, supportCheck52, supportCheck53, supportCheck54, supportCheck55, supportCheck56, supportCheck57, supportCheck58, supportCheck59, supportCheck60, supportCheck61, supportCheck62, supportCheck63, supportCheck64, supportCheck65, supportCheck66, supportCheck67, supportCheck68, supportCheck69, supportCheck70, supportCheck71, supportCheck72, supportCheck73, supportCheck74, supportCheck75, supportCheck76, supportCheck77, supportCheck78, supportCheck79, supportCheck80, supportCheck81, supportCheck82, supportCheck83, supportCheck84, supportCheck85, supportCheck86, supportCheck87, supportCheck88, supportCheck89, supportCheck90, supportCheck91, supportCheck92, supportCheck93, supportCheck94, supportCheck95, supportCheck96, supportCheck97, supportCheck98, supportCheck99, supportCheck100, supportCheck101, supportCheck102, supportCheck103, supportCheck104, supportCheck105, supportCheck106, supportCheck107, supportCheck108, supportCheck109, supportCheck110, supportCheck111, supportCheck112]

theorem boxes_check : boxes.all Box.check = true := by
  rw [boxes, supports_exact, List.all_flatMap]
  exact supportRows_check


theorem makeBox_mem_boxes (support : Support) (es : ExponentTuple)
    (hs : support ∈ candidateSupports) (he : es ∈ exponentsForSupport support) :
    makeBox support es ∈ boxes := by
  simp only [boxes, List.mem_flatMap]
  exact ⟨support, hs, by simpa [boxesForSupport] using List.mem_map.mpr ⟨es, he, rfl⟩⟩

theorem makeBox_check_of_mem (support : Support) (es : ExponentTuple)
    (hs : support ∈ candidateSupports) (he : es ∈ exponentsForSupport support) :
    Box.check (makeBox support es) = true := by
  have hall := (List.all_eq_true.mp boxes_check)
  exact hall _ (makeBox_mem_boxes support es hs he)

end FourSigmaCertificate

namespace SigmaFive.Four

open FourSigmaCertificate

private theorem factor_as_rat {p : ℕ} (hp : p.Prime) (e : Option ℕ) :
    ((factorNum p e : ℕ) : ℚ) / (factorDen p e : ℕ) =
      e.elim ((p : ℚ) / ((p : ℚ)-1)) (ratio p) := by
  cases e with
  | none => simp [factorNum, factorDen, Nat.cast_sub hp.pos]
  | some e => exact (ratio_as_cross hp e).symm

private theorem factor_den_pos {p : ℕ} (hp : p.Prime) (e : Option ℕ) :
    0 < factorDen p e := by
  have h₀ : 0 < p - 1 := by have := hp.two_le; omega
  cases e with
  | none => exact h₀
  | some e => exact Nat.mul_pos (pow_pos hp.pos _) h₀

private theorem product_cross {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (A B C D : Option ℕ) :
    ((ratioNum [p,q,r,s] [A,B,C,D] : ℕ) : ℚ) /
        (ratioDen [p,q,r,s] [A,B,C,D] : ℕ) =
      A.elim ((p : ℚ) / ((p : ℚ)-1)) (ratio p) *
      B.elim ((q : ℚ) / ((q : ℚ)-1)) (ratio q) *
      C.elim ((r : ℚ) / ((r : ℚ)-1)) (ratio r) *
      D.elim ((s : ℚ) / ((s : ℚ)-1)) (ratio s) := by
  rw [← factor_as_rat hp, ← factor_as_rat hq, ← factor_as_rat hr, ← factor_as_rat hs]
  simp only [ratioNum, ratioDen, product, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, one_mul, Nat.cast_mul, div_mul_div_comm]

private theorem product_den_pos {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (A B C D : Option ℕ) :
    0 < ratioDen [p,q,r,s] [A,B,C,D] := by
  simpa only [ratioDen, product, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, one_mul] using
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factor_den_pos hp A) (factor_den_pos hq B))
        (factor_den_pos hr C)) (factor_den_pos hs D)

private def toUpper (e : ℕ) : Option ℕ := if e == 10 then none else some e

private theorem upper_as_option (p e : ℕ) (he : e ≤ 10) :
    upperRatio p e = (toUpper e).elim ((p : ℚ) / ((p : ℚ)-1)) (ratio p) := by
  by_cases h : e < 10
  · have hn : e ≠ 10 := by omega
    simp [upperRatio, toUpper, h, hn]
  · have hEq : e = 10 := by omega
    subst e
    rfl

theorem checked_box_separated {q r s A B C D : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hA : A ≤ 10) (hB : B ≤ 10) (hC : C ≤ 10) (hD : D ≤ 10)
    (hchecked : (Box.mk [3,q,r,s] [toUpper A,toUpper B,toUpper C,toUpper D] [A,B,C,D]).check = true) :
    clipsSeparated q r s A B C D := by
  have hp : Nat.Prime 3 := by decide
  unfold Box.check at hchecked
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hchecked
  unfold clipsSeparated
  rcases hchecked with hu | hl
  · left
    rw [upper_as_option _ _ hA, upper_as_option _ _ hB, upper_as_option _ _ hC,
      upper_as_option _ _ hD, ← product_cross hp hq hr hs]
    exact cross_upper (product_den_pos hp hq hr hs _ _ _ _) hu
  · right
    have hn : 0 < lowerSize [3,q,r,s] [A,B,C,D] := by
      simpa only [lowerSize, product, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.foldl_cons, List.foldl_nil, one_mul] using
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos A) (pow_pos hq.pos B))
          (pow_pos hr.pos C)) (pow_pos hs.pos D)
    simp only [List.map_cons, List.map_nil] at hl
    have hh := cross_lower (product_den_pos hp hq hr hs (some A) (some B) (some C) (some D)) hn hl
    rw [product_cross hp hq hr hs] at hh
    simpa only [lowerSize, product, List.zipWith_cons_cons, List.zipWith_nil_left,
      List.foldl_cons, List.foldl_nil, one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Option.elim_some] using hh


end SigmaFive.Four

namespace SigmaFive.Four

open FourSigmaCertificate

private theorem bounded_prime_mem {p : ℕ} (hp : p.Prime) (hb : p ≤ 251) : p ∈ primesUpTo251 := by
  simp [primesUpTo251, hp, show p < 252 by omega]

private theorem support_mem {q r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hq : q = 5 ∨ q = 7) (hqr : q < r) (hrs : r < s)
    (hr29 : r ≤ 29) (hs251 : s ≤ 251) (hr7 : q = 5 → r ≠ 7)
    (hl : prefixNum q r < 2 * prefixDen q r)
    (hu : 2 * prefixDen q r * (s-1) < prefixNum q r * s) :
    (3,q,r,s) ∈ candidateSupports := by
  unfold candidateSupports
  rw [List.mem_flatMap]
  refine ⟨q, by simpa using hq, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨r, ?_, ?_⟩
  · have hm := bounded_prime_mem hr (hr29.trans (by decide))
    have hne : ¬ (q = 5 ∧ r = 7) := fun hp => hr7 hp.1 hp.2
    simpa [List.mem_filter, hm, hqr, show r < 31 by omega] using not_and_or.mp hne
  · rw [List.mem_map]
    exact ⟨s, by simp [List.mem_filter, bounded_prime_mem hs hs251, hrs, hl, hu], rfl⟩

private theorem make_box_mem {q r s A B C D : ℕ}
    (hS : (3,q,r,s) ∈ candidateSupports)
    (hA : q = 5 → (r = 11 ∨ r = 13) → A = 2)
    (hAm : A ∈ exponents) (hBm : B ∈ exponents)
    (hCm : C ∈ exponents) (hDm : D ∈ exponents) :
    Box.mk [3,q,r,s] [toUpper A,toUpper B,toUpper C,toUpper D] [A,B,C,D] ∈ boxes := by
  unfold boxes
  rw [List.mem_flatMap]
  refine ⟨(3,q,r,s), hS, ?_⟩
  rw [boxesForSupport, List.mem_map]
  refine ⟨(A,B,C,D), ?_, ?_⟩
  · unfold exponentsForSupport FourSigmaCertificate.exponents
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨A, ?_, B, hBm, C, hCm, D, hDm, rfl⟩
    by_cases h : q = 5 ∧ (r = 11 ∨ r = 13)
    · rcases h with ⟨hQ,hR⟩
      have h2 := hA hQ hR
      simp [firstExp, hQ, hR, h2]
    · simpa [firstExp, h, exponents, clippedExponents] using hAm
  · by_cases h : q = 5 ∧ (r = 11 ∨ r = 13)
    · rcases h with ⟨hQ,hR⟩
      have h2 := hA hQ hR
      simp [makeBox, firstExp, hQ, hR, h2, toUpper]
    · simp [makeBox, firstExp, h, toUpper]

end SigmaFive.Four

namespace SigmaFive.Four

open FourSigmaCertificate

private theorem prefix_lt_two {q r : ℕ} (hq : q = 5 ∨ q = 7) (hqr : q < r)
    (hr : r.Prime) (hr7 : q = 5 → r ≠ 7) :
    prefixNum q r < 2 * prefixDen q r := by
  rcases hq with rfl | rfl
  · by_cases hr11 : r = 11
    · subst r; decide
    by_cases hr13 : r = 13
    · subst r; decide
    have hr17 : 17 ≤ r := by
      have hrne := hr7 rfl
      by_contra! hh
      interval_cases r <;> first | omega | (revert hr; decide)
    simp [prefixNum, prefixDen, firstExp, factorNum, factorDen, hr11, hr13]
    omega
  · have hr11 : 11 ≤ r := by
      by_contra! hh
      interval_cases r <;> (revert hr; decide)
    simp [prefixNum, prefixDen, firstExp, factorNum, factorDen]
    omega

private theorem clip_le_ideal {p : ℕ} (hp : p.Prime) (a : ℕ) :
    upperRatio p a ≤ (p : ℚ) / ((p : ℚ)-1) := by
  unfold upperRatio
  split_ifs with h
  · exact ratio_upper hp a
  · exact le_rfl

theorem prefilter_separated {q r s A B C D : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hA : q = 5 → (r = 11 ∨ r = 13) → A = 2)
    (hu : prefixNum q r * s ≤ 2 * prefixDen q r * (s-1)) :
    clipsSeparated q r s A B C D := by
  have h3 : (3 : ℕ).Prime := by decide
  have hP : upperRatio 3 A ≤ (firstExp q r).elim (((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ)-1)) (ratio 3) := by
    by_cases h : q = 5 ∧ (r = 11 ∨ r = 13)
    · rw [hA h.1 h.2]
      simp [firstExp, h, upperRatio]
    · simp [firstExp, h]
      exact clip_le_ideal h3 A
  have hq' := clip_le_ideal hq B
  have hr' := clip_le_ideal hr C
  have hs' := clip_le_ideal hs D
  have hnonneg {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 ≤ upperRatio p e := by
    unfold upperRatio
    split_ifs
    · unfold ratio
      positivity
    · have hle : (1 : ℚ) ≤ p := by exact_mod_cast hp.pos
      exact div_nonneg (by positivity) (sub_nonneg.mpr hle)
  have hfrac := product_cross h3 hq hr hs (firstExp q r) none none none
  have hpos := product_den_pos h3 hq hr hs (firstExp q r) none none none
  have hua : ratioNum [3,q,r,s] [firstExp q r, none, none, none] ≤
      2 * ratioDen [3,q,r,s] [firstExp q r, none, none, none] := by
    simp only [ratioNum, ratioDen, product, List.zipWith_cons_cons, List.zipWith_nil_left,
      List.foldl_cons, List.foldl_nil, one_mul, prefixNum, prefixDen, factorNum, factorDen] at hu ⊢
    simpa only [Nat.mul_assoc] using hu
  have hupper := cross_upper hpos hua
  rw [hfrac] at hupper
  simp only [Option.elim_none] at hupper
  have h0 {p : ℕ} (hp : p.Prime) : 0 ≤ (p : ℚ) / ((p : ℚ)-1) := by
    have hle : (1 : ℚ) ≤ p := by exact_mod_cast hp.pos
    exact div_nonneg (by positivity) (sub_nonneg.mpr hle)
  have hP0 : 0 ≤ (firstExp q r).elim (((3 : ℕ) : ℚ) / (((3 : ℕ) : ℚ)-1)) (ratio 3) := by
    cases h : firstExp q r
    · exact h0 h3
    · simp [ratio]
      positivity
  have hPQ := mul_le_mul hP hq' (hnonneg hq B) hP0
  have hPQR := mul_le_mul hPQ hr' (hnonneg hr C) (mul_nonneg hP0 (h0 hq))
  have hPQRS := mul_le_mul hPQR hs' (hnonneg hs D)
    (mul_nonneg (mul_nonneg hP0 (h0 hq)) (h0 hr))
  exact Or.inl (hPQRS.trans hupper)

end SigmaFive.Four

namespace SigmaFive.Four

open FourSigmaCertificate

theorem certified_odd_five_support
    (hcert : boxes.all Box.check = true)
    {n : ℕ} (hn : Odd n) (h : sigma 1 n % n = 5) :
    5 ≤ n.primeFactors.card := by
  apply odd_five_support_of_boxes _ hn h
  intro q r s A B C D hq hr hs hqcase hqr hrs hr29 hs251 hr7 hA hAm hBm hCm hDm
  by_cases hupper : prefixNum q r * s ≤ 2 * prefixDen q r * (s-1)
  · exact prefilter_separated hq hr hs hA hupper
  · have hm := support_mem hr hs hqcase hqr hrs hr29 hs251 hr7
      (prefix_lt_two hqcase hqr hr hr7) (Nat.lt_of_not_ge hupper)
    have hchecked := List.all_eq_true.mp hcert _ (make_box_mem hm hA hAm hBm hCm hDm)
    have hclip {e : ℕ} (he : e ∈ exponents) : e ≤ 10 := by
      simp [exponents] at he
      omega
    exact checked_box_separated hq hr hs
      (hclip hAm) (hclip hBm) (hclip hCm) (hclip hDm) hchecked


end SigmaFive.Four

theorem SigmaFive.odd_five_support {n : ℕ} (hn : Odd n)
    (h : ArithmeticFunction.sigma 1 n % n = 5) : 5 ≤ n.primeFactors.card :=
  SigmaFive.Four.certified_odd_five_support FourSigmaCertificate.boxes_check hn h


namespace SigmaFive.Four

private theorem rank_filter_bound {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (i : Fin k) (t : ℕ) (hfi : s.orderEmbOfFin hs i < t) :
    i.val + 1 ≤ (s.filter (fun x => x < t)).card := by
  let f := s.orderEmbOfFin hs
  let pre := Finset.Iic i
  have hsub : Finset.image f pre ⊆ s.filter (fun x => x < t) := by
    apply Finset.image_subset_iff.mpr
    intro j hj
    have hjle : j ≤ i := Finset.mem_Iic.mp hj
    have hmem : f j ∈ s := Finset.orderEmbOfFin_mem _ _ _
    have hlt : f j < t := lt_of_le_of_lt (f.monotone hjle) hfi
    exact Finset.mem_filter.mpr ⟨hmem, hlt⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective pre f.injective, Fin.card_Iic] at hc
  exact hc

private def primeLower (i : ℕ) : ℕ :=
  match i with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 17
  | _ => 19

private theorem prime_rank_lower {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (hk : k ≤ 7) (hprime : ∀ p ∈ s, p.Prime) (hlower : ∀ p ∈ s, 3 ≤ p) :
    ∀ i : Fin k, primeLower i.val ≤ s.orderEmbOfFin hs i := by
  intro i
  have hi7 : i.val < 7 := lt_of_lt_of_le i.isLt hk
  interval_cases hval : i.val
  all_goals
    by_contra! hlt
    have hsub : s.filter (fun p => p < primeLower i.val) ⊆
        (Finset.range (primeLower i.val)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hps, hpt⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hpt, ?_⟩
      exact ⟨hprime p hps, hlower p hps⟩
    have hcount :
        (s.filter (fun p => p < primeLower i.val)).card ≤ i.val := by
      calc
        (s.filter (fun p => p < primeLower i.val)).card ≤
            ((Finset.range (primeLower i.val)).filter (fun p => p.Prime ∧ 3 ≤ p)).card :=
          Finset.card_le_card hsub
        _ = i.val := by
          rw [hval]
          simp [primeLower]
          decide
    have hprefix := rank_filter_bound hs i (primeLower i.val) (by
      simpa [primeLower, hval] using hlt)
    omega

private theorem prime_product_ratio_lt_three {s : Finset ℕ} {k : ℕ}
    (hs : s.card = k) (hklo : 4 ≤ k) (hkhi : k ≤ 7)
    (hprime : ∀ p ∈ s, p.Prime) (hlower : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) < 3 := by
  classical
  let f := s.orderEmbOfFin hs
  have hfmem (i : Fin k) : f i ∈ s := Finset.orderEmbOfFin_mem _ _ _
  have hfrank (i : Fin k) : primeLower i.val ≤ f i :=
    prime_rank_lower hs hkhi hprime hlower i
  have hprodMap :
      (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) =
        ∏ i : Fin k, (f i : ℚ) / ((f i : ℚ) - 1) := by
    rw [← Finset.map_orderEmbOfFin_univ s hs, Finset.prod_map]
    simp [f]
  have hprodBound :
      (∏ i : Fin k, (f i : ℚ) / ((f i : ℚ) - 1)) ≤
        ∏ i : Fin k, (primeLower i.val : ℚ) / ((primeLower i.val : ℚ) - 1) := by
    apply Finset.prod_le_prod
    · intro i hi
      have hp := hprime (f i) (hfmem i)
      have hl := hlower (f i) (hfmem i)
      have hp1 : (1 : ℚ) < f i := by exact_mod_cast (show 1 < f i by omega)
      linarith [div_nonneg (show (0 : ℚ) ≤ f i by positivity)
        (show (0 : ℚ) ≤ (f i : ℚ) - 1 by linarith)]
    · intro i hi
      have hti := hfrank i
      have ht3 : 3 ≤ primeLower i.val := by
        have hi7 : i.val < 7 := lt_of_lt_of_le i.isLt hkhi
        interval_cases i.val <;> norm_num [primeLower]
      have hp1 : (1 : ℚ) < f i := by
        exact_mod_cast (show 1 < f i from (hprime (f i) (hfmem i)).two_le)
      have ht1 : (1 : ℚ) < primeLower i.val := by exact_mod_cast (by omega : 1 < primeLower i.val)
      have hcast : (primeLower i.val : ℚ) ≤ f i := by exact_mod_cast hti
      have hpden : 0 < (f i : ℚ) - 1 := by linarith
      have htden : 0 < (primeLower i.val : ℚ) - 1 := by linarith
      rw [div_le_div_iff₀ hpden htden]
      nlinarith
  have hlim :
      (∏ i : Fin k, (primeLower i.val : ℚ) / ((primeLower i.val : ℚ) - 1)) < 3 := by
    interval_cases k <;> norm_num [primeLower, Fin.prod_univ_succ]
  rw [hprodMap]
  exact lt_of_le_of_lt hprodBound hlim

end SigmaFive.Four

namespace SigmaFive

/-- If every prime valuation is even, the prime factorization is a square. -/
private theorem square_of_even_factorization {n : ℕ} (hn0 : n ≠ 0)
    (h : ∀ p, p.Prime → Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun a b => a ^ (b / 2), ?_⟩
  rw [← pow_two, ← powMonoidHom_apply, map_finsuppProd]
  nth_rw 1 [← Nat.prod_factorization_pow_eq_self hn0]
  refine Finsupp.prod_congr fun p hp => ?_
  rw [powMonoidHom_apply, ← pow_mul,
    Nat.div_two_mul_two_of_even (h p (Nat.prime_of_mem_primeFactors hp))]

/-- An odd nonsquare has an even divisor sum: a prime with odd valuation
contributes an even prime-power divisor sum to the multiplicative factorization. -/
theorem even_sigma_of_odd_nonsquare {n : ℕ} (hn0 : n ≠ 0) (hn : Odd n)
    (hnsq : ¬ IsSquare n) : Even (sigma 1 n) := by
  classical
  have hex : ∃ p, p.Prime ∧ ¬ Even (n.factorization p) := by
    by_contra! h
    exact hnsq (square_of_even_factorization hn0 h)
  obtain ⟨p, hp, he⟩ := hex
  have hepos : n.factorization p ≠ 0 := by
    intro hz
    apply he
    simp [hz]
  have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos hepos
  have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn0⟩
  have hpne : p ≠ 2 := by
    intro hp2
    subst p
    apply (Nat.not_even_iff.mpr (by rcases hn with ⟨j, hj⟩; omega))
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) hpdvd)
  have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hpne
  have hpOdd : Odd p := by
    refine ⟨p / 2, ?_⟩
    omega
  have hpowOdd : ∀ i, Odd (p^i) := by
    intro i
    exact hpOdd.pow
  have hemod : n.factorization p % 2 = 1 := Nat.not_even_iff.mp he
  have hlocal : Even (sigma 1 (p ^ n.factorization p)) := by
    rw [sigma_one_apply_prime_pow hp, Finset.even_sum_iff_even_card_odd]
    have hfilter : {i ∈ Finset.range (n.factorization p + 1) | Odd (p^i)} =
        Finset.range (n.factorization p + 1) := by
      ext i
      simp [hpowOdd]
    rw [hfilter, Finset.card_range]
    refine ⟨n.factorization p / 2 + 1, ?_⟩
    omega
  have hfact : sigma 1 n = ∏ q ∈ n.primeFactors, sigma 1 (q ^ n.factorization q) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp [Finsupp.prod, Nat.support_factorization]
  rw [hfact]
  apply even_iff_two_dvd.mpr
  exact dvd_trans (even_iff_two_dvd.mp hlocal) (Finset.dvd_prod_of_mem _ hpmem)

/-- For an odd input, an even divisor sum and remainder five force the
integer quotient to be odd. -/
theorem odd_quotient_of_even_sigma {n : ℕ} (hn : Odd n)
    (hmod : sigma 1 n % n = 5) (hs : Even (sigma 1 n)) :
    Odd (sigma 1 n / n) := by
  let k := sigma 1 n / n
  have hdiv := Nat.mod_add_div (sigma 1 n) n
  rw [hmod] at hdiv
  change 5 + n*k = sigma 1 n at hdiv
  have hnmod : n % 2 = 1 := by
    rcases hn with ⟨j, rfl⟩
    omega
  have hsmod : sigma 1 n % 2 = 0 := Nat.even_iff.mp hs
  have hkm : k % 2 = 1 := by
    have he := congrArg (fun x : ℕ => x % 2) hdiv
    rw [Nat.add_mod, Nat.mul_mod] at he
    rw [hnmod, hsmod] at he
    omega
  refine ⟨k / 2, ?_⟩
  omega

/-- An odd quotient and the divisor contribution from two distinct primes make a
remainder-five candidate incompatible with a sigma-to-number ratio below three. -/
theorem exclude_remainder_five_of_ratio_lt_three
    {n : ℕ} (hmod : sigma 1 n % n = 5)
    (hquotOdd : Odd (sigma 1 n / n)) (hbig : n + 5 < sigma 1 n)
    (hratio : sigma 1 n < 3*n) : False := by
  let k := sigma 1 n / n
  have hdiv := Nat.mod_add_div (sigma 1 n) n
  rw [hmod] at hdiv
  change 5 + n*k = sigma 1 n at hdiv
  have hklt : k < 3 := by
    by_contra! hk
    have hmul := Nat.mul_le_mul_left n (show 3 ≤ k by omega)
    omega
  have hk : k = 1 := by
    rcases hquotOdd with ⟨j, hj⟩
    omega
  rw [hk] at hdiv
  omega

end SigmaFive
namespace SigmaFive

/-- Four distinct odd prime factors force a proper divisor at least seven. -/
theorem large_sigma_of_four_odd_factors {n : ℕ} (hn : Odd n)
    (hcard : 4 ≤ n.primeFactors.card) : n + 5 < sigma 1 n := by
  classical
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    rcases hn with ⟨j, hj⟩
    omega
  have hsmall : n.primeFactors.filter (fun p => p < 7) ⊆ ({3, 5} : Finset ℕ) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hup⟩
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hn.not_two_dvd_nat hdiv
    have hlo : 3 ≤ p := by have := hprime.two_le; omega
    interval_cases p <;> norm_num at hprime <;> norm_num
  have hex : ∃ q ∈ n.primeFactors, 7 ≤ q := by
    by_contra! h
    have hsub : n.primeFactors ⊆ ({3, 5} : Finset ℕ) := by
      intro p hp
      apply hsmall
      apply Finset.mem_filter.mpr
      refine ⟨hp, ?_⟩
      have hp_lt : p < 7 := h p hp
      exact hp_lt
    have hcard' : n.primeFactors.card ≤ ({3, 5} : Finset ℕ).card :=
      Finset.card_le_card hsub
    norm_num at hcard'
    omega
  obtain ⟨q, hqmem, hq7⟩ := hex
  have hqprime := Nat.prime_of_mem_primeFactors hqmem
  have hnprime : ¬ n.Prime := by
    intro hp
    have hc : n.primeFactors.card = 1 := by simp [hp]
    omega
  have hqn : q ≠ n := by
    intro heq
    subst q
    exact hnprime hqprime
  have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
    (Nat.dvd_of_mem_primeFactors hqmem)
  have hq_lt : q < n := lt_of_le_of_ne hqle hqn
  let T : Finset ℕ := {n, q}
  have hTsub : T ⊆ n.divisors := by
    intro d hd
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hdn | hdq
    · subst d
      exact Nat.mem_divisors_self n hn0
    · subst d
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hqmem, hn0⟩
  have hTsum : (∑ d ∈ T, d) = n + q := by
    simp [T, Finset.sum_pair (Ne.symm hqn)]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hTsub
    (fun d _ _ => Nat.zero_le d)
  rw [← sigma_one_apply n] at hsum
  rw [hTsum] at hsum
  omega

/-- An odd nonsquare with at most seven distinct prime factors cannot have
divisor-sum remainder five. -/
theorem exclude_odd_nonsquare_le_seven {n : ℕ} (hn : Odd n)
    (hnsq : ¬ IsSquare n) (hmod : sigma 1 n % n = 5)
    (hcard : n.primeFactors.card ≤ 7) : False := by
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    rcases hn with ⟨j, hj⟩
    omega
  have hcardLo := odd_four_support hn hmod
  have hbig := large_sigma_of_four_odd_factors hn hcardLo
  have hsigmaEven := even_sigma_of_odd_nonsquare hn0 hn hnsq
  have hquotOdd := odd_quotient_of_even_sigma hn hmod hsigmaEven
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have hlower (p : ℕ) (hp : p ∈ n.primeFactors) : 3 ≤ p := by
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hn.not_two_dvd_nat hdiv
    have := (hprime p hp).two_le
    omega
  have hupperPrimeProduct :
      (∏ p ∈ n.primeFactors, Four.ratio p (n.factorization p)) < 3 := by
    have hupper :
        (∏ p ∈ n.primeFactors, Four.ratio p (n.factorization p)) ≤
          ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp0 : (0 : ℚ) < p := by exact_mod_cast (hprime p hp).pos
        unfold Four.ratio
        positivity
      · intro p hp
        exact Four.ratio_upper (hprime p hp) _
    exact lt_of_le_of_lt hupper
      (Four.prime_product_ratio_lt_three rfl hcardLo hcard hprime hlower)
  have hratioQ : Four.ratio n 1 < 3 := by
    rw [← Four.ratio_prod_of_factorization hn0]
    exact hupperPrimeProduct
  have hnrat : (sigma 1 n : ℚ) / (n : ℚ) < 3 := by
    simpa [Four.ratio] using hratioQ
  have hq : (sigma 1 n : ℚ) < 3 * n :=
    (div_lt_iff₀ (show (0 : ℚ) < n by exact_mod_cast Nat.pos_of_ne_zero hn0)).mp hnrat
  have hratio : sigma 1 n < 3*n := by exact_mod_cast hq
  exact exclude_remainder_five_of_ratio_lt_three hmod hquotOdd hbig hratio

end SigmaFive

namespace OMA.R_OeisA76495_conjecture_R1

open ArithmeticFunction

/-- Odd candidates have at least five prime factors, and nonsquares have at least eight. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 5 ≤ n.primeFactors.card → (IsSquare n ∨ 8 ≤ n.primeFactors.card) → sigma 1 n % n ≠ 5

/-- The remaining even case has at least three distinct prime factors and odd divisor sum. -/
def H2 : Prop :=
  ∀ n : ℕ, Even n → 3 ≤ n.primeFactors.card → Odd (sigma 1 n) → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → type_of% @OeisA76495.conjecture := by
  classical
  intro odd_case even_case
  unfold OeisA76495.a
  split_ifs with h
  · obtain ⟨n, hn, hmod⟩ := h
    have hcard := SigmaFive.three_le_primeFactors_card hn hmod
    exfalso
    rcases Nat.even_or_odd n with he | ho
    · have hodd : Odd (sigma 1 n) := by
        obtain ⟨v, hv⟩ := he
        have heq := Nat.mod_add_div (sigma 1 n) n
        rw [hmod, hv] at heq
        rw [hv]
        refine ⟨v * (sigma 1 (v+v) / (v+v)) + 2, ?_⟩
        nlinarith only [heq]
      exact even_case n he hcard hodd hmod
    · apply odd_case n ho (SigmaFive.odd_five_support ho hmod) _ hmod
      by_cases hsq : IsSquare n
      · exact Or.inl hsq
      · right
        by_contra! hc
        exact SigmaFive.exclude_odd_nonsquare_le_seven ho hsq hmod (by omega)
  · rfl

end OMA.R_OeisA76495_conjecture_R1
