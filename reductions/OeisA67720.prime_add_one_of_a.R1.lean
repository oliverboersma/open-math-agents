import FormalConjectures.OEIS.«67720»

/-!
# Totient equality exception (A067720)

Reduction by @LDJAI. The two remaining cases are separated by the parity of the input.
-/

namespace OMA.R_OeisA67720_prime_add_one_of_a_R1

/-- A prime divisor bounds the relative totient of a positive integer. -/
private theorem prime_factor_bound {p n : ℕ} (hp : p.Prime) (hn : p ∣ n) :
    p * n.totient ≤ (p - 1) * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, rfl⟩ := hn
    by_cases hm : m = 0
    · simp [hm]
    by_cases hd : p ∣ m
    · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      have hmp : 0 < m := Nat.pos_of_ne_zero hm
      have hlt : m < p * m := by nlinarith [Nat.mul_le_mul_right m hp.two_le]
      have h := Nat.mul_le_mul_left p (ih m hlt hd)
      nlinarith
    · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
      have h := Nat.mul_le_mul_left (p * (p - 1)) m.totient_le
      nlinarith

/-- A composite integer is bounded by the square of its cototient. -/
private theorem le_cototient_sq {n : ℕ} (hn : 1 < n) (hc : ¬ n.Prime) :
    n ≤ (n - n.totient)^2 := by
  let p := n.minFac
  let m := n / p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdiv : p ∣ n := Nat.minFac_dvd n
  have hm : p * m = n := Nat.mul_div_cancel' hpdiv
  have hpm : p ≤ m := Nat.minFac_le_div (by omega) hc
  have hφ := prime_factor_bound hp hpdiv
  have hsub : p-1+1=p := by have := hp.pos; omega
  have hnm : n.totient + m ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := p) _ hp.pos
    nlinarith only [hφ, hm, congrArg (fun z : ℕ => z*n) hsub]
  have hcot : m ≤ n - n.totient := by omega
  calc
    n = p*m := hm.symm
    _ ≤ (n - n.totient) * (n - n.totient) := Nat.mul_le_mul (hpm.trans hcot) hcot
    _ = _ := by ring

/-- A relation between the smaller prime factor minus one and the cototient deficit. -/
private theorem semiprime_defect_bound {x k d : ℕ}
    (hx : 0 < x) (hxk : x < k) (hd : 2 ≤ d)
    (hr : x^2 + k^2 = k * (d * (x+1))) : d^3 ≤ k := by
  have hdiv : k ∣ x^2 := by
    apply (Nat.dvd_add_iff_left (dvd_pow (dvd_refl k) (by decide : 2 ≠ 0))).mpr
    rw [hr]
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra! hz
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have htk : t < x := by
    by_contra! hf
    nlinarith only [ht, Nat.mul_le_mul_left k hf, Nat.mul_lt_mul_of_pos_right hxk hx]
  have he : k+t = d*(x+1) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k)
    nlinarith only [ht, hr]
  have hnext : x^2+t^2=d*t*(x+1) := by
    nlinarith only [ht, congrArg (fun z : ℕ => z*t) he]
  have htd : d ≤ t := by
    by_contra! hsmall
    have hl : d*t < x := by
      by_contra! hl
      nlinarith only [Nat.mul_le_mul_right x hl, hnext,
        Nat.mul_lt_mul_of_pos_right hsmall htpos]
    nlinarith only [Nat.mul_le_mul_right x (show d*t+1 ≤ x by omega), hnext, hl,
      Nat.zero_le (t*t)]
  have hux : x ≤ d*t := by
    by_contra! hbad
    nlinarith only [Nat.mul_lt_mul_of_pos_right hbad hx, hnext, Nat.mul_le_mul_right t htd]
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hux
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le htd
  have huv : x*v=t*s := by
    nlinarith only [congrArg (fun z : ℕ => z*x) hv,
      congrArg (fun z : ℕ => z*t) hs,hnext]
  have hvs : v ≤ s := by
    by_contra! hf
    nlinarith only [Nat.mul_lt_mul_of_pos_left hf hx, Nat.mul_le_mul_right s htk.le, huv]
  have hxu : (d-1)*t+d ≤ x := by
    have hds : d-1+1=d := by omega
    nlinarith only [hv,hs,hvs,congrArg (fun z : ℕ => z*t) hds]
  obtain ⟨r, hd2⟩ := Nat.exists_eq_add_of_le hd
  rw [hd2] at he hxu hs
  rw [show 2+r-1=1+r by omega, hs] at hxu
  rw [hs] at he
  rw [hd2]
  nlinarith only [he, Nat.mul_le_mul_left (2+r) hxu,
    Nat.zero_le (s*(r*r+3*r+1))]

/-- The full totient-exception assertion when the quadratic value is a product of two primes. -/
private theorem semiprime_case {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hprod : k^2+1 = p*q)
    (heq : (k^2+1).totient = k*(k+1).totient) : k=8 ∨ (k+1).Prime := by
  wlog ho : p ≤ q generalizing p q
  · exact this hq hp (by simpa [Nat.mul_comm] using hprod) (by omega)
  by_contra! hn
  have hk : 0 < k := by
    by_contra! hz
    have : k = 0 := by omega
    simp [this] at heq
  have hple : p ≤ k := by
    by_contra! hf
    nlinarith only [hprod, Nat.mul_le_mul (show k+1 ≤ p by omega) (show k+1 ≤ q by omega), hk]
  have hne : p ≠ q := by
    rintro rfl
    nlinarith only [hprod, Nat.mul_le_mul hple hple]
  let x := p-1
  let d := k-(k+1).totient
  have hxp : x+1=p := by dsimp [x]; have := hp.pos; omega
  have hx : 0<x := by have := hp.one_lt; omega
  have hxk : x<k := by omega
  have hz : (k+1).totient < k+1 := Nat.totient_lt _ (by omega)
  have hdf : d+(k+1).totient=k := by dsimp [d]; omega
  have hbd := le_cototient_sq (by omega : 1 < k+1) hn.2
  have hsmall : k+1 ≤ (d+1)^2 := by
    rwa [show k+1-(k+1).totient = d+1 by omega] at hbd
  have hcalc : x^2+k^2=k*(d*(x+1)) := by
    rw [hprod, Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hne),
      Nat.totient_prime hp, Nat.totient_prime hq] at heq
    have hqpred : q-1+1=q := by have := hq.pos; omega
    have hsum : p+q=k*d+2 := by
      have hleft : (p-1)*(q-1)+p+q=p*q+1 := by
        have hppred : p-1+1=p := by omega
        nlinarith only [congrArg (fun z : ℕ => z*(q-1)) hppred,
          congrArg (fun z : ℕ => p*z) hqpred,hppred,hqpred]
      nlinarith only [hleft,hprod,heq,congrArg (fun z : ℕ => k*z) hdf]
    nlinarith only [hprod, congrArg (fun z : ℕ => p*z) hsum,
      congrArg (fun z : ℕ => z*z) hxp,congrArg (fun z : ℕ => (k*d)*z) hxp,hxp]
  have hkcases : k ≤ 3 ∨ k=8 := by
    by_cases hdd : 2 ≤ d
    · have hc := semiprime_defect_bound hx hxk hdd hcalc
      have htwo : d=2 := by
        by_contra! hno
        obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (show 3 ≤ d by omega)
        rw [hs] at hc hsmall
        nlinarith only [hc,hsmall,Nat.zero_le (s*(s^2+8*s+19))]
      rw [htwo] at hc hsmall
      omega
    · interval_cases d <;> norm_num at hsmall <;> omega
  rcases hkcases with hsmall | h8
  · interval_cases k <;> first
      | exact hn.2 (by decide)
      | exact (by decide : (3^2+1).totient ≠ 3*(3+1).totient) heq

  · exact hn.1 h8

/-- A prime dividing a totient without dividing its argument occurs in a prime divisor minus one. -/
private theorem exists_prime_factor_one_mod {p N : ℕ} (hp : Nat.Prime p) (hN : ¬ p ∣ N)
    (hφ : p ∣ N.totient) : ∃ q, Nat.Prime q ∧ q ∣ N ∧ p ∣ (q - 1) := by
  have hprod := dvd_mul_of_dvd_left hφ (∏ q ∈ N.primeFactors, q)
  rw [Nat.totient_mul_prod_primeFactors] at hprod
  have hf := (hp.dvd_mul.mp hprod).resolve_left hN
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hf
  exact ⟨q, Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq, hpq⟩

/-- For a nonprime quadratic endpoint, each prime factor of k is at most the square of
its cofactor as soon as k divides the quadratic endpoint's totient. -/
private theorem factor_le_cofactor_sq {p d : ℕ} (hp : Nat.Prime p)
    (hφ : p ∣ ((p * d)^2 + 1).totient) (hcomp : ¬ Nat.Prime ((p * d)^2 + 1)) : p ≤ d^2 := by
  have hpd : p ∣ (p * d)^2 := dvd_pow (dvd_mul_right p d) (by decide)
  have hn : ¬ p ∣ (p * d)^2 + 1 := by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpd).mpr h)
  obtain ⟨q, hq, ⟨t, ht⟩, hqp⟩ := exists_prime_factor_one_mod hp hn hφ
  obtain ⟨a, ha⟩ := hqp
  have hqval : q = p*a+1 := by have := hq.two_le; omega
  have ht2 : 2 ≤ t := by
    by_contra! hsmall
    interval_cases t <;> simp_all
  have hφmod : (p * d)^2 + 1 ≡ 1 [MOD p] := by simpa using hpd.modEq_zero_nat.add_right 1
  have hqmod : q ≡ 1 [MOD p] := by rw [hqval]; exact Nat.ModEq.modulus_mul_add
  have htmod : 1 ≡ t [MOD p] := by
    rw [ht] at hφmod
    exact hφmod.symm.trans (by simpa using hqmod.mul_right t)
  obtain ⟨b, hb⟩ := htmod.dvd'
  have htval : t = p*b+1 := by omega
  have ha1 : 1 ≤ a := by
    by_contra! hall
    have : a = 0 := by omega
    simp_all
  have hb1 : 1 ≤ b := by
    by_contra! hall
    have : b = 0 := by omega
    simp_all
  have heq : d^2*p = a*b*p + (a+b) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [hqval,htval] at ht
    nlinarith only [ht]
  have hlt : a*b < d^2 := by
    by_contra! hle
    have := Nat.mul_le_mul_right p hle
    omega
  have hab : a+b ≤ a*b+1 := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ha1
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb1
    nlinarith [Nat.zero_le (u*v)]
  have hfin := Nat.mul_le_mul_right p (show a*b+1 ≤ d^2 by omega)
  nlinarith only [hfin,heq,hab,hlt]

private theorem totient_prime_mul_upper {p : ℕ} (hp : p.Prime) (s : ℕ) :
    (p*s).totient ≤ (p-1)*s := by
  have h := prime_factor_bound hp (dvd_mul_right p s)
  apply Nat.le_of_mul_le_mul_left (c := p) _ hp.pos
  nlinarith only [h]

private theorem not_totient_eq_of_successor_twice_prime {k p : ℕ} (hp : p.Prime)
    (hk : k+1 = 2*p) : (k^2+1).totient ≠ k*(k+1).totient := by
  by_cases hp2 : p = 2
  · have hk3 : k=3 := by omega
    subst k
    decide
  have hpodd := hp.odd_of_ne_two hp2
  let u := p-1
  have hu : p=u+1 := by have := hp.one_lt; dsimp [u]; omega
  have hku : k=2*u+1 := by omega
  let m := 2*u^2+2*u+1
  have hm : k^2+1 = 2*m := by rw [hku]; dsimp [m]; ring
  have hmodd : Odd m := ⟨u^2+u, by dsimp [m]; ring⟩
  intro he
  rw [hm,Nat.totient_two_mul_of_odd hmodd,hk,Nat.totient_two_mul_of_odd hpodd,
    Nat.totient_prime hp] at he
  have hdef : m = m.totient+p := by rw [he,hku]; change 2*u^2+2*u+1 = (2*u+1)*u+p; rw [hu]; ring
  have hlt : p^2 < m := by
    have : 1 ≤ u := by have := hp.two_le; omega
    rw [hu]; dsimp [m]; nlinarith [Nat.mul_le_mul this this]
  have hmgt : 1 < m := by have := hp.two_le; nlinarith
  by_cases hprime : m.Prime
  · rw [Nat.totient_prime hprime] at hdef
    have := hp.two_le
    omega
  · have hb := le_cototient_sq hmgt hprime
    have : m-m.totient=p := by omega
    rw [this] at hb
    omega

/-- No solution has a successor equal to four times a prime. -/
private theorem not_totient_eq_of_successor_four_times_prime {k p : ℕ} (hp : p.Prime)
    (hk : k+1 = 4*p) : (k^2+1).totient ≠ k*(k+1).totient := by
  by_cases hsmall : k < 33
  · have hp8 : p ≤ 8 := by omega
    set_option maxRecDepth 10000 in
    interval_cases p <;>
      first | contradiction | (have hv : k = _ := Nat.eq_sub_of_add_eq hk; subst k; decide)
  have hkbig : 33 ≤ k := by omega
  have hpo := hp.odd_of_ne_two (by omega)
  let u := 2*p-1
  have hku : k=2*u+1 := by have := hp.two_le; dsimp [u]; omega
  let n := 2*u^2+2*u+1
  have hn : k^2+1 = 2*n := by rw [hku]; dsimp [n]; ring
  have hno : Odd n := ⟨u^2+u, by dsimp [n]; ring⟩
  have hngt : 1 < n := by nlinarith [Nat.mul_le_mul hkbig hkbig]
  have hdiv4 : (4*p).totient = 2*(p-1) := by
    rw [show 4*p=2*(2*p) by ring,
      Nat.totient_two_mul_of_even (show Even (2*p) from ⟨p,by ring⟩),
      Nat.totient_two_mul_of_odd hpo, Nat.totient_prime hp]
  intro he
  rw [hn,Nat.totient_two_mul_of_odd hno,hk,hdiv4] at he
  have hdef : 2*n = 2*n.totient + 3*k+1 := by
    have hp1 : p-1+1=p := by have := hp.pos; omega
    nlinarith only [hn,he, congrArg (fun a : ℕ => a*k) hk,
      congrArg (fun a : ℕ => a*k) hp1]
  have hnp : ¬n.Prime := by
    intro hpr
    rw [Nat.totient_prime hpr] at hdef
    omega
  let q := n.minFac
  let s := n/q
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqs : q*s=n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  have hle : q ≤ s := Nat.minFac_le_div (by omega) hnp
  have h2 : 2 ≤ q := hq.two_le
  have hbound := totient_prime_mul_upper hq s
  rw [hqs] at hbound
  have hq1 : q-1+1=q := by omega
  have hsbound : 2*s ≤ 3*k+1 := by
    nlinarith only [hbound,hdef,hqs,congrArg (fun a : ℕ => a*s) hq1]
  have hqlower : k < 4*q := by
    by_contra! hbad
    nlinarith only [hn,hqs,Nat.mul_le_mul hbad hsbound,
      Nat.mul_le_mul_right k (show 2 ≤ k by omega)]
  have hsp : s.Prime := by
    by_contra hb
    have hsmin : q ≤ s.minFac :=
      Nat.minFac_le_of_dvd (Nat.minFac_prime (show s ≠ 1 by omega)).two_le
        (dvd_trans (Nat.minFac_dvd s) (hqs ▸ dvd_mul_left s q))
    have hs2 := Nat.minFac_sq_le_self (show 0 < s by omega) hb
    have hqs2 : q*q ≤ s := by nlinarith only [Nat.mul_le_mul hsmin hsmin,hs2]
    have hkk : k*k < (4*q)*(4*q) :=
      Nat.mul_lt_mul_of_pos_right hqlower (by omega : 0<k) |>.trans_le
        (Nat.mul_le_mul_left (4*q) hqlower.le)
    nlinarith only [hsbound,hqs2,hkk,Nat.mul_le_mul_right k hkbig,hkbig]
  by_cases heq : q=s
  · rw [← hqs,← heq,Nat.totient_mul_of_prime_of_dvd hq (dvd_refl _),
      Nat.totient_prime hq] at hdef
    have hqval : 2*q=3*k+1 := by
      nlinarith only [hdef,congrArg (fun a : ℕ => q*a) hq1]
    rw [← hqs,← heq] at hn
    nlinarith only [hn, congrArg (fun a : ℕ => a*a) hqval,
      Nat.mul_le_mul_right k hkbig,hkbig]
  have hsd : ¬q ∣ s := fun hd => heq ((Nat.prime_dvd_prime_iff_eq hq hsp).mp hd)
  rw [← hqs,Nat.totient_mul_of_prime_of_not_dvd hq hsd,Nat.totient_prime hsp] at hdef
  have hs1 : s-1+1=s := by omega
  have hsum : 2*q+2*s=3*k+3 := by
    have e1 := congrArg (fun a : ℕ => a*(s-1)) hq1
    have e2 := congrArg (fun a : ℕ => q*a) hs1
    nlinarith only [e1,e2,hdef,hs1]
  let w := 2*(s-q)
  have hw : w+2*q=2*s := by dsimp [w]; omega
  have hdisc : w^2+80=(k+9)^2 := by
    nlinarith only [congrArg (fun a : ℕ => a*a) hsum,
      congrArg (fun a : ℕ => a*a) hw, congrArg (fun a : ℕ => a*q) hw, hn,hqs]
  by_cases hlow : w ≤ k+8
  · nlinarith only [Nat.mul_le_mul hlow hlow,hdisc,hkbig]
  · have hhigh : k+9 ≤ w := by omega
    nlinarith only [Nat.mul_le_mul hhigh hhigh,hdisc]

/-- Every odd prime dividing a quadratic value contributes a factor of four
to the corresponding shifted-prime factor of the totient. -/
private theorem four_dvd_quadratic_prime_sub_one {k p : ℕ}
    (hp : p.Prime) (hp₂ : p ≠ 2) (hdiv : p ∣ k ^ 2 + 1) : 4 ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  push_cast at hz
  have hn := ZMod.mod_four_ne_three_of_sq_eq_neg_one
    (show (k : ZMod p) ^ 2 = -1 by linear_combination hz)
  have ho := hp.mod_two_eq_one_iff_ne_two.mpr hp₂
  omega

/-- Count all the shifted prime factors simultaneously. -/
private theorem four_pow_quadratic_factors_dvd {k : ℕ}
    (hodd : ∀ p ∈ (k ^ 2 + 1).primeFactors, p ≠ 2) :
    4 ^ (k ^ 2 + 1).primeFactors.card ∣ (k ^ 2 + 1).totient := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  apply dvd_mul_of_dvd_right
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
    four_dvd_quadratic_prime_sub_one (Nat.prime_of_mem_primeFactors hp) (hodd p hp)
      (Nat.dvd_of_mem_primeFactors hp)

/-- With a squarefree quadratic value and three powers of four absent, the main
conjecture reduces to the semiprime case. -/
private theorem low_valuation_squarefree {k : ℕ} (hk : 1 < k)
    (heq : (k ^ 2 + 1).totient = k * (k + 1).totient)
    (hsq : Squarefree (k ^ 2 + 1))
    (hodd : ∀ p ∈ (k ^ 2 + 1).primeFactors, p ≠ 2)
    (h64 : ¬64 ∣ k * (k + 1).totient)
    (hsemi : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      k ^ 2 + 1 = p * q → k = 8 ∨ (k + 1).Prime) :
    k = 8 ∨ (k + 1).Prime := by
  have hcard : (k ^ 2 + 1).primeFactors.card < 3 := by
    by_contra! h
    apply h64
    rw [← heq]
    exact dvd_trans (pow_dvd_pow 4 h) (four_pow_quadratic_factors_dvd hodd)
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hz : (k ^ 2 + 1).primeFactors.card = 0
  · rw [Finset.card_eq_zero.mp hz] at hprod
    simp at hprod
    omega
  by_cases ho : (k ^ 2 + 1).primeFactors.card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp ho
    have hmem : p ∈ (k ^ 2 + 1).primeFactors := by simp [hp]
    have hpr := Nat.prime_of_mem_primeFactors hmem
    rw [hp, Finset.prod_singleton] at hprod
    rw [hprod] at hpr
    rw [Nat.totient_prime hpr, Nat.add_sub_cancel, pow_two] at heq
    have ht := Nat.eq_of_mul_eq_mul_left (show 0 < k by omega) heq
    exact Or.inr ((Nat.totient_eq_iff_prime (by omega)).mp (by omega))
  · obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp
      (show (k ^ 2 + 1).primeFactors.card = 2 by omega)
    have hp : p ∈ (k ^ 2 + 1).primeFactors := by simp [hs]
    have hq : q ∈ (k ^ 2 + 1).primeFactors := by simp [hs]
    apply hsemi p q (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq) hpq
    simpa [hs, hpq] using hprod.symm

/-- The odd half of a quadratic of an odd solution has at least two distinct primes. -/
private theorem odd_half_not_prime_power {k m : ℕ} (hk : 1 < k) (hm : k^2+1 = 2*m)
    (hd : k ∣ m.totient) : ¬IsPrimePow m := by
  intro hpow
  obtain ⟨q,a,hq,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hpow
  have hqdiv : q ∣ k^2+1 := by
    rw [hm]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
  have hsq : k ∣ k^2 := by simp [pow_two]
  have hcop : k.Coprime q :=
    Nat.Coprime.of_dvd_right hqdiv ((Nat.coprime_add_iff_right hsq).2 (by simp))
  rw [Nat.totient_prime_pow hq ha] at hd
  have hs := (hcop.pow_right (a-1)).dvd_of_dvd_mul_left hd
  obtain ⟨b,hb⟩ := hs
  have hq1 : q = k*b+1 := by have := hq.one_lt; omega
  have hmodeq : q ≡ 1 [MOD k] := by
    change q%k = 1%k
    simp [hq1, Nat.add_mod]
  have hz := congrArg (fun x : ℕ => x % k) hm
  have hpowmod : q^a % k = 1%k := by change q^a ≡ 1 [MOD k]; simpa using hmodeq.pow a
  have hk2 : 2 ≤ k := by omega
  simp only [pow_two, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod, hpowmod, Nat.mod_eq_of_lt hk] at hz
  rcases eq_or_lt_of_le hk2 with htwo | htwo
  · subst k; simp at hz
  · rw [Nat.mod_eq_of_lt htwo] at hz
    simp [Nat.mod_eq_of_lt htwo] at hz

private theorem sixteen_dvd_successor_totient_of_odd {k : ℕ} (hk : 1 < k) (hodd : Odd k)
    (he : (k^2+1).totient = k*(k+1).totient) : 16 ∣ (k+1).totient := by
  obtain ⟨u,hu⟩ := hodd
  let m := 2*u^2+2*u+1
  have hm : k^2+1 = 2*m := by rw [hu]; dsimp [m]; ring
  have hmodd : Odd m := ⟨u^2+u, by dsimp [m]; ring⟩
  rw [hm,Nat.totient_two_mul_of_odd hmodd] at he
  have hmd : k ∣ m.totient := he ▸ dvd_mul_right _ _
  have hmn := odd_half_not_prime_power hk hm hmd
  have hm2 : 2 ≤ m := by nlinarith [Nat.mul_le_mul (show 2 ≤ k by omega) (show 2 ≤ k by omega)]
  obtain ⟨q,hq,r,hr,hqr⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm2).mp hmn
  have four (v : ℕ) (hv : v ∈ m.primeFactors) : 4 ∣ v-1 := by
    have hp := Nat.prime_of_mem_primeFactors hv
    have hdiv := Nat.dvd_of_mem_primeFactors hv
    have hv2 : v ≠ 2 := by rintro rfl; exact hmodd.not_two_dvd_nat hdiv
    exact four_dvd_quadratic_prime_sub_one hp hv2 (hm ▸ dvd_mul_of_dvd_right hdiv 2)
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hcop := (Nat.coprime_primes hqp hrp).mpr hqr
  have hh := Nat.totient_dvd_of_dvd (hcop.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hr))
  rw [Nat.totient_mul hcop,Nat.totient_prime hqp,Nat.totient_prime hrp,he] at hh
  have hs : 16 ∣ k*(k+1).totient := dvd_trans (Nat.mul_dvd_mul (four q hq) (four r hr)) hh
  have h16 : Nat.Coprime 16 k := by
    change (2^4).Coprime k
    exact (Odd.coprime_two_left (show Odd k from ⟨u,hu⟩)).pow_left 4
  exact h16.dvd_of_dvd_mul_left hs

/-- No solution has a successor equal to eight times a prime. -/
private theorem not_totient_eq_of_successor_eight_times_prime {k p : ℕ} (hp : p.Prime)
    (hk : k+1 = 8*p) : (k^2+1).totient ≠ k*(k+1).totient := by
  by_cases hsmall : k < 250
  · have hp32 : p ≤ 32 := by omega
    set_option maxRecDepth 10000 in
    set_option maxHeartbeats 1600000 in
    interval_cases p <;> first | omega | (
      have hv : k = _ := Nat.eq_sub_of_add_eq hk
      subst k
      rw [Nat.totient_eq_div_primeFactors_mul, Nat.totient_eq_div_primeFactors_mul]
      decide +kernel)
  have hkbig : 250 ≤ k := by omega
  have hpo := hp.odd_of_ne_two (by omega)
  let u := 4*p-1
  have hku : k=2*u+1 := by have := hp.two_le; dsimp [u]; omega
  let n := 2*u^2+2*u+1
  have hn : k^2+1 = 2*n := by rw [hku]; dsimp [n]; ring
  have hno : Odd n := ⟨u^2+u, by dsimp [n]; ring⟩
  have hngt : 1 < n := by nlinarith [Nat.mul_le_mul hkbig hkbig]
  have hdiv8 : (8*p).totient = 4*(p-1) := by
    rw [show 8*p=2*(2*(2*p)) by ring,
      Nat.totient_two_mul_of_even (show Even (2*(2*p)) from ⟨2*p,by ring⟩),
      Nat.totient_two_mul_of_even (show Even (2*p) from ⟨p,by ring⟩),
      Nat.totient_two_mul_of_odd hpo, Nat.totient_prime hp]
    ring
  intro he
  rw [hn,Nat.totient_two_mul_of_odd hno,hk,hdiv8] at he
  have hdef : 2*n = 2*n.totient + 7*k+1 := by
    have hp1 : p-1+1=p := by have := hp.pos; omega
    nlinarith only [hn,he, congrArg (fun a : ℕ => a*k) hk,
      congrArg (fun a : ℕ => a*k) hp1]
  have hnp : ¬n.Prime := by
    intro hpr
    rw [Nat.totient_prime hpr] at hdef
    omega
  let q := n.minFac
  let s := n/q
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqs : q*s=n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  have hle : q ≤ s := Nat.minFac_le_div (by omega) hnp
  have h2 : 2 ≤ q := hq.two_le
  have hbound := totient_prime_mul_upper hq s
  rw [hqs] at hbound
  have hq1 : q-1+1=q := by omega
  have hsbound : 2*s ≤ 7*k+1 := by
    nlinarith only [hbound,hdef,hqs,congrArg (fun a : ℕ => a*s) hq1]
  have hqlower : k < 8*q := by
    by_contra! hbad
    nlinarith only [hn,hqs,Nat.mul_le_mul hbad hsbound,
      Nat.mul_le_mul_right k (show 2 ≤ k by omega)]
  have hsp : s.Prime := by
    by_contra hb
    have hsmin : q ≤ s.minFac :=
      Nat.minFac_le_of_dvd (Nat.minFac_prime (show s ≠ 1 by omega)).two_le
        (dvd_trans (Nat.minFac_dvd s) (hqs ▸ dvd_mul_left s q))
    have hs2 := Nat.minFac_sq_le_self (show 0 < s by omega) hb
    have hqs2 : q*q ≤ s := by nlinarith only [Nat.mul_le_mul hsmin hsmin,hs2]
    have hkk : k*k < (8*q)*(8*q) :=
      Nat.mul_lt_mul_of_pos_right hqlower (by omega : 0<k) |>.trans_le
        (Nat.mul_le_mul_left (8*q) hqlower.le)
    nlinarith only [hsbound,hqs2,hkk,Nat.mul_le_mul_right k hkbig,hkbig]
  by_cases heq : q=s
  · rw [← hqs,← heq,Nat.totient_mul_of_prime_of_dvd hq (dvd_refl _),
      Nat.totient_prime hq] at hdef
    have hqval : 2*q=7*k+1 := by
      nlinarith only [hdef,congrArg (fun a : ℕ => q*a) hq1]
    rw [← hqs,← heq] at hn
    nlinarith only [hn, congrArg (fun a : ℕ => a*a) hqval,
      Nat.mul_le_mul_right k hkbig,hkbig]
  have hsd : ¬q ∣ s := fun hd => heq ((Nat.prime_dvd_prime_iff_eq hq hsp).mp hd)
  rw [← hqs,Nat.totient_mul_of_prime_of_not_dvd hq hsd,Nat.totient_prime hsp] at hdef
  have hs1 : s-1+1=s := by omega
  have hsum : 2*q+2*s=7*k+3 := by
    have e1 := congrArg (fun a : ℕ => a*(s-1)) hq1
    have e2 := congrArg (fun a : ℕ => q*a) hs1
    nlinarith only [e1,e2,hdef,hs1]
  let w := 2*(s-q)
  have hw : w+2*q=2*s := by dsimp [w]; omega
  have hdisc : w^2 = 41*k^2+42*k+1 := by
    nlinarith only [congrArg (fun a : ℕ => a*a) hsum,
      congrArg (fun a : ℕ => a*a) hw, congrArg (fun a : ℕ => a*q) hw, hn,hqs]
  have heval : w^2+320*p=2624*p^2 := by
    have e1 := congrArg (fun a : ℕ => a*a) hk
    nlinarith only [hdisc,e1,hk]
  have hwdiv : p ∣ w^2 := by
    apply (Nat.dvd_add_iff_left (dvd_mul_left p 320)).mpr
    rw [heval]
    exact dvd_mul_of_dvd_right (dvd_pow (dvd_refl p) (by decide : 2 ≠ 0)) _
  obtain ⟨t, ht⟩ := hp.dvd_of_dvd_pow hwdiv
  have hcancel : p*t^2+320=2624*p := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [ht] at heval
    nlinarith only [heval]
  have h320 : p ∣ 320 := by
    apply (Nat.dvd_add_iff_right (dvd_mul_right p (t^2))).mpr
    rw [hcancel]
    exact dvd_mul_left _ _
  have hcon : p=2 ∨ p=5 := by
    rw [show 320=2^6*5 by decide] at h320
    rcases hp.dvd_mul.mp h320 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  omega

/-- Two distinct primes congruent to 1 modulo 4 are at least 5 and 13. -/
private theorem shifted_pair_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hord : p < q) (h4p : 4 ∣ p - 1) (h4q : 4 ∣ q - 1) :
    48 * (p*q) ≤ 65 * ((p-1)*(q-1)) := by
  have h5 : 5 ≤ p := by have := hp.one_lt; omega
  have h13 : 13 ≤ q := by
    have hs := hq.one_lt
    by_contra! h
    have hn : q = 9 := by omega
    subst q
    exact (by decide : ¬ Nat.Prime 9) hq
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le h5
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le h13
  simp only [hu, hv] at *
  have hp' : 5 + u - 1 = 4+u := by omega
  have hq' : 13 + v - 1 = 12+v := by omega
  rw [hp', hq']
  nlinarith [Nat.zero_le (u*v)]

/-- Odd quadratic values with at most two distinct prime factors have
totient ratio at least 48/65, regardless of the prime multiplicities. -/
private theorem sparse_quadratic_ratio {k : ℕ}
    (hodd : ∀ p ∈ (k^2+1).primeFactors, p ≠ 2)
    (hcard : (k^2+1).primeFactors.card ≤ 2) :
    48 * (k^2+1) ≤ 65 * (k^2+1).totient := by
  let s := (k^2+1).primeFactors
  have hratio : 48 * (∏ p ∈ s, p) ≤ 65 * (∏ p ∈ s, (p-1)) := by
    by_cases hz : s.card = 0
    · simp [Finset.card_eq_zero.mp hz]
    by_cases ho : s.card = 1
    · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp ho
      have hmem : p ∈ s := by simp [hp]
      have hpr := Nat.prime_of_mem_primeFactors hmem
      have hpp := hpr.one_lt
      have h4 := four_dvd_quadratic_prime_sub_one hpr (hodd p hmem) (Nat.dvd_of_mem_primeFactors hmem)
      simp [hp]
      omega
    · change s.card ≤ 2 at hcard
      obtain ⟨p,q,hpq,hs⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      have hp : p ∈ s := by simp [hs]
      have hq : q ∈ s := by simp [hs]
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hqp := Nat.prime_of_mem_primeFactors hq
      have h4p := four_dvd_quadratic_prime_sub_one hpp (hodd p hp) (Nat.dvd_of_mem_primeFactors hp)
      have h4q := four_dvd_quadratic_prime_sub_one hqp (hodd q hq) (Nat.dvd_of_mem_primeFactors hq)
      simp [hs,hpq]
      rcases lt_or_gt_of_ne hpq with h | h
      · exact shifted_pair_ratio hpp hqp h h4p h4q
      · simpa [Nat.mul_comm] using shifted_pair_ratio hqp hpp h h4q h4p
  have hprod := Nat.totient_mul_prod_primeFactors (k^2+1)
  change (k^2+1).totient * (∏ p ∈ s, p) = (k^2+1) * (∏ p ∈ s, (p-1)) at hprod
  have hpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
  apply Nat.le_of_mul_le_mul_right _ hpos
  nlinarith only [Nat.mul_le_mul_left (k^2+1) hratio,
    congrArg (fun z : ℕ => 65*z) hprod]

/-- Pointwise lower bounds on the ordered prime factors give both multiplicative
bounds. The first uses divisibility of the radical, the second Euler's formula. -/
private theorem factor_profile_bound {n m : ℕ} (hn : 0 < n) (hm : n.primeFactors.card = m)
    (c : Fin m → ℕ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ n.primeFactors.orderEmbOfFin hm i) :
    (∏ i, c i) ≤ n ∧ (∏ i, (c i - 1)) * n ≤ (∏ i, c i) * n.totient := by
  let e := n.primeFactors.orderEmbOfFin hm
  have hrew (f : ℕ → ℕ) : (∏ i, f (e i)) = ∏ p ∈ n.primeFactors, f p := by
    rw [← n.primeFactors.map_orderEmbOfFin_univ hm, Finset.prod_map]
    rfl
  have h1 : (∏ i, c i) ≤ ∏ i, e i := Finset.prod_le_prod' (fun i _ => (hc i).2)
  have h2 : (∏ i, (c i - 1) * e i) ≤ ∏ i, c i * (e i - 1) := by
    apply Finset.prod_le_prod'
    intro i _
    obtain ⟨hci,hei⟩ := hc i
    change c i ≤ e i at hei
    have hx : c i - 1 + 1 = c i := by omega
    have hy : e i - 1 + 1 = e i := by omega
    nlinarith only [congrArg (fun z : ℕ => z * e i) hx,
      congrArg (fun z : ℕ => c i * z) hy, hei]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h2
  have he := Nat.totient_mul_prod_primeFactors n
  have hid : (∏ i, e i) = ∏ p ∈ n.primeFactors, p := hrew (fun p => p)
  rw [← hid, ← hrew (fun z => z-1)] at he
  have hpos : 0 < ∏ i, e i := Finset.prod_pos
    (fun i _ => Nat.pos_of_mem_primeFactors (n.primeFactors.orderEmbOfFin_mem hm i))
  constructor
  · have hd := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    exact h1.trans (hid ▸ hd)
  · apply Nat.le_of_mul_le_mul_right _ hpos
    nlinarith only [Nat.mul_le_mul_left n h2,
      congrArg (fun x : ℕ => (∏ i, c i)*x) he]

private theorem first_bound {p : ℕ} (hp : p.Prime) (hp4 : 4 ∣ p - 1) : 5 ≤ p := by
  have := hp.one_lt
  omega

private theorem second_bound {p : ℕ} (hp : p.Prime) (hp4 : 4 ∣ p - 1) (hl : 5 < p) : 13 ≤ p := by
  by_contra! h
  have h9 : p = 9 := by omega
  exact (by decide : ¬ Nat.Prime 9) (h9 ▸ hp)

private theorem third_bound {p : ℕ} (_hp : p.Prime) (hp4 : 4 ∣ p - 1) (hl : 13 < p) : 17 ≤ p := by
  omega

private theorem fourth_bound {p : ℕ} (hp : p.Prime) (hp4 : 4 ∣ p - 1) (hl : 17 < p) : 29 ≤ p := by
  by_contra! h
  have ht : p = 21 ∨ p = 25 := by omega
  rcases ht with rfl | rfl
  · exact (by decide : ¬ Nat.Prime 21) hp
  · exact (by decide : ¬ Nat.Prime 25) hp

private theorem quadratic_profile_3 {k : ℕ}
    (hodd : ∀ p ∈ (k^2+1).primeFactors, p ≠ 2)
    (hcard : (k^2+1).primeFactors.card = 3) :
    1105 ≤ k^2+1 ∧ 768 * (k^2+1) ≤ 1105 * (k^2+1).totient := by
  let s := (k^2+1).primeFactors
  let e := s.orderEmbOfFin hcard
  have hmem (i : Fin 3) : e i ∈ s := s.orderEmbOfFin_mem hcard i
  have hpr (i : Fin 3) := Nat.prime_of_mem_primeFactors (hmem i)
  have hmod (i : Fin 3) := four_dvd_quadratic_prime_sub_one (hpr i) (hodd _ (hmem i)) (Nat.dvd_of_mem_primeFactors (hmem i))
  have hb0 := first_bound (hpr 0) (hmod 0)
  have hb1 := second_bound (hpr 1) (hmod 1) (lt_of_le_of_lt hb0
    (e.strictMono (show (0 : Fin 3) < 1 by decide)))
  have hb2 := third_bound (hpr 2) (hmod 2) (lt_of_le_of_lt hb1
    (e.strictMono (show (1 : Fin 3) < 2 by decide)))
  let c : Fin 3 → ℕ := ![5,13,17]
  have hc (i : Fin 3) : 0 < c i ∧ c i ≤ e i := by
    fin_cases i
    · exact ⟨by decide, hb0⟩
    · exact ⟨by decide, hb1⟩
    · exact ⟨by decide, hb2⟩
  have h := factor_profile_bound (show 0 < k^2+1 by omega) hcard c hc
  simpa [c, Fin.prod_univ_succ] using h

private theorem quadratic_profile_4 {k : ℕ}
    (hodd : ∀ p ∈ (k^2+1).primeFactors, p ≠ 2)
    (hcard : (k^2+1).primeFactors.card = 4) :
    32045 ≤ k^2+1 ∧ 21504 * (k^2+1) ≤ 32045 * (k^2+1).totient := by
  let s := (k^2+1).primeFactors
  let e := s.orderEmbOfFin hcard
  have hmem (i : Fin 4) : e i ∈ s := s.orderEmbOfFin_mem hcard i
  have hpr (i : Fin 4) := Nat.prime_of_mem_primeFactors (hmem i)
  have hmod (i : Fin 4) := four_dvd_quadratic_prime_sub_one (hpr i) (hodd _ (hmem i)) (Nat.dvd_of_mem_primeFactors (hmem i))
  have hb0 := first_bound (hpr 0) (hmod 0)
  have hb1 := second_bound (hpr 1) (hmod 1) (lt_of_le_of_lt hb0
    (e.strictMono (show (0 : Fin 4) < 1 by decide)))
  have hb2 := third_bound (hpr 2) (hmod 2) (lt_of_le_of_lt hb1
    (e.strictMono (show (1 : Fin 4) < 2 by decide)))
  have hb3 := fourth_bound (hpr 3) (hmod 3) (lt_of_le_of_lt hb2
    (e.strictMono (show (2 : Fin 4) < 3 by decide)))
  let c : Fin 4 → ℕ := ![5,13,17,29]
  have hc (i : Fin 4) : 0 < c i ∧ c i ≤ e i := by
    fin_cases i
    · exact ⟨by decide, hb0⟩
    · exact ⟨by decide, hb1⟩
    · exact ⟨by decide, hb2⟩
    · exact ⟨by decide, hb3⟩
  have h := factor_profile_bound (show 0 < k^2+1 by omega) hcard c hc
  simpa [c, Fin.prod_univ_succ] using h

/-- An even solution beyond eight whose successor is divisible by three
has at least five different primes dividing its quadratic value. -/
private theorem five_quadratic_primes_of_three_dvd {k : ℕ} (hk : 8 < k)
    (heven : Even k) (h3 : 3 ∣ k+1)
    (heq : (k^2+1).totient = k*(k+1).totient) :
    5 ≤ (k^2+1).primeFactors.card := by
  obtain ⟨u,hu⟩ := heven
  have hod : Odd (k^2+1) := ⟨2*u^2, by rw [hu]; ring⟩
  have ho : ∀ p ∈ (k^2+1).primeFactors, p ≠ 2 := by
    rintro p hp rfl
    exact hod.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have ht := prime_factor_bound Nat.prime_three h3
  norm_num at ht
  by_contra! h
  by_cases h2 : (k^2+1).primeFactors.card ≤ 2
  · have hb := sparse_quadratic_ratio ho h2
    have hscaled := Nat.mul_le_mul_left (65*k) ht
    rw [heq] at hb
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le (show 9 ≤ k by omega)
    rw [hw] at hscaled hb
    nlinarith only [hscaled,hb,Nat.zero_le (w*w),Nat.zero_le w]
  rcases (show (k^2+1).primeFactors.card = 3 ∨ (k^2+1).primeFactors.card = 4 by omega)
    with h3p | h4p
  · obtain ⟨hl,hb⟩ := quadratic_profile_3 ho h3p
    have hlow : 34 ≤ k := by
      by_contra! hx
      have hx' : k ≤ 33 := by omega
      nlinarith only [hl, Nat.mul_le_mul hx' hx']
    have hscaled := Nat.mul_le_mul_left (1105*k) ht
    rw [heq] at hb
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hlow
    rw [hw] at hb hscaled
    nlinarith only [hscaled,hb,Nat.zero_le (w*w),Nat.zero_le w]
  · obtain ⟨hl,hb⟩ := quadratic_profile_4 ho h4p
    have hlow : 180 ≤ k := by
      by_contra! hx
      have hx' : k ≤ 179 := by omega
      nlinarith only [hl, Nat.mul_le_mul hx' hx']
    have hscaled := Nat.mul_le_mul_left (32045*k) ht
    rw [heq] at hb
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hlow
    rw [hw] at hb hscaled
    nlinarith only [hscaled,hb,Nat.zero_le (w*w),Nat.zero_le w]

private theorem three_pow_double_exp_base {t : ℕ} (ht : 5 ≤ t) :
    6 * t + 2 ≤ 3 ^ (2 ^ (t-3)) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [show t+1-3 = (t-3)+1 by omega, pow_succ, pow_mul, pow_two]
    nlinarith only [Nat.mul_le_mul ih ih, Nat.zero_le (t*t), ht]

private theorem power_three_growth {t a : ℕ} (ht : 5 ≤ t) (ha : 2^(2*t-3) ≤ a) :
    (6*t)^(2^t)+1 < 3^a := by
  have hb := three_pow_double_exp_base ht
  have hm : 0 < (2:ℕ)^t := by positivity
  have h1 := Nat.pow_lt_pow_left (show 6*t < 6*t+1 by omega) hm.ne'
  have h2 := Nat.pow_lt_pow_left (show 6*t+1 < 6*t+2 by omega) hm.ne'
  calc
    (6*t)^(2^t)+1 < (6*t+2)^(2^t) := by omega
    _ ≤ (3^(2^(t-3)))^(2^t) := Nat.pow_le_pow_left hb _
    _ = 3^(2^(2*t-3)) := by
      rw [← pow_mul, ← pow_add, show t-3+t=2*t-3 by omega]
    _ ≤ 3^a := Nat.pow_le_pow_right (by decide) ha

/-- A growth inequality for finite products with a chosen common rate and size threshold. -/
private theorem prefix_growth_general {s : Finset ℕ} {k c gate lower : ℕ} (hc : 0 < c)
    (hgate : gate ≤ c) (hlc : lower ≤ c) (hlower : k ≤ lower * ∏ q ∈ s, q)
    (step : ∀ u ⊆ s, u.card < s.card → gate*(∏ q ∈ u,q) ≤ k →
      ∃ q ∈ s \ u, q ≤ c*(∏ r ∈ u,r)) :
    k ≤ c^(2^s.card) := by
  by_contra! hlarge
  have grow (j : ℕ) (hj : j ≤ s.card) : ∃ u ⊆ s, u.card = j ∧
      c*(∏ q ∈ u, q) ≤ c^(2^j) := by
    induction j with
    | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | succ j ih =>
      obtain ⟨u,hus,huj,hprod⟩ := ih (by omega)
      have hpow := Nat.pow_le_pow_right hc
        (Nat.pow_le_pow_right (by decide : 0 < 2) (show j ≤ s.card by omega))
      have hb : gate*(∏ q ∈ u,q) ≤ k := le_trans
        (Nat.mul_le_mul_right _ hgate) (le_trans hprod (le_trans hpow hlarge.le))
      obtain ⟨q,hq,hsmall⟩ := step u hus (by omega) hb
      have hqs := (Finset.mem_sdiff.mp hq).1
      have hqu := (Finset.mem_sdiff.mp hq).2
      refine ⟨insert q u,Finset.insert_subset hqs hus,by simp [hqu,huj],?_⟩
      rw [Finset.prod_insert hqu]
      change q ≤ c * (∏ r ∈ u, r) at hsmall
      calc
        c * (q*(∏ r ∈ u,r)) = q*(c*(∏ r ∈ u,r)) := by ring
        _ ≤ (c*(∏ r ∈ u,r))*(c*(∏ r ∈ u,r)) := Nat.mul_le_mul_right _ hsmall
        _ ≤ c^(2^j)*c^(2^j) := Nat.mul_le_mul hprod hprod
        _ = c^(2^(j+1)) := by rw [pow_succ, Nat.mul_two, pow_add]
  obtain ⟨u,hus,hcard,hprod⟩ := grow s.card (by rfl)
  have hus' : u=s := Finset.eq_of_subset_of_card_le hus hcard.ge
  subst u
  exact hlarge.not_ge (hlower.trans ((Nat.mul_le_mul_right _ hlc).trans hprod))

/-- The common rate for an odd prime power with prime base p. -/
private theorem prefix_growth_prime_base {s : Finset ℕ} {k p : ℕ} (hp : 2 ≤ p) (ht : 0 < s.card)
    (hlower : k ≤ (p-1) * ∏ q ∈ s,q)
    (step : ∀ u ⊆ s, u.card < s.card → 2*(p-1)*(∏ q ∈ u,q) ≤ k →
      ∃ q ∈ s \ u, q ≤ 2*p*s.card*(∏ r ∈ u,r)) :
    k ≤ (2*p*s.card)^(2^s.card) := by
  have hr : 2*p ≤ 2*p*s.card := by
    simpa using Nat.mul_le_mul_left (2*p) (show 1 ≤ s.card from ht)
  exact prefix_growth_general (by omega) (by omega) (by omega) hlower step

private theorem prefix_growth_bound {s : Finset ℕ} {k : ℕ} (ht : 0 < s.card)
    (hlower : k ≤ 2 * ∏ q ∈ s, q)
    (step : ∀ u ⊆ s, u.card < s.card → 4*(∏ q ∈ u,q) ≤ k →
      ∃ q ∈ s \ u, q ≤ 6*s.card*(∏ r ∈ u,r)) :
    k ≤ (6*s.card)^(2^s.card) :=
  prefix_growth_prime_base (p := 3) (by decide) ht hlower step

/-- Integer version of the union bound on the missing Euler factors. -/
private theorem prefix_suffix_loss (s : Finset ℕ) {r : ℕ} (hr : 0 < r)
    (hmin : ∀ q ∈ s, r ≤ q) :
    r * (∏ q ∈ s, q) ≤ r * (∏ q ∈ s, (q-1)) + s.card * (∏ q ∈ s, q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hra := hmin a (Finset.mem_insert_self _ _)
    have has : a-1+1=a := by omega
    have hj := ih (fun q hq => hmin q (Finset.mem_insert_of_mem hq))
    have hprod : (∏ q ∈ s, (q-1)) ≤ ∏ q ∈ s,q := Finset.prod_le_prod' fun _ _ => Nat.sub_le _ _
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    nlinarith only [Nat.mul_le_mul_left a hj, Nat.mul_le_mul hra hprod,
      congrArg (fun z : ℕ => r*z*(∏ q ∈ s, (q-1))) has]

/-- The integral numerator of a prefix sits strictly above two thirds. -/
private theorem prefix_integer_gap {k B C P Q : ℕ} (hk : 1 < k) (hB : 0 < B) (hP : 0 < P)
    (hQP : Q ≤ P) (he : 3*(k^2+1)*C*Q=2*k*(k+1)*B*P) :
    2*B+1 ≤ 3*C := by
  by_contra! hg
  have h1 := Nat.mul_le_mul (show 3*C ≤ 2*B by omega) hQP
  have h2 := Nat.mul_le_mul_left (k^2+1) h1
  have h3 := Nat.mul_lt_mul_of_pos_right hk (Nat.mul_pos hB hP)
  nlinarith only [he,h2,h3]

private theorem prefix_next_arithmetic {k B C P Q r t : ℕ} (hk : 1 < k)
    (hB : 0 < B) (hP : 0 < P) (hCB : C ≤ B) (hQP : Q ≤ P)
    (he : 3*(k^2+1)*C*Q=2*k*(k+1)*B*P)
    (hsize : 4*B ≤ k) (hloss : r*P ≤ r*Q + t*P) : r ≤ 6*t*B := by
  have hgap := prefix_integer_gap hk hB hP hQP he
  let N := k^2+1
  have hNP : 0 < N*P := Nat.mul_pos (by dsimp [N]; positivity) hP
  have hscaled := Nat.mul_le_mul_right (N*P) hgap
  have hdisc := Nat.mul_le_mul_right k hsize
  have hdisc' : 4 * k * B ≤ N := by dsimp [N]; nlinarith only [hdisc]
  have hfull : N*P + 6*N*C*Q ≤ 6*N*C*P := by
    change 3*N*C*Q=2*k*(k+1)*B*P at he
    have hdiscP := Nat.mul_le_mul_right P hdisc'
    have hN : N=k^2+1 := rfl
    nlinarith only [hscaled,hdiscP,he,congrArg (fun z : ℕ => z*B*P) hN,
      Nat.zero_le (B*P)]
  have hbound : r*(N*P) ≤ 6*t*B*(N*P) := by
    nlinarith only [Nat.mul_le_mul_left r hfull,
      Nat.mul_le_mul_left (6*N*C) hloss, Nat.mul_le_mul_right (6*t*N*P) hCB]
  exact Nat.le_of_mul_le_mul_right hbound hNP

/-- The lower bound on the final denominator for the prefix-growth argument. -/
private theorem full_prefix_denominator {k : ℕ} (hk : 1 < k)
    (he : 3*(k^2+1).totient=2*k*(k+1)) :
    k ≤ 2*(∏ q ∈ (k^2+1).primeFactors, q) := by
  let s := (k^2+1).primeFactors
  let B := ∏ q ∈ s,q
  let C := ∏ q ∈ s,(q-1)
  have hB : 0 < B := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors hq)
  have htotal : 3*(k^2+1)*C=2*k*(k+1)*B := by
    have h := Nat.totient_mul_prod_primeFactors (k^2+1)
    change _*B=(k^2+1)*C at h
    nlinarith only [h, congrArg (fun z : ℕ => z*B) he]
  have hgap := prefix_integer_gap hk hB (by decide : 0<1) (le_refl 1) (by simpa using htotal)
  change k ≤ 2*B
  by_contra! hb
  nlinarith only [Nat.mul_le_mul_right (k^2+1) hgap, htotal, Nat.mul_lt_mul_of_pos_left hb (by omega : 0<k)]

/-- Every proper prefix whose product is at most k/4 admits a small next prime. -/
private theorem euler_prefix_step {k : ℕ} (hk : 1 < k)
    (he : 3*(k^2+1).totient=2*k*(k+1))
    (u : Finset ℕ) (hu : u ⊆ (k^2+1).primeFactors)
    (hlt : u.card < (k^2+1).primeFactors.card) (hsize : 4*(∏ q ∈ u,q) ≤ k) :
    ∃ q ∈ (k^2+1).primeFactors \ u, q ≤ 6*(k^2+1).primeFactors.card*(∏ x ∈ u,x) := by
  let s := (k^2+1).primeFactors
  let v := s \ u
  have hv : v.Nonempty := by
    by_contra! h
    have heq : v=∅ := h
    have : s⊆u := Finset.sdiff_eq_empty_iff_subset.mp heq
    exact (Nat.not_le_of_gt hlt) (Finset.card_le_card this)
  let r := v.min' hv
  have hr : r ∈ v := Finset.min'_mem v hv
  have hh : v ⊆ s := Finset.sdiff_subset
  have hrp : 0<r := Nat.pos_of_mem_primeFactors (hh hr)
  let B := ∏ q ∈ u,q
  let C := ∏ q ∈ u,(q-1)
  let P := ∏ q ∈ v,q
  let Q := ∏ q ∈ v,(q-1)
  have hB : 0 < B := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors (hu hq))
  have hP : 0 < P := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors (hh hq))
  have hCB : C≤B := Finset.prod_le_prod' (fun q _ => Nat.sub_le q 1)
  have hQP : Q≤P := Finset.prod_le_prod' (fun q _ => Nat.sub_le q 1)
  have hPB : P*B=∏ q ∈ s,q := Finset.prod_sdiff hu
  have hQC : Q*C=∏ q ∈ s,(q-1) := Finset.prod_sdiff hu
  have htot := Nat.totient_mul_prod_primeFactors (k^2+1)
  change (k^2+1).totient*(∏ q ∈ s,q)=(k^2+1)*(∏ q ∈ s,(q-1)) at htot
  rw [←hPB,←hQC] at htot
  have hcombine : 3*(k^2+1)*C*Q=2*k*(k+1)*B*P := by
    nlinarith only [htot,congrArg (fun z : ℕ => z*(P*B)) he]
  have hloss := prefix_suffix_loss v hrp (fun q hq => Finset.min'_le _ _ hq)
  have hnext := prefix_next_arithmetic hk hB hP hCB hQP hcombine hsize hloss
  exact ⟨r, hr, hnext.trans (Nat.mul_le_mul_right B (Nat.mul_le_mul_left 6 (Finset.card_le_card hh)))⟩

/-- Uniform LTE bound, including odd exponents. Apply the even-exponent formula
at twice the exponent and remove the even geometric cofactor. -/
private theorem three_power_sub_one_valuation {a : ℕ} (ha : 0 < a) :
    padicValNat 2 (3^a-1) ≤ 2 + padicValNat 2 a := by
  have h3 : 1 < (3:ℕ)^a := one_lt_pow₀ (by decide) ha.ne'
  have h4 : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2^2) = 2
    exact padicValNat.prime_pow 2
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have h := padicValNat.pow_two_sub_one (x:=3) (n:=a*2) (by decide) (by decide)
    (by positivity) (by exact ⟨a, by ring⟩)
  have he : (3:ℕ)^(a*2)-1 = (3^a-1)*(3^a+1) := by
    rw [pow_mul]
    have hs : 3^a-1+1=3^a := by omega
    have hm := congrArg (fun x : ℕ => x*(3^a+1)) hs
    have hp : 0 < (3^a)^2 := pow_pos (by omega) _
    nlinarith only [hm,Nat.sub_add_cancel hp]
  have heven : 2 ∣ (3:ℕ)^a+1 := by
    have ho := (show Odd (3:ℕ) by decide).pow (n:=a)
    obtain ⟨b,hb⟩ := ho
    omega
  have hval : 1 ≤ padicValNat 2 (3^a+1) :=
    (padicValNat_dvd_iff_le (by positivity : (3:ℕ)^a+1 ≠ 0)).mp (by simpa using heven)
  rw [he,padicValNat.mul (by omega) (by positivity), padicValNat.mul ha.ne' (by decide)] at h
  change padicValNat 2 (3^a-1)+padicValNat 2 (3^a+1)+1 =
    padicValNat 2 4+padicValNat 2 2+(padicValNat 2 a+padicValNat 2 2) at h
  omega

/-- Any prescribed power of four dividing the right-hand side imposes an exponentially
growing lower bound on the exponent of the successor. -/
private theorem power_three_exponent_bound {k a t : ℕ} (ha : 0 < a) (hk : k+1=3^a)
    (hd : 4^t ∣ k*(k+1).totient) : 2^(2*t-3) ≤ a := by
  have hkpos : 0 < k := by have := one_lt_pow₀ (by decide : 1 < (3:ℕ)) ha.ne'; omega
  have hrewrite : (k+1).totient = 3^(a-1)*2 := by
    rw [hk,Nat.totient_prime_pow (by decide : Nat.Prime 3) ha]
  have h3pos : 0 < (3:ℕ)^(a-1) := by positivity
  have hodd : ¬2 ∣ (3:ℕ)^(a-1) := by exact ((show Odd (3:ℕ) by decide).pow).not_two_dvd_nat
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have hdiv : 2^(2*t) ∣ k*(3^(a-1)*2) := by simpa [pow_mul,hrewrite] using hd
  have hval := (padicValNat_dvd_iff_le (by positivity : k*(3^(a-1)*2) ≠ 0)).mp hdiv
  rw [padicValNat.mul hkpos.ne' (by positivity), padicValNat.mul h3pos.ne' (by decide),
    padicValNat.eq_zero_of_not_dvd hodd,h2] at hval
  have hpre := three_power_sub_one_valuation ha
  rw [show 3^a-1=k by omega] at hpre
  apply Nat.le_of_dvd ha
  exact (padicValNat_dvd_iff_le ha.ne').mpr (by omega)

/-- The totient equality with a power of three as successor occurs
precisely for k = 2 and k = 8. -/
private theorem power_three_classification {k a : ℕ} (hpow : k+1 = 3^a) :
    (k^2+1).totient = k*(k+1).totient ↔ k = 2 ∨ k = 8 := by
  constructor
  swap
  · rintro (rfl | rfl) <;> decide
  intro heq
  by_cases h2 : a ≤ 2
  · interval_cases a <;> norm_num at hpow
    · have hk : k = 0 := by omega
      simp [hk] at heq
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have ha : 3 ≤ a := by omega
  have hk : 8 < k := by
    have hb := Nat.pow_le_pow_right (by decide : 0 < 3) ha
    norm_num at hb
    omega
  have hod : Odd (k+1) := hpow ▸ (show Odd (3^a) from (by decide : Odd 3).pow)
  have hkeven : Even k := by obtain ⟨m, hm⟩ := hod; exact ⟨m, by omega⟩
  have h3 : 3 ∣ k+1 := hpow ▸ dvd_pow_self 3 (by omega)
  have ht := five_quadratic_primes_of_three_dvd hk hkeven h3 heq
  have hak : 0 < a := by omega
  obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero hak.ne'
  have hphi : 3*(k+1).totient = 2*(k+1) := by
    rw [hpow,hb,Nat.totient_prime_pow_succ Nat.prime_three,pow_succ]
    ring
  have heratio : 3*(k^2+1).totient = 2*k*(k+1) := by
    nlinarith only [congrArg (fun z : ℕ => 3*z) heq, congrArg (fun z : ℕ => k*z) hphi]
  have hgt : 1 < k := by omega
  have hsmall := prefix_growth_bound (show 0 < (k^2+1).primeFactors.card by omega)
    (full_prefix_denominator hgt heratio) (euler_prefix_step hgt heratio)
  have hodd_quad : Odd (k^2+1) := by
    obtain ⟨m,hm⟩ := hkeven
    exact ⟨2*m^2, by rw [hm]; ring⟩
  have hd := four_pow_quadratic_factors_dvd
    (show ∀ p ∈ (k^2+1).primeFactors, p ≠ 2 by
      rintro p hp rfl
      exact hodd_quad.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  rw [heq] at hd
  have hg := power_three_growth ht (power_three_exponent_bound hak hpow hd)
  omega

/-- In a totient equality with a prime-power successor, every quadratic prime divisor
strictly exceeds the prime underlying the successor. -/
private theorem prime_gt_successor_base {k r a p : ℕ} (hk : 1 < k)
    (hr : r.Prime) (hpow : k + 1 = r ^ (a + 1))
    (heq : (k ^ 2 + 1).totient = k * (k + 1).totient)
    (hp : p.Prime) (hdiv : p ∣ k ^ 2 + 1) : r < p := by
  have hrs := hr.one_lt
  have hps := hp.one_lt
  have hrsub : r - 1 + 1 = r := by omega
  have hpsub : p - 1 + 1 = p := by omega
  have hbound := prime_factor_bound hp hdiv
  have hle := (k ^ 2 + 1).totient_le
  let t := (k ^ 2 + 1).totient
  change p * t ≤ (p - 1) * (k ^ 2 + 1) at hbound
  change t ≤ k ^ 2 + 1 at hle
  have hbound' : p * (k ^ 2 + 1 - t) ≥ k ^ 2 + 1 := by
    have hd : k ^ 2 + 1 - t + t = k ^ 2 + 1 := by omega
    nlinarith [congrArg (fun z : ℕ => z * (k ^ 2 + 1)) hpsub,
      congrArg (fun z : ℕ => p * z) hd]
  by_contra! hpr
  have hh := (hbound'.trans (Nat.mul_le_mul_right _ hpr))
  have heq' : r * t = (r - 1) * k * (k + 1) := by
    dsimp [t]
    rw [heq, hpow, Nat.totient_prime_pow_succ hr, pow_succ]
    ring
  have hd : k ^ 2 + 1 - t + t = k ^ 2 + 1 := by omega
  nlinarith [congrArg (fun z : ℕ => r * z) hd,
    congrArg (fun z : ℕ => z * (k ^ 2 + 1)) hrsub,
    Nat.mul_pos (show 0 < r-1 by omega) (show 0 < k-1 by omega),
    Nat.mul_le_mul_left (r - 1) (show 2 ≤ k by omega)]

/-- The integral numerator of a prefix sits strictly above two thirds. -/
private theorem ratio_prefix_integer_gap {g a k B C P Q : ℕ} (ha : 0<a) (hk : 1 < k) (hB : 0 < B) (hP : 0 < P)
    (hQP : Q ≤ P) (he : g*(k^2+1)*C*Q=a*k*(k+1)*B*P) :
    a*B+1 ≤ g*C := by
  by_contra! hg
  have h1 := Nat.mul_le_mul (show g*C ≤ a*B by omega) hQP
  have h2 := Nat.mul_le_mul_left (k^2+1) h1
  have h3 := Nat.mul_lt_mul_of_pos_right hk (Nat.mul_pos ha (Nat.mul_pos hB hP))
  nlinarith only [he,h2,h3]

private theorem ratio_prefix_next_arithmetic {g a k B C P Q r t : ℕ} (ha : 0<a) (hk : 1 < k)
    (hB : 0 < B) (hP : 0 < P) (hCB : C ≤ B) (hQP : Q ≤ P)
    (he : g*(k^2+1)*C*Q=a*k*(k+1)*B*P)
    (hsize : 2*a*B ≤ k) (hloss : r*P ≤ r*Q + t*P) : r ≤ 2*g*t*B := by
  have hgap := ratio_prefix_integer_gap ha hk hB hP hQP he
  let N := k^2+1
  have hNP : 0 < N*P := Nat.mul_pos (by dsimp [N]; positivity) hP
  have hscaled := Nat.mul_le_mul_right (N*P) hgap
  have hdisc := Nat.mul_le_mul_right k hsize
  have hdisc' : 2 * a * k * B ≤ N := by dsimp [N]; nlinarith only [hdisc]
  have hfull : N*P + 2*g*N*C*Q ≤ 2*g*N*C*P := by
    change g*N*C*Q=a*k*(k+1)*B*P at he
    have hdiscP := Nat.mul_le_mul_right P hdisc'
    have hN : N=k^2+1 := rfl
    nlinarith only [hscaled,hdiscP,he,congrArg (fun z : ℕ => z*(a*B*P)) hN,
      Nat.zero_le (a*B*P)]
  have hbound : r*(N*P) ≤ 2*g*t*B*(N*P) := by
    nlinarith only [Nat.mul_le_mul_left r hfull,
      Nat.mul_le_mul_left (2*g*N*C) hloss, Nat.mul_le_mul_right (2*g*t*N*P) hCB]
  exact Nat.le_of_mul_le_mul_right hbound hNP

/-- The lower bound on the final denominator for the prefix-growth argument. -/
private theorem ratio_full_prefix_denominator {g a k : ℕ} (ha : 0<a) (hk : 1 < k)
    (he : g*(k^2+1).totient=a*k*(k+1)) :
    k ≤ a*(∏ q ∈ (k^2+1).primeFactors, q) := by
  let s := (k^2+1).primeFactors
  let B := ∏ q ∈ s,q
  let C := ∏ q ∈ s,(q-1)
  have hB : 0 < B := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors hq)
  have htotal : g*(k^2+1)*C=a*k*(k+1)*B := by
    have h := Nat.totient_mul_prod_primeFactors (k^2+1)
    change _*B=(k^2+1)*C at h
    nlinarith only [congrArg (fun z : ℕ => g*z) h, congrArg (fun z : ℕ => z*B) he]
  have hgap := ratio_prefix_integer_gap ha hk hB (by decide : 0<1) (le_refl 1) (by simpa using htotal)
  change k ≤ a*B
  by_contra! hb
  nlinarith only [Nat.mul_le_mul_right (k^2+1) hgap, htotal, Nat.mul_lt_mul_of_pos_left hb (by omega : 0<k), Nat.zero_le (a*B)]

/-- Every proper prefix whose product is at most k/4 admits a small next prime. -/
private theorem euler_ratio_prefix_step {g a k : ℕ} (ha : 0<a) (hk : 1 < k)
    (he : g*(k^2+1).totient=a*k*(k+1))
    (u : Finset ℕ) (hu : u ⊆ (k^2+1).primeFactors)
    (hlt : u.card < (k^2+1).primeFactors.card) (hsize : 2*a*(∏ q ∈ u,q) ≤ k) :
    ∃ q ∈ (k^2+1).primeFactors \ u, q ≤ 2*g*(k^2+1).primeFactors.card*(∏ x ∈ u,x) := by
  let s := (k^2+1).primeFactors
  let v := s \ u
  have hv : v.Nonempty := by
    by_contra! h
    have heq : v=∅ := h
    have : s⊆u := Finset.sdiff_eq_empty_iff_subset.mp heq
    exact (Nat.not_le_of_gt hlt) (Finset.card_le_card this)
  let r := v.min' hv
  have hr : r ∈ v := Finset.min'_mem v hv
  have hh : v ⊆ s := Finset.sdiff_subset
  have hrp : 0<r := Nat.pos_of_mem_primeFactors (hh hr)
  let B := ∏ q ∈ u,q
  let C := ∏ q ∈ u,(q-1)
  let P := ∏ q ∈ v,q
  let Q := ∏ q ∈ v,(q-1)
  have hB : 0 < B := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors (hu hq))
  have hP : 0 < P := Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors (hh hq))
  have hCB : C≤B := Finset.prod_le_prod' (fun q _ => Nat.sub_le q 1)
  have hQP : Q≤P := Finset.prod_le_prod' (fun q _ => Nat.sub_le q 1)
  have hPB : P*B=∏ q ∈ s,q := Finset.prod_sdiff hu
  have hQC : Q*C=∏ q ∈ s,(q-1) := Finset.prod_sdiff hu
  have htot := Nat.totient_mul_prod_primeFactors (k^2+1)
  change (k^2+1).totient*(∏ q ∈ s,q)=(k^2+1)*(∏ q ∈ s,(q-1)) at htot
  rw [←hPB,←hQC] at htot
  have hcombine : g*(k^2+1)*C*Q=a*k*(k+1)*B*P := by
    nlinarith only [congrArg (fun z : ℕ => g*z) htot,congrArg (fun z : ℕ => z*(P*B)) he]
  have hloss := prefix_suffix_loss v hrp (fun q hq => Finset.min'_le _ _ hq)
  have hnext := ratio_prefix_next_arithmetic ha hk hB hP hCB hQP hcombine hsize hloss
  exact ⟨r, hr, hnext.trans (Nat.mul_le_mul_right B (Nat.mul_le_mul_left (2*g) (Finset.card_le_card hh)))⟩

private theorem prime_power_euler_gap_bound {k p a : ℕ} (hk : 1<k) (hp : p.Prime)
    (hpow : k+1=p^a) (heq : (k^2+1).totient=k*(k+1).totient) :
    k ≤ (2*p*(k^2+1).primeFactors.card)^(2^(k^2+1).primeFactors.card) := by
  have hap : 0<a := by
    by_contra! h
    have hz : a=0 := by omega
    simp [hz] at hpow
    omega
  have hp' : 0<p-1 := by have := hp.two_le; omega
  obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero hap.ne'
  have hphi : p*(k+1).totient=(p-1)*(k+1) := by
    rw [hpow,hb,Nat.totient_prime_pow_succ hp,pow_succ]
    ring
  have h : p*(k^2+1).totient=(p-1)*k*(k+1) := by
    nlinarith only [congrArg (fun x : ℕ => p*x) heq,congrArg (fun x : ℕ => k*x) hphi]
  have ht := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by nlinarith : 1<k^2+1))
  exact prefix_growth_prime_base hp.two_le ht
    (ratio_full_prefix_denominator hp' hk h) (euler_ratio_prefix_step hp' hk h)

/-- Uniform LTE bound, including odd exponents. Apply the even-exponent formula
at twice the exponent and remove the even geometric cofactor. -/
private theorem five_power_sub_one_valuation {a : ℕ} (ha : 0 < a) :
    padicValNat 2 (5^a-1) ≤ 2 + padicValNat 2 a := by
  have h3 : 1 < (5:ℕ)^a := one_lt_pow₀ (by decide) ha.ne'
  have h4 : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2^2) = 2
    exact padicValNat.prime_pow 2
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have h6 : padicValNat 2 6 = 1 := by
    change padicValNat 2 (2*3)=1
    rw [padicValNat.mul (by decide) (by decide),h2,padicValNat.eq_zero_of_not_dvd (by decide : ¬2 ∣ 3)]
  have h := padicValNat.pow_two_sub_one (x:=5) (n:=a*2) (by decide) (by decide)
    (by positivity) (by exact ⟨a, by ring⟩)
  have he : (5:ℕ)^(a*2)-1 = (5^a-1)*(5^a+1) := by
    rw [pow_mul]
    have hs : 5^a-1+1=5^a := by omega
    have hm := congrArg (fun x : ℕ => x*(5^a+1)) hs
    have hp : 0 < (5^a)^2 := pow_pos (by omega) _
    nlinarith only [hm,Nat.sub_add_cancel hp]
  have heven : 2 ∣ (5:ℕ)^a+1 := by
    have ho := (show Odd (5:ℕ) by decide).pow (n:=a)
    obtain ⟨b,hb⟩ := ho
    omega
  have hval : 1 ≤ padicValNat 2 (5^a+1) :=
    (padicValNat_dvd_iff_le (by positivity : (5:ℕ)^a+1 ≠ 0)).mp (by simpa using heven)
  rw [he,padicValNat.mul (by omega) (by positivity), padicValNat.mul ha.ne' (by decide)] at h
  change padicValNat 2 (5^a-1)+padicValNat 2 (5^a+1)+1 =
    padicValNat 2 6+padicValNat 2 4+(padicValNat 2 a+padicValNat 2 2) at h
  omega

/-- Any prescribed power of four dividing the right-hand side imposes an exponentially
growing lower bound on the exponent of the successor. -/
private theorem power_five_exponent_dvd {k a t : ℕ} (ha : 0 < a) (hk : k+1=5^a)
    (hd : 4^t ∣ k*(k+1).totient) : 2^(2*t-4) ∣ a := by
  have hkpos : 0 < k := by have := one_lt_pow₀ (by decide : 1 < (5:ℕ)) ha.ne'; omega
  have hrewrite : (k+1).totient = 5^(a-1)*4 := by
    rw [hk,Nat.totient_prime_pow (by decide : Nat.Prime 5) ha]
  have h3pos : 0 < (5:ℕ)^(a-1) := by positivity
  have hodd : ¬2 ∣ (5:ℕ)^(a-1) := by exact ((show Odd (5:ℕ) by decide).pow).not_two_dvd_nat
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have h4 : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2^2) = 2
    exact padicValNat.prime_pow 2
  have hdiv : 2^(2*t) ∣ k*(5^(a-1)*4) := by simpa [pow_mul,hrewrite] using hd
  have hval := (padicValNat_dvd_iff_le (by positivity : k*(5^(a-1)*4) ≠ 0)).mp hdiv
  rw [padicValNat.mul hkpos.ne' (by positivity), padicValNat.mul h3pos.ne' (by decide),
    padicValNat.eq_zero_of_not_dvd hodd,h4] at hval
  have hpre := five_power_sub_one_valuation ha
  rw [show 5^a-1=k by omega] at hpre
  exact (padicValNat_dvd_iff_le ha.ne').mpr (by omega)

private theorem five_pow_double_exp_base {t : ℕ} (ht : 6 ≤ t) :
    10 * t + 2 ≤ 5 ^ (2 ^ (t-4)) := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [show t+1-4 = (t-4)+1 by omega, pow_succ, pow_mul, pow_two]
    nlinarith only [Nat.mul_le_mul ih ih, Nat.zero_le (t*t), ht]

private theorem power_five_growth {t a : ℕ} (ht : 6 ≤ t) (ha : 2^(2*t-4) ≤ a) :
    (10*t)^(2^t)+1 < 5^a := by
  have hb := five_pow_double_exp_base ht
  have hm : 0 < (2:ℕ)^t := by positivity
  have h1 := Nat.pow_lt_pow_left (show 10*t < 10*t+1 by omega) hm.ne'
  have h2 := Nat.pow_lt_pow_left (show 10*t+1 < 10*t+2 by omega) hm.ne'
  calc
    (10*t)^(2^t)+1 < (10*t+2)^(2^t) := by omega
    _ ≤ (5^(2^(t-4)))^(2^t) := Nat.pow_le_pow_left hb _
    _ = 5^(2^(2*t-4)) := by
      rw [← pow_mul, ← pow_add, show t-4+t=2*t-4 by omega]
    _ ≤ 5^a := Nat.pow_le_pow_right (by decide) ha

/-- At exponent 64, the factor 37 forces 36 to divide the totient, which
contradicts the explicit right hand side modulo 36. -/
private theorem not_solution_exponent_sixty_four {k : ℕ} (hk : k+1=5^64) :
    (k^2+1).totient ≠ k*(k+1).totient := by
  intro heq
  have hk' : k=(5:ℕ)^64-1 := by omega
  have hd : 37 ∣ k^2+1 := by rw [hk']; decide
  have hf := Nat.totient_dvd_of_dvd hd
  rw [Nat.totient_prime (by decide : Nat.Prime 37),heq,hk,
    Nat.totient_prime_pow (by decide : Nat.Prime 5) (by decide : 0 < 64),hk'] at hf
  exact (by decide : ¬ (37-1) ∣ (5^64-1)*(5^(64-1)*(5-1))) hf

/-- No solution with a power of five as successor can have five or more
quadratic primes and meet the Euler-product upper bound. -/
private theorem power_five_gap_contradiction {k a t : ℕ} (ha : 0 < a) (ht : 5 ≤ t)
    (hp : k+1=5^a) (heq : (k^2+1).totient = k*(k+1).totient)
    (hd : 4^t ∣ k*(k+1).totient) (hu : k ≤ (10*t)^(2^t)) : False := by
  have hdiv := power_five_exponent_dvd ha hp hd
  by_cases h6 : 6 ≤ t
  · have hg := power_five_growth h6 (Nat.le_of_dvd ha hdiv)
    omega
  have ht5 : t=5 := by omega
  subst t
  change 64 ∣ a at hdiv
  change k ≤ 50^32 at hu
  have ha128 : a < 128 := by
    by_contra! h
    have hle := Nat.pow_le_pow_right (by decide : 0 < 5) h
    have hbig : 50^32 + 1 < (5:ℕ)^128 := by decide
    omega
  have ha64 : a=64 := by omega
  exact not_solution_exponent_sixty_four (ha64 ▸ hp) heq

private theorem five_factors_of_power_five {k a : ℕ} (ha : 3 ≤ a) (hk : k+1=5^a)
    (heq : (k^2+1).totient=k*(k+1).totient) : 5 ≤ (k^2+1).primeFactors.card := by
  have hkbig : 124 ≤ k := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 5) ha
    norm_num at h
    omega
  let N := k^2+1
  let s := N.primeFactors
  have hpos : 0 < N := by dsimp [N]; positivity
  have hcard : 0<s.card := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by dsimp [N]; nlinarith))
  obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  have hpow : k+1=5^(b+1) := by simpa [hb] using hk
  have hphi : 5*N.totient=4*k*(k+1) := by
    have h : 5*(k+1).totient=4*(k+1) := by
      rw [hpow,Nat.totient_prime_pow_succ (by decide : Nat.Prime 5),pow_succ]
      ring
    change 5*(k^2+1).totient=4*k*(k+1)
    nlinarith only [congrArg (fun z : ℕ => 5*z) heq,congrArg (fun z : ℕ => k*z) h]
  have hlow (p : ℕ) (hps : p ∈ s) : 13 ≤ p ∧ 4 ∣ p-1 := by
    have hp := Nat.prime_of_mem_primeFactors hps
    have hd : p ∣ k^2+1 := Nat.dvd_of_mem_primeFactors hps
    have hp5 := prime_gt_successor_base (by omega : 1<k) (by decide : Nat.Prime 5) hpow heq hp hd
    have h4 := four_dvd_quadratic_prime_sub_one hp (by omega) hd
    refine ⟨?_,h4⟩
    by_contra! h
    have h9 : p=9 := by omega
    exact (by decide : ¬ Nat.Prime 9) (h9 ▸ hp)
  have h17 (p : ℕ) (hps : p ∈ s) (hg : 13 < p) : 17 ≤ p := by
    have := (hlow p hps).2
    omega
  have h29 (p : ℕ) (hps : p ∈ s) (hg : 17 < p) : 29 ≤ p := by
    have := (hlow p hps).2
    have hp := Nat.prime_of_mem_primeFactors hps
    by_contra! h
    rcases (show p=21 ∨ p=25 by omega) with rfl | rfl
    · exact (by decide : ¬Nat.Prime 21) hp
    · exact (by decide : ¬Nat.Prime 25) hp
  have h37 (p : ℕ) (hps : p ∈ s) (hg : 29 < p) : 37 ≤ p := by
    have := (hlow p hps).2
    have hp := Nat.prime_of_mem_primeFactors hps
    by_contra! h
    have h33 : p=33 := by omega
    exact (by decide : ¬ Nat.Prime 33) (h33 ▸ hp)
  change 5 ≤ s.card
  by_contra! h
  have hbound : 193536*N ≤ 237133*N.totient := by
    interval_cases hₜ : s.card
    · let e := s.orderEmbOfFin hₜ
      have hmem (i : Fin 1) : e i ∈ s := s.orderEmbOfFin_mem hₜ i
      have h₀ := (hlow (e 0) (hmem 0)).1
      let c : Fin 1 → ℕ := ![13]
      have hc (i : Fin 1) : 0<c i ∧ c i≤e i := by
        fin_cases i
        · exact ⟨by decide,h₀⟩
      have hb := (factor_profile_bound hpos hₜ c hc).2
      simp [c, Fin.prod_univ_succ] at hb
      omega
    · let e := s.orderEmbOfFin hₜ
      have hmem (i : Fin 2) : e i ∈ s := s.orderEmbOfFin_mem hₜ i
      have h₀ := (hlow (e 0) (hmem 0)).1
      have h₁ := h17 (e 1) (hmem 1) (lt_of_le_of_lt h₀ (e.strictMono (show (0:Fin 2)<1 by decide)))
      let c : Fin 2 → ℕ := ![13,17]
      have hc (i : Fin 2) : 0<c i ∧ c i≤e i := by
        fin_cases i
        · exact ⟨by decide,h₀⟩
        · exact ⟨by decide,h₁⟩
      have hb := (factor_profile_bound hpos hₜ c hc).2
      simp [c, Fin.prod_univ_succ] at hb
      omega
    · let e := s.orderEmbOfFin hₜ
      have hmem (i : Fin 3) : e i ∈ s := s.orderEmbOfFin_mem hₜ i
      have h₀ := (hlow (e 0) (hmem 0)).1
      have h₁ := h17 (e 1) (hmem 1) (lt_of_le_of_lt h₀ (e.strictMono (show (0:Fin 3)<1 by decide)))
      have h₂ := h29 (e 2) (hmem 2) (lt_of_le_of_lt h₁ (e.strictMono (show (1:Fin 3)<2 by decide)))
      let c : Fin 3 → ℕ := ![13,17,29]
      have hc (i : Fin 3) : 0<c i ∧ c i≤e i := by
        fin_cases i
        · exact ⟨by decide,h₀⟩
        · exact ⟨by decide,h₁⟩
        · exact ⟨by decide,h₂⟩
      have hb := (factor_profile_bound hpos hₜ c hc).2
      simp [c, Fin.prod_univ_succ] at hb
      omega
    · let e := s.orderEmbOfFin hₜ
      have hmem (i : Fin 4) : e i ∈ s := s.orderEmbOfFin_mem hₜ i
      have h₀ := (hlow (e 0) (hmem 0)).1
      have h₁ := h17 (e 1) (hmem 1) (lt_of_le_of_lt h₀ (e.strictMono (show (0:Fin 4)<1 by decide)))
      have h₂ := h29 (e 2) (hmem 2) (lt_of_le_of_lt h₁ (e.strictMono (show (1:Fin 4)<2 by decide)))
      have h₃ := h37 (e 3) (hmem 3) (lt_of_le_of_lt h₂ (e.strictMono (show (2:Fin 4)<3 by decide)))
      let c : Fin 4 → ℕ := ![13,17,29,37]
      have hc (i : Fin 4) : 0<c i ∧ c i≤e i := by
        fin_cases i
        · exact ⟨by decide,h₀⟩
        · exact ⟨by decide,h₁⟩
        · exact ⟨by decide,h₂⟩
        · exact ⟨by decide,h₃⟩
      have hb := (factor_profile_bound hpos hₜ c hc).2
      simp [c, Fin.prod_univ_succ] at hb
      omega
  dsimp [N] at hphi hbound
  nlinarith only [hbound, hphi, Nat.mul_le_mul_left k hkbig]

/-- For a successor which is a power of five, the equality holds exactly at four. -/
private theorem power_five_classification {k a : ℕ} (hpow : k+1=5^a) :
    (k^2+1).totient = k*(k+1).totient ↔ k=4 := by
  constructor
  swap
  · rintro rfl
    decide
  intro heq
  by_cases h2 : a ≤ 2
  · interval_cases a <;> norm_num at hpow
    · have hk : k = 0 := by omega
      simp [hk] at heq
    · omega
    · have hk : k=24 := by omega
      subst k
      rw [show 24^2+1=577 by decide, Nat.totient_prime (by norm_num : Nat.Prime 577),
        show 24+1=5^2 by decide, Nat.totient_prime_pow (by decide : Nat.Prime 5)
        (by decide : 0 < 2)] at heq
      norm_num at heq
  have ha : 3 ≤ a := by omega
  have hk : 1 < k := by
    have hb := Nat.pow_le_pow_right (by decide : 0 < 5) ha
    norm_num at hb
    omega
  have hp := five_factors_of_power_five ha hpow heq
  have hu := prime_power_euler_gap_bound hk (by decide : Nat.Prime 5) hpow heq
  have hodd : Odd (k+1) := hpow ▸ (show Odd (5^a) from (by decide : Odd 5).pow)
  obtain ⟨m,hm⟩ := hodd
  have hke : k=m+m := by omega
  have hquad : Odd (k^2+1) := ⟨2*m^2, by rw [hke]; ring⟩
  have hd := four_pow_quadratic_factors_dvd
    (show ∀ p ∈ (k^2+1).primeFactors, p ≠ 2 by
      rintro p hp rfl
      exact hquad.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  rw [heq] at hd
  exact (power_five_gap_contradiction (by omega) hp hpow heq hd hu).elim

/-- An odd solution greater than one must lie in this remaining arithmetic case. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 < k → Odd k →
    (k ^ 2 + 1).totient = k * (k + 1).totient →
    (∀ p d : ℕ, p.Prime → k = p * d → p ≤ d ^ 2) →
    ¬ (k ^ 2 + 1).Prime →
    (∀ p q : ℕ, p.Prime → q.Prime → k ^ 2 + 1 ≠ p * q) →
    16 ∣ (k + 1).totient →
    (∀ p : ℕ, p.Prime → k + 1 ≠ 2 * p ∧ k + 1 ≠ 4 * p ∧ k + 1 ≠ 8 * p) → False

/-- For even inputs the quadratic must have at least three distinct primes if squarefree. -/
def H2 : Prop :=
  ∀ k : ℕ, 1 < k → Even k →
    (k ^ 2 + 1).totient = k * (k + 1).totient →
    (∀ p d : ℕ, p.Prime → k = p * d → p ≤ d ^ 2) →
    ¬ (k ^ 2 + 1).Prime →
    (∀ p q : ℕ, p.Prime → q.Prime → k ^ 2 + 1 ≠ p * q) →
    (Squarefree (k ^ 2 + 1) → 64 ∣ k * (k + 1).totient) →
    (∀ a : ℕ, k + 1 ≠ 3 ^ a ∧ k + 1 ≠ 5 ^ a) → (k + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA67720.prime_add_one_of_a := by
  intro hOdd hEven k heq h8
  change (k ^ 2 + 1).totient = k * (k + 1).totient at heq
  by_contra hcom
  have hk : 1 < k := by
    by_contra! h
    interval_cases k <;> simp_all [Nat.prime_two]
  have hn : ¬ (k ^ 2 + 1).Prime := by
    intro hn
    rw [Nat.totient_prime hn, Nat.add_sub_cancel, pow_two] at heq
    have ht := Nat.eq_of_mul_eq_mul_left (show 0 < k by omega) heq
    exact hcom ((Nat.totient_eq_iff_prime (by omega)).mp (by omega))
  have hsize (p d : ℕ) (hp : p.Prime) (hpd : k = p * d) : p ≤ d ^ 2 := by
    subst k
    apply factor_le_cofactor_sq hp _ hn
    rw [heq]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hsemi (p q : ℕ) (hp : p.Prime) (hq : q.Prime) : k ^ 2 + 1 ≠ p * q :=
    fun hpq => (semiprime_case hp hq hpq heq).elim h8 hcom
  have hpow3 (a : ℕ) : k + 1 ≠ 3 ^ a := by
    intro h
    rcases (power_three_classification h).mp heq with h2 | h8'
    · subst k
      exact hcom (by decide)
    · exact h8 h8'
  have hpow5 (a : ℕ) : k + 1 ≠ 5 ^ a := by
    intro h
    have hk4 := (power_five_classification h).mp heq
    subst k
    exact hcom (by decide)
  rcases Nat.even_or_odd k with he | ho
  · apply hcom (hEven k hk he heq hsize hn hsemi ?_ (fun a => ⟨hpow3 a, hpow5 a⟩))
    intro hsf
    by_contra h64
    have hodd : ∀ p ∈ (k ^ 2 + 1).primeFactors, p ≠ 2 := by
      intro p hp h
      subst p
      have hd := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨a, ha⟩ := he
      have ho : Odd (k ^ 2 + 1) := ⟨2*a^2, by rw [ha]; ring⟩
      exact ho.not_two_dvd_nat hd
    exact (low_valuation_squarefree hk heq hsf hodd h64
      (fun _ _ hp hq _ hpq => semiprime_case hp hq hpq heq)).elim h8 hcom
  · apply hOdd k hk ho heq hsize hn hsemi (sixteen_dvd_successor_totient_of_odd hk ho heq)
    intro p hp
    exact ⟨fun h => not_totient_eq_of_successor_twice_prime hp h heq,
      fun h => not_totient_eq_of_successor_four_times_prime hp h heq,
      fun h => not_totient_eq_of_successor_eight_times_prime hp h heq⟩

end OMA.R_OeisA67720_prime_add_one_of_a_R1
