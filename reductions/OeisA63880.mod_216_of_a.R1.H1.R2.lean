import OMAReductions.R_OeisA63880_mod_216_of_a_R1

-- Credit: @PanPapag. The unitary divisor sum decomposition is adapted from
-- desenyon's reduction in PR 1353.
-- A prime power contributes (p*x-1)/((p-1)*(x+1)), where x is that prime
-- power. For three odd primes the limiting product leaves only the supports
-- (3,5,7), (3,5,11), and (3,5,13). For each support, six exponent intervals
-- per prime suffice: singletons 1 through 5, then the entire tail from 6.
open OeisA63880
open scoped ArithmeticFunction.sigma

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2

private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

theorem local_bound {p k a : ℕ} (hp : p.Prime) (hk : k+1 ≤ p) :
    k * σ 1 (p^a) < (k+1)*(p^a+1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  induction a with
  | zero => simp; omega
  | succ a ih =>
    rw [Finset.sum_range_succ, Nat.pow_succ p a, Nat.mul_add]
    have h := Nat.mul_le_mul_right (p^a) hk
    nlinarith

theorem triple_bound {p q r a b c i j k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hi : i+1 ≤ p) (hj : j+1 ≤ q) (hk : k+1 ≤ r)
    (h : A (p^a*q^b*r^c)) : 2*i*j*k < (i+1)*(j+1)*(k+1) := by
  have pq := ((Nat.coprime_primes hp hq).2 hpq).pow a b
  have pr := ((Nat.coprime_primes hp hr).2 hpr).pow a c
  have qr := ((Nat.coprime_primes hq hr).2 hqr).pow b c
  have pqr := pr.mul_left qr
  have U : usigma (p^a) = p^a+1 := by
    have t := unitarySum (m := 1) (q := p^a) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨p,a,hp,ha,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simpa [one] using t
  have eqn := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pqr,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pq,
    unitarySum (Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)) ((isPrimePow_nat_iff _).2 ⟨r,c,hr,hc,rfl⟩) pqr.symm,
    unitarySum (pow_pos hp.pos a) ((isPrimePow_nat_iff _).2 ⟨q,b,hq,hb,rfl⟩) pq.symm,
    U] at eqn
  have lim := Nat.mul_lt_mul_of_lt_of_lt
    (Nat.mul_lt_mul_of_lt_of_lt (local_bound (a := a) hp hi) (local_bound (a := b) hq hj))
    (local_bound (a := c) hr hk)
  let D := (p^a+1)*(q^b+1)*(r^c+1)
  have scaled : (2*i*j*k)*D < ((i+1)*(j+1)*(k+1))*D := by
    dsimp [D]
    calc
      _ = (i*j*k)*(2*((p^a+1)*(q^b+1)*(r^c+1))) := by ring
      _ = _ := by rw [← eqn]; ring
      _ < _ := lim
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_right scaled
theorem odd_triple_support {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ho : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : A (p^a*q^b*r^c)) :
    p = 3 ∧ q = 5 ∧ (r = 7 ∨ r = 11 ∨ r = 13) := by
  have bound := @triple_bound p q r a b c
  have psmall : p < 5 := by
    by_contra! hh
    have bad := @bound 4 4 4 hp hq hr hpq.ne (hpq.trans hqr).ne hqr.ne ha hb hc
      (by omega) (by omega) (by omega) h
    omega
  have p3 : p = 3 := by interval_cases p <;> norm_num at *
  subst p
  have qsmall : q < 7 := by
    by_contra! hh
    have hr9 : 9 ≤ r := by
      by_contra! tmp
      have : r = 8 := by omega
      subst r
      norm_num at hr
    have bad := @bound 2 6 8 hp hq hr hpq.ne (hpq.trans hqr).ne hqr.ne ha hb hc
      (by decide) (by omega) (by omega) h
    omega
  have q5 : q = 5 := by interval_cases q <;> norm_num at *
  subst q
  have rsmall : r < 17 := by
    by_contra! hh
    have bad := @bound 2 4 16 hp hq hr hpq.ne (hpq.trans hqr).ne hqr.ne ha hb hc
      (by decide) (by decide) (by omega) h
    omega
  refine ⟨rfl, rfl, ?_⟩
  interval_cases r <;> norm_num at *

private theorem separated {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : A (p^a*q^b*r^c)) :
    σ 1 (p^a) * σ 1 (q^b) * σ 1 (r^c) = 2*((p^a+1)*(q^b+1)*(r^c+1)) := by
  have pq := ((Nat.coprime_primes hp hq).2 hpq.ne).pow a b
  have pr := ((Nat.coprime_primes hp hr).2 (hpq.trans hqr).ne).pow a c
  have qr := ((Nat.coprime_primes hq hr).2 hqr.ne).pow b c
  have pqr := pr.mul_left qr
  have U : usigma (p^a) = p^a+1 := by
    have t := unitarySum (m := 1) (q := p^a) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨p,a,hp,ha,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simpa [one] using t
  have eqn := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pqr,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pq,
    unitarySum (Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)) ((isPrimePow_nat_iff _).2 ⟨r,c,hr,hc,rfl⟩) pqr.symm,
    unitarySum (pow_pos hp.pos a) ((isPrimePow_nat_iff _).2 ⟨q,b,hq,hb,rfl⟩) pq.symm,
    U] at eqn
  exact eqn

set_option maxRecDepth 15000 in
set_option maxHeartbeats 5000000 in
theorem odd_triple_exclusion {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ho : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ¬ A (p^a*q^b*r^c) := by
  let rat (p : ℕ) (x : ℚ) : ℚ :=
    (p*x-1)/(((p:ℚ)-1)*(x+1))

  have rat_mono {p : ℕ} (hp : 2 ≤ p) {x y : ℚ}
      (hx : 0 ≤ x) (hxy : x ≤ y) : rat p x ≤ rat p y := by
    have h : (2:ℚ) ≤ p := by exact_mod_cast hp
    have hy : 0 ≤ y := hx.trans hxy
    unfold rat
    apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ (p:ℚ)^2-1 by nlinarith)]

  have rat_upper {p : ℕ} (hp : 2 ≤ p) {x : ℚ} (hx : 0 ≤ x) :
      rat p x ≤ (p:ℚ)/(p-1) := by
    have h : (2:ℚ) ≤ p := by exact_mod_cast hp
    unfold rat
    apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)).2
    nlinarith

  have rat_sigma {p : ℕ} (hp : p.Prime) (a : ℕ) :
      rat p ((p:ℚ)^a) = (σ 1 (p^a) : ℚ)/((p:ℚ)^a+1) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    change p = k+1 at hk
    have hg := geom_sum_mul_add k (a+1)
    rw [← hk, ← ArithmeticFunction.sigma_one_apply_prime_pow hp, pow_succ] at hg
    have he : (σ 1 (p^a):ℚ) * k + 1 = (p:ℚ)^a*p := by exact_mod_cast hg
    have hl : (2:ℚ) ≤ p := by exact_mod_cast hp.two_le
    have hk' : (p:ℚ) = k+1 := by exact_mod_cast hk
    have hx : 0 < (p:ℚ)^a+1 := by positivity
    unfold rat
    rw [div_mul_eq_div_div, div_left_inj' hx.ne']
    apply (div_eq_iff (by linarith : (p:ℚ)-1 ≠ 0)).2
    have hk2 : (p:ℚ)-1 = k := by linarith
    rw [hk2]
    linarith

  let low (p : ℕ) (i : Fin 6) := rat p ((p:ℚ)^(i.val+1))
  let high (p : ℕ) (i : Fin 6) :=
    if i.val = 5 then (p:ℚ)/(p-1) else low p i

  have box {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
      ∃ i : Fin 6, low p i ≤ rat p ((p:ℚ)^a) ∧ rat p ((p:ℚ)^a) ≤ high p i := by
    by_cases h : a ≤ 5
    · let i : Fin 6 := ⟨a-1, by omega⟩
      have hi : i.val+1 = a := by dsimp [i]; omega
      have hh : i.val ≠ 5 := by dsimp [i]; omega
      exact ⟨i, by simp [low,hi], by simp [high,hh,low,hi]⟩
    · refine ⟨5, rat_mono hp.two_le (by positivity) ?_, rat_upper hp.two_le (by positivity)⟩
      apply pow_le_pow_right₀ (by exact_mod_cast hp.one_le)
      change 6 ≤ a
      omega

  have low_nn {p : ℕ} (hp : p.Prime) (i : Fin 6) : 0 ≤ low p i := by
    unfold low
    rw [rat_sigma hp]
    positivity

  let cert (r : ℕ) := ∀ i j k : Fin 6,
    2 < low 3 i * low 5 j * low r k ∨ high 3 i * high 5 j * high r k < 2

  have certs : cert 7 ∧ cert 11 ∧ cert 13 := by dsimp only [cert, low, high, rat]; decide +kernel

  intro h
  obtain ⟨rfl,rfl,hrs⟩ := odd_triple_support hp hq hr ho hpq hqr ha hb hc h
  have certR : cert r := by rcases hrs with rfl|rfl|rfl; exact certs.1; exact certs.2.1; exact certs.2.2
  obtain ⟨i, il, iu⟩ := box hp ha
  obtain ⟨j, jl, ju⟩ := box hq hb
  obtain ⟨k, kl, ku⟩ := box hr hc
  have eqn := separated hp hq hr hpq hqr ha hb hc h
  have e : rat 3 (((3:ℕ):ℚ)^a)*rat 5 (((5:ℕ):ℚ)^b)*rat r ((r:ℚ)^c) = 2 := by
    rw [rat_sigma hp, rat_sigma hq, rat_sigma hr, div_mul_div_comm, div_mul_div_comm]
    apply (div_eq_iff (by positivity)).2
    exact_mod_cast eqn
  have i0 := low_nn hp i
  have j0 := low_nn hq j
  have k0 := low_nn hr k
  rcases certR i j k with lt | gt
  · have bound := mul_le_mul (mul_le_mul il jl j0 (i0.trans il)) kl k0
      (mul_nonneg (i0.trans il) (j0.trans jl))
    linarith
  · have bound := mul_le_mul (mul_le_mul iu ju (j0.trans jl) ((i0.trans il).trans iu)) ku
      (k0.trans kl) (mul_nonneg ((i0.trans il).trans iu) ((j0.trans jl).trans ju))
    linarith

theorem two_prime_exclusion {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    ¬ A (p^a*q^b) := by
  intro h
  have hc := ((Nat.coprime_primes hp hq).2 hne).pow a b
  have U {r e : ℕ} (hr : r.Prime) (he : 0 < e) : usigma (r^e) = r^e+1 := by
    have t := unitarySum (m := 1) (q := r^e) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨r,e,hr,he,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simpa [one] using t
  have eqn := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
    unitarySum (pow_pos hp.pos a) ((isPrimePow_nat_iff _).2 ⟨q,b,hq,hb,rfl⟩) hc.symm,
    U hp ha] at eqn
  have lim := Nat.mul_lt_mul_of_lt_of_lt (local_bound (a := a) hp hp3)
    (local_bound (a := b) hq hq5)
  nlinarith only [lim, eqn, Nat.zero_le ((p^a+1)*(q^b+1))]


def H1 : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card = 4 → ¬ A n

def H2 : Prop := ∀ n : ℕ, Odd n → 5 ≤ n.primeFactors.card → ¬ A n

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1.H1 := by
  intro h1 h2 n ho h
  have hn := h.1.ne'
  have fac := Nat.prod_primeFactors_pow_factorization hn
  have info {p : ℕ} (hm : p ∈ n.primeFactors) :
      p.Prime ∧ 3 ≤ p ∧ 0 < n.factorization p := by
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.1 hm
    refine ⟨hp, ?_, hp.factorization_pos_of_dvd hn hd⟩
    have := hp.two_le
    obtain ⟨k,hk⟩ := ho
    by_contra! lt
    have : p = 2 := by omega
    subst p
    omega
  have small : n.primeFactors.card ≤ 3 := by
    by_contra! large
    by_cases he : n.primeFactors.card = 4
    · exact h1 n ho he h
    · exact h2 n ho (by omega) h
  interval_cases hh : n.primeFactors.card
  · rw [Finset.card_eq_zero.1 hh, Finset.prod_empty] at fac
    have bad : A 1 := fac ▸ h
    have eqn := bad.2
    have one : usigma 1 = 1 := by decide
    simp [one] at eqn
  · obtain ⟨p,hs⟩ := Finset.card_eq_one.1 hh
    obtain ⟨hp,hp3,ha⟩ := info (p := p) (by simp [hs])
    rw [hs, Finset.prod_singleton] at fac
    rw [fac] at h
    have U := unitarySum (m := 1) (q := p^(n.factorization p)) (by decide)
      ((isPrimePow_nat_iff _).2 ⟨p,_,hp,ha,rfl⟩) (Nat.coprime_one_right _)
    have one : usigma 1 = 1 := by decide
    simp only [one_mul, one] at U
    have eqn := h.2
    rw [U] at eqn
    have lim := local_bound (a := n.factorization p) (k := 1) hp hp.two_le
    omega
  · obtain ⟨p,q,hpq,hs⟩ := Finset.card_eq_two.1 hh
    obtain ⟨hp,hp3,ha⟩ := info (p := p) (by simp [hs])
    obtain ⟨hq,hq3,hb⟩ := info (p := q) (by simp [hs])
    rw [hs, Finset.prod_pair hpq] at fac
    rw [fac] at h
    have gap {v w : ℕ} (hv : 3 ≤ v) (hw : w.Prime) (lt : v < w) : 5 ≤ w := by
      by_contra! hh
      have : w = 4 := by omega
      subst w
      norm_num at hw
    rcases lt_or_gt_of_ne hpq with lt|lt
    · exact two_prime_exclusion hp hq hp3 (gap hp3 hq lt) hpq ha hb h
    · rw [mul_comm] at h
      exact two_prime_exclusion hq hp hq3 (gap hq3 hp lt) hpq.symm hb ha h
  · obtain ⟨p,q,r,hpq,hpr,hqr,hs⟩ := Finset.card_eq_three.1 hh
    obtain ⟨hp,hp3,ha⟩ := info (p := p) (by simp [hs])
    obtain ⟨hq,hq3,hb⟩ := info (p := q) (by simp [hs])
    obtain ⟨hr,hr3,hc⟩ := info (p := r) (by simp [hs])
    rw [hs, Finset.prod_insert (by simp [hpq,hpr]), Finset.prod_pair hqr] at fac
    rw [fac] at h
    by_cases ordpqr : p < q ∧ q < r
    · exact odd_triple_exclusion hp hq hr hp3 ordpqr.1 ordpqr.2 ha hb hc (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    by_cases ordprq : p < r ∧ r < q
    · exact odd_triple_exclusion hp hr hq hp3 ordprq.1 ordprq.2 ha hc hb (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    by_cases ordqpr : q < p ∧ p < r
    · exact odd_triple_exclusion hq hp hr hq3 ordqpr.1 ordqpr.2 hb ha hc (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    by_cases ordqrp : q < r ∧ r < p
    · exact odd_triple_exclusion hq hr hp hq3 ordqrp.1 ordqrp.2 hb hc ha (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    by_cases ordrpq : r < p ∧ p < q
    · exact odd_triple_exclusion hr hp hq hr3 ordrpq.1 ordrpq.2 hc ha hb (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    by_cases ordrqp : r < q ∧ q < p
    · exact odd_triple_exclusion hr hq hp hr3 ordrqp.1 ordrqp.2 hc hb ha (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    omega

end OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2
