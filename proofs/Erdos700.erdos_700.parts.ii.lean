import FormalConjectures.ErdosProblems.«700»

/-!
Erdős–Szekeres, problem 700(b). This formalizes the elementary prime-triple
argument of Adam Tresmontant. The Lucas digit bounds and Chebyshev/pigeonhole
proof below are adapted from implicitall's PRs 1393 and 1422, following
their reduction in PR 1069. Marcus Buffett also formalized the two steps
in PRs 1285 and 1261. The independent argument prompted by Price is cited
on the Erdős Problems page. We also identify the exact minimum at k = r
and quantify the approximation of f(n)^3 by n^2.

https://www.erdosproblemaday.com/day/700-tresmontant-elementary-proof-of-b-checked
https://www.erdosproblems.com/700
-/

namespace OMA_E700H1

lemma dig {P x y : ℕ} (hP : P.Prime) (h : ¬ P ∣ x.choose y) :
    y % P ≤ x % P ∧ ¬ P ∣ (x / P).choose (y / P) := by
  have := Fact.mk hP
  have hm : x.choose y ≡ (x % P).choose (y % P) * (x / P).choose (y / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hiff := Nat.ModEq.dvd_iff hm (dvd_refl P)
  constructor
  · by_contra hlt
    push Not at hlt
    apply h
    rw [hiff, Nat.choose_eq_zero_of_lt hlt, zero_mul]
    exact dvd_zero P
  · intro hd
    apply h
    rw [hiff]
    exact Dvd.dvd.mul_left hd _

lemma dm {P x u v : ℕ} (h : x = P * u + v) (hv : v < P) : x % P = v ∧ x / P = u := by
  have hP : 0 < P := by omega
  have e : P * u + v = v + P * u := by ring
  subst h
  rw [e]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hv, zero_add]


lemma ar_ab (a b p : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) : a * b < p := by
  have : a * b ≤ b * b := Nat.mul_le_mul_right b hab
  nlinarith

lemma ar_apb (a b p : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) : a + b < p := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp at hab; subst hab; omega
  · have : b ≤ b ^ 2 := by nlinarith
    omega

lemma ar_prod (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : 2 * j ≤ p + b) :
    (p + a) * j < p * p := by
  have h1 := ar_ab a b p hab hs
  have h2 := ar_apb a b p hab hs
  have h3 : 2 * ((p + a) * j) ≤ (p + a) * (p + b) := by
    have := Nat.mul_le_mul_left (p + a) hj
    linarith
  have h4 : (p + a) * (p + b) < 2 * (p * p) := by
    have : (a + b + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    nlinarith
  omega

lemma ar_aj (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : j ≤ a + b) : a * j < p := by
  have : a * j ≤ b * (2 * b) := Nat.mul_le_mul hab (by omega)
  nlinarith


/-- Case: `p` and `q = p + a` both fail to divide. -/
lemma casePQ (p a c j : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + (2 * a + 1 + c))
    (h1 : ¬ p ∣ ((p + a) * (p + (2 * a + 1 + c))).choose ((p + a) * j))
    (h2 : ¬ (p + a) ∣ (p * (p + (2 * a + 1 + c))).choose (p * j)) : False := by
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  obtain ⟨d1, d1'⟩ := dig hp h1
  have d2 := (dig hp d1').1
  obtain ⟨e1, e2⟩ := dm (P := p) (x := (p + a) * (p + b)) (u := p + a + b) (v := a * b)
    (by ring) hab
  rw [e1] at d1
  rw [e2] at d2
  obtain ⟨e3, -⟩ := dm (P := p) (x := p + a + b) (u := 1) (v := a + b) (by ring) hapb
  rw [e3] at d2
  have hlt : (p + a) * j < p * p := ar_prod a b p j hab' hs hj2
  have hjle : j ≤ (p + a) * j / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    have := Nat.mul_le_mul_right j (show p ≤ p + a by omega)
    linarith
  have hdlt : (p + a) * j / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at d2
  have hjab : j ≤ a + b := by omega
  have haj : a * j < p := ar_aj a b p j hab' hs hjab
  obtain ⟨e4, -⟩ := dm (P := p) (x := (p + a) * j) (u := j) (v := a * j) (by ring) haj
  rw [e4] at d1
  have hjb : j ≤ b := by
    by_contra hh; push Not at hh
    have : a * b < a * j := Nat.mul_lt_mul_of_pos_left hh ha
    omega
  -- base q = p + a
  obtain ⟨f1, f1'⟩ := dig hq h2
  have f2 := (dig hq f1').1
  have hw : a * (a + 1 + c) < p := ar_ab a (a + 1 + c) p (by omega)
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)) hs)
  obtain ⟨v, hv⟩ : ∃ v, p + a = a * (a + 1 + c) + v := ⟨p + a - a * (a + 1 + c), by omega⟩
  have hw1 : 1 ≤ a * (a + 1 + c) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hvq : v < p + a := by omega
  obtain ⟨g1, g2⟩ := dm (P := p + a) (x := p * (p + b)) (u := p + a + c) (v := v)
    (by rw [hb]; zify at hv ⊢; linear_combination hv) hvq
  rw [g1] at f1
  rw [g2] at f2
  have hc : c < p + a := by
    have : c ≤ b := by omega
    have : b < p := by omega
    omega
  obtain ⟨g3, -⟩ := dm (P := p + a) (x := p + a + c) (u := 1) (v := c) (by ring) hc
  rw [g3] at f2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have haj2 : a * (j' + 1) < p + a := by
    have : a * (j' + 1) ≤ a * b := Nat.mul_le_mul_left a hjb
    omega
  obtain ⟨t, ht⟩ : ∃ t, p + a = a * (j' + 1) + t := ⟨p + a - a * (j' + 1), by omega⟩
  have hta : 1 ≤ a * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + a := by omega
  obtain ⟨g4, g5⟩ := dm (P := p + a) (x := p * (j' + 1)) (u := j') (v := t)
    (by zify at ht ⊢; linear_combination ht) htq
  rw [g4] at f1
  rw [g5] at f2
  have hj'q : j' < p + a := by omega
  rw [Nat.mod_eq_of_lt hj'q] at f2
  have h3 : a * (a + 1 + c) ≤ a * (j' + 1) := by omega
  have := Nat.le_of_mul_le_mul_left h3 ha
  omega


lemma ar_prod' (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : 2 * j ≤ p + a) :
    (p + b) * j < p * p := by
  have h1 := ar_ab a b p hab hs
  have h2 := ar_apb a b p hab hs
  have h3 : 2 * ((p + b) * j) ≤ (p + b) * (p + a) := by
    have := Nat.mul_le_mul_left (p + b) hj
    linarith
  have h4 : (p + b) * (p + a) < 2 * (p * p) := by
    have : (a + b + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    nlinarith
  omega

/-- `p * q` written in base `r = p + b`. -/
lemma pq_base_r (p a c : ℕ) (hs : 2 * (2 * a + 1 + c) ^ 2 < p) :
    (p * (p + a)) % (p + (2 * a + 1 + c)) = (2 * a + 1 + c) * (a + 1 + c) := by
  have hb : a + 1 + c ≤ 2 * a + 1 + c := by omega
  have hm : (2 * a + 1 + c) * (a + 1 + c) < p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) (by nlinarith)
  have hle : a + 1 + c ≤ (2 * a + 1 + c) * (a + 1 + c) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨u, hu⟩ : ∃ u, p = u + (a + 1 + c) := ⟨p - (a + 1 + c), by omega⟩
  refine (dm (P := p + (2 * a + 1 + c)) (u := u) (by rw [hu]; ring) (by omega)).1

/-- Case: `p` and `r = p + b` both fail to divide. -/
lemma casePR (p a c j : ℕ) (hp : p.Prime) (hr : (p + (2 * a + 1 + c)).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + a)
    (h1 : ¬ p ∣ ((p + (2 * a + 1 + c)) * (p + a)).choose ((p + (2 * a + 1 + c)) * j))
    (h2 : ¬ (p + (2 * a + 1 + c)) ∣ (p * (p + a)).choose (p * j)) : False := by
  have hpq := pq_base_r p a c hs
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  obtain ⟨d1, d1'⟩ := dig hp h1
  have d2 := (dig hp d1').1
  obtain ⟨e1, e2⟩ := dm (P := p) (x := (p + b) * (p + a)) (u := p + a + b) (v := a * b)
    (by ring) hab
  rw [e1] at d1
  rw [e2] at d2
  obtain ⟨e3, -⟩ := dm (P := p) (x := p + a + b) (u := 1) (v := a + b) (by ring) hapb
  rw [e3] at d2
  have hlt : (p + b) * j < p * p := ar_prod' a b p j hab' hs hj2
  have hjle : j ≤ (p + b) * j / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    have := Nat.mul_le_mul_right j (show p ≤ p + b by omega)
    linarith
  have hdlt : (p + b) * j / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at d2
  have hjab : j ≤ a + b := by omega
  have hbj : b * j < p := ar_aj b b p j le_rfl hs (by omega)
  obtain ⟨e4, -⟩ := dm (P := p) (x := (p + b) * j) (u := j) (v := b * j) (by ring) hbj
  rw [e4] at d1
  have hja : j ≤ a := by
    by_contra hh; push Not at hh
    have : b * a < b * j := Nat.mul_lt_mul_of_pos_left hh (by omega)
    have : a * b = b * a := Nat.mul_comm a b
    omega
  -- base r = p + b, one digit suffices
  have f1 := (dig hr h2).1
  rw [hpq] at f1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hbj2 : b * (j' + 1) ≤ b * a := Nat.mul_le_mul_left b hja
  obtain ⟨t, ht⟩ : ∃ t, p + b = b * (j' + 1) + t := ⟨p + b - b * (j' + 1), by omega⟩
  have hta : 1 ≤ b * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + b := by omega
  obtain ⟨g4, -⟩ := dm (P := p + b) (x := p * (j' + 1)) (u := j') (v := t)
    (by zify at ht ⊢; linear_combination ht) htq
  rw [g4] at f1
  -- f1 : t ≤ b * (a + 1 + c), so p + b ≤ b * a + b * (a + 1 + c) = b * b < p
  have hbb : b * a + b * (a + 1 + c) = b * b := by rw [hb]; ring
  have : b * b < p := by nlinarith
  omega

/-- Case: `q = p + a` and `r = p + b` both fail to divide. -/
lemma caseQR (p a c j : ℕ) (hq : (p + a).Prime) (hr : (p + (2 * a + 1 + c)).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p)
    (h1 : ¬ (p + a) ∣ ((p + (2 * a + 1 + c)) * p).choose ((p + (2 * a + 1 + c)) * j))
    (h2 : ¬ (p + (2 * a + 1 + c)) ∣ ((p + a) * p).choose ((p + a) * j)) : False := by
  have hpq := pq_base_r p a c hs
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  -- base q = p + a, two digits
  obtain ⟨f1, f1'⟩ := dig hq h1
  have f2 := (dig hq f1').1
  have hw : a * (a + 1 + c) < p := lt_of_le_of_lt (Nat.mul_le_mul_left a (by omega)) hab
  obtain ⟨v, hv⟩ : ∃ v, p + a = a * (a + 1 + c) + v := ⟨p + a - a * (a + 1 + c), by omega⟩
  have hw1 : 1 ≤ a * (a + 1 + c) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hvq : v < p + a := by omega
  obtain ⟨g1, g2⟩ := dm (P := p + a) (x := (p + b) * p) (u := p + a + c) (v := v)
    (by rw [hb]; zify at hv ⊢; linear_combination hv) hvq
  rw [g2] at f2
  have hc : c < p + a := by omega
  obtain ⟨g3, -⟩ := dm (P := p + a) (x := p + a + c) (u := 1) (v := c) (by ring) hc
  rw [g3] at f2
  have hlt : (p + b) * j < (p + a) * (p + a) := by
    have h3 : 2 * ((p + b) * j) ≤ (p + b) * p := by
      have := Nat.mul_le_mul_left (p + b) hj2
      linarith
    have h4 : (p + b) * p < 2 * ((p + a) * (p + a)) := by
      have : b * p < p * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      nlinarith
    omega
  have hjle : j ≤ (p + b) * j / (p + a) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.mul_le_mul_right j (show p + a ≤ p + b by omega)
    linarith
  have hdlt : (p + b) * j / (p + a) < p + a := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at f2
  have hjc : j ≤ c := by omega
  -- base r = p + b, one digit
  have k1 := (dig hr h2).1
  have hpq' : (p + a) * p = p * (p + a) := Nat.mul_comm _ _
  rw [hpq', hpq] at k1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hm : (a + 1 + c) * (j' + 1) ≤ (a + 1 + c) * c := Nat.mul_le_mul_left _ hjc
  have hmc : (a + 1 + c) * c < p := by
    have : (a + 1 + c) * c ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, p + b = (a + 1 + c) * (j' + 1) + t :=
    ⟨p + b - (a + 1 + c) * (j' + 1), by omega⟩
  have hta : 1 ≤ (a + 1 + c) * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + b := by omega
  obtain ⟨g4, -⟩ := dm (P := p + b) (x := (p + a) * (j' + 1)) (u := j') (v := t)
    (by rw [hb] at ht ⊢; zify at ht ⊢; linear_combination ht) htq
  rw [g4] at k1
  -- k1 : t ≤ b * (a + 1 + c); so p + b ≤ (a+1+c) * (j'+1) + b * (a+1+c) < 2 b^2 < p
  have h5 : (a + 1 + c) * (j' + 1) + b * (a + 1 + c) ≤ 2 * b ^ 2 := by
    have : (a + 1 + c) * (j' + 1) ≤ b * b := le_trans hm (Nat.mul_le_mul (by omega) (by omega))
    have : b * (a + 1 + c) ≤ b * b := Nat.mul_le_mul_left b (by omega)
    nlinarith
  omega


lemma red {P X Y : ℕ} (hP : P.Prime) (h : ¬ P ∣ (P * X).choose (P * Y)) : ¬ P ∣ X.choose Y := by
  have := (dig hP h).2
  rwa [Nat.mul_div_cancel_left _ hP.pos, Nat.mul_div_cancel_left _ hP.pos] at this

lemma key (p a c k : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + (2 * a + 1 + c)).Prime)
    (ha : 0 < a) (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hk1 : 1 < k)
    (hk2 : k ≤ p * (p + a) * (p + (2 * a + 1 + c)) / 2) :
    p * (p + a) ≤ Nat.gcd (p * (p + a) * (p + (2 * a + 1 + c)))
      ((p * (p + a) * (p + (2 * a + 1 + c))).choose k) := by
  set b := 2 * a + 1 + c with hb
  set n := p * (p + a) * (p + b) with hn
  have hp2 := hp.two_le
  have hn0 : 0 < n := by positivity
  have hg0 : 0 < Nat.gcd n (n.choose k) := Nat.gcd_pos_of_pos_left _ hn0
  have hk2' : k * 2 ≤ n := (Nat.le_div_iff_mul_le two_pos).mp hk2
  have cpq : Nat.Coprime p (p + a) := (Nat.coprime_primes hp hq).2 (by omega)
  have cpr : Nat.Coprime p (p + b) := (Nat.coprime_primes hp hr).2 (by omega)
  have cqr : Nat.Coprime (p + a) (p + b) := (Nat.coprime_primes hq hr).2 (by omega)
  have dpn : p ∣ n := ⟨(p + a) * (p + b), by rw [hn]; ring⟩
  have dqn : (p + a) ∣ n := ⟨p * (p + b), by rw [hn]; ring⟩
  have drn : (p + b) ∣ n := ⟨p * (p + a), by rw [hn]; ring⟩
  by_cases h1 : p ∣ n.choose k <;> by_cases h2 : (p + a) ∣ n.choose k <;>
    by_cases h3 : (p + b) ∣ n.choose k
  · exact Nat.le_of_dvd hg0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq
      (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd dqn h2))
  · exact Nat.le_of_dvd hg0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq
      (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd dqn h2))
  · refine le_trans (Nat.mul_le_mul_left p (by omega)) (Nat.le_of_dvd hg0
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpr (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd drn h3)))
  · -- only p divides: q and r do not
    exfalso
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    have hrk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hr drn h3
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cqr hqk hrk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p := by
      have : (p + a) * (p + b) * (2 * j) ≤ (p + a) * (p + b) * p := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = (p + a) * ((p + b) * p) := by rw [hn]; ring
    have e2 : (p + a) * (p + b) * j = (p + a) * ((p + b) * j) := by ring
    have e3 : n = (p + b) * ((p + a) * p) := by rw [hn]; ring
    have e4 : (p + a) * (p + b) * j = (p + b) * ((p + a) * j) := by ring
    have h2' := h2
    rw [e1, e2] at h2'
    rw [e3, e4] at h3
    exact caseQR p a c j hq hr ha hs hj hj2 (red hq h2') (red hr h3)
  · refine le_trans ?_ (Nat.le_of_dvd hg0
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cqr (Nat.dvd_gcd dqn h2) (Nat.dvd_gcd drn h3)))
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  · -- only q divides: p and r do not
    exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hrk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hr drn h3
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpr hpk hrk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + a := by
      have : p * (p + b) * (2 * j) ≤ p * (p + b) * (p + a) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + b) * (p + a)) := by rw [hn]; ring
    have e2 : p * (p + b) * j = p * ((p + b) * j) := by ring
    have e3 : n = (p + b) * (p * (p + a)) := by rw [hn]; ring
    have e4 : p * (p + b) * j = (p + b) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h3
    exact casePR p a c j hp hr ha hs hj hj2 (red hp h1') (red hr h3)
  · -- only r divides (or none): p and q do not
    exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hpk hqk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + b := by
      have : p * (p + a) * (2 * j) ≤ p * (p + a) * (p + b) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + a) * (p + b)) := by rw [hn]; ring
    have e2 : p * (p + a) * j = p * ((p + a) * j) := by ring
    have e3 : n = (p + a) * (p * (p + b)) := by rw [hn]; ring
    have e4 : p * (p + a) * j = (p + a) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h2
    exact casePQ p a c j hp hq ha hs hj hj2 (red hp h1') (red hq h2)
  · exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hpk hqk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + b := by
      have : p * (p + a) * (2 * j) ≤ p * (p + a) * (p + b) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + a) * (p + b)) := by rw [hn]; ring
    have e2 : p * (p + a) * j = p * ((p + a) * j) := by ring
    have e3 : n = (p + a) * (p * (p + b)) := by rw [hn]; ring
    have e4 : p * (p + a) * j = (p + a) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h2
    exact casePQ p a c j hp hq ha hs hj hj2 (red hp h1') (red hq h2)

end OMA_E700H1

namespace OMA_E700H2

open Finset

lemma cheb (n : ℕ) (hn : 0 < n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := by
  refine le_trans (Nat.four_pow_le_two_mul_add_one_mul_central_binom n) ?_
  apply Nat.mul_le_mul_left
  have hC0 : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  calc (2 * n).choose n
      = ∏ p ∈ ((2 * n).choose n).primeFactors, p ^ ((2 * n).choose n).factorization p :=
        Nat.prod_primeFactors_pow_factorization hC0
    _ ≤ (2 * n) ^ ((2 * n).choose n).primeFactors.card :=
        Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_factorization_choose_le (by omega))
    _ ≤ (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [Nat.count_eq_card_filter_range]
        apply Finset.card_le_card
        intro p hp
        have hp' := Nat.mem_primeFactors.mp hp
        have hv : 0 < ((2 * n).choose n).factorization p :=
          hp'.1.factorization_pos_of_dvd hC0 hp'.2.1
        have h1 : p ≤ p ^ ((2 * n).choose n).factorization p := Nat.le_self_pow hv.ne' p
        have h2 : p ^ ((2 * n).choose n).factorization p ≤ 2 * n :=
          Nat.pow_factorization_choose_le (by omega)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp'.1⟩

lemma chebPow (s : ℕ) :
    2 ^ (s + 1) ≤ s + 2 + (s + 1) * Nat.count Nat.Prime (2 ^ (s + 1) + 1) := by
  have h := cheb (2 ^ s) (by positivity)
  have e1 : 2 * 2 ^ s = 2 ^ (s + 1) := by ring
  rw [e1] at h
  have e2 : (4 : ℕ) ^ (2 ^ s) = 2 ^ (2 ^ (s + 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have e3 : 2 ^ (s + 1) + 1 ≤ 2 ^ (s + 2) := by
    have : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (s + 1)]; omega
  have e4 : ((2 : ℕ) ^ (s + 1)) ^ Nat.count Nat.Prime (2 ^ (s + 1) + 1) =
      2 ^ ((s + 1) * Nat.count Nat.Prime (2 ^ (s + 1) + 1)) := by rw [← pow_mul]
  rw [e2, e4] at h
  set c := Nat.count Nat.Prime (2 ^ (s + 1) + 1) with hc
  have h2 : 2 ^ (2 ^ (s + 1)) ≤ 2 ^ (s + 2 + (s + 1) * c) :=
    calc 2 ^ (2 ^ (s + 1)) ≤ (2 ^ (s + 1) + 1) * 2 ^ ((s + 1) * c) := h
      _ ≤ 2 ^ (s + 2) * 2 ^ ((s + 1) * c) := Nat.mul_le_mul_right _ e3
      _ = 2 ^ (s + 2 + (s + 1) * c) := (pow_add 2 (s + 2) ((s + 1) * c)).symm
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

lemma triple (K : ℕ) : ∀ S : Finset ℕ, K + 2 ≤ S.card → (∀ a ∈ S, ∀ b ∈ S, b - a < 2 ^ K) →
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p < q ∧ q < r ∧ q - p < r - q := by
  induction K with
  | zero =>
    intro S hS hd
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have h1 := hd a ha b hb
    have h2 := hd b hb a ha
    simp at h1 h2
    omega
  | succ K ih =>
    intro S hS hd
    have hne : S.Nonempty := Finset.card_pos.mp (show 0 < S.card by omega)
    set x1 := S.min' hne with hx1
    set z := S.max' hne with hz
    have hx1S : x1 ∈ S := Finset.min'_mem S hne
    set S' := S.erase x1 with hS'
    have hS'c : K + 2 ≤ S'.card := by
      rw [hS', Finset.card_erase_of_mem hx1S]; omega
    have hne' : S'.Nonempty := Finset.card_pos.mp (show 0 < S'.card by omega)
    set x2 := S'.min' hne' with hx2
    have hx2S' : x2 ∈ S' := Finset.min'_mem S' hne'
    have hx2S : x2 ∈ S := Finset.mem_of_mem_erase hx2S'
    have hx12 : x1 < x2 := by
      have hne2 : x2 ≠ x1 := Finset.ne_of_mem_erase hx2S'
      have : x1 ≤ x2 := Finset.min'_le S x2 hx2S
      omega
    obtain ⟨w, hw⟩ : (S'.erase x2).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hx2S']; omega)
    have hwS' : w ∈ S' := Finset.mem_of_mem_erase hw
    have hwS : w ∈ S := Finset.mem_of_mem_erase hwS'
    have hw2 : x2 < w := by
      have hne2 : w ≠ x2 := Finset.ne_of_mem_erase hw
      have : x2 ≤ w := Finset.min'_le S' w hwS'
      omega
    have hzS : z ∈ S := Finset.max'_mem S hne
    have hwz : w ≤ z := Finset.le_max' S w hwS
    by_cases h : x2 - x1 < z - x2
    · exact ⟨x1, hx1S, x2, hx2S, z, hzS, hx12, by omega, h⟩
    · have hzx := hd x1 hx1S z hzS
      rw [pow_succ] at hzx
      obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3⟩ := ih S' hS'c (by
        intro a ha b hb
        have : x2 ≤ a := Finset.min'_le S' a ha
        have : b ≤ z := Finset.le_max' S b (Finset.mem_of_mem_erase hb)
        omega)
      exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq, r,
        Finset.mem_of_mem_erase hr, h1, h2, h3⟩

lemma big (m : ℕ) (hm : 10 ≤ m) : 4 * m ^ 2 + 20 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have e : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [e]
    nlinarith

end OMA_E700H2

namespace Erdos700Proof

open OMA_E700H2

private theorem exists_close_triple (N : ℕ) :
    ∃ p q r : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
      q - p < r - q ∧ 2 * (r - p)^2 < p := by
  set m := N + 10 with hm
  set Y := 2 ^ m with hY
  have hYbig : 4 * m ^ 2 + 20 * m ≤ Y := big m (by omega)
  have hY1 : m < Y := Nat.lt_two_pow_self
  have hX : 2 ^ (3 * m) = Y * Y * Y := by rw [hY, ← pow_add, ← pow_add]; ring_nf
  have hch := chebPow (3 * m - 1)
  rw [show 3 * m - 1 + 1 = 3 * m by omega, hX] at hch
  set M := Nat.count Nat.Prime (Y * Y * Y + 1) with hM
  set S := (Finset.Ioc (2 * Y * Y) (Y * Y * Y)).filter Nat.Prime with hS
  have hSc : M ≤ (2 * Y * Y + 1) + S.card := by
    rw [hM, Nat.count_eq_card_filter_range]
    calc ((Finset.range (Y * Y * Y + 1)).filter Nat.Prime).card
        ≤ (Finset.range (2 * Y * Y + 1) ∪ S).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp
          simp only [Finset.mem_union, Finset.mem_range, hS, Finset.mem_filter, Finset.mem_Ioc]
          by_cases h : p ≤ 2 * Y * Y
          · left; omega
          · right; exact ⟨⟨by omega, by omega⟩, hp.2⟩
      _ ≤ _ := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_range]
  -- counting inequality
  have hcount : (Finset.range (Y * Y + 1)).card * (m + 1) < S.card := by
    rw [Finset.card_range]
    have h3m : 3 * m - 1 + 2 = 3 * m + 1 := by omega
    rw [h3m] at hch
    have hY2 : Y * Y * (4 * m ^ 2 + 20 * m) ≤ Y * Y * Y := Nat.mul_le_mul_left _ hYbig
    have hpos : 0 < m := by omega
    have key : 3 * m * ((Y * Y + 1) * (m + 1) + 2 * Y * Y + 1) < 3 * m * M := by nlinarith
    have key2 : (Y * Y + 1) * (m + 1) + 2 * Y * Y + 1 < M := Nat.lt_of_mul_lt_mul_left key
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.range (Y * Y + 1)) (f := fun p => p / Y) (n := m + 1)
    (by
      intro p hp
      simp only [hS, Finset.mem_filter, Finset.mem_Ioc] at hp
      simp only [Finset.mem_range]
      have : p / Y ≤ Y * Y := Nat.div_le_of_le_mul (by nlinarith)
      omega) hcount
  set F := S.filter (fun p => p / Y = i) with hF
  obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3⟩ := triple m F (by omega) (by
    intro a ha b hb
    simp only [hF, Finset.mem_filter] at ha hb
    have hYpos : 0 < Y := by positivity
    have ea := Nat.div_add_mod a Y
    have eb := Nat.div_add_mod b Y
    have ma := Nat.mod_lt a hYpos
    have mb := Nat.mod_lt b hYpos
    rw [ha.2] at ea
    rw [hb.2] at eb
    rw [← hY]
    omega)
  simp only [hF, hS, Finset.mem_filter, Finset.mem_Ioc] at hp hq hr
  have hYpos : 0 < Y := by positivity
  have hrp : r - p < Y := by
    have ea := Nat.div_add_mod p Y
    have eb := Nat.div_add_mod r Y
    have ma := Nat.mod_lt p hYpos
    have mb := Nat.mod_lt r hYpos
    rw [hp.2] at ea
    rw [hr.2] at eb
    omega
  have hsq : (r - p) ^ 2 < Y * Y := by rw [sq]; exact Nat.mul_self_lt_mul_self hrp
  have e2 : 2 * Y * Y = 2 * (Y * Y) := by ring
  refine ⟨p, q, r, ?_, hp.1.2, hq.1.2, hr.1.2, h1, h2, h3, ?_⟩
  · have : Y ≤ 2 * Y * Y := by nlinarith
    omega
  · omega

/-- At index r, one Lucas step excludes r from the gcd. -/
private lemma upper_at_prime {s r : ℕ} (hs : 2 ≤ s) (hr : r.Prime) (hcop : ¬ r ∣ s) :
    Erdos700.f (s * r) ≤ s := by
  have : Fact r.Prime := ⟨hr⟩
  have hmod : (s * r).choose r ≡ s [MOD r] := by
    have h : (s * r).choose r ≡
        ((s * r) % r).choose (r % r) * ((s * r) / r).choose (r / r) [MOD r] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    simpa [Nat.mul_div_cancel _ hr.pos, Nat.div_self hr.pos] using h
  let g := Nat.gcd (s * r) ((s * r).choose r)
  have hrg : ¬ r ∣ g := fun h => hcop ((hmod.dvd_iff (dvd_refl r)).mp
    (h.trans (Nat.gcd_dvd_right _ _)))
  have hgs : g ∣ s :=
    (hr.coprime_iff_not_dvd.mpr hrg).symm.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
  apply (Erdos700.f_le _ r hr.one_lt ?_).trans (Nat.le_of_dvd (by omega) hgs)
  rw [Nat.le_div_iff_mul_le two_pos, Nat.mul_comm r 2]
  exact Nat.mul_le_mul_right r hs

/-- The minimum is attained at the largest prime of every qualifying triple. -/
theorem close_triple_value {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsmall : 2 * (r - p)^2 < p) :
    Erdos700.f (p * q * r) = p * q := by
  have hp2 := hp.two_le
  have hprod : 2 ≤ p * q := hp2.trans (Nat.le_mul_of_pos_right _ hq.pos)
  apply le_antisymm (upper_at_prime hprod hr ?_) ?_
  · exact fun hd => (hr.dvd_mul.mp hd).elim
      (fun h => (not_le_of_gt (hpq.trans hqr)) (Nat.le_of_dvd hp.pos h))
      (fun h => (not_le_of_gt hqr) (Nat.le_of_dvd hq.pos h))
  · obtain ⟨a, rfl⟩ : ∃ a, q = p + a := ⟨q - p, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, r = p + (2 * a + 1 + c) := ⟨r - p - (2 * a + 1), by omega⟩
    rw [Erdos700.f_eq]
    apply le_csInf
    · refine ⟨_, Erdos700.f_mem _ _ hr.one_lt ?_⟩
      rw [Nat.le_div_iff_mul_le two_pos, Nat.mul_comm _ 2]
      exact Nat.mul_le_mul_right _ hprod
    · rintro _ ⟨k, hk1, hk2, rfl⟩
      exact OMA_E700H1.key p a c k hp hq hr (by omega) (by simpa using hsmall) hk1 hk2

/-- A quantitative form of the two-thirds exponent. The relative error in f(n)^3
compared with n^2 can be made smaller than any given positive tolerance. -/
theorem close_triple_witness (N : ℕ) :
    ∃ n > N, ¬ n.Prime ∧ 1 < n ∧ n < (Erdos700.f n)^2 ∧
      (Erdos700.f n)^3 ≤ n^2 ∧ N * (n^2 - (Erdos700.f n)^3) ≤ n^2 := by
  obtain ⟨p, q, r, hN, hp, hq, hr, hpq, hqr, hgap, hsmall⟩ :=
    exists_close_triple ((2 * N + 1)^2)
  have hf := close_triple_value hp hq hr hpq hqr hgap hsmall
  let d := r - p
  have hrd : r = p + d := by dsimp [d]; omega
  have hpd : 2 * d^2 < p := hsmall
  have hNp : N < p := by nlinarith
  have hpr : p < r := hpq.trans hqr
  have hp2 := hp.two_le
  have hd : d < p := by nlinarith
  have hpqr : r < p * q := by nlinarith [Nat.mul_le_mul_right q hp2]
  have hscale : 2 * N * d ≤ r := by
    rcases le_total d (2 * N) with h | h
    · nlinarith [Nat.mul_le_mul_left (2 * N) h]
    · nlinarith [Nat.mul_le_mul_right d h]
  have hs : p * q ≤ r^2 := by simpa [sq] using Nat.mul_le_mul hpr.le hqr.le
  have hdef : r^2 - p*q ≤ 2*d*r := by
    have hsum : r^2 ≤ 2*d*r + p*q := by
      rw [hrd]
      nlinarith [Nat.mul_le_mul_left p hpq.le]
    omega
  have herr : N * (r^2 - p*q) ≤ r^2 := calc
    N * (r^2 - p*q) ≤ N * (2*d*r) := Nat.mul_le_mul_left _ hdef
    _ = (2*N*d)*r := by ring
    _ ≤ r^2 := by simpa [sq] using Nat.mul_le_mul_right r hscale
  have hpos : 0 < p*q := Nat.mul_pos hp.pos hq.pos
  refine ⟨p*q*r, hNp.trans_le ((Nat.le_mul_of_pos_right p hq.pos).trans
    (Nat.le_mul_of_pos_right _ hr.pos)), ?_, ?_, ?_⟩
  · exact Nat.not_prime_mul (by nlinarith : p*q ≠ 1) hr.one_lt.ne'
  · nlinarith [Nat.le_mul_of_pos_right (p*q) hr.pos]
  rw [hf]
  refine ⟨by simpa [sq] using Nat.mul_lt_mul_of_pos_left hpqr hpos, ?_, ?_⟩
  · rw [pow_succ (p*q) 2, mul_pow (p*q) r]
    exact Nat.mul_le_mul_left _ hs
  · have h := Nat.mul_le_mul_left ((p*q)^2) herr
    calc N * ((p*q*r)^2 - (p*q)^3) = (p*q)^2 * (N * (r^2 - p*q)) := by
           rw [mul_pow, pow_succ (p*q) 2, ← Nat.mul_sub, mul_left_comm]
         _ ≤ (p*q*r)^2 := by simpa only [mul_pow] using h

end Erdos700Proof

theorem OMA.solution : type_of% @Erdos700.erdos_700.parts.ii := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hc, h1, hf, _⟩ := Erdos700Proof.close_triple_witness N
  exact ⟨n, ⟨hc, h1, hf⟩, hn⟩
