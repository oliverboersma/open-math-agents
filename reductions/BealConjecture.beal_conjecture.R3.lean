import FormalConjectures.Wikipedia.BealConjecture
import Mathlib.NumberTheory.Multiplicity

/-! A reduction of Beal's conjecture using the two factors of a sum of
odd prime powers. Lifting the exponent identifies the one prime these
factors can share. A multiplicative order condition restricts all primes
in the remaining cyclotomic factor.

Compare the Barlow–Abel identities in https://arxiv.org/html/2509.18275v1
and the primitive-divisor theorem in https://bartmichels.github.io/files/zsigmondy_en.pdf.
The arithmetic implications here are proved directly.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R3

/-- Distinct normalized summand exponents, in increasing order. -/
def H1 : Prop :=
  ∀ a b c i j r : ℕ, 0 < a → 0 < b → 0 < c → a.Coprime b →
    (i = 4 ∨ (i.Prime ∧ Odd i)) → (j = 4 ∨ (j.Prime ∧ Odd j)) →
    (r = 4 ∨ (r.Prime ∧ Odd r)) → i < j → a ^ i + b ^ j ≠ c ^ r

/-- The two quartics, with odd prime output exponent and restricted prime support. -/
def H2 : Prop :=
  ∀ a b c r : ℕ, 0 < a → 0 < b → 0 < c → a.Coprime b → r.Prime → Odd r →
    (∀ q : ℕ, q.Prime → q ∣ c → 8 ∣ q - 1) → a ^ 4 + b ^ 4 ≠ c ^ r

/-- The linear factor is a perfect power. Test its coprime cyclotomic cofactor. -/
def H3 : Prop :=
  ∀ u v p r s t : ℕ, 0 < u → 0 < v → u.Coprime v → p.Prime → Odd p →
    (r = 4 ∨ (r.Prime ∧ Odd r)) → ¬ p ∣ u + v → u + v = s ^ r →
    1 < t → (∀ q : ℕ, q.Prime → q ∣ t → 2 * p ∣ q - 1) →
    (u ^ p + v ^ p) / (u + v) ≠ t ^ r

/-- When the exponent prime divides the linear factor, move exactly one copy
of that prime from the cyclotomic cofactor to the linear factor. -/
def H4 : Prop :=
  ∀ u v p r s t : ℕ, 0 < u → 0 < v → u.Coprime v → p.Prime → Odd p →
    (r = 4 ∨ (r.Prime ∧ Odd r)) → p ∣ u + v → (u + v) * p = s ^ r →
    ¬ p ∣ t → 1 < t → (∀ q : ℕ, q.Prime → q ∣ t → 2 * p ∣ q - 1) →
    (u ^ p + v ^ p) / (u + v) ≠ p * t ^ r


/-- For an odd exponent the 2-part of the sum is the 2-part of the linear factor. -/
private theorem twoVal_sum {u v n : ℕ} (hn : Odd n) (hu : 0 < u)
    (he : 2 ∣ u + v) (hnu : ¬ 2 ∣ u) :
    padicValNat 2 (u ^ n + v ^ n) = padicValNat 2 (u + v) := by
  have he' : (2 : ℤ) ∣ (u : ℤ) - -(v : ℤ) := by
    rw [sub_neg_eq_add]
    exact_mod_cast he
  have hnu' : ¬ (2 : ℤ) ∣ (u : ℤ) := by exact_mod_cast hnu
  have hnn' : ¬ (2 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn.not_two_dvd_nat
  have h := emultiplicity_pow_sub_pow_of_prime Int.prime_two he' hnu' hnn'
  rw [hn.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at h
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity (by positivity), padicValNat_eq_emultiplicity (by omega),
    ← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity]
  push_cast
  exact h

/-- If the sum of powers has no prime outside the support of the linear factor,
it divides the linear factor times the exponent. -/
theorem sum_dvd_of_no_new_prime {u v n : ℕ} (hu : 0 < u) (hc : u.Coprime v)
    (hn : Odd n) (hs : ∀ q : ℕ, q.Prime → q ∣ u ^ n + v ^ n → q ∣ u + v) :
    u ^ n + v ^ n ∣ (u + v) * n := by
  have hn0 := hn.pos
  apply (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mp
  intro q hq
  by_cases hdiv : q ∣ u ^ n + v ^ n
  · have hsum := hs q hq hdiv
    have hqu : ¬ q ∣ u := by
      intro h
      exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq, h, (Nat.dvd_add_iff_right h).mpr hsum⟩) hc
    let : Fact q.Prime := ⟨hq⟩
    rw [Nat.factorization_mul (by omega) hn0.ne', Finsupp.add_apply]
    simp only [Nat.factorization_def _ hq]
    rcases hq.eq_two_or_odd with rfl | ho
    · rw [twoVal_sum hn hu hsum hqu]
      omega
    · exact (padicValNat.pow_add_pow (Nat.odd_iff.mpr ho) hsum hqu hn).le
  · simp [Nat.factorization_eq_zero_of_not_dvd hdiv]

/-- Once the larger base has passed the initial threshold, exponential growth
preserves the strict inequality for every subsequent exponent. -/
private theorem grow {u v n k : ℕ} (huv : u ≤ v) (hv : 2 ≤ v) (hk : 1 ≤ k)
    (hstart : 2 * v * k < v ^ k) (hkn : k ≤ n) :
    (u + v) * n < u ^ n + v ^ n := by
  have step : 2 * v * n < v ^ n := by
    induction n, hkn using Nat.le_induction with
    | base => exact hstart
    | succ m hkm ih =>
      rw [pow_succ]
      have h1 : 2 * v * (m+1) ≤ 2 * v * m * 2 := by
        have hm : m + 1 ≤ m * 2 := by omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (2*v) hm
      calc
        _ ≤ _ := h1
        _ < v ^ m * 2 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hv
  have hsmall := Nat.mul_le_mul_right n (show u + v ≤ 2*v by omega)
  omega

private theorem two_or_nine_ne_high_power {c z : ℕ} (hz : 2 < z) :
    c ^ z ≠ 2 ∧ c ^ z ≠ 9 := by
  rcases lt_or_ge c 3 with hc | hc
  · interval_cases c
    · simp [Nat.ne_of_gt (show 0 < z by omega)]
    · simp
    · rcases eq_or_lt_of_le (show 3 ≤ z by omega) with rfl | h
      · decide
      · have h16 : 16 ≤ 2 ^ z := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ z by omega)
        omega
  · have h27 : 27 ≤ c ^ z := (Nat.pow_le_pow_left hc 3).trans
          (Nat.pow_le_pow_right (by omega) (show 3 ≤ z by omega))
    omega

private theorem new_prime_ordered {u v c n z : ℕ} (hu : 0 < u) (huv : u ≤ v)
    (hc : u.Coprime v) (hn : Odd n) (hn3 : 3 ≤ n) (hz : 2 < z)
    (he : u ^ n + v ^ n = c ^ z) :
    ∃ q : ℕ, q.Prime ∧ q ∣ c ∧ ¬ q ∣ u + v := by
  by_contra! h
  have hs := sum_dvd_of_no_new_prime hu hc hn (by
    intro q hq hd
    exact h q hq (hq.dvd_of_dvd_pow (he ▸ hd)))
  have hn0 := hn.pos
  have bound := Nat.le_of_dvd (by positivity) hs
  by_cases h3 : 3 ≤ v
  · have hstart : 2 * v * 3 < v ^ 3 := by nlinarith [Nat.pow_le_pow_left h3 2]
    exact (not_lt_of_ge bound) (grow huv (by omega) (by decide) hstart hn3)
  by_cases h1 : v = 1
  · have hu1 : u = 1 := by omega
    simp [h1, hu1] at he
    exact (two_or_nine_ne_high_power hz).1 he.symm
  have hv2 : v = 2 := by omega
  subst v
  have hu1 : u = 1 := by
    interval_cases u <;> simp_all
  subst u
  by_cases h5 : 5 ≤ n
  · exact (not_lt_of_ge bound) (grow (by decide : 1 ≤ 2) (by decide) (by decide : 1 ≤ 5) (by decide) h5)
  have hn' : n = 3 := by have := Nat.odd_iff.mp hn; omega
  subst n
  exact (two_or_nine_ne_high_power hz).2 he.symm

theorem exists_new_prime {u v c n z : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hc : u.Coprime v) (hn : Odd n) (hn3 : 3 ≤ n) (hz : 2 < z)
    (he : u ^ n + v ^ n = c ^ z) :
    ∃ q : ℕ, q.Prime ∧ q ∣ c ∧ ¬ q ∣ u + v := by
  rcases le_total u v with h | h
  · exact new_prime_ordered hu h hc hn hn3 hz he
  · simpa only [add_comm v u] using
      new_prime_ordered hv h hc.symm hn hn3 hz (he := (add_comm ..).trans he)

/-- At a new prime the ratio of the signed bases has the full prime-power order. -/
theorem new_prime_congruence {u v p q k : ℕ} (hp : p.Prime) (ho : Odd p) (hq : q.Prime)
    (hc : u.Coprime v) (hs : q ∣ u ^ (p ^ (k+1)) + v ^ (p ^ (k+1)))
    (hns : ¬ q ∣ u ^ (p ^ k) + v ^ (p ^ k)) :
    2 * p ^ (k+1) ∣ q - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hsum : (u : ZMod q) ^ (p ^ (k+1)) + (v : ZMod q) ^ (p ^ (k+1)) = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 hs
  have hnot : (u : ZMod q) ^ (p ^ k) + (v : ZMod q) ^ (p ^ k) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using mt (ZMod.natCast_eq_zero_iff _ _).mp hns
  have hv : (v : ZMod q) ≠ 0 := by
    intro hv
    have hu : (u : ZMod q) ^ (p ^ (k+1)) = 0 := by simpa [hv, hp.ne_zero] using hsum
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq,
      (ZMod.natCast_eq_zero_iff _ _).1 (by by_contra h; exact pow_ne_zero _ h hu), (ZMod.natCast_eq_zero_iff _ _).1 hv⟩) hc
  have hu : (u : ZMod q) ≠ 0 := by
    intro hu
    simp [hu, hp.ne_zero, pow_ne_zero _ hv] at hsum
  let t := -(u : ZMod q) / (v : ZMod q)
  have hratio (j : ℕ) : t ^ (p ^ j) = 1 ↔
      (u : ZMod q) ^ (p ^ j) + (v : ZMod q) ^ (p ^ j) = 0 := by
    rw [show t = _ from rfl, div_pow, (ho.pow).neg_pow, div_eq_iff (pow_ne_zero _ hv), one_mul]
    constructor <;> intro h <;> linear_combination -h
  have horder : orderOf t = p ^ (k+1) :=
    orderOf_eq_prime_pow (mt (hratio k).mp hnot) ((hratio (k+1)).mpr hsum)
  have hd : p ^ (k+1) ∣ q - 1 := horder ▸ ZMod.orderOf_dvd_card_sub_one (div_ne_zero (neg_ne_zero.mpr hu) hv)
  have hpdiv : p ∣ q - 1 := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hd
  have hq2 : q ≠ 2 := by
    intro e
    simp [e, hp.not_dvd_one] at hpdiv
  have hqo := hq.eq_two_or_odd.resolve_left hq2
  exact (Nat.prime_two.coprime_iff_not_dvd.mpr (ho.pow.not_two_dvd_nat)).mul_dvd_of_dvd_of_dvd
    (by omega) hd

private theorem odd_prime_ge_three {p : ℕ} (hp : p.Prime) (ho : Odd p) : 3 ≤ p := by
  have := hp.two_le
  have := Nat.odd_iff.mp ho
  omega

/-- Compute the valuation of the quotient at every prime of the linear factor. -/
private theorem quotient_valuation {u v p q f : ℕ} (hu : 0 < u) (hf : 0 < f)
    (hc : u.Coprime v) (ho : Odd p) (hq : q.Prime) (hd : q ∣ u + v)
    (hfac : u ^ p + v ^ p = (u + v) * f) :
    f.factorization q = p.factorization q := by
  have hqu : ¬ q ∣ u := by
    intro h
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq, h, (Nat.dvd_add_iff_right h).mpr hd⟩) hc
  let : Fact q.Prime := ⟨hq⟩
  simp only [Nat.factorization_def _ hq]
  have h : padicValNat q (u ^ p + v ^ p) = padicValNat q (u+v) + padicValNat q p := by
    rcases hq.eq_two_or_odd with rfl | hodd
    · rw [twoVal_sum ho hu hd hqu, padicValNat.eq_zero_of_not_dvd ho.not_two_dvd_nat, add_zero]
    · exact padicValNat.pow_add_pow (Nat.odd_iff.mpr hodd) hd hqu ho
  rw [hfac, padicValNat.mul (by omega) hf.ne'] at h
  omega

private theorem roots_of_coprime_product {a b c r : ℕ}
    (hc : a.Coprime b) (he : a * b = c ^ r) :
    ∃ s t : ℕ, a = s ^ r ∧ b = t ^ r := by
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hc.gcd_eq_one) he
  obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hc.symm.gcd_eq_one) ((mul_comm b a).trans he)
  exact ⟨s, t, hs, ht⟩

private theorem exclude_equal_odd (h3 : H3) (h4 : H4) {u v c p r : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hc : u.Coprime v) (hp : p.Prime) (ho : Odd p)
    (hr : r = 4 ∨ (r.Prime ∧ Odd r)) :
    u ^ p + v ^ p ≠ c ^ r := by
  intro he
  have hr3 : 3 ≤ r := hr.elim (fun h => by omega) (fun h => odd_prime_ge_three h.1 h.2)
  obtain ⟨q, hq, hqc, hnew⟩ := exists_new_prime hu hv hc ho (odd_prime_ge_three hp ho) hr3 he
  have hqs : q ∣ u ^ p + v ^ p := he ▸ dvd_pow hqc (by omega)
  obtain ⟨f, hfac⟩ := ho.nat_add_dvd_pow_add_pow u v
  have hf : 0 < f := by
    by_contra! h
    have hzero : f = 0 := by omega
    have := pow_pos hu p
    simp [hzero] at hfac
    omega
  have hdiv : (u ^ p + v ^ p) / (u+v) = f := by rw [hfac, Nat.mul_div_cancel_left _ (by omega)]
  have hprod : (u+v) * f = c ^ r := hfac.symm.trans he
  have hqf : q ∣ f := (hq.dvd_mul.mp (hfac ▸ hqs)).resolve_left hnew
  have common {l : ℕ} (hl : l.Prime) (hs : l ∣ u+v) (hd : l ∣ f) : l = p := by
    apply (Nat.prime_dvd_prime_iff_eq hl hp).mp
    apply (hl.dvd_iff_one_le_factorization hp.ne_zero).mpr
    rw [← quotient_valuation hu hf hc ho hl hs hfac]
    exact (hl.dvd_iff_one_le_factorization hf.ne').mp hd
  have all_mod {g : ℕ} (hcop : (u+v).Coprime g) (hg : g ∣ f)
      (l : ℕ) (hl : l.Prime) (hlg : l ∣ g) : 2*p ∣ l-1 := by
    have hls : ¬ l ∣ u+v := fun hd => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l,hl,hd,hlg⟩) hcop
    have hlf := hlg.trans hg
    have hlsum : l ∣ u^p+v^p := hfac ▸ dvd_mul_of_dvd_right hlf _
    simpa using new_prime_congruence (k := 0) hp ho hl hc (by simpa using hlsum) (by simpa using hls)
  by_cases hps : p ∣ u+v
  · have hvp := quotient_valuation hu hf hc ho hp hps hfac
    rw [hp.factorization_self] at hvp
    obtain ⟨g, hfg⟩ := (hp.dvd_iff_one_le_factorization hf.ne').mpr hvp.ge
    have hg : g ≠ 0 := by intro e; simp [e] at hfg; omega
    have hpg : ¬ p ∣ g := by
      rw [hfg, Nat.factorization_mul hp.ne_zero hg, Finsupp.add_apply, hp.factorization_self] at hvp
      rw [hp.dvd_iff_one_le_factorization hg]
      omega
    have hcop : ((u+v)*p).Coprime g := by
      by_contra h
      obtain ⟨l, hl, hlsp, hlg⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      rcases hl.dvd_mul.mp hlsp with hls | hlp
      · have e := common hl hls (hfg ▸ dvd_mul_of_dvd_right hlg p)
        exact hpg (e ▸ hlg)
      · exact hpg ((Nat.prime_dvd_prime_iff_eq hl hp).mp hlp ▸ hlg)
    obtain ⟨s,t,hs,ht⟩ := roots_of_coprime_product hcop (by simpa [hfg, Nat.mul_assoc] using hprod)
    have hqt : q ∣ t := hq.dvd_of_dvd_pow (ht ▸ (hq.dvd_mul.mp (hfg ▸ hqf)).resolve_left (fun h =>
      hnew ((Nat.prime_dvd_prime_iff_eq hq hp).mp h ▸ hps)))
    have htpos : t ≠ 0 := fun e => hg (by simp [ht, e, show r ≠ 0 by omega])
    exact h4 u v p r s t hu hv hc hp ho hr hps hs (fun h => hpg (ht ▸ dvd_pow h (by omega)))
      (hq.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero htpos) hqt))
      (fun l hl hd => all_mod hcop.coprime_mul_right (hfg ▸ dvd_mul_left g p) l hl
        (ht ▸ dvd_pow hd (by omega))) (by rw [hdiv, hfg, ht])
  · have hcop : (u+v).Coprime f := by
      by_contra h
      obtain ⟨l, hl, hls, hlf⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      exact hps (common hl hls hlf ▸ hls)
    obtain ⟨s,t,hs,ht⟩ := roots_of_coprime_product hcop hprod
    have htpos : t ≠ 0 := by intro e; simp [ht, e, show r ≠ 0 by omega] at hf
    exact h3 u v p r s t hu hv hc hp ho hr hps hs
      (hq.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero htpos) (hq.dvd_of_dvd_pow (ht ▸ hqf))))
      (fun l hl hd => all_mod hcop (dvd_refl _) l hl (ht ▸ dvd_pow hd (by omega))) (hdiv.trans ht)

private theorem quartic_prime_support {a b c r q : ℕ}
    (hc : a.Coprime b) (hr : 2 ≤ r) (he : a^4 + b^4 = c^r) (hq : q.Prime) (hqc : q ∣ c) :
    8 ∣ q-1 := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ c ^ r :=
      (show 4 ∣ c^2 from pow_dvd_pow_of_dvd hqc 2).trans (pow_dvd_pow c hr)
    rw [← he, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod a, Nat.pow_mod b] at h4
    have ha := Nat.mod_lt a (by decide : 0 < 4)
    have hb := Nat.mod_lt b (by decide : 0 < 4)
    apply (Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, Nat.prime_two, ?_, ?_⟩) hc
    all_goals
      interval_cases ea : a % 4 <;> interval_cases eb : b % 4 <;> norm_num at h4 <;> omega
  let : Fact q.Prime := ⟨hq⟩
  have hsum : (a : ZMod q)^4 + (b : ZMod q)^4 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr (he ▸ dvd_pow hqc (show r ≠ 0 by omega))
    push_cast at h
    exact h
  have hb : (b : ZMod q) ≠ 0 := by
    intro h
    have ha : (a : ZMod q)^4 = 0 := by simpa [h] using hsum
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq,
      (ZMod.natCast_eq_zero_iff _ _).mp (by by_contra hn; exact pow_ne_zero _ hn ha),
      (ZMod.natCast_eq_zero_iff _ _).mp h⟩) hc
  let t := (a : ZMod q) / (b : ZMod q)
  have ht : t^4 = -1 := by
    rw [show t = _ from rfl, div_pow, div_eq_iff (pow_ne_zero _ hb)]
    linear_combination hsum
  have htwo : (2 : ZMod q) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (mt (ZMod.natCast_eq_zero_iff 2 q).mp
      (mt (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2))
  have ho : orderOf t = 2^(2+1) := by
    apply orderOf_eq_prime_pow (p := 2) (n := 2)
    · change ¬ t^4 = 1
      intro h
      apply htwo
      linear_combination ht - h
    · change t^8 = 1
      rw [show (8 : ℕ) = 4*2 by decide, pow_mul, ht]
      norm_num
  have htn : t ≠ 0 := by
    intro h
    simp [h] at ht
  have h := ZMod.orderOf_dvd_card_sub_one htn
  rwa [ho] at h

private theorem normalize_exponent {n : ℕ} (hn : 2 < n) :
    ∃ p k : ℕ, (p = 4 ∨ (p.Prime ∧ Odd p)) ∧ n = k*p := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn with h | ⟨p,hp,h,ho⟩
  · obtain ⟨k,hk⟩ := h
    exact ⟨4,k,Or.inl rfl,hk.trans (Nat.mul_comm ..)⟩
  · obtain ⟨k,hk⟩ := h
    exact ⟨p,k,Or.inr ⟨hp,ho⟩,hk.trans (Nat.mul_comm ..)⟩

private theorem common_gcd_of_non_coprime {a b c x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (he : a^x + b^y = c^z) (hn : ¬ a.Coprime b) (ha : 0 < a) :
    1 < Finset.gcd {a,b,c} id := by
  obtain ⟨p,hp,hpa,hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  have hpc : p ∣ c := hp.dvd_of_dvd_pow (he ▸ dvd_add (dvd_pow hpa hx.ne') (dvd_pow hpb hy.ne'))
  have hd : p ∣ Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hda : Finset.gcd {a,b,c} id ∣ a := Finset.gcd_dvd (Finset.mem_insert_self a _)
  have hg : 0 < Finset.gcd {a,b,c} id := by
    by_contra! h
    have hz0 : Finset.gcd {a,b,c} id = 0 := by omega
    rw [hz0, zero_dvd_iff] at hda
    omega
  exact hp.one_lt.trans_le (Nat.le_of_dvd hg hd)

theorem main : H1 → H2 → H3 → H4 → type_of% @BealConjecture.beal_conjecture := by
  intro h1 h2 h3 h4 a b c x y z ha hb hc hx hy hz he
  by_cases hab : a.Coprime b
  · exfalso
    obtain ⟨i,m,hi,rfl⟩ := normalize_exponent hx
    obtain ⟨j,n,hj,rfl⟩ := normalize_exponent hy
    obtain ⟨r,k,hr,rfl⟩ := normalize_exponent hz
    simp only [pow_mul] at he
    have ha' := pow_pos (Nat.pos_of_ne_zero ha) m
    have hb' := pow_pos (Nat.pos_of_ne_zero hb) n
    have hc' := pow_pos (Nat.pos_of_ne_zero hc) k
    have hcop := hab.pow m n
    rcases lt_trichotomy i j with h | rfl | h
    · exact h1 _ _ _ _ _ _ ha' hb' hc' hcop hi hj hr h he
    · rcases hi with rfl | ⟨hip,hio⟩
      · rcases hr with rfl | ⟨hrp,hro⟩
        · exact fermatLastTheoremFour _ _ _ ha'.ne' hb'.ne' hc'.ne' he
        · exact h2 _ _ _ _ ha' hb' hc' hcop hrp hro
            (fun _ => quartic_prime_support hcop hrp.two_le he) he
      · exact exclude_equal_odd h3 h4 ha' hb' hcop hip hio hr he
    · exact h1 _ _ _ _ _ _ hb' ha' hc' hcop.symm hj hi hr h ((Nat.add_comm ..).trans he)
  · exact common_gcd_of_non_coprime (by omega) (by omega) he hab (Nat.pos_of_ne_zero ha)

end OMA.R_BealConjecture_beal_conjecture_R3
