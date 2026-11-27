import OMAStatements.S_oeis_a221981

namespace OMA.S_oeis_a221981


/-- Control: 29, 149, 269 are terms. -/
theorem first_terms : InSeq 29 ∧ InSeq 149 ∧ InSeq 269 := by
  refine ⟨⟨by norm_num, 7, by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, 37, by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, 67, by norm_num, by norm_num, by norm_num⟩⟩

/-- Divisors of `c t` (`c ∈ {4, 8}`, `t` prime) that do not divide `(c/2) t` and differ from `c`
equal `c t`. -/
theorem dvd_cases (d t c : ℕ) (ht : t.Prime) (hc : c = 4 ∨ c = 8) (h1 : d ∣ c * t)
    (h2 : ¬ d ∣ (c / 2) * t) (h3 : d ≠ c) : d = c * t := by
  have ht1 := ht.one_lt
  by_cases hpd : t ∣ d
  · obtain ⟨e, rfl⟩ := hpd
    have he : e ∣ c := by
      have : t * e ∣ t * c := by rw [mul_comm t c]; exact h1
      exact Nat.dvd_of_mul_dvd_mul_left ht.pos this
    have hle : e ≤ c := Nat.le_of_dvd (by omega) he
    have h2' : ¬ e ∣ c / 2 := by
      intro h
      apply h2
      rw [mul_comm (c / 2) t]
      exact Nat.mul_dvd_mul_left t h
    rcases hc with rfl | rfl
    · interval_cases e <;> omega
    · interval_cases e <;> omega
  · have hcop : Nat.Coprime d t :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd ht).mpr hpd)
    have hd : d ∣ c := hcop.dvd_of_dvd_mul_right h1
    have hle : d ≤ c := Nat.le_of_dvd (by omega) hd
    have h2' : ¬ d ∣ c / 2 := fun h => h2 (Dvd.dvd.mul_right h t)
    exfalso
    rcases hc with rfl | rfl
    · interval_cases d <;> omega
    · interval_cases d <;> omega

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem legendre_five_three : legendreSym 5 3 = -1 := by
  have h := legendreSym.eq_pow 5 3
  rcases legendreSym.eq_one_or_neg_one 5 (a := 3) (by decide) with h1 | h1
  · rw [h1] at h; revert h; decide
  · exact h1

/-- If `x^(c t / 2) = -1` in `ZMod r`, `r - 1 = c t`, `x^c ≠ 1`, then `x` has order `r - 1`. -/
theorem order_eq (r t c : ℕ) [hr : Fact r.Prime] (ht : t.Prime) (hc : c = 4 ∨ c = 8)
    (hrc : r = c * t + 1) (x : ZMod r) (hx : x ^ ((c / 2) * t) = -1) (hxc : x ^ c ≠ 1) :
    orderOf x = r - 1 := by
  have hr2 : 2 < r := by have := ht.two_le; rcases hc with rfl | rfl <;> omega
  haveI : Fact (2 < r) := ⟨hr2⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := ht.two_le; rcases hc with rfl | rfl <;> omega)] at hx
    have h1 : (-1 : ZMod r) = 0 := hx.symm
    exact one_ne_zero (neg_eq_zero.mp h1)
  have h1 : orderOf x ∣ c * t := by
    have := ZMod.pow_card_sub_one_eq_one hx0
    rw [show r - 1 = c * t by omega] at this
    exact orderOf_dvd_of_pow_eq_one this
  have h2 : ¬ orderOf x ∣ (c / 2) * t := by
    intro h
    have := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hx] at this
    exact ZMod.neg_one_ne_one this
  have h3 : orderOf x ≠ c := by
    intro h
    apply hxc
    rw [← h]
    exact pow_orderOf_eq_one x
  rw [dvd_cases _ t c ht hc h1 h2 h3]
  omega

theorem p_odd (p : ℕ) (hp : p.Prime) (hq : (4 * p + 1).Prime) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h
  · subst h; norm_num at hq
  · exact h

/-- Conjecture (a): every term `q` has primitive root 40. -/
theorem conjecture_a (q : ℕ) (hq : InSeq q) : orderOf (40 : ZMod q) = q - 1 := by
  obtain ⟨hqp, p, hp, hp5, rfl⟩ := hq
  haveI := Fact.mk hqp
  have hpo := p_odd p hp hqp
  have hq2 : 4 * p + 1 ≠ 2 := by omega
  have hl2 : legendreSym (4 * p + 1) 2 = -1 := by
    rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
    have a : (4 * p + 1) % 2 = 1 := by omega
    have b : (4 * p + 1) % 8 = 5 := by omega
    simp [a, b]
  have hl5 : legendreSym (4 * p + 1) 5 = 1 := by
    have :=legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := 4 * p + 1)
      (by norm_num) hq2
    push_cast at this
    rw [this, legendreSym.mod]
    have e : ((4 * (p : ℤ) + 1) % ((5 : ℕ) : ℤ)) = 2 ^ 2 := by omega
    rw [e]
    exact legendreSym.sq_one' 5 (by decide)
  have hl : legendreSym (4 * p + 1) 40 = -1 := by
    rw [show (40 : ℤ) = 2 * 2 * 2 * 5 by norm_num, legendreSym.mul, legendreSym.mul,
      legendreSym.mul, hl2, hl5]
    norm_num
  have hx : (40 : ZMod (4 * p + 1)) ^ ((4 / 2) * p) = -1 := by
    have := legendreSym.eq_pow (4 * p + 1) 40
    rw [hl, show (4 * p + 1) / 2 = (4 / 2) * p by omega] at this
    push_cast at this
    exact this.symm
  have hx4 : (40 : ZMod (4 * p + 1)) ^ 4 ≠ 1 := by
    intro h4
    have hz : ((2559999 : ℕ) : ZMod (4 * p + 1)) = 0 := by
      have : ((2559999 : ℕ) : ZMod (4 * p + 1)) = 40 ^ 4 - 1 := by push_cast; ring
      rw [this, h4, sub_self]
    have hdvd : 4 * p + 1 ∣ 3 * (13 * (41 * 1601)) := by
      have := (ZMod.natCast_eq_zero_iff _ _).mp hz
      simpa using this
    have hm5 : (4 * p + 1) % 5 = 4 := by omega
    have hm8 : (4 * p + 1) % 8 = 5 := by omega
    rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h; omega
  exact order_eq (4 * p + 1) p 4 hp (Or.inl rfl) (by ring) _ hx hx4

/-- Conjecture (b): if `r = 8 q + 1` is prime for a term `q`, then `r` has primitive root 10. -/
theorem conjecture_b (q : ℕ) (hq : InSeq q) (hr : (8 * q + 1).Prime) :
    orderOf (10 : ZMod (8 * q + 1)) = 8 * q + 1 - 1 := by
  obtain ⟨hqp, p, hp, hp5, rfl⟩ := hq
  haveI := Fact.mk hr
  have hpo := p_odd p hp hqp
  set r := 8 * (4 * p + 1) + 1 with hrdef
  have hr2 : r ≠ 2 := by omega
  have hl2 : legendreSym r 2 = 1 := by
    rw [legendreSym.at_two hr2, ZMod.χ₈_nat_eq_if_mod_eight]
    have a : r % 2 = 1 := by omega
    have b : r % 8 = 1 := by omega
    simp [a, b]
  have hl5 : legendreSym r 5 = -1 := by
    have :=legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := r) (by norm_num) hr2
    push_cast at this
    rw [this, legendreSym.mod]
    have e : ((r : ℤ) % ((5 : ℕ) : ℤ)) = 3 := by omega
    rw [e]
    exact legendre_five_three
  have hl : legendreSym r 10 = -1 := by
    rw [show (10 : ℤ) = 2 * 5 by norm_num, legendreSym.mul, hl2, hl5]
    norm_num
  have hx : (10 : ZMod r) ^ ((8 / 2) * (4 * p + 1)) = -1 := by
    have := legendreSym.eq_pow r 10
    rw [hl, show r / 2 = (8 / 2) * (4 * p + 1) by omega] at this
    push_cast at this
    exact this.symm
  have hx8 : (10 : ZMod r) ^ 8 ≠ 1 := by
    intro h8
    have hz : ((99999999 : ℕ) : ZMod r) = 0 := by
      have : ((99999999 : ℕ) : ZMod r) = 10 ^ 8 - 1 := by push_cast; ring
      rw [this, h8, sub_self]
    have hdvd : r ∣ 3 * (3 * (11 * (73 * (101 * 137)))) := by
      have := (ZMod.natCast_eq_zero_iff _ _).mp hz
      simpa using this
    have hm5 : r % 5 = 3 := by omega
    have hm64 : r % 64 = 41 := by omega
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h; omega
  exact order_eq r (4 * p + 1) 8 hqp (Or.inr rfl) (by omega) _ hx hx8

end OMA.S_oeis_a221981

theorem OMA.solution : type_of% @OMA.S_oeis_a221981.main :=
  ⟨OMA.S_oeis_a221981.conjecture_a, OMA.S_oeis_a221981.conjecture_b⟩
