import FormalConjectures.OEIS.«135508»

/-!
Cubic introduction and a balanced semiprime residual.

For m=p-2, let q be its least prime factor and r=m/q. Cubic introduction
handles r>=q^2. If r<q^2, then r is prime, since every prime factor of r
is at least q. The second hypothesis covers this remaining semiprime range.
An odd prime cannot first enter x at a multiple of itself, so stock at x(m)
already occurs in x(m-1). The hypotheses remain open.
-/

namespace OMA.R_OeisA135508_conjecture_R2

open OeisA135508

lemma x_pos (n : ℕ) (hn : 1 ≤ n) : 0 < x n := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => decide
    | succ n ih =>
      change 0 < 2 * x (n + 1) + Nat.lcm (x (n + 1)) (n + 2)
      omega

lemma x_succ_fact (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = x n * (2 + (n + 1) / Nat.gcd (x n) (n + 1)) := by
  cases n with
  | zero => omega
  | succ k =>
    change 2 * x (k + 1) + Nat.lcm (x (k + 1)) (k + 2) = _
    rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    ring

lemma a_eq_div_gcd (n : ℕ) (hn : 1 ≤ n) :
    a n = (n + 1) / Nat.gcd (x n) (n + 1) := by
  rw [a, if_neg (by omega), x_succ_fact n hn]
  simp [x_pos n hn]

lemma a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ n + 1 := by
  rw [a_eq_div_gcd n hn]
  exact Nat.div_le_self _ _

lemma x_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x n ∣ x (n + 1) := by
  rw [x_succ_fact n hn]
  exact Nat.dvd_mul_right _ _

lemma prime_not_dvd_x_before {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n)
    (hsmall : n + 2 < p) : ¬ p ∣ x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · omega
    · simp [x, hp.not_dvd_one]
    · rw [x_succ_fact (k + 1) (by omega)]
      intro hd
      rcases hp.dvd_mul.mp hd with hleft | hright
      · exact ih (k + 1) (by omega) (by omega) (by omega) hleft
      · have hpos : 0 < (2 + (k + 2) / Nat.gcd (x (k + 1)) (k + 2) : ℕ) := by positivity
        have hle := Nat.div_le_self (k + 2) (Nat.gcd (x (k + 1)) (k + 2))
        exact Nat.not_dvd_of_pos_of_lt hpos (by omega) hright

lemma a_at_prime (p : ℕ) (hp : p.Prime) :
    a (p - 1) = if p ∣ x (p - 1) then 1 else p := by
  rw [a_eq_div_gcd _ (by have := hp.two_le; omega), Nat.sub_add_cancel hp.one_le]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, Nat.div_self hp.pos]
  · have hc : Nat.Coprime (x (p - 1)) p := (hp.coprime_iff_not_dvd.mpr hd).symm
    rw [hc.gcd_eq_one, Nat.div_one]

lemma a_dvd (n : ℕ) (hn : 1 ≤ n) : a n ∣ n + 1 := by
  rw [a_eq_div_gcd n hn]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

lemma x_succ_mul_a (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (a n + 2) := by
  rw [x_succ_fact n hn, a_eq_div_gcd n hn, Nat.add_comm 2]

lemma prime_dvd_x_at_next {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ x (p - 1) ↔ p ∣ x (p - 2) := by
  have he : p - 1 = (p - 2) + 1 := by omega
  rw [he, x_succ_mul_a _ (by omega), hp.dvd_mul]
  constructor
  · rintro (h | h)
    · exact h
    · have hb := a_le (p - 2) (by omega)
      have ha := a_dvd (p - 2) (by omega)
      have hupper : a (p - 2) + 2 < 2 * p := by omega
      have heq : a (p - 2) + 2 = p := by
        obtain ⟨k, hk⟩ := h
        have hkpos : 0 < k := by nlinarith
        have hkone : k = 1 := by nlinarith
        simpa only [hkone, Nat.mul_one] using hk
      have hane : a (p - 2) = p - 2 := by omega
      rw [hane] at ha
      have hh : p - 2 ∣ 1 := by
        have ha' : p - 2 ∣ (p - 2) + 1 := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using ha
        exact (Nat.dvd_add_iff_right (dvd_refl (p - 2))).mpr ha'
      have := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hh
      omega
  · exact Or.inl

lemma prime_dvd_x_iff {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ x (p - 1) ↔ a (p - 3) = p - 2 := by
  rw [prime_dvd_x_at_next hp hp5]
  have he : p - 2 = (p - 3) + 1 := by omega
  rw [he, x_succ_mul_a _ (by omega), hp.dvd_mul]
  have hpre := prime_not_dvd_x_before hp (p - 3) (by omega) (by omega)
  rw [or_iff_right hpre]
  constructor
  · intro hd
    have hb := a_le (p - 3) (by omega)
    have hl := Nat.le_of_dvd (by omega : 0 < a (p - 3) + 2) hd
    omega
  · intro ha
    have heq : a (p - 3) + 2 = p := by omega
    rw [heq]

lemma prime_target_iff {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    a (p - 1) = p ↔ a (p - 3) ≠ p - 2 := by
  constructor
  · intro ha heq
    have hd := (prime_dvd_x_iff hp hp5).mpr heq
    rw [a_at_prime p hp, if_pos hd] at ha
    omega
  · intro heq
    have hd : ¬ p ∣ x (p - 1) := fun hd => heq ((prime_dvd_x_iff hp hp5).mp hd)
    rw [a_at_prime p hp, if_neg hd]

lemma divides_later {d m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hd : d ∣ x m) :
    d ∣ x n := by
  induction n, hmn using Nat.le_induction with
  | base => exact hd
  | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))

lemma target_of_noncoprime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnot : ¬ Nat.Coprime (x (p - 3)) (p - 2)) : a (p - 1) = p := by
  rw [prime_target_iff hp h5]
  intro ha
  apply hnot
  have hmul : a (p - 3) * Nat.gcd (x (p - 3)) ((p - 3) + 1) = (p - 3) + 1 := by
    rw [a_eq_div_gcd _ (by omega)]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have he : (p - 3) + 1 = p - 2 := by omega
  rw [he, ha] at hmul
  change Nat.gcd (x (p - 3)) (p - 2) = 1
  nlinarith [Nat.zero_le (Nat.gcd (x (p - 3)) (p - 2))]

lemma absent_persists_at_multiple {q n : ℕ} (hq : q.Prime) (hodd : 2 < q)
    (hn : 1 ≤ n) (hqn : q ∣ n + 1) (habsent : ¬ q ∣ x n) :
    ¬ q ∣ x (n + 1) := by
  rw [x_succ_mul_a n hn]
  intro hd
  rcases hq.dvd_mul.mp hd with hx | hm
  · exact habsent hx
  · have hprod : a n * Nat.gcd (x n) (n + 1) = n + 1 := by
      rw [a_eq_div_gcd n hn]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hdiv : q ∣ a n * Nat.gcd (x n) (n + 1) := by rwa [hprod]
    have hqa : q ∣ a n := by
      rcases hq.dvd_mul.mp hdiv with ha | hg
      · exact ha
      · exact False.elim (habsent (hg.trans (Nat.gcd_dvd_left _ _)))
    have htwo : q ∣ 2 := (Nat.dvd_add_iff_right hqa).mpr hm
    have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) htwo
    omega

lemma prime_dvd_before_multiple {d m : ℕ} (hd : d.Prime) (hd2 : 2 < d)
    (hm : 2 ≤ m) (hdm : d ∣ m) (hdx : d ∣ x m) : d ∣ x (m-1) := by
  by_contra habsent
  have hdiv : d ∣ m-1+1 := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hdm
  have hh := absent_persists_at_multiple hd hd2 (by omega : 1 ≤ m-1) hdiv habsent
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hh
  exact hh hdx

/-- Every prime at least 5 is introduced by its cube. -/
def H1 : Prop := ∀ q : ℕ, q.Prime → 5 ≤ q → q ∣ x (q^3)

/-- A balanced semiprime preceding a prime has one of its factors in the stock. -/
def H2 : Prop := ∀ q r : ℕ, q.Prime → r.Prime → 5 ≤ q → q ≤ r → r < q^2 →
  (q*r+2).Prime → q ∣ x (q*r) ∨ r ∣ x (q*r)

theorem main : H1 → H2 → type_of% @OeisA135508.conjecture := by
  intro hintro hsemi p hp hnot
  by_cases hp5 : 5 ≤ p
  · have hp6 : p ≠ 6 := fun he => by subst p; exact (by decide : ¬ Nat.Prime 6) hp
    have hpne5 : p ≠ 5 := fun he => by subst p; exact hnot (by decide)
    have hp7 : 7 ≤ p := by omega
    let q := (p-2).minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hqm : q ∣ p-2 := Nat.minFac_dvd _
    apply target_of_noncoprime hp hp5
    intro hc
    have exclude {d : ℕ} (hd : d.Prime) (hdm : d ∣ p-2) (hdx : d ∣ x (p-3)) : False := by
      have hh := Nat.dvd_gcd hdx hdm
      rw [hc.gcd_eq_one] at hh
      exact hd.not_dvd_one hh
    have exclude_at {d : ℕ} (hd : d.Prime) (hd2 : 2 < d)
        (hdm : d ∣ p-2) (hdx : d ∣ x (p-2)) : False := by
      apply exclude hd hdm
      have hh := prime_dvd_before_multiple hd hd2 (by omega : 2 ≤ p-2) hdm hdx
      simpa only [show p-2-1 = p-3 by omega] using hh
    by_cases hq5 : 5 ≤ q
    · let r := (p-2)/q
      have hprod : q*r = p-2 := Nat.mul_div_cancel' hqm
      have hsq : q^2 ≤ p-2 := Nat.minFac_sq_le_self (by omega) hnot
      have hqr : q ≤ r := by nlinarith [hq.two_le]
      have hr5 : 5 ≤ r := hq5.trans hqr
      have hrm : r ∣ p-2 := by rw [← hprod]; exact dvd_mul_left _ _
      by_cases hlarge : q^2 ≤ r
      · have hcube : q^3 ≤ p-2 := by
          have hh := Nat.mul_le_mul_left q hlarge
          have he : q*q^2 = q^3 := by ring
          rwa [he, hprod] at hh
        have hqcube : q ≤ q^3 := by
          simpa only [pow_one] using pow_le_pow_right₀ hq.one_le (by decide : 1 ≤ (3:ℕ))
        have hpow2 : 2 ≤ q^3 := hq.two_le.trans hqcube
        exact exclude_at hq (by omega) hqm (divides_later (by omega : 1 ≤ q^3)
          hcube (hintro q hq hq5))
      · have hr : r.Prime := by
          by_contra hr
          let s := r.minFac
          have hs : s.Prime := Nat.minFac_prime (by omega)
          have hsr : s ∣ r := Nat.minFac_dvd _
          have hsm : s ∣ p-2 := hsr.trans hrm
          have hqs : q ≤ s := Nat.minFac_le_of_dvd hs.two_le hsm
          have hssq : s^2 ≤ r := Nat.minFac_sq_le_self (by omega) hr
          have hh := Nat.mul_le_mul hqs hqs
          have hh' : q^2 ≤ s^2 := by simpa only [pow_two] using hh
          exact hlarge (hh'.trans hssq)
        have hpp : (q*r+2).Prime := by
          have he : q*r+2 = p := by omega
          rwa [he]
        rcases hsemi q r hq hr hq5 hqr (by omega) hpp with hd | hd
        · exact exclude_at hq (by omega) hqm (by simpa only [hprod] using hd)
        · exact exclude_at hr (by omega) hrm (by simpa only [hprod] using hd)
    · have hq2 := hq.two_le
      have hq4 : q ≠ 4 := fun he => by rw [he] at hq; exact (by decide : ¬ Nat.Prime 4) hq
      have h23 : q = 2 ∨ q = 3 := by omega
      apply exclude hq hqm
      apply divides_later (m := 4) (by decide) (by omega)
      rcases h23 with he | he <;> rw [he] <;> decide
  · have hp4 : p ≠ 4 := fun he => by subst p; exact (by decide : ¬ Nat.Prime 4) hp
    have h : p = 2 ∨ p = 3 := by have := hp.two_le; omega
    rcases h with rfl | rfl <;> decide

end OMA.R_OeisA135508_conjecture_R2
