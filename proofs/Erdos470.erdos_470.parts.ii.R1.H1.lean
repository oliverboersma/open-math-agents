import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

-- Step H1 of the reduction Erdos470.erdos_470.parts.ii.R1 (Erdős Problem 470, part ii).
-- Credit: @biondadave
--
-- G. Melfi, On the conditional infiniteness of primitive weird numbers, J. Number Theory 147
-- (2015), 508-514, Theorem 1, with the size condition a * (a + b) < 2^(k+2).
-- Write M = 2^(k+1), p = 2M - a, q = 2M + b, n = 2^k * p * q.  Both primes are odd, so a and b
-- are odd and a = b + 4 + 2c for some c.
--   * sigma(n) + (p + 1)(q + 1) = M (p + 1)(q + 1), and the abundance is
--     sigma(n) - 2n = M (2c + 1) + (a - 1)(b + 1) > 0.
--   * If a set of proper divisors sums to n, its complement sums to the abundance.  That sum is
--     below p * q, so no element is a multiple of p * q, and the sum is A0 + p B + q C with
--     A0 < M a sum of distinct powers of two (decomp).  With h = B + C: if h <= c the sum is at
--     most M - 1 + q c, too small; if h > c it is at least p (c + 1), too large (gap).
--   * Every proper divisor divides n / 2, n / p or n / q, none of which is abundant, so no proper
--     divisor is abundant (Nat.Abundant.of_dvd), let alone weird.

namespace OMAMelfi

open Finset

-- The divisors of 2^k sum to 2^(k+1) - 1.
lemma sum_divisors_two_pow (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d + 1 = 2 ^ (k + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

lemma coprime_two_pow_of_prime {k r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : Nat.Coprime (2 ^ k) r :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))

-- sigma(2^k * r) for an odd prime r.
lemma sum_divisors_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∑ d ∈ (2 ^ k * r).divisors, d + (r + 1) = 2 ^ (k + 1) * (r + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (coprime_two_pow_of_prime hr hr2), Nat.Prime.sum_divisors hr]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- sigma(2^k * p * q) for distinct odd primes p, q.
lemma sum_divisors_two_pow_mul_mul (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d + (p + 1) * (q + 1) = 2 ^ (k + 1) * ((p + 1) * (q + 1)) := by
  have hcop1 : Nat.Coprime (2 ^ k) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_prime hp hp2) (coprime_two_pow_of_prime hq hq2)
  have hcop2 : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [mul_assoc, Nat.Coprime.sum_divisors_mul hcop1, Nat.Coprime.sum_divisors_mul hcop2,
    Nat.Prime.sum_divisors hp, Nat.Prime.sum_divisors hq]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- 2^k * r is not abundant when r is an odd prime with 2^(k+1) <= r + 1.
lemma not_abundant_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hbig : 2 ^ (k + 1) ≤ r + 1) : ¬ (2 ^ k * r).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_prime k r hr hr2
  have h2 : 2 * (2 ^ k * r) = 2 ^ (k + 1) * r := by ring
  rw [h2]
  nlinarith

-- 2^j * p * q is not abundant when p, q are distinct odd primes, both at least 2^(j+2).
lemma not_abundant_two_pow_mul_mul (j p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (hpbig : 2 ^ (j + 2) ≤ p) (hqbig : 2 ^ (j + 2) ≤ q) :
    ¬ (2 ^ j * p * q).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_mul j p q hp hq hp2 hq2 hpq
  set m := 2 ^ (j + 1) with hm
  have h2 : 2 * (2 ^ j * p * q) = m * (p * q) := by rw [hm]; ring
  have h4 : 2 ^ (j + 2) = 2 * m := by rw [hm]; ring
  rw [h2]
  obtain ⟨u, rfl⟩ : ∃ u, p = 2 * m + u := ⟨p - 2 * m, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, q = 2 * m + v := ⟨q - 2 * m, by omega⟩
  nlinarith [Nat.zero_le (u * v), Nat.zero_le (m * u), Nat.zero_le (m * v), Nat.zero_le m]

-- A proper divisor of 2^k * p * q divides one of the three maximal proper divisors.
lemma dvd_cases (k p q d : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hd : d ∈ (2 ^ k * p * q).properDivisors) :
    d ∣ 2 ^ (k - 1) * p * q ∨ d ∣ 2 ^ k * q ∨ d ∣ 2 ^ k * p := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨e, he⟩, hlt⟩ := hd
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at he
    omega
  have hen : e ∣ 2 ^ k * p * q := ⟨d, by rw [he]; ring⟩
  have hr := Nat.minFac_prime he1
  have hrn : e.minFac ∣ 2 ^ k * p * q := (Nat.minFac_dvd e).trans hen
  have hre := Nat.minFac_dvd e
  generalize e.minFac = r at hr hrn hre
  obtain ⟨e', rfl⟩ := hre
  rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      left
      refine ⟨e', ?_⟩
      have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2, hk'] at he
      have : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * e') := by rw [← mul_assoc, ← mul_assoc, he]; ring
      omega
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      right; left
      refine ⟨e', ?_⟩
      rw [h2] at he
      have : p * (2 ^ k * q) = p * (d * e') := by linarith [he]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
    right; right
    refine ⟨e', ?_⟩
    rw [h2] at he
    have : q * (2 ^ k * p) = q * (d * e') := by linarith [he]
    exact Nat.eq_of_mul_eq_mul_left hq.pos this

-- A set of divisors of 2^k * p * q with sum below p * q sums to A0 + p * B + q * C, where A0 is a
-- sum of distinct divisors of 2^k.
lemma decomp (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (t : Finset ℕ)
    (ht : t ⊆ (2 ^ k * p * q).divisors) (hsmall : ∑ d ∈ t, d < p * q) :
    ∃ A0 B C : ℕ, ∑ d ∈ t, d = A0 + p * B + q * C ∧ A0 + 1 ≤ 2 ^ (k + 1) := by
  have hno : ∀ d ∈ t, p ∣ d → ¬ q ∣ d := by
    intro d hdt h1 h2
    have hpqd : p * q ∣ d :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) h1 h2
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (ht hdt)
    have h3 : p * q ≤ d := Nat.le_of_dvd hd0 hpqd
    have h4 : d ≤ ∑ d ∈ t, d :=
      Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hdt
    omega
  have e1 : ∑ d ∈ t.filter (fun d => p ∣ d), d = p * ∑ d ∈ t.filter (fun d => p ∣ d), d / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have e2 : ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d =
      q * ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm
  have hsub : (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d) ⊆ (2 ^ k).divisors := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨⟨hdt, hnp⟩, hnq⟩ := hd
    have hdn := Nat.dvd_of_mem_divisors (ht hdt)
    have hcp : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
    have hcq : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnq).symm
    have h1 : d ∣ 2 ^ k * p := Nat.Coprime.dvd_of_dvd_mul_right hcq hdn
    have h2 : d ∣ 2 ^ k := Nat.Coprime.dvd_of_dvd_mul_right hcp h1
    exact Nat.mem_divisors.mpr ⟨h2, by positivity⟩
  refine ⟨∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d,
    ∑ d ∈ t.filter (fun d => p ∣ d), d / p,
    ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => q ∣ d), d / q, ?_, ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not t (fun d => p ∣ d),
      ← Finset.sum_filter_add_sum_filter_not (t.filter (fun d => ¬ p ∣ d)) (fun d => q ∣ d),
      e1, e2]
    ring
  · calc ∑ d ∈ (t.filter (fun d => ¬ p ∣ d)).filter (fun d => ¬ q ∣ d), d + 1
        ≤ ∑ d ∈ (2 ^ k).divisors, d + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) 1
      _ = 2 ^ (k + 1) := sum_divisors_two_pow k

-- The abundance lies strictly between two consecutive blocks of divisor sums.
lemma gap (M p q b c A0 B C : ℕ) (hpa : p + (b + 4 + 2 * c) = 2 * M) (hqb : q = 2 * M + b)
    (hA0 : A0 + 1 ≤ M) (hsize : (b + 4 + 2 * c) * ((b + 4 + 2 * c) + b) < 2 * M)
    (heq : A0 + p * B + q * C = M * (2 * c + 1) + (b + 3 + 2 * c) * (b + 1)) : False := by
  have hpq : p ≤ q := by omega
  rcases Nat.lt_or_ge c (B + C) with h | h
  swap
  · have h1 : p * B ≤ q * B := Nat.mul_le_mul_right B hpq
    have h2 : q * (B + C) ≤ q * c := Nat.mul_le_mul_left q h
    subst hqb
    nlinarith
  · have h1 : p * C ≤ q * C := Nat.mul_le_mul_right C hpq
    have h2 : p * (c + 1) ≤ p * (B + C) := Nat.mul_le_mul_left p h
    have e : p * (c + 1) + (b + 4 + 2 * c) * (c + 1) = 2 * M * (c + 1) := by
      rw [← hpa]; ring
    nlinarith

-- Melfi 2015, Theorem 1, in the variables M = 2^(k+1), p = 2M - a, q = 2M + b, a = b + 4 + 2c.
theorem core (k M p q b c : ℕ) (hM : M = 2 ^ (k + 1)) (hpa : p + (b + 4 + 2 * c) = 2 * M)
    (hqb : q = 2 * M + b) (hsize : (b + 4 + 2 * c) * ((b + 4 + 2 * c) + b) < 2 * M)
    (hp : p.Prime) (hq : q.Prime) : Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  -- basic size facts
  have hM2 : 2 ≤ M := by rw [hM]; exact Nat.le_self_pow (by omega) 2
  have ha : b + 4 + 2 * c < M := by
    rcases Nat.lt_or_ge (b + 4 + 2 * c) M with h | h
    · exact h
    · nlinarith
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at hM
      subst hM
      nlinarith
    · exact h0
  have hpM : M < p := by omega
  have hqM : 2 * M ≤ q := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq : p ≠ q := by omega
  have hn0 : 2 ^ k * p * q ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero
  have hσ := sum_divisors_two_pow_mul_mul k p q hp hq hp2 hq2 hpq
  rw [← hM] at hσ
  have h2n : 2 * (2 ^ k * p * q) = M * (p * q) := by rw [hM]; ring
  -- the key identity: (p + 1)(q + 1) + abundance = M (p + q + 1)
  have key : (p + 1) * (q + 1) + (M * (2 * c + 1) + (b + 3 + 2 * c) * (b + 1)) =
      M * (p + q + 1) := by
    have hp' : (p : ℤ) = 2 * M - b - 4 - 2 * c := by
      have := congrArg (fun x : ℕ => (x : ℤ)) hpa
      push_cast at this
      linarith
    have hq' : (q : ℤ) = 2 * M + b := by exact_mod_cast hqb
    have : ((p : ℤ) + 1) * ((q : ℤ) + 1) + ((M : ℤ) * (2 * c + 1) + (b + 3 + 2 * c) * (b + 1)) =
        (M : ℤ) * (p + q + 1) := by
      rw [hp', hq']; ring
    exact_mod_cast this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [Nat.abundant_iff_sum_divisors, h2n]
    nlinarith
  · -- not pseudoperfect
    rintro ⟨-, s, hs, hsum⟩
    have hsd := Finset.sum_sdiff hs (f := fun x => x)
    have hpd := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ k * p * q)
    set T := ∑ x ∈ (2 ^ k * p * q).properDivisors \ s, x with hT
    -- T + 2n = sigma(n), so T is the abundance
    have hTeq : T = M * (2 * c + 1) + (b + 3 + 2 * c) * (b + 1) := by
      nlinarith
    have hsmall : T < p * q := by
      rw [hTeq]
      nlinarith
    have htsub : (2 ^ k * p * q).properDivisors \ s ⊆ (2 ^ k * p * q).divisors :=
      (Finset.sdiff_subset).trans (Nat.properDivisors_subset_divisors)
    obtain ⟨A0, B, C, hABC, hA0⟩ := decomp k p q hp hq hpq _ htsub hsmall
    rw [← hM] at hA0
    exact gap M p q b c A0 B C hpa hqb hA0 hsize (by rw [← hABC, ← hT, hTeq])
  · -- primitive: every proper divisor is non-abundant
    intro d hd hw
    have hab := hw.1
    rcases dvd_cases k p q d hk hp hq hd with h | h | h
    · have hk' : k - 1 + 2 = k + 1 := by omega
      have hnot := not_abundant_two_pow_mul_mul (k - 1) p q hp hq hp2 hq2 hpq
        (by rw [hk', ← hM]; omega) (by rw [hk', ← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h
        (Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k q hq hq2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k p hp hp2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hp.ne_zero))

-- The statement of step H1 of the reduction Erdos470.erdos_470.parts.ii.R1.
theorem melfi : ∀ k a b : ℕ, b + 3 < a → a * (a + b) < 2 ^ (k + 2) → (2 ^ (k + 2) - a).Prime →
    (2 ^ (k + 2) + b).Prime →
    Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b)) := by
  intro k a b hab hsize hp hq
  set M := 2 ^ (k + 1) with hM
  have hX : 2 ^ (k + 2) = 2 * M := by rw [hM]; ring
  rw [hX] at hsize hp hq ⊢
  have hM2 : 2 ≤ M := by rw [hM]; exact Nat.le_self_pow (by omega) 2
  have haM : a < M := by
    rcases Nat.lt_or_ge a M with h | h
    · exact h
    · nlinarith
  set p := 2 * M - a with hpdef
  set q := 2 * M + b with hqdef
  have hpa : p + a = 2 * M := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  obtain ⟨i, hi⟩ := hp.odd_of_ne_two hp2
  obtain ⟨j, hj⟩ := hq.odd_of_ne_two hq2
  obtain ⟨c, hc⟩ : ∃ c, a = b + 4 + 2 * c := ⟨(a - b - 4) / 2, by omega⟩
  subst hc
  exact core k M p q b c hM hpa hqdef hsize hp hq

end OMAMelfi

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := OMAMelfi.melfi
