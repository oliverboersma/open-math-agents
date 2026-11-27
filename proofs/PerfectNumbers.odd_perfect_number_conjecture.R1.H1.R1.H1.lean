import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1

-- An odd perfect number whose least prime factor is 3 has at least three distinct prime factors.
-- Original Lean proof of an elementary bound of Gruen type. The divisor sum satisfies
-- sigma(n) * prod (p - 1) <= n * prod p over the primes dividing n (prime powers by the geometric sum, then
-- multiplicativity), so a perfect n needs 2 * prod (p - 1) <= prod p. For r distinct odd numbers >= m the
-- product of p / (p - 1) is at most prod_{j<r} (m + 2j) / (m + 2j - 1), by induction adding the largest element,
-- and that is below 2 for r <= 2.
-- An elementary case of the odd perfect number problem, not progress on it.

namespace OMA.OPNH1

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- The abundancy bound: `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`. -/
lemma sigma_bound (n : ℕ) :
    sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton,
      sigma_one_apply_prime_pow hp]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := geom p hp.one_lt.le (j + 1)
    have h2 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := pow_succ p (j + 1)
    omega
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors, Finset.prod_union hab.disjoint_primeFactors]
    calc sigma 1 a * sigma 1 b * ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
        = (sigma 1 a * ∏ p ∈ a.primeFactors, (p - 1)) *
            (sigma 1 b * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
      _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
          Nat.mul_le_mul iha ihb
      _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- For distinct numbers `≥ c + 1` of the parity of `c + 1`:
`∏ p / (p - 1) ≤ ∏_{j < r} (c + 2j + 1) / (c + 2j)`. -/
lemma odd_prod_bound_from (c : ℕ) (s : Finset ℕ) :
    (∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2) →
    (∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2 :=
      fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, (x - (c + 1)) / 2 ∈ range ((a - (c + 1)) / 2) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x - (c + 1)) / 2) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ (a - (c + 1)) / 2 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => (x - (c + 1)) / 2) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (c + 2 * s.card) * a ≤ (c + 2 * s.card + 1) * (a - 1) := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : c + 2 * s.card ≤ d := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (c + 2 * j)) * (c + 2 * s.card) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (c + 2 * j)) * ∏ p ∈ s, p) * ((c + 2 * s.card) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (c + 2 * j + 1)) * ∏ p ∈ s, (p - 1)) *
            ((c + 2 * s.card + 1) * (a - 1)) := Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (c + 2 * j + 1)) * (c + 2 * s.card + 1) *
            ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

/-- An odd perfect number whose least prime factor is at least `c + 1` (odd) has so many distinct
prime factors `r` that `2 * ∏_{j<r} (c + 2j) ≤ ∏_{j<r} (c + 2j + 1)`. -/
lemma perfect_key (n c : ℕ) (hperf : Nat.Perfect n) (hodd : Odd n) (hmin : c + 1 ≤ n.minFac)
    (hc : (c + 1) % 2 = 1) :
    2 * (∏ j ∈ range n.primeFactors.card, (c + 2 * j)) ≤
      ∏ j ∈ range n.primeFactors.card, (c + 2 * j + 1) := by
  have hpos : 0 < n := hperf.2
  have hs : sigma 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have hbound := sigma_bound n
  rw [hs] at hbound
  have hkey : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    have h2 : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) ≤ n * ∏ p ∈ n.primeFactors, p := by
      calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
        _ ≤ _ := hbound
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hge : ∀ p ∈ n.primeFactors, c + 1 ≤ p ∧ p % 2 = (c + 1) % 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpo : p % 2 = 1 := by
      obtain ⟨e, hcb⟩ := hodd
      obtain ⟨d, hd⟩ := hpd
      by_contra hne
      have hpe : p % 2 = 0 := by omega
      have : (p * d) % 2 = 0 := by rw [Nat.mul_mod, hpe]; simp
      omega
    have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    exact ⟨by omega, by omega⟩
  have hodd' := odd_prod_bound_from c n.primeFactors hge
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
  have h3 : (∏ p ∈ n.primeFactors, (p - 1)) * (2 * ∏ j ∈ range n.primeFactors.card, (c + 2 * j)) ≤
      (∏ p ∈ n.primeFactors, (p - 1)) * ∏ j ∈ range n.primeFactors.card, (c + 2 * j + 1) := by
    calc (∏ p ∈ n.primeFactors, (p - 1)) * (2 * ∏ j ∈ range n.primeFactors.card, (c + 2 * j))
        = (∏ j ∈ range n.primeFactors.card, (c + 2 * j)) * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := by
          ring
      _ ≤ (∏ j ∈ range n.primeFactors.card, (c + 2 * j)) * ∏ p ∈ n.primeFactors, p :=
          Nat.mul_le_mul_left _ hkey
      _ ≤ (∏ j ∈ range n.primeFactors.card, (c + 2 * j + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := hodd'
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h3 hQ

theorem few (n : ℕ) (hperf : Nat.Perfect n) (hodd : Odd n) (hc : n.primeFactors.card ≤ 2) :
    Nat.minFac n ≠ 3 := by
  intro h3
  have hk := perfect_key n 2 hperf hodd (by omega) (by norm_num)
  generalize n.primeFactors.card = r at hc hk
  interval_cases r <;> simp [Finset.prod_range_succ] at hk

end OMA.OPNH1

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1.H1 := by
  intro n hperf hodd hc
  exact OMA.OPNH1.few n hperf hodd hc
