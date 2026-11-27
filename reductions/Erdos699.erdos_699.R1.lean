import FormalConjectures.ErdosProblems.«699»

/-! Reduction of Erdős 699. The square bound is ported from Paul Lee's public Lean
proof, Paulee314/erdos699-lean, commit 814f545f5f64, under Apache-2.0.
Copyright 2025 The Formal Conjectures Authors. Copyright 2026 Paul Lee.
The remaining range is divided at the Erdős Problems exposition's threshold of
three halves. In the near range a sufficiently large divisor with large prime factors
suffices by binomial cancellation. In the far range one needs two modular witnesses
in the same prime base, possibly at different digit positions. -/
-- Credit: @marcusbuffett
namespace OMA.R_Erdos699_erdos_699_R1

/-- For `j ≤ n`: `j(j-1)⋯(j-i+1) · n^i ≤ n(n-1)⋯(n-i+1) · j^i`. -/
private theorem descFactorial_mul_pow_le {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.descFactorial i * n ^ i ≤ n.descFactorial i * j ^ i
  | 0 => by simp
  | i + 1 => by
    have ih := descFactorial_mul_pow_le hjn i
    have key : (j - i) * n ≤ (n - i) * j := by
      rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n j]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hjn) _
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (j - i) * j.descFactorial i * (n ^ i * n)
        = ((j - i) * n) * (j.descFactorial i * n ^ i) := by ring
      _ ≤ ((n - i) * j) * (n.descFactorial i * j ^ i) := Nat.mul_le_mul key ih
      _ = (n - i) * n.descFactorial i * (j ^ i * j) := by ring

/-- For `j ≤ n`: `C(j, i) · n^i ≤ C(n, i) · j^i`, i.e. `C(n, i) / C(j, i) ≥ (n / j)^i`. -/
private theorem choose_mul_pow_le {i j n : ℕ} (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by
  have h := descFactorial_mul_pow_le hjn i
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos i)

/-- The identity `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)` gives
`C(n, i) ∣ gcd(C(n, i), C(n, j)) · C(j, i)` (Erdős and Szekeres). -/
private theorem choose_dvd_gcd_mul {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
  rw [← Nat.gcd_mul_right]
  refine Nat.dvd_gcd (Nat.dvd_mul_right _ _) ?_
  rw [Nat.choose_mul (n := n) hij]
  exact Nat.dvd_mul_right _ _

/-- A divisor `g` of `C(n, i)`, with `i ≤ n`, is at most `n ^ ω(g)`, because
`p ^ v_p(C(n, i)) ≤ n` for every prime `p` (Kummer). -/
private theorem le_pow_card_of_dvd_choose {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hdvd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
  calc g = g.factorization.prod (fun p k => p ^ k) := (Nat.prod_factorization_pow_eq_self hg).symm
    _ = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
        rw [Finsupp.prod, Nat.support_factorization]
    _ ≤ ∏ _p ∈ g.primeFactors, n := by
        refine Finset.prod_le_prod (by intros; exact Nat.zero_le _) (fun p hp => ?_)
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        calc p ^ g.factorization p ≤ p ^ (n.choose i).factorization p :=
              Nat.pow_le_pow_right hp'.pos ((Nat.factorization_le_iff_dvd hg hc).2 hdvd p)
          _ ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hp'.pos Nat.factorization_choose_le_log
          _ ≤ n := Nat.pow_log_le_self p hn
    _ = n ^ g.primeFactors.card := Finset.prod_const n

/-- A set of primes below `i` has at most `i / 2` elements: `p ↦ (p - 1) / 2` is injective on
primes and maps those below `i` into `[0, i / 2)`. -/
private theorem two_mul_card_le {s : Finset ℕ} {i : ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p < i) :
    2 * s.card ≤ i := by
  have h : s.card ≤ (Finset.range (i / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      have hp' : p ∈ s := by simpa using hp
      obtain ⟨hpp, hpi⟩ := hs p hp'
      have := hpp.two_le
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro p hp q hq hpq
      have hp' : p ∈ s := by simpa using hp
      have hq' : q ∈ s := by simpa using hq
      obtain ⟨hpp, -⟩ := hs p hp'
      obtain ⟨hqp, -⟩ := hs q hq'
      have h2p := hpp.two_le
      have h2q := hqp.two_le
      have hop := hpp.eq_two_or_odd
      have hoq := hqp.eq_two_or_odd
      simp only at hpq
      omega
  simp only [Finset.card_range] at h
  omega

/-- If no prime `p ≥ i` divides `gcd(C(n, i), C(n, j))`, with `1 ≤ i < j ≤ n / 2`, then
`n ≤ j²`. -/
private theorem le_sq_of_counterexample {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (hcon : ∀ p : ℕ, p.Prime → i ≤ p → ¬ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    n ≤ j ^ 2 := by
  have hjn' : j ≤ n := le_trans hjn (Nat.div_le_self n 2)
  have hin : i ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hA : 0 < n.choose i := Nat.choose_pos hin
  have hB : 0 < j.choose i := Nat.choose_pos hij.le
  set g := Nat.gcd (n.choose i) (n.choose j) with hg_def
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ hA).ne'
  -- `C(n, i) ≤ g · C(j, i)`
  have h1 : n.choose i ≤ g * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hg0) hB) (choose_dvd_gcd_mul hij.le)
  -- `g ≤ n ^ c` with `2c ≤ i`, since every prime factor of `g` is below `i`
  have h3 : g ≤ n ^ g.primeFactors.card :=
    le_pow_card_of_dvd_choose hn0 hg0 hin (Nat.gcd_dvd_left _ _)
  have hc : 2 * g.primeFactors.card ≤ i := by
    refine two_mul_card_le (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩)
    by_contra hpi
    exact hcon p (Nat.prime_of_mem_primeFactors hp) (not_lt.1 hpi)
      (Nat.dvd_of_mem_primeFactors hp)
  set c := g.primeFactors.card
  -- `C(j, i) · n^i ≤ C(n, i) · j^i`
  have h2 := choose_mul_pow_le (i := i) hjn'
  have h4 : j.choose i * n ^ i ≤ j.choose i * (n ^ c * j ^ i) :=
    calc j.choose i * n ^ i ≤ n.choose i * j ^ i := h2
      _ ≤ g * j.choose i * j ^ i := Nat.mul_le_mul_right _ h1
      _ ≤ n ^ c * j.choose i * j ^ i := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
      _ = j.choose i * (n ^ c * j ^ i) := by ring
  have h5 : n ^ i ≤ n ^ c * j ^ i := Nat.le_of_mul_le_mul_left h4 hB
  have h6 : n ^ i * n ^ i ≤ n ^ i * (j ^ 2) ^ i :=
    calc n ^ i * n ^ i ≤ (n ^ c * j ^ i) * (n ^ c * j ^ i) := Nat.mul_le_mul h5 h5
      _ = n ^ (2 * c) * (j ^ 2) ^ i := by ring
      _ ≤ n ^ i * (j ^ 2) ^ i := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hnpos hc)
  have h7 : n ^ i ≤ (j ^ 2) ^ i := Nat.le_of_mul_le_mul_left h6 (Nat.pow_pos hnpos)
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h7

/-- Erdős Problem 699 holds whenever `j² < n`. -/
private theorem of_sq_lt :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by
  intro n i j hi hij hjn hsq
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have := le_sq_of_counterexample hi hij hjn hcon
  omega



private theorem prime_of_rough_divisor {n i j d : ℕ} (hij : i ≤ j)
    (hd : d ∣ n.choose i) (hsize : j.choose i < d)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ d → i ≤ p) :
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  have hnd : ¬ d.Coprime (n.choose j) := by
    intro hcop
    have hdprod : d ∣ n.choose j * j.choose i := by
      rw [Nat.choose_mul (n := n) hij]
      exact dvd_mul_of_dvd_left hd _
    exact (Nat.not_le_of_gt hsize) (Nat.le_of_dvd (Nat.choose_pos hij)
      (hcop.dvd_of_dvd_mul_left hdprod))
  obtain ⟨p, hp, hpd, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnd
  exact ⟨p, hp, hrough p hp hpd, Nat.dvd_gcd (dvd_trans hpd hd) hpj⟩

private theorem dvd_choose_of_digit {n k p e : ℕ} (hp : p.Prime) (hk : k ≤ n)
    (he : 0 < e) (hw : n % p ^ e < k % p ^ e) : p ∣ n.choose k := by
  have hc : p ^ e ≤ k % p ^ e + (n-k) % p ^ e := by
    by_contra! h
    have hr := Nat.add_mod k (n-k) (p ^ e)
    rw [Nat.add_sub_of_le hk, Nat.mod_eq_of_lt h] at hr
    exact (Nat.not_le_of_lt hw) (hr ▸ Nat.le_add_right _ _)
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose hp hk (b := max e (Nat.log p n) + 1) (by omega)]
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨he, by omega⟩, hc⟩⟩

private theorem small_index {n i j : ℕ} (hi : 1 ≤ i) (hs : i ≤ 2) (hij : i < j)
    (hjn : j ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  apply prime_of_rough_divisor hij.le (dvd_refl _)
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    have key : j.choose (a+1) < (j+1).choose (a+1) := by
      rw [Nat.choose_succ_succ]
      exact Nat.lt_add_of_pos_left (Nat.choose_pos (by omega))
    exact key.trans_le (Nat.choose_le_choose _ (by omega))
  · exact fun p hp _ => hs.trans hp.two_le

/-- Large-prime part estimate for the near range. -/
def H1 : Prop := ∀ n i j : ℕ, 3 ≤ i → i < j → j ≤ n / 2 → n ≤ j ^ 2 →
    2 * j ≤ 3 * i → ∃ d : ℕ, d ∣ n.choose i ∧ j.choose i < d ∧
      ∀ p : ℕ, p.Prime → p ∣ d → i ≤ p

/-- A simultaneous base-p digit obstruction in the remaining far range. -/
def H2 : Prop := ∀ n i j : ℕ, 3 ≤ i → i < j → j ≤ n / 2 → n ≤ j ^ 2 →
    3 * i < 2 * j → ∃ p a b : ℕ, p.Prime ∧ i ≤ p ∧ 0 < a ∧ 0 < b ∧
      n % p ^ a < i % p ^ a ∧ n % p ^ b < j % p ^ b

theorem main : H1 → H2 → type_of% @Erdos699.erdos_699 := by
  intro near far n i j hi hij hjn
  by_cases hs : i ≤ 2
  · exact small_index hi hs hij hjn
  by_cases hsq : j ^ 2 < n
  · exact of_sq_lt n i j hi hij hjn hsq
  by_cases hnear : 2 * j ≤ 3 * i
  · obtain ⟨d, hd, hsize, hrough⟩ := near n i j (by omega) hij hjn (by omega) hnear
    exact prime_of_rough_divisor hij.le hd hsize hrough
  · obtain ⟨p, a, b, hp, hpi, ha, hb, hia, hjb⟩ :=
      far n i j (by omega) hij hjn (by omega) (by omega)
    exact ⟨p, hp, hpi, Nat.dvd_gcd (dvd_choose_of_digit hp (by omega) ha hia)
      (dvd_choose_of_digit hp (by omega) hb hjb)⟩

end OMA.R_Erdos699_erdos_699_R1
