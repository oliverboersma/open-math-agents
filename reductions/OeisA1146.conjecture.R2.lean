import FormalConjectures.OEIS.«1146»

-- Credit: @artificialkral
-- Reduction of Hasler's 2015 conjecture on OEIS A001146.
namespace OMA.R_OeisA1146_conjecture_R2

theorem pow_two_divisibility_iff {t : ℕ} :
    (2 ^ t) ^ 4 - 1 ∣ 2 ^ (2 ^ t) - 1 ↔ t * 4 ∣ 2 ^ t := by
  rw [← pow_mul]
  constructor
  · intro h
    have hrem := Nat.mod_eq_zero_of_dvd h
    rw [Nat.pow_sub_one_mod_pow_sub_one] at hrem
    have hzero : 2 ^ t % (t * 4) = 0 := by
      by_contra hne
      have hlt : 1 < 2 ^ (2 ^ t % (t * 4)) := by
        exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hne
      omega
    exact Nat.dvd_of_mod_eq_zero hzero
  · rintro ⟨j, hj⟩
    rw [hj, pow_mul 2 (t * 4) j]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ (t * 4)) j

theorem classification_of_power_two {t : ℕ}
    (h : (2 ^ t) ^ 4 - 1 ∣ 2 ^ (2 ^ t) - 1) : ∃ n : ℕ, 2 ≤ n ∧ t = 2 ^ n := by
  have h' := pow_two_divisibility_iff.mp h
  have ht : t ∣ 2 ^ t := dvd_trans (dvd_mul_right t 4) h'
  obtain ⟨n, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht
  refine ⟨n, ?_, rfl⟩
  by_contra hn
  interval_cases n <;> norm_num at h'

theorem sub_one_dvd_of_divisibility {k : ℕ} (h : k ^ 4 - 1 ∣ 2 ^ k - 1) :
    k - 1 ∣ 2 ^ k - 1 :=
  dvd_trans (Nat.sub_one_dvd_pow_sub_one k 4) h

theorem square_add_one_dvd_of_divisibility {k : ℕ}
    (h : k ^ 4 - 1 ∣ 2 ^ k - 1) : k ^ 2 + 1 ∣ 2 ^ k - 1 := by
  apply dvd_trans _ h
  refine ⟨k ^ 2 - 1, ?_⟩
  have hmul : (k ^ 2 + 1) * k ^ 2 = k ^ 4 + k ^ 2 := by ring
  rw [Nat.mul_sub_left_distrib, mul_one, hmul]
  omega

theorem pow_two_eq_one_of_dvd {k q : ℕ} (h : q ∣ 2 ^ k - 1) :
    (2 : ZMod q) ^ k = 1 := by
  have hmod : 1 ≡ 2 ^ k [MOD q] := Nat.modEq_of_dvd' (Nat.one_le_pow k 2 (by decide)) h
  simpa using ((ZMod.natCast_eq_natCast_iff 1 (2 ^ k) q).mpr hmod).symm

theorem square_le_of_dvd_sub_one {k q d : ℕ} (hk : 1 < k) (hq : 1 < q)
    (hdiv : q ∣ k - 1) (hdk : d ∣ k) (hdq : d ∣ q - 1) : d ^ 2 ≤ k := by
  obtain ⟨b, hb⟩ := hdiv
  have hkb : k = q * b + 1 := by omega
  have hqmod : 1 ≡ q [MOD d] := Nat.modEq_of_dvd' (by omega) hdq
  have hbmod : q * b + 1 ≡ b + 1 [MOD d] := by
    simpa using (hqmod.symm.mul_right b).add_right 1
  have hdmod : k ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hdk
  have hdb : d ∣ b + 1 := by
    rw [hkb] at hdmod
    exact Nat.modEq_zero_iff_dvd.mp (hbmod.symm.trans hdmod)
  have hdq' := Nat.le_of_dvd (by omega : 0 < q - 1) hdq
  have hdb' := Nat.le_of_dvd (Nat.succ_pos b) hdb
  have hprod := Nat.mul_le_mul (by omega : d + 1 ≤ q) (by omega : d - 1 ≤ b)
  cases d with
  | zero => simp
  | succ e =>
      simp only [Nat.succ_sub_one] at hprod ⊢
      nlinarith only [hkb, hprod]

theorem order_two_square_le {k q : ℕ} (hk : 1 < k) (hq : q.Prime)
    (hdiv : q ∣ k - 1) (h : k ^ 4 - 1 ∣ 2 ^ k - 1) :
    orderOf (2 : ZMod q) ^ 2 ≤ k := by
  let : Fact q.Prime := ⟨hq⟩
  have hpow' := pow_two_eq_one_of_dvd (dvd_trans hdiv (sub_one_dvd_of_divisibility h))
  have hne : (2 : ZMod q) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : k ≠ 0)] at hpow'
    exact zero_ne_one hpow'
  exact square_le_of_dvd_sub_one hk hq.one_lt hdiv (orderOf_dvd_of_pow_eq_one hpow')
    (ZMod.orderOf_dvd_card_sub_one hne)

theorem prime_order_witness {n k p e : ℕ} (hk : 0 < k) (hc : n.Coprime k)
    (h : n ∣ 2 ^ k - 1) (hp : p.Prime) (he : 0 < e)
    (hpe : p ^ e ∣ orderOf (2 : ZMod n)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ p ^ e ∣ orderOf (2 : ZMod q) := by
  let d := orderOf (2 : ZMod n)
  have hdk : d ∣ k := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd h)
  have hdpos := Nat.pos_of_dvd_of_pos hdk hk
  obtain ⟨s, hs⟩ : p ^ e ∣ d := hpe
  obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  let u := s * p ^ f
  have hud : u * p = d := by rw [hs]; dsimp [u]; ring
  have hu : u < d := by
    have hupos : 0 < u := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hud; omega
    nlinarith [hp.two_le, hud, Nat.mul_le_mul_left u hp.two_le]
  have hnA : ¬ n ∣ 2 ^ u - 1 := by
    intro ha
    exact (not_le_of_gt hu) (Nat.le_of_dvd (by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hud; omega)
      (orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd ha)))
  have hnd : n ∣ 2 ^ d - 1 := by
    apply (Nat.modEq_iff_dvd' (Nat.one_le_pow d 2 (by decide))).mp
    apply (ZMod.natCast_eq_natCast_iff 1 (2 ^ d) n).mp
    simp [d]
  let S : ℕ := ∑ i ∈ Finset.range p, ((2 : ℕ) ^ u) ^ i
  have hprod : n ∣ S * (2 ^ u - 1) := by
    change n ∣ (∑ i ∈ Finset.range p, ((2 : ℕ) ^ u) ^ i) * (2 ^ u - 1)
    rwa [geom_sum_mul_of_one_le (Nat.one_le_pow u 2 (by decide)), ← pow_mul, hud]
  have hnS : ¬ n.Coprime S := fun hcop => hnA (hcop.dvd_mul_left.mp hprod)
  obtain ⟨q, hq, hqn, hqS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnS
  let t := orderOf (2 : ZMod q)
  have htd : t ∣ d := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd (hqn.trans hnd))
  have htu : ¬ t ∣ u := by
    intro ht
    have hz : (2 : ZMod q) ^ u = 1 := orderOf_dvd_iff_pow_eq_one.mp ht
    have hqp : q ∣ p := by
      apply (ZMod.natCast_eq_zero_iff p q).mp
      simpa [S, hz] using (ZMod.natCast_eq_zero_iff S q).mpr hqS
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨q, hq, hqn, hqp.trans ((dvd_mul_left p u).trans (hud ▸ hdk))⟩ hc
  rw [hs, mul_comm] at htd
  obtain ⟨x, y, hx, hy, hxy⟩ := dvd_mul.mp htd
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
  have hj' : j = f + 1 := by
    by_contra hn
    apply htu
    rw [hxy]
    exact Nat.mul_dvd_mul hx (pow_dvd_pow _ (by omega))
  exact ⟨q, hq, hqn, by change p ^ (f + 1) ∣ t; rw [hxy, hj']; exact dvd_mul_left _ _⟩

/-- The sixteen divisors of 2^16 - 1 settle all periods dividing 16. -/
theorem power_two_of_small_period {k : ℕ} (hk : 1 < k)
    (h : k ^ 4 - 1 ∣ 2 ^ k - 1) (hd : k - 1 ∣ 65535) : ∃ s : ℕ, k = 2 ^ s := by
  obtain ⟨a, b, ha, hb, hab⟩ := dvd_mul.mp (show k - 1 ∣ (3 * 5) * (17 * 257) from hd)
  obtain ⟨x, y, hx, hy, rfl⟩ := dvd_mul.mp ha
  obtain ⟨z, w, hz, hw, rfl⟩ := dvd_mul.mp hb
  have heq : k = x * y * (z * w) + 1 := by omega
  have hm := pow_two_eq_one_of_dvd h
  clear hab hd hk h
  subst k
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hx with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hy with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hz with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 257)).mp hw with rfl | rfl
  all_goals
    first
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨16, rfl⟩
    | exfalso
      reduce_mod_char at hm <;> revert hm <;> decide

/-- Exclude an odd prime in a local order at a prime divisor of k - 1,
for the candidates surviving the two other order tests. -/
def H1 : Prop := ∀ k q p : ℕ, 1 < k → k - 1 ∣ 2 ^ k - 1 →
  orderOf (2 : ZMod (k + 1)) ∣ k → orderOf (2 : ZMod (k ^ 2 + 1)) ∣ k →
  q.Prime → q ∣ k - 1 → p.Prime → p ∣ orderOf (2 : ZMod q) → p ^ 2 ≤ k → p = 2

/-- In the power-of-two period case, test the two remaining moduli
on divisors of a Mersenne number with power-of-two exponent. -/
def H2 : Prop := ∀ k t : ℕ, 5 ≤ t → 1 < k → orderOf (2 : ZMod (k - 1)) = 2 ^ t → 2 ^ t ∣ k →
  orderOf (2 : ZMod (k + 1)) ∣ k → orderOf (2 : ZMod (k ^ 2 + 1)) ∣ k →
  ∃ s : ℕ, k = 2 ^ s

theorem main : H1 → H2 → type_of% @OeisA1146.conjecture := by
  intro h1 h2 k h hk
  have hminus := sub_one_dvd_of_divisibility h
  have hplus : k + 1 ∣ k ^ 4 - 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    refine ⟨j * ((j + 1) ^ 2 + 1), Nat.sub_eq_of_eq_add ?_⟩
    simp only [Nat.succ_eq_add_one]
    ring
  have hp1 := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd (hplus.trans h))
  have hp2 := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd (square_add_one_dvd_of_divisibility h))
  let d := orderOf (2 : ZMod (k - 1))
  have hdk : d ∣ k := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd hminus)
  have hpos := Nat.pos_of_dvd_of_pos hdk (by omega)
  have hc : (k - 1).Coprime k := by
    conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hpow : d = 2 ^ d.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne'
    intro p hp hpd
    obtain ⟨q, hq, hqn, hqpe⟩ := prime_order_witness (by omega : 0 < k) hc hminus hp
      (by decide : 0 < 1) (by simpa using hpd : p ^ 1 ∣ d)
    have hqt : p ∣ orderOf (2 : ZMod q) := by simpa using hqpe
    have hqk := orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_dvd (hqn.trans hminus))
    have hple := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hqk (by omega)) hqt
    exact h1 k q p hk hminus hp1 hp2 hq hqn hp hqt
      ((pow_le_pow_left' hple 2).trans (order_two_square_le hk hq hqn h))
  have hdM : k - 1 ∣ 2 ^ d - 1 := by
    apply (Nat.modEq_iff_dvd' (Nat.one_le_pow d 2 (by decide))).mp
    apply (ZMod.natCast_eq_natCast_iff 1 (2 ^ d) (k - 1)).mp
    simp [d]
  have hclass : ∃ s : ℕ, k = 2 ^ s := by
    by_cases ht : 5 ≤ d.primeFactorsList.length
    · exact h2 k _ ht hk hpow (hpow ▸ hdk) hp1 hp2
    · have hd16 : d ∣ 16 := hpow ▸ pow_dvd_pow 2 (by omega : d.primeFactorsList.length ≤ 4)
      obtain ⟨j, hj⟩ := hd16
      have hM16 : 2 ^ d - 1 ∣ 2 ^ 16 - 1 := by
        rw [hj, pow_mul 2 d j]
        exact Nat.sub_one_dvd_pow_sub_one _ _
      exact power_two_of_small_period hk h (hdM.trans hM16)
  obtain ⟨s, hs⟩ := hclass
  rw [hs] at h ⊢
  obtain ⟨n, hn, hsn⟩ := classification_of_power_two h
  exact ⟨n, hn, congrArg (fun t => (2 : ℕ) ^ t) hsn⟩

end OMA.R_OeisA1146_conjecture_R2
