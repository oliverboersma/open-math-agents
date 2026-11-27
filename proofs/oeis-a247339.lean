import OMAStatements.S_oeis_a247339

namespace OMA.S_oeis_a247339


theorem gpf_eq (m p : ℕ) (hm : m ≠ 0) (hp : p.Prime) (hd : p ∣ m)
    (hq : ∀ q, q.Prime → q ∣ m → q ≤ p) : gpf m = p := by
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq'
    rw [Nat.mem_primeFactors] at hq'
    exact hq q hq'.1 hq'.2.1
  · exact Finset.le_sup (f := id) (hp.mem_primeFactors hd hm)

/-- The conjecture: for every `n ≥ 1` some `m` with `1 ≤ m ≤ n` has
`gpf (m^2+1) = minFac (n^2+1)`. -/
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ gpf (m ^ 2 + 1) = Nat.minFac (n ^ 2 + 1) := by
  set p := Nat.minFac (n ^ 2 + 1) with hpdef
  have hp : p.Prime := Nat.minFac_prime (by nlinarith)
  have hpd : p ∣ n ^ 2 + 1 := Nat.minFac_dvd _
  have hp2 := hp.two_le
  set r := n % p with hr
  have hrlt : r < p := Nat.mod_lt _ (by omega)
  have hrn : r ≤ n := Nat.mod_le _ _
  have hr0 : r ≠ 0 := by
    intro h0
    have h1 : p ∣ n := Nat.dvd_of_mod_eq_zero h0
    have h2 : p ∣ n ^ 2 := dvd_pow h1 (by norm_num)
    have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp hpd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  -- `n ≡ r (mod p)` in `ZMod p`
  have hnr : (n : ZMod p) = (r : ZMod p) := by
    rw [hr, ZMod.natCast_mod]
  have hn0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  -- the choice of `m`
  obtain ⟨m, hm1, hmn, hm2, hmz⟩ : ∃ m, 1 ≤ m ∧ m ≤ n ∧ 2 * m ≤ p ∧
      ((m ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    by_cases hc : 2 * r ≤ p
    · refine ⟨r, by omega, hrn, hc, ?_⟩
      push_cast at hn0 ⊢
      rw [← hnr]; exact hn0
    · refine ⟨p - r, by omega, by omega, by omega, ?_⟩
      have : ((p - r : ℕ) : ZMod p) = -(r : ZMod p) := by
        rw [Nat.cast_sub hrlt.le, ZMod.natCast_self, zero_sub]
      push_cast at hn0 ⊢
      rw [Nat.cast_sub hrlt.le, ZMod.natCast_self, zero_sub, neg_sq, ← hnr]
      exact hn0
  have hmd : p ∣ m ^ 2 + 1 := (ZMod.natCast_eq_zero_iff _ _).mp hmz
  refine ⟨m, hm1, hmn, gpf_eq _ _ (by positivity) hp hmd ?_⟩
  intro q hq hqd
  by_contra hlt
  push_neg at hlt
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hpq : p * q ∣ m ^ 2 + 1 := hcop.mul_dvd_of_dvd_of_dvd hmd hqd
  have hle : p * q ≤ m ^ 2 + 1 := Nat.le_of_dvd (by positivity) hpq
  have h4 : 4 * m ^ 2 ≤ p ^ 2 := by nlinarith
  have hq1 : p + 1 ≤ q := hlt
  nlinarith

end OMA.S_oeis_a247339

theorem OMA.solution : type_of% @OMA.S_oeis_a247339.main :=
  fun n hn => OMA.S_oeis_a247339.conjecture n hn
