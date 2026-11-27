import OMAStatements.S_oeis_a269454

namespace OMA.S_oeis_a269454

lemma key (p : ℕ) (h : InA269454 p) :
    orderOf (2 : ZMod p) = 2 * ((p - 1) / 2) ∧ p = 2 * ((p - 1) / 2) + 1 := by
  obtain ⟨⟨hp, hr⟩, h8⟩ := h
  set r := (p - 1) / 2 with hrdef
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_prime_zero (by simpa [hrdef] using hr)
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hpr : p = 2 * r + 1 := by omega
  have hr2 : 2 ≤ r := hr.two_le
  have h87 : p % 8 ≠ 7 := by
    intro h
    apply h8
    unfold Int.ModEq
    omega
  have h81 : p % 8 ≠ 1 := by
    rcases hr.eq_two_or_odd with h | h <;> omega
  have := Fact.mk hp
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hpow : (2 : ZMod p) ^ r ≠ 1 := by
    intro h
    apply hns
    rw [ZMod.euler_criterion p h2ne, show p / 2 = r by omega]
    exact h
  have hferm : (2 : ZMod p) ^ (2 * r) = 1 := by
    rw [show 2 * r = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h2ne
  refine ⟨?_, hpr⟩
  have hd : orderOf (2 : ZMod p) ∣ 2 * r := orderOf_dvd_of_pow_eq_one hferm
  obtain ⟨d1, d2, hd1, hd2, hdd⟩ := Nat.dvd_mul.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with rfl | rfl
  · exfalso
    apply hpow
    rw [← orderOf_dvd_iff_pow_eq_one, ← hdd, one_mul]
    exact hd2
  · rcases (Nat.dvd_prime hr).mp hd2 with rfl | rfl
    · exfalso
      have h1 : (2 : ZMod p) ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, ← hdd]
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h1
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact hdd.symm

end OMA.S_oeis_a269454

open OMA.S_oeis_a269454 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269454.main := by
  intro p q hpq hp hq
  obtain ⟨hop, hpe⟩ := key p hp
  obtain ⟨hoq, hqe⟩ := key q hq
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.1.1 hq.1.1).mpr hpq
  have hrs : Nat.Coprime ((p - 1) / 2) ((q - 1) / 2) :=
    (Nat.coprime_primes hp.1.2 hq.1.2).mpr (by omega)
  let e := ZMod.chineseRemainder hcop
  have h1 : orderOf (2 : ZMod (p * q)) = orderOf (e 2) :=
    (orderOf_injective e.toMonoidHom e.injective 2).symm
  have h2 : e 2 = (2, 2) := map_ofNat e 2
  rw [h1, h2, Prod.orderOf, hop, hoq, Nat.lcm_mul_left, hrs.lcm_eq_mul,
    Nat.totient_mul hcop, Nat.totient_prime hp.1.1, Nat.totient_prime hq.1.1]
  set r := (p - 1) / 2
  set s := (q - 1) / 2
  rw [show p - 1 = 2 * r by omega, show q - 1 = 2 * s by omega,
    show 2 * r * (2 * s) = 2 * (2 * (r * s)) by ring]
  omega
