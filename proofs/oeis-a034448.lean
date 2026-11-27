import OMAStatements.S_oeis_a034448

section
open Finset Nat

theorem U_mul {m n : ℕ} (hmn : m.Coprime n) :
    OMA.S_oeis_a034448.unitarySum (m * n) =
      OMA.S_oeis_a034448.unitarySum m * OMA.S_oeis_a034448.unitarySum n := by
  unfold OMA.S_oeis_a034448.unitarySum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum,
    hmn.divisors_mul, Finset.sum_map]
  refine (Finset.sum_attach (Nat.divisors m ×ˢ Nat.divisors n)
      (fun p : ℕ × ℕ => if (p.1 * p.2).Coprime (m * n / (p.1 * p.2)) then p.1 * p.2 else 0)).trans ?_
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [mem_divisors] at ha hb
  obtain ⟨⟨a', ha'⟩, hm⟩ := ha
  obtain ⟨⟨b', hb'⟩, hn⟩ := hb
  have hapos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at ha'; exact hm ha')
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hb'; exact hn hb')
  have e1 : m / a = a' := by rw [ha']; exact Nat.mul_div_cancel_left _ hapos
  have e2 : n / b = b' := by rw [hb']; exact Nat.mul_div_cancel_left _ hbpos
  have e3 : m * n / (a * b) = a' * b' := by
    rw [ha', hb']; rw [show a * a' * (b * b') = (a * b) * (a' * b') by ring]
    exact Nat.mul_div_cancel_left _ (Nat.mul_pos hapos hbpos)
  simp only [e1, e2, e3]
  have cop : ∀ x y : ℕ, x ∣ m → y ∣ n → x.Coprime y := fun x y hx hy =>
    (hmn.coprime_dvd_left hx).coprime_dvd_right hy
  have hcab : a.Coprime b' := cop a b' ⟨a', by rw [ha']⟩ ⟨b, by rw [hb']; ring⟩
  have hca'b : a'.Coprime b := (cop a' b ⟨a, by rw [ha']; ring⟩ ⟨b', by rw [hb']⟩)
  have hca'b' : a'.Coprime b' := cop a' b' ⟨a, by rw [ha']; ring⟩ ⟨b, by rw [hb']; ring⟩
  have hcab0 : a.Coprime b := cop a b ⟨a', by rw [ha']⟩ ⟨b', by rw [hb']⟩
  have key : (a * b).Coprime (a' * b') ↔ a.Coprime a' ∧ b.Coprime b' := by
    rw [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨⟨h1, _⟩, _, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩; exact ⟨⟨h1, hcab⟩, hca'b.symm, h4⟩
  by_cases h1 : a.Coprime a' <;> by_cases h2 : b.Coprime b'
  · rw [if_pos (key.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]
  · rw [if_neg (fun h => h2 (key.1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (key.1 h).1), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (key.1 h).1), if_neg h1, zero_mul]

theorem U_prime_pow {p e : ℕ} (hp : p.Prime) :
    OMA.S_oeis_a034448.unitarySum (p ^ (e + 1)) = 1 + p ^ (e + 1) := by
  unfold OMA.S_oeis_a034448.unitarySum
  rw [Finset.sum_filter, Nat.divisors_prime_pow hp, Finset.sum_map]
  have : ∀ i ∈ range (e + 1 + 1), (if (p ^ i).Coprime (p ^ (e + 1) / p ^ i) then p ^ i else 0) =
      (if i = 0 then 1 else 0) + (if i = e + 1 then p ^ (e + 1) else 0) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hd : p ^ (e + 1) / p ^ i = p ^ (e + 1 - i) := Nat.pow_div (by omega) hp.pos
    rw [hd]
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases hk : i = e + 1
      · subst hk; simp [h0]
      · rw [if_neg h0, if_neg hk, if_neg, zero_add]
        intro hc
        have h1 : p ∣ p ^ i := dvd_pow_self p h0
        have h2 : p ∣ p ^ (e + 1 - i) := dvd_pow_self p (by omega)
        exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc h1 h2)
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

open UniqueFactorizationMonoid ArithmeticFunction in
theorem main_aux : ∀ n : ℕ, 0 < n →
    OMA.S_oeis_a034448.unitarySum n * sigma 1 (n / radical n) =
      sigma 1 (n ^ 2 / radical n) := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one => intro _; simp [OMA.S_oeis_a034448.unitarySum, Finset.sum_filter]
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    have hrad : radical (p ^ (e + 1)) = p := by
      rw [radical_pow_of_prime hp.prime (by omega)]; simp
    rw [hrad, U_prime_pow hp]
    have d1 : p ^ (e + 1) / p = p ^ e := Nat.div_eq_of_eq_mul_left hp.pos (by ring)
    have d2 : (p ^ (e + 1)) ^ 2 / p = p ^ (2 * e + 1) :=
      Nat.div_eq_of_eq_mul_left hp.pos (by ring)
    rw [d1, d2, sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp,
      show 2 * e + 1 + 1 = (e + 1) + (e + 1) by ring]
    have hh : ∑ x ∈ range (e + 1), p ^ (e + 1 + x) = p ^ (e + 1) * ∑ x ∈ range (e + 1), p ^ x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => pow_add _ _ _)
    rw [Finset.sum_range_add (fun k => p ^ k) (e + 1) (e + 1)]
    beta_reduce
    rw [hh]; ring
  | coprime a b ha hb hab iha ihb =>
    intro _
    have hr : radical (a * b) = radical a * radical b :=
      radical_mul (Nat.coprime_iff_isRelPrime.1 hab)
    have hra : radical a ∣ a := radical_dvd_self
    have hrb : radical b ∣ b := radical_dvd_self
    have hra2 : radical a ∣ a ^ 2 := hra.trans (dvd_pow_self a (by norm_num))
    have hrb2 : radical b ∣ b ^ 2 := hrb.trans (dvd_pow_self b (by norm_num))
    have q1 : a * b / (radical a * radical b) = (a / radical a) * (b / radical b) :=
      (Nat.div_mul_div_comm hra hrb).symm
    have q2 : (a * b) ^ 2 / (radical a * radical b) = (a ^ 2 / radical a) * (b ^ 2 / radical b) := by
      rw [mul_pow]; exact (Nat.div_mul_div_comm hra2 hrb2).symm
    have c1 : (a / radical a).Coprime (b / radical b) :=
      (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hra)).coprime_dvd_right (Nat.div_dvd_of_dvd hrb)
    have c2 : (a ^ 2 / radical a).Coprime (b ^ 2 / radical b) :=
      ((hab.pow 2 2).coprime_dvd_left (Nat.div_dvd_of_dvd hra2)).coprime_dvd_right
        (Nat.div_dvd_of_dvd hrb2)
    rw [hr, q1, q2, U_mul hab, isMultiplicative_sigma.map_mul_of_coprime c1,
      isMultiplicative_sigma.map_mul_of_coprime c2, ← iha (by omega), ← ihb (by omega)]
    ring

end

theorem OMA.solution : type_of% @OMA.S_oeis_a034448.main := by
  intro n hn
  exact main_aux n hn
