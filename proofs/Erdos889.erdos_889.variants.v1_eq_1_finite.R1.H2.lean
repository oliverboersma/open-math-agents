import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1
import Mathlib.NumberTheory.Fermat

/-!
For an odd starting point, the first shift forces n+1 to be a power of two.
The second shift forces a Fermat exponent outside the computed small range.
The two Sophie Germain factors at the fifth shift have distinct prime divisors
above five. The potential all-five factor is excluded modulo three and seven.
-/
-- Credit: @dk8827

open Finset Nat

namespace OMA.Erdos889Odd

/-- A prime-power value of 2^a+1 beyond a=3 must be prime. -/
private theorem prime_power_plus_one {a : ℕ} (ha : 3 < a)
    (h : IsPrimePow ((2 : ℕ) ^ a + 1)) : ((2 : ℕ) ^ a + 1).Prime := by
  obtain ⟨q, b, hq, hb, heq⟩ := (isPrimePow_nat_iff _).mp h
  by_cases hb1 : b = 1
  · rw [hb1, pow_one] at heq
    exact heq ▸ hq
  have hpowEven : Even ((2 : ℕ) ^ a) :=
    even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have hpowOdd : Odd ((2 : ℕ) ^ a + 1) := hpowEven.add_odd odd_one
  have hq2 : q ≠ 2 := by
    intro hqeq
    subst q
    exact hpowOdd.not_two_dvd_nat (heq ▸ dvd_pow_self 2 hb.ne')
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  rcases Nat.even_or_odd b with hbe | hbo
  · obtain ⟨c, hc⟩ := hbe
    let Q := q ^ c
    have hQ : 3 ≤ Q := by
      have hqle : q ≤ q ^ c := by
        simpa only [pow_one] using (Nat.pow_le_pow_right hq.pos (show 1 ≤ c by omega))
      exact hq3.trans hqle
    have hQsq : Q ^ 2 = 2 ^ a + 1 := by
      simpa only [Q, hc, pow_two, pow_add] using heq
    have hfactor : (Q - 1) * (Q + 1) = 2 ^ a := by
      have hdiff : (Q - 1) * (Q + 1) + 1 = Q ^ 2 := by
        obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q ≠ 0)
        rw [hw, Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring
      omega
    have hleft : Q - 1 ∣ 2 ^ a := by rw [← hfactor]; exact dvd_mul_right _ _
    have hright : Q + 1 ∣ 2 ^ a := by rw [← hfactor]; exact dvd_mul_left _ _
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hleft
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hright
    have hj2 : 2 ≤ j := by
      by_contra! ht
      interval_cases j <;> norm_num at hj <;> omega
    have hi2 : i < 2 := by
      by_contra! ht
      have hfourL : 4 ∣ Q - 1 := by rw [hi]; exact pow_dvd_pow 2 ht
      have hfourR : 4 ∣ Q + 1 := by rw [hj]; exact pow_dvd_pow 2 hj2
      have hfour := Nat.dvd_sub hfourR hfourL
      rw [show Q + 1 - (Q - 1) = 2 by omega] at hfour
      exact (by decide : ¬ (4 : ℕ) ∣ 2) hfour
    have hQeq : Q = 3 := by
      interval_cases i <;> norm_num at hi <;> omega
    have hexp : (2 : ℕ) ^ a = 2 ^ 3 := by
      rw [← hfactor, hQeq]
      decide
    have haeq := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hexp
    omega
  · let U := ∑ j ∈ range b, q ^ j
    have hgeo : U * (q - 1) + 1 = q ^ b := by
      simpa only [U, Nat.sub_add_cancel (show 1 ≤ q by omega)] using geom_sum_mul_add (q - 1) b
    have hu : U ∣ 2 ^ a := by
      rw [show (2 : ℕ) ^ a = U * (q - 1) by omega]
      exact dvd_mul_right _ _
    have hqmod : q ≡ 1 [MOD 2] := by
      simpa [Nat.ModEq] using Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
    have humod : U ≡ b [MOD 2] := by
      simpa [U] using
        (Nat.ModEq.sum (s := range b) (f := fun j ↦ q ^ j) (g := fun _ ↦ 1)
          (fun j _ ↦ by simpa using hqmod.pow j))
    have huodd : Odd U := by
      change U % 2 = b % 2 at humod
      exact Nat.odd_iff.mpr (humod.trans (Nat.odd_iff.mp hbo))
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
    have hi0 : i = 0 := by
      by_contra hne
      apply huodd.not_two_dvd_nat
      rw [hi]
      exact dvd_pow_self 2 hne
    have hUone : U = 1 := by rw [hi, hi0, pow_zero]
    have hbU : b ≤ U := by
      calc
        b = ∑ _j ∈ range b, (1 : ℕ) := by simp
        _ ≤ U := sum_le_sum (fun j _ ↦ Nat.one_le_pow j q hq.pos)
    omega

private theorem pow_mod_period {m t : ℕ} (h : (2 : ZMod m) ^ t = 1) (e : ℕ) :
    (2 : ZMod m) ^ e = (2 : ZMod m) ^ (e % t) := by
  conv_lhs => rw [← Nat.div_add_mod e t, pow_add, pow_mul, h, one_pow, one_mul]

private theorem small_prime_cases {p : ℕ} (hp : p.Prime) (hle : p ≤ 5) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have htwo := hp.two_le
  have hne : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) hp
  omega

private theorem no_dvd_of_cast_ne_zero {p m : ℕ} (hm : (m : ZMod p) ≠ 0) :
    ¬ p ∣ m := fun h ↦ hm ((CharP.cast_eq_zero_iff (ZMod p) p m).mpr h)

/-- Factor the fifth shift and obtain one large prime from each factor. -/
private theorem fermat_shift_has_two_primes (s : ℕ) (hs : 4 ≤ s) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 5 < p ∧ 5 < q ∧ p ≠ q ∧
      p ∣ (2 : ℕ) ^ (2 ^ s) + 4 ∧ q ∣ (2 : ℕ) ^ (2 ^ s) + 4 := by
  let d := (2 : ℕ) ^ (s - 2)
  let w := (2 : ℕ) ^ (d - 1)
  let A := 2 * w * (w + 1) + 1
  let B := 2 * w * (w - 1) + 1
  have hd : 4 ≤ d := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ s - 2 by omega)
  have hw : 2 ≤ w := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ d - 1 by omega)
  have hd4 : (4 : ℕ) ∣ d := pow_dvd_pow 2 (show 2 ≤ s - 2 by omega)
  have h4 : (d - 1) % 4 = 3 := by
    have h := Nat.dvd_iff_mod_eq_zero.mp hd4
    omega
  have hd3 : ¬ (3 : ℕ) ∣ d := by
    intro h
    exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have h3 : (d - 1) % 3 = 0 ∨ (d - 1) % 3 = 1 := by
    have h : d % 3 ≠ 0 := fun hz ↦ hd3 (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  have hw3 : (w : ZMod 3) = 2 := by
    dsimp [w]
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_mod_period (m := 3) (t := 4) (by decide), h4]
    decide
  have hw5 : (w : ZMod 5) = 3 := by
    dsimp [w]
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_mod_period (m := 5) (t := 4) (by decide), h4]
    decide
  have hw7 : (w : ZMod 7) = 1 ∨ (w : ZMod 7) = 2 := by
    dsimp [w]
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_mod_period (m := 7) (t := 3) (by decide)]
    rcases h3 with h | h <;> rw [h] <;> decide
  have hA3 : (A : ZMod 3) = 1 := by
    simp only [A, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hw3]
    decide
  have hB3 : (B : ZMod 3) = 2 := by
    simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ w),
      Nat.cast_ofNat, Nat.cast_one, hw3]
    decide
  have hB5 : (B : ZMod 5) = 3 := by
    simp only [B, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ w),
      Nat.cast_ofNat, Nat.cast_one, hw5]
    decide
  have hA7 : (A : ZMod 7) = 5 ∨ (A : ZMod 7) = 6 := by
    rcases hw7 with h | h <;>
      simp only [A, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, h] <;> decide
  have hAodd : Odd A := ⟨w * (w + 1), by simp only [A]; ring⟩
  have hBodd : Odd B := ⟨w * (w - 1), by simp only [B]; ring⟩
  have hA3prime : ¬ (3 : ℕ) ∣ A := no_dvd_of_cast_ne_zero (by rw [hA3]; decide)
  have hB3prime : ¬ (3 : ℕ) ∣ B := no_dvd_of_cast_ne_zero (by rw [hB3]; decide)
  have hB5prime : ¬ (5 : ℕ) ∣ B := no_dvd_of_cast_ne_zero (by rw [hB5]; decide)
  have hAnosquare : ¬ IsSquare A := by
    rintro ⟨x, hx⟩
    have hcast : (A : ZMod 7) = (x : ZMod 7) ^ 2 := by
      rw [hx, Nat.cast_mul, pow_two]
    have hfinite : ∀ v : ZMod 7, v ^ 2 ≠ 5 ∧ v ^ 2 ≠ 6 := by decide +kernel
    rcases hA7 with h | h
    · exact (hfinite (x : ZMod 7)).1 (hcast.symm.trans h)
    · exact (hfinite (x : ZMod 7)).2 (hcast.symm.trans h)
  have hAgt : 1 < A := by
    have hpos : 0 < w := by omega
    have hprod : 0 < 2*w*(w+1) := by positivity
    dsimp [A]
    omega
  have hBgt : 1 < B := by
    have hpos : 0 < w := by omega
    have hsub : 0 < w - 1 := by omega
    have hprod : 0 < 2*w*(w-1) := by positivity
    dsimp [B]
    omega
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (show B ≠ 1 by omega)
  have hpgt : 5 < p := by
    by_contra! h
    rcases small_prime_cases hpp h with rfl | rfl | rfl
    · exact hBodd.not_two_dvd_nat hpd
    · exact hB3prime hpd
    · exact hB5prime hpd
  have hqext : ∃ q : ℕ, q.Prime ∧ 5 < q ∧ q ∣ A := by
    by_contra h
    have hpower := Nat.eq_prime_pow_of_unique_prime_dvd (p := 5) (show A ≠ 0 by omega)
      (fun {q} hq hqd ↦ by
        have hle : q ≤ 5 := by
          by_contra! hgt
          exact h ⟨q, hq, hgt, hqd⟩
        rcases small_prime_cases hq hle with rfl | rfl | rfl
        · exact (hAodd.not_two_dvd_nat hqd).elim
        · exact (hA3prime hqd).elim
        · rfl)
    let e := A.primeFactorsList.length
    change A = (5 : ℕ) ^ e at hpower
    have he : Even e := by
      rcases Nat.even_or_odd e with hE | hO
      · exact hE
      apply False.elim
      have h5 := hA3
      rw [hpower, Nat.cast_pow, Nat.cast_ofNat, show (5 : ZMod 3) = -1 by decide,
        hO.neg_pow, one_pow] at h5
      exact (by decide : (-1 : ZMod 3) ≠ 1) h5
    obtain ⟨j, hj⟩ := he
    apply hAnosquare
    exact ⟨(5 : ℕ) ^ j, by rw [hpower, hj, pow_add]⟩
  obtain ⟨q, hqp, hqgt, hqd⟩ := hqext
  have hdiff : A - B = 4 * w := by
    have hwpos : 0 < w := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hwpos.ne'
    have hAB : A = B + 4*w := by
      dsimp [A, B]
      rw [hj, Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    omega
  have hpq : p ≠ q := by
    rintro rfl
    have hdiv := Nat.dvd_sub hqd hpd
    rw [hdiff] at hdiv
    have hpow : 4 * w = (2 : ℕ) ^ ((d - 1) + 2) := by
      dsimp [w]
      rw [pow_add]
      ring
    rw [hpow] at hdiv
    have htwo := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
      (hpp.dvd_of_dvd_pow hdiv)
    omega
  have hsize : 4 * d = (2 : ℕ) ^ s := by
    dsimp [d]
    calc
      _ = (2 : ℕ) ^ (2 + (s - 2)) := by simp only [pow_add, show (2 : ℕ) ^ 2 = 4 by decide]
      _ = _ := by congr 1; omega
  have htwice : 2 * w = (2 : ℕ) ^ d := by
    dsimp [w]
    rw [← _root_.pow_succ']
    congr 1
    omega
  have hformula : 4 * (A * B) = (2 : ℕ) ^ (2 ^ s) + 4 := by
    have hAlg : 4 * (A * B) = (2 * w) ^ 4 + 4 := by
      have hwpos : 0 < w := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hwpos.ne'
      dsimp [A, B]
      rw [hj, Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    rw [hAlg, htwice, ← pow_mul, show d * 4 = 2 ^ s by omega]
  refine ⟨p, q, hpp, hqp, hpgt, hqgt, hpq, ?_, ?_⟩
  · rw [← hformula]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpd A) 4
  · rw [← hformula]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hqd B) 4

private theorem bounded_odd (n : Fin 256) :
    Odd n.val → (∀ k : Fin 5, 1 ≤ k.val → k.val ^ 2 < n.val →
      ((n.val + k.val).primeFactors.filter (fun p ↦ k.val < p)).card ≤ 1) →
    n.val = 1 ∨ n.val = 3 ∨ n.val = 7 ∨ n.val = 15 := by
  revert n
  decide +kernel

theorem odd_values (n : ℕ) (ho : Odd n)
    (ht : ∀ k : ℕ, 1 ≤ k → k ^ 2 < n →
      ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1) :
    n ∈ ({1, 3, 7, 15} : Set ℕ) := by
  by_cases hsmall : n < 256
  · have hfin := bounded_odd ⟨n, hsmall⟩ ho (fun k ↦ ht k.val)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfin
  have hc1 := ht 1 (by decide) (by omega)
  have h2d : 2 ∣ n + 1 := by
    obtain ⟨r, hr⟩ := ho.exists_bit1
    exact ⟨r + 1, by omega⟩
  have hp2 : 2 ∈ (n + 1).primeFactors.filter (fun p ↦ 1 < p) :=
    mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2d, by omega⟩, by decide⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n + 1 = (2 : ℕ) ^ a :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hqd ↦
      (card_le_one.mp hc1) q
        (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩, hq.one_lt⟩) 2 hp2)⟩
  have haBig : 3 < a := by
    by_contra! h
    have hl : (2 : ℕ) ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) h
    norm_num at hl
    omega
  have hn2 : n + 2 = (2 : ℕ) ^ a + 1 := by omega
  have hodd2 : Odd (n + 2) := by
    obtain ⟨r, hr⟩ := ho.exists_bit1
    exact ⟨r + 1, by omega⟩
  have hfilter : ((n + 2).primeFactors.filter (fun p ↦ 2 < p)) = (n + 2).primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    have ⟨hP, hD, _⟩ := Nat.mem_primeFactors.mp hp
    have hne : p ≠ 2 := by
      rintro rfl
      exact hodd2.not_two_dvd_nat hD
    have := hP.two_le
    omega
  have hc2 := ht 2 (by decide) (by omega)
  change ((n + 2).primeFactors.filter (fun p ↦ 2 < p)).card ≤ 1 at hc2
  rw [hfilter] at hc2
  have hpos2 : 0 < (n + 2).primeFactors.card := by
    apply card_pos.mpr
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show n + 2 ≠ 1 by omega)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩⟩
  have hPrimePower : IsPrimePow ((2 : ℕ) ^ a + 1) := by
    rw [← hn2, isPrimePow_iff_card_primeFactors_eq_one]
    omega
  obtain ⟨s, hs⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < (2 : ℕ))
    (by omega : a ≠ 0) (prime_power_plus_one haBig hPrimePower)
  have hs4 : 4 ≤ s := by
    by_contra! hf
    have h8 : (2 : ℕ) ^ s ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    have h256 : (2 : ℕ) ^ a ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by
      rw [hs]
      exact h8)
    norm_num at h256
    omega
  obtain ⟨p, q, hp, hq, hp5, hq5, hpq, hpD, hqD⟩ := fermat_shift_has_two_primes s hs4
  have hn5 : n + 5 = (2 : ℕ) ^ (2 ^ s) + 4 := by rw [hs] at ha; omega
  have hpM : p ∈ (n + 5).primeFactors.filter (fun r ↦ 5 < r) :=
    mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hn5.symm ▸ hpD, by omega⟩, hp5⟩
  have hqM : q ∈ (n + 5).primeFactors.filter (fun r ↦ 5 < r) :=
    mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hn5.symm ▸ hqD, by omega⟩, hq5⟩
  have hcard := ht 5 (by decide) (by omega)
  exact (hpq ((card_le_one.mp hcard) p hpM q hqM)).elim

end OMA.Erdos889Odd

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1.H2 :=
  OMA.Erdos889Odd.odd_values
