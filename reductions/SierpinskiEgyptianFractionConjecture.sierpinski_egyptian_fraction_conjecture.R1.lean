import FormalConjectures.Wikipedia.SierpinskiEgyptianFractionConjecture

open SierpinskiEgyptianFractionConjecture

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1

lemma decomposition_of_identity {n x y z : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 5 * x * y * z = n * (y * z + x * z + x * y)) :
    HasSierpinskiDecomposition n := by
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  have hq : (5 : ℚ) * x * y * z =
      (n : ℚ) * ((y : ℚ) * z + (x : ℚ) * z + (x : ℚ) * y) := by
    exact_mod_cast h
  have hn' : (n : ℚ) ≠ 0 := by positivity
  have hx' : (x : ℚ) ≠ 0 := by positivity
  have hy' : (y : ℚ) ≠ 0 := by positivity
  have hz' : (z : ℚ) ≠ 0 := by positivity
  field_simp [hn', hx', hy', hz']
  linear_combination hq

lemma class_five_three (k : ℕ) : HasSierpinskiDecomposition (5 * k + 3) := by
  let n := 5 * k + 3
  let a := k + 1
  apply decomposition_of_identity (x := a) (y := n * a) (z := n * a)
  all_goals try dsimp [n, a]
  all_goals first | positivity | ring

lemma class_five_four (k : ℕ) : HasSierpinskiDecomposition (5 * k + 4) := by
  let n := 5 * k + 4
  let a := k + 1
  apply decomposition_of_identity (x := a) (y := 2 * n * a) (z := 2 * n * a)
  all_goals try dsimp [n, a]
  all_goals first | positivity | ring

lemma class_ten_seven (k : ℕ) : HasSierpinskiDecomposition (10 * k + 7) := by
  let n := 10 * k + 7
  let a := 2 * (k + 1)
  apply decomposition_of_identity (x := a) (y := n * (k + 1)) (z := n * a)
  all_goals try dsimp [n, a]
  all_goals first | positivity | ring

lemma class_fifteen_eleven (k : ℕ) : HasSierpinskiDecomposition (15 * k + 11) := by
  let n := 15 * k + 11
  let a := 3 * (k + 1)
  apply decomposition_of_identity (x := a) (y := n * (k + 1)) (z := n * a)
  all_goals try dsimp [n, a]
  all_goals first | positivity | ring

lemma class_twenty_eleven (k : ℕ) : HasSierpinskiDecomposition (20 * k + 11) := by
  let n := 20 * k + 11
  let a := 4 * k + 3
  let b := k + 1
  apply decomposition_of_identity (x := a) (y := n * b) (z := n * a * b)
  all_goals try dsimp [n, a, b]
  all_goals first | positivity | ring

lemma prime_outside_one_mod_sixty (p : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (hnot : p % 60 ≠ 1) : HasSierpinskiDecomposition p := by
  have nonzero (d : ℕ) (hd : 2 ≤ d) (hd' : d ≤ 5) : p % d ≠ 0 := by
    intro hdvd
    have h := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hdvd)
    omega
  have classes : ∀ r : Fin 60, r.val % 2 = 0 ∨ r.val % 3 = 0 ∨ r.val % 5 = 0 ∨
      r.val = 1 ∨ r.val % 5 = 3 ∨ r.val % 5 = 4 ∨ r.val % 10 = 7 ∨
      r.val % 15 = 11 ∨ r.val % 20 = 11 := by decide
  have h := classes ⟨p % 60, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 60),
    Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 60), Nat.mod_mod_of_dvd _ (by decide : 5 ∣ 60),
    Nat.mod_mod_of_dvd _ (by decide : 10 ∣ 60), Nat.mod_mod_of_dvd _ (by decide : 15 ∣ 60),
    Nat.mod_mod_of_dvd _ (by decide : 20 ∣ 60)] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact (nonzero 2 (by decide) (by decide) h).elim
  · exact (nonzero 3 (by decide) (by decide) h).elim
  · exact (nonzero 5 (by decide) (by decide) h).elim
  · exact (hnot h).elim
  · convert class_five_three (p / 5) using 1
    omega
  · convert class_five_four (p / 5) using 1
    omega
  · convert class_ten_seven (p / 10) using 1
    omega
  · convert class_fifteen_eleven (p / 15) using 1
    omega
  · convert class_twenty_eleven (p / 20) using 1
    omega

lemma class_one_eighty_sixty_one (k : ℕ) :
    HasSierpinskiDecomposition (180 * k + 61) := by
  let n := 180 * k + 61
  let a := 36 * k + 14
  let b := 720 * k ^ 2 + 524 * k + 95
  apply decomposition_of_identity (x := a) (y := b) (z := b * n * a)
  all_goals try dsimp [n, a, b]
  all_goals first | positivity | ring

lemma class_one_eighty_one_twenty_one (k : ℕ) :
    HasSierpinskiDecomposition (180 * k + 121) := by
  let n := 180 * k + 121
  let a := 36 * k + 26
  let b := 4 * k + 3
  apply decomposition_of_identity (x := a) (y := n * b) (z := n * a * b)
  all_goals try dsimp [n, a, b]
  all_goals first | positivity | ring

lemma prime_outside_one_mod_one_eighty (p : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (hnot : p % 180 ≠ 1) : HasSierpinskiDecomposition p := by
  by_cases h : p % 60 = 1
  · have hr : p % 180 % 60 = 1 := by
      simpa only [Nat.mod_mod_of_dvd _ (by decide : 60 ∣ 180)] using h
    have hrange : p % 180 < 180 := Nat.mod_lt _ (by decide)
    have hrest : p % 180 = 61 ∨ p % 180 = 121 := by omega
    rcases hrest with h61 | h121
    · convert class_one_eighty_sixty_one (p / 180) using 1
      omega
    · convert class_one_eighty_one_twenty_one (p / 180) using 1
      omega
  · exact prime_outside_one_mod_sixty p hp hp5 h

-- Write 5/p = 1/a + t/(pa). For a divisor q of pa with q+1 = tb,
-- put c = pa/q. Then t/(pa) = 1/(cb) + 1/(pab).
lemma decomposition_of_remainder {p a t q : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hpa : 5 * a = p + t) (hd : q ∣ p * a) (ht : t ∣ q + 1) :
    HasSierpinskiDecomposition p := by
  obtain ⟨c, hc⟩ := hd
  obtain ⟨b, hb⟩ := ht
  have hprod := Nat.mul_pos hp ha
  have hcp : 0 < c := by
    by_contra! hz
    have : c = 0 := by omega
    rw [this, Nat.mul_zero] at hc
    omega
  have hbp : 0 < b := by
    by_contra! hz
    have : b = 0 := by omega
    simp [this] at hb
  have hsum : t * (c * b) = p * a + c := by
    calc
      t * (c * b) = (t * b) * c := by ring
      _ = p * a + c := by rw [← hb, add_mul, one_mul, ← hc]
  apply decomposition_of_identity (x := a) (y := c*b) (z := p*a*b)
    hp ha (by positivity) (by positivity)
  calc
    5 * a * (c*b) * (p*a*b) = p * (c*b) * (p*a*b) + (p*a*b) * (t*(c*b)) := by
      rw [hpa]
      ring
    _ = _ := by rw [hsum]; ring

-- For p = 180k+1 up to 18001, the finite search chooses a small offset, then
-- tests six candidate divisors. Every returned certificate is checked by divisibility.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
lemma initial_progression (k : ℕ) (hk : 0 < k) (hub : k ≤ 100) :
    HasSierpinskiDecomposition (180 * k + 1) := by
  let divisors (p a t j : ℕ) :=
    [t*j-1, (p*a)/j, a*j, p*j, a/j, p/j]
  have certified : ∀ i : Fin 100, ∃ s : Fin 5, ∃ v : Fin 34,
      let p := 180 * (i.val + 1) + 1
      let a := 36 * (i.val + 1) + 1 + s.val
      let t := 4 + 5 * s.val
      (divisors p a t (v.val + 1)).any (fun q => decide (q ∣ p*a ∧ t ∣ q+1)) = true := by
    decide +kernel
  obtain ⟨i, hi⟩ : ∃ i : Fin 100, k = i.val + 1 := ⟨⟨k-1, by omega⟩, by simp; omega⟩
  subst k
  obtain ⟨s, v, hv⟩ := certified i
  obtain ⟨q, _, hq⟩ := List.any_eq_true.mp hv
  obtain ⟨hd, ht⟩ := of_decide_eq_true hq
  apply decomposition_of_remainder (a := 36 * (i.val+1) + 1 + s.val) (q := q)
    (t := 4 + 5*s.val) (by positivity) (by positivity) _ hd ht
  omega

-- If q = 4j+3 divides a = (p+4)/5, then 4/q splits as
-- 1/(j+1) + 1/(q*(j+1)). Scale this identity by the cofactor and by p.
lemma decomposition_of_divisor {p a q : ℕ} (hp : 0 < p) (ha : 5 * a = p + 4)
    (hq : q % 4 = 3) (hd : q ∣ a) : HasSierpinskiDecomposition p := by
  apply decomposition_of_remainder (a := a) (t := 4) (q := q)
    hp (by omega) ha (hd.trans (dvd_mul_left a p))
  exact ⟨q / 4 + 1, by omega⟩

lemma scale_decomposition {p k : ℕ} (hk : 0 < k) (h : HasSierpinskiDecomposition p) :
    HasSierpinskiDecomposition (p * k) := by
  obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
  refine ⟨x * k, y * k, z * k, Nat.mul_pos hx hk, Nat.mul_pos hy hk,
    Nat.mul_pos hz hk, ?_⟩
  simp only [Nat.cast_mul, ← div_div, ← add_div, he]

-- The first remaining family has two linked primes, p and (p+4)/5.
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime → HasSierpinskiDecomposition p

-- In the second family the cofactor is composite and has no divisor congruent to 3 modulo 4.
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ¬ ((p + 4) / 5).Prime →
    (∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3) → HasSierpinskiDecomposition p

theorem main : H1 → H2 → type_of% @SierpinskiEgyptianFractionConjecture.sierpinski_egyptian_fraction_conjecture := by
  intro h1 h2 n hn
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hkpos : 0 < k := by
    by_contra! hz
    have : k = 0 := by omega
    rw [this, Nat.mul_zero] at hk
    omega
  rw [hk]
  apply scale_decomposition hkpos
  by_cases hsmall : p ≤ 5
  · have hlo := hp.two_le
    have hs := sierpinski_small_cases
    interval_cases p <;> tauto
  by_cases h180 : p % 180 = 1
  · by_cases hbound : p ≤ 18001
    · convert initial_progression (p / 180) (by omega) (by omega) using 1
      omega
    by_cases hprime : ((p + 4) / 5).Prime
    · exact h1 p hp h180 (by omega) hprime
    by_cases hsieve : ∀ q : ℕ, q ∣ (p + 4) / 5 → q % 4 ≠ 3
    · exact h2 p hp h180 (by omega) hprime hsieve
    push Not at hsieve
    obtain ⟨q, hd, hq⟩ := hsieve
    apply decomposition_of_divisor hp.pos (a := (p + 4) / 5) (q := q) _ hq hd
    omega
  · exact prime_outside_one_mod_one_eighty p hp (by omega) h180

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1
