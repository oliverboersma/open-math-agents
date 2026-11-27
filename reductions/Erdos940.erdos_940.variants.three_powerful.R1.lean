import FormalConjectures.ErdosProblems.«940»

/-!
# Sums of three powerful numbers: reduction to the residue class `7` modulo `8`

Heath-Brown's theorem says that every large integer is a sum of at most three `2`-full numbers.
Legendre's three-square theorem (`H1`) settles every `n` that is not of the form
`4 ^ a * (8 * b + 7)`, since squares are `2`-full. This file shows that Legendre's theorem also
settles every multiple of `4`, so that only the integers `n ≡ 7 (mod 8)` remain (`H2`).

Let `n = 4 * m`.

* If `2 * m` is not of the form `4 ^ a * (8 * b + 7)`, write `2 * m = P ^ 2 + Q ^ 2 + R ^ 2`.
  The sum is even, so after reordering `R` is even and `P ≡ Q (mod 2)`. With `P = Q + 2 * y`
  and `R = 2 * z` this gives `m = (Q + y) ^ 2 + y ^ 2 + 2 * z ^ 2`, hence
  `n = (2 * (Q + y)) ^ 2 + (2 * y) ^ 2 + 8 * z ^ 2`, and `8 * z ^ 2` is `2`-full.
* If `2 * m = 4 ^ a * (8 * b + 7)`, then `n = 2 * 4 ^ a * (8 * b + 7)` has odd `2`-adic
  valuation, so `n` itself is not of the form `4 ^ c * (8 * d + 7)` and is a sum of three squares.

If `4 ∤ n` and `n` is not `7` modulo `8`, then `n` is not of the form `4 ^ a * (8 * b + 7)`.
-/

namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1

/-- Legendre's three-square theorem (the direction that produces a representation). -/
def H1 : Prop :=
  ∀ n : ℕ, (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) → ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2

/-- Heath-Brown's theorem restricted to the residue class `7` modulo `8`. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, n % 8 = 7 →
    ∃ x y z : ℕ, Nat.Full 2 x ∧ Nat.Full 2 y ∧ Nat.Full 2 z ∧ n = x + y + z

lemma sq_full (x : ℕ) : Nat.Full 2 (x ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2

lemma eight_sq_full (z : ℕ) : Nat.Full 2 (8 * z ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  rcases h.1.dvd_mul.mp h.2.1 with hd | hd
  · have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8] at hd
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).1 (h.1.dvd_of_dvd_pow hd)
    rw [hp2]
    exact dvd_mul_of_dvd_left (by norm_num) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow hd) 2) _

lemma of_triple {n x y z : ℕ} (hx : Nat.Full 2 x) (hy : Nat.Full 2 y) (hz : Nat.Full 2 z)
    (h : n = x + y + z) :
    ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ s ∈ S, Nat.Full 2 s) ∧ n = S.sum := by
  refine ⟨x ::ₘ y ::ₘ z ::ₘ 0, ?_, ?_, ?_⟩
  · simp
  · intro s hs
    rcases Multiset.mem_cons.1 hs with h1 | hs
    · rw [h1]
      exact hx
    rcases Multiset.mem_cons.1 hs with h1 | hs
    · rw [h1]
      exact hy
    rcases Multiset.mem_cons.1 hs with h1 | hs
    · rw [h1]
      exact hz
    exact absurd hs (Multiset.notMem_zero s)
  · rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_zero, h]
    omega

/-- A number with odd `2`-adic valuation is not of the form `4 ^ c * v` with `v` odd. -/
lemma val_parity : ∀ (a c u v : ℕ), u % 2 = 1 → v % 2 = 1 → 2 * (4 ^ a * u) ≠ 4 ^ c * v := by
  intro a
  induction a with
  | zero =>
    intro c u v hu hv h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h
      omega
    · simp only [pow_zero, one_mul] at h
      have h' : 2 * u = 4 * (4 ^ c * v) := by
        rw [h, pow_succ]
        ring
      omega
  | succ a ih =>
    intro c u v hu hv h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h
      omega
    · apply ih c u v hu hv
      have h' : 4 * (2 * (4 ^ a * u)) = 4 * (4 ^ c * v) := by
        calc 4 * (2 * (4 ^ a * u)) = 2 * (4 ^ (a + 1) * u) := by
              rw [pow_succ]
              ring
          _ = 4 ^ (c + 1) * v := h
          _ = 4 * (4 ^ c * v) := by
              rw [pow_succ]
              ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

lemma sq_mod_two (t : ℕ) : t ^ 2 % 2 = t % 2 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rw [hk]
    have h : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  · rw [hk]
    have h : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

/-- From a three-square representation of `2 * m` with `P ≡ Q (mod 2)` and `R` even. -/
lemma rep_of_parity (m P Q R : ℕ) (h : 2 * m = P ^ 2 + Q ^ 2 + R ^ 2) (hle : Q ≤ P)
    (hPQ : P % 2 = Q % 2) (hR : R % 2 = 0) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y, P = Q + 2 * y := ⟨(P - Q) / 2, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, R = 2 * z := ⟨R / 2, by omega⟩
  refine ⟨Q + y, y, z, ?_⟩
  have h2 : 2 * m = 2 * ((Q + y) ^ 2 + y ^ 2 + 2 * z ^ 2) := by
    rw [h, hy, hz]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

lemma rep_of_parity' (m P Q R : ℕ) (h : 2 * m = P ^ 2 + Q ^ 2 + R ^ 2)
    (hPQ : P % 2 = Q % 2) (hR : R % 2 = 0) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  rcases le_total Q P with hle | hle
  · exact rep_of_parity m P Q R h hle hPQ hR
  · refine rep_of_parity m Q P R ?_ hle hPQ.symm hR
    rw [h]
    ring

/-- Legendre's theorem gives representations by `x ^ 2 + y ^ 2 + 2 * z ^ 2`. -/
lemma rep_one_one_two (h1 : H1) (m : ℕ) (hm : ∀ a b : ℕ, 2 * m ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  obtain ⟨A, B, C, hABC⟩ := h1 (2 * m) hm
  have hA := sq_mod_two A
  have hB := sq_mod_two B
  have hC := sq_mod_two C
  rcases Nat.mod_two_eq_zero_or_one C with hc | hc
  · exact rep_of_parity' m A B C hABC (by omega) hc
  · rcases Nat.mod_two_eq_zero_or_one B with hb | hb
    · refine rep_of_parity' m A C B ?_ (by omega) hb
      rw [hABC]
      ring
    · refine rep_of_parity' m B C A ?_ (by omega) (by omega)
      rw [hABC]
      ring

theorem main : H1 → H2 → type_of% @Erdos940.erdos_940.variants.three_powerful := by
  intro h1 h2
  have h2' : ∀ᶠ n : ℕ in Filter.atTop, n % 8 = 7 →
      ∃ x y z : ℕ, Nat.Full 2 x ∧ Nat.Full 2 y ∧ Nat.Full 2 z ∧ n = x + y + z := h2
  refine h2'.mono fun n hn => ?_
  by_cases h7 : n % 8 = 7
  · obtain ⟨x, y, z, hx, hy, hz, hsum⟩ := hn h7
    exact of_triple hx hy hz hsum
  · by_cases h4 : n % 4 = 0
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
      by_cases hB : ∀ a b : ℕ, 2 * m ≠ 4 ^ a * (8 * b + 7)
      · obtain ⟨x, y, z, hxyz⟩ := rep_one_one_two h1 m hB
        refine of_triple (sq_full (2 * x)) (sq_full (2 * y)) (eight_sq_full z) ?_
        rw [hm, hxyz]
        ring
      · obtain ⟨a, ha⟩ := not_forall.1 hB
        obtain ⟨b, hb⟩ := not_forall.1 ha
        have hab : 2 * m = 4 ^ a * (8 * b + 7) := not_not.1 hb
        have hno : ∀ c d : ℕ, n ≠ 4 ^ c * (8 * d + 7) := by
          intro c d hcd
          refine val_parity a c (8 * b + 7) (8 * d + 7) (by omega) (by omega) ?_
          rw [← hab, ← hcd, hm]
          ring
        obtain ⟨x, y, z, hxyz⟩ := h1 n hno
        exact of_triple (sq_full x) (sq_full y) (sq_full z) hxyz
    · have hno : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7) := by
        intro a b h
        rcases a with _ | a
        · simp only [pow_zero, one_mul] at h
          omega
        · have h' : n = 4 * (4 ^ a * (8 * b + 7)) := by
            rw [h, pow_succ]
            ring
          omega
      obtain ⟨x, y, z, hxyz⟩ := h1 n hno
      exact of_triple (sq_full x) (sq_full y) (sq_full z) hxyz

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1
