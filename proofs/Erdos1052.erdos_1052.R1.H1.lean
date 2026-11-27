import OMAReductions.R_Erdos1052_erdos_1052_R1

-- Step Erdos1052.erdos_1052.R1.H1: Graham (1989), unitary perfect numbers with squarefree odd part.
-- Credit: @adammcarter

/-!
# Graham's theorem on unitary perfect numbers with squarefree odd part

S. W. Graham, Unitary perfect numbers with squarefree odd part,
Fibonacci Quart. 27 (1989), no. 4, 317-322.

Main result (last declaration of this file, root namespace): `graham_H1`.
If n is unitary perfect and its odd part n / 2 ^ v_2(n) is squarefree, then n is 6, 60 or 87360.

Write n = 2 ^ m * s with s odd and squarefree, and let P be the set of primes of s.  Then
  (E)   (2 ^ m + 1) * prod over P of (p + 1) = 2 ^ (m + 1) * prod over P of p.
Every odd prime on the left is in P, and no odd prime divides two factors on the left (`facts`).
For m at most 9 this pins everything down by hand (`core`).  For m at least 10 (`big`) we follow
Graham, with two simplifications that avoid his chain bookkeeping and infinite products:

* each p in P keeps only its least odd prime child (the least odd prime factor of p + 1).  The
  kept edges form disjoint increasing paths that start at the Mersenne primes of P;
* with B x = (x + 1) / (x - 1) one has (1 + 1 / c) * B p ≤ B c whenever p + 1 ≥ 2 * c, so a path
  starting at a Mersenne prime q contributes at most B q (`path_bound`), and the Mersenne primes
  from 8191 on contribute at most 2048 / 2047 in total (`tail_bound`).

`master` packages this: any weight function between 1 + 1 / p and B p that is consistent along kept
edges bounds prod over P of (1 + 1 / p), and the bound must stay below 2 * 1024 / 1025.  The case
split of Graham's Section 4 (m odd; 4 dividing m; m = 2 mod 4 with subcases on 13 and 103) then only
has to supply weights at 3, 5, 7, 13, 103 and 127.
-/

-- Section 0. Product formula for the unitary divisor sum (Subbarao-Warren 1966).

namespace Graham1052

-- Membership in the set of all unitary divisors of n (n itself included).
theorem mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

theorem self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

theorem proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n = (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

theorem sum_udiv_eq_sum_proper_add {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  rw [proper_eq_erase, Finset.sum_erase_add _ _ (self_mem_udiv hn)]

-- A unitary perfect number is positive and its unitary divisor sum equals 2 * n.
theorem sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [sum_udiv_eq_sum_proper_add hpos.ne', hs]
  ring

theorem factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

theorem ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

theorem factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

theorem primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

theorem ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

theorem eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

-- Product formula: the unitary divisor sum of n is the product of (1 + p^a) over p^a || n.
theorem sum_udiv_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

theorem prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
  (eq_ppart_of_mem_udiv (self_mem_udiv hn)).symm

-- Balance equation: for a unitary perfect n the product of (1 + p^a) over p^a || n is 2 * n.
theorem prod_eq_two_mul {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  rw [← sum_udiv_eq_prod hpos.ne']
  exact hs


end Graham1052

-- Section 1. Telescoping bounds: paths of primes and the Mersenne tail.

namespace Graham1052

theorem B_step {c p : ℕ} (hc : 2 ≤ c) (hp : 2 * c ≤ p + 1) :
    (1 + 1 / (c : ℚ)) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ ((c : ℚ) + 1) / ((c : ℚ) - 1) := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have hp' : 2 * (c : ℚ) ≤ p + 1 := by exact_mod_cast hp
  have h1 : (0 : ℚ) < c - 1 := by linarith
  have h2 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have h3 : (0 : ℚ) < c := by linarith
  have e : (1 + 1 / (c : ℚ)) = ((c : ℚ) + 1) / c := by field_simp
  rw [e, div_mul_div_comm, div_le_div_iff₀ (mul_pos h3 h2) h1]
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1) (by linarith : (0 : ℚ) ≤ (p : ℚ) + 1 - 2 * c)]

theorem B_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ((b : ℚ) + 1) / ((b : ℚ) - 1) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 1) := by
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem one_add_le_B {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have e : (1 + 1 / (p : ℚ)) = ((p : ℚ) + 1) / p := by field_simp
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem path_bound (g : ℕ → ℕ) (β : ℕ → ℚ) : ∀ (n : ℕ) (P : Finset ℕ), P.card = n →
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, g p ∈ P → g p < p) →
    (∀ p ∈ P, ∀ p' ∈ P, g p ∈ P → g p = g p' → p = p') →
    (∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p) →
    (∀ p ∈ P, g p ∈ P → (1 + 1 / ((g p : ℕ) : ℚ)) * β p ≤ β (g p)) →
    ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤ ∏ q ∈ P.filter (fun q => g q ∉ P), β q := by
  intro n
  induction n with
  | zero =>
    intro P hP _ _ _ _ _
    rw [Finset.card_eq_zero.mp hP]
    simp
  | succ n ih =>
    intro P hcard hpos hlt hinj hβ hstep
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqP, hqmin⟩ : ∃ q ∈ P, ∀ p ∈ P, q ≤ p :=
      ⟨P.min' hne, Finset.min'_mem P hne, fun p hp => Finset.min'_le P p hp⟩
    have hgq : g q ∉ P := fun h => absurd (hqmin _ h) (not_le.mpr (hlt q hqP h))
    have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
      have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
      linarith [hβ p hp]
    have hmem : ∀ x, x ∈ P.erase q → x ∈ P := fun x hx => Finset.mem_of_mem_erase hx
    have ih' := ih (P.erase q) (by rw [Finset.card_erase_of_mem hqP, hcard]; rfl)
      (fun p hp => hpos p (hmem p hp))
      (fun p hp hg => hlt p (hmem p hp) (hmem _ hg))
      (fun p hp p' hp' hg he => hinj p (hmem p hp) p' (hmem p' hp') (hmem _ hg) he)
      (fun p hp => hβ p (hmem p hp))
      (fun p hp hg => hstep p (hmem p hp) (hmem _ hg))
    have hqL : q ∈ P.filter (fun q => g q ∉ P) := Finset.mem_filter.mpr ⟨hqP, hgq⟩
    have hrest0 : 0 ≤ ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x :=
      Finset.prod_nonneg fun x hx =>
        (hβpos x (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1).le
    have hq0 : (0 : ℚ) ≤ 1 + 1 / (q : ℚ) := by positivity
    have key : (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x ≤
        β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := by
      by_cases hpar : ∃ p ∈ P, g p = q
      · obtain ⟨p, hpP, hpq⟩ := hpar
        have hpne : p ≠ q := by
          intro h
          have := hlt p hpP (hpq ▸ hqP)
          omega
        have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            insert p ((P.filter (fun q => g q ∉ P)).erase q) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            by_cases hgx : g x = q
            · left
              exact (hinj p hpP x hxP (hpq ▸ hqP) (hpq.trans hgx.symm)).symm
            · right
              exact ⟨hxq, hxP, fun h => hx hgx h⟩
          · rintro (rfl | ⟨hxq, hxP, hx⟩)
            · exact ⟨⟨hpne, hpP⟩, fun h => absurd hpq h⟩
            · exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        have hnotin : p ∉ (P.filter (fun q => g q ∉ P)).erase q := by
          intro h
          exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2 (hpq ▸ hqP)
        rw [hset, Finset.prod_insert hnotin, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hrest0
        have := hstep p hpP (hpq ▸ hqP)
        rwa [hpq] at this
      · have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            (P.filter (fun q => g q ∉ P)).erase q := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            exact ⟨hxq, hxP, fun h => hx (fun hgx => hpar ⟨x, hxP, hgx⟩) h⟩
          · rintro ⟨hxq, hxP, hx⟩
            exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        rw [hset]
        exact mul_le_mul_of_nonneg_right (hβ q hqP) hrest0
    calc ∏ p ∈ P, (1 + 1 / (p : ℚ))
        = (1 + 1 / (q : ℚ)) * ∏ p ∈ P.erase q, (1 + 1 / (p : ℚ)) :=
          (Finset.mul_prod_erase P (fun p : ℕ => (1 + 1 / (p : ℚ))) hqP).symm
      _ ≤ (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x :=
          mul_le_mul_of_nonneg_left ih' hq0
      _ ≤ β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := key
      _ = ∏ q ∈ P.filter (fun q => g q ∉ P), β q := Finset.mul_prod_erase _ β hqL

theorem tail_bound : ∀ (n : ℕ) (Q : Finset ℕ) (a : ℕ), Q.card = n → 4 ≤ a → (∀ q ∈ Q, a ≤ q) →
    (∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 2 * q + 1 ≤ q') →
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
  intro n
  induction n with
  | zero =>
    intro Q a hQ ha _ _
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    rw [Finset.card_eq_zero.mp hQ, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro Q a hcard ha hge hdbl
    have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqQ, hqmin⟩ : ∃ q ∈ Q, ∀ p ∈ Q, q ≤ p :=
      ⟨Q.min' hne, Finset.min'_mem Q hne, fun p hp => Finset.min'_le Q p hp⟩
    have haq : a ≤ q := hge q hqQ
    have ih' := ih (Q.erase q) (2 * q + 1) (by rw [Finset.card_erase_of_mem hqQ, hcard]; rfl)
      (by omega)
      (fun x hx => hdbl q hqQ x (Finset.mem_of_mem_erase hx)
        (lt_of_le_of_ne (hqmin x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm))
      (fun x hx y hy => hdbl x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    have haq' : (a : ℚ) ≤ q := by exact_mod_cast haq
    have hB0 : (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
    rw [← Finset.mul_prod_erase Q _ hqQ]
    calc ((q : ℚ) + 1) / ((q : ℚ) - 1) * ∏ x ∈ Q.erase q, (((x : ℚ) + 1) / ((x : ℚ) - 1))
        ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) * ((((2 * q + 1 : ℕ) : ℚ) + 1) / (((2 * q + 1 : ℕ) : ℚ) - 3)) :=
          mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ ((q : ℚ) + 1) / ((q : ℚ) - 3) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
          nlinarith
      _ ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith

theorem exists_child : ∃ g : ℕ → ℕ, ∀ p : ℕ, g p ∣ p + 1 ∧ (g p = 1 → ∃ k, p + 1 = 2 ^ k) ∧
    (g p ≠ 1 → (g p).Prime ∧ g p ≠ 2) ∧ (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → g p ≤ c) := by
  refine ⟨fun p => Nat.minFac ((p + 1) / 2 ^ (p + 1).factorization 2), fun p => ?_⟩
  beta_reduce
  have hN : p + 1 ≠ 0 := by omega
  have hmul := Nat.ordProj_mul_ordCompl_eq_self (p + 1) 2
  have hodvd : (p + 1) / 2 ^ (p + 1).factorization 2 ∣ p + 1 := Dvd.intro_left _ hmul
  refine ⟨(Nat.minFac_dvd _).trans hodvd, ?_, ?_, ?_⟩
  · intro h
    have h1 : (p + 1) / 2 ^ (p + 1).factorization 2 = 1 := Nat.minFac_eq_one_iff.mp h
    exact ⟨(p + 1).factorization 2, by rw [h1, mul_one] at hmul; exact hmul.symm⟩
  · intro h
    have ho1 : (p + 1) / 2 ^ (p + 1).factorization 2 ≠ 1 := fun h' => h (Nat.minFac_eq_one_iff.mpr h')
    refine ⟨Nat.minFac_prime ho1, fun h2 => ?_⟩
    have hd := Nat.minFac_dvd ((p + 1) / 2 ^ (p + 1).factorization 2)
    rw [h2] at hd
    exact Nat.not_dvd_ordCompl Nat.prime_two hN hd
  · intro c hc hc2 hcd
    apply Nat.minFac_le_of_dvd hc.two_le
    have h1 : c ∣ 2 ^ (p + 1).factorization 2 * ((p + 1) / 2 ^ (p + 1).factorization 2) := by
      rw [hmul]; exact hcd
    exact (Nat.Coprime.dvd_mul_left
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hc Nat.prime_two).mpr hc2))).mp h1

theorem mersenne_small {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k) (hlt : q < 8191) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 := by
  have hk13 : k < 13 := by
    by_contra h
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at hk <;> subst hk <;> first | omega | (norm_num at hq)

end Graham1052

-- Section 2. Structure of the balance equation (E).

namespace Graham1052

theorem two_mul_le {c p : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : c ∣ p + 1) : 2 * c ≤ p + 1 := by
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcop : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
  exact Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hd)

theorem S_mem {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hd : c ∣ (2 ^ m + 1) * ∏ p ∈ P, (p + 1)) : c ∈ P := by
  rw [E] at hd
  rcases (Nat.Prime.dvd_mul hc).mp hd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hc (hP p hp).1).mp hcp]

theorem S_sq {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) : ¬ c * c ∣ (2 ^ m + 1) * ∏ p ∈ P, (p + 1) := by
  intro hd
  have hcP : c ∈ P := S_mem hP E hc hc2 ((dvd_mul_right c c).trans hd)
  rw [E, ← Finset.mul_prod_erase P (fun p => p) hcP, mul_left_comm] at hd
  have h1 : c ∣ 2 ^ (m + 1) * ∏ p ∈ P.erase c, p := Nat.dvd_of_mul_dvd_mul_left hc.pos hd
  rcases (Nat.Prime.dvd_mul hc).mp h1 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hc (hP p (Finset.mem_of_mem_erase hp)).1).mp hcp
    exact (Finset.ne_of_mem_erase hp) this.symm

theorem facts {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p) :
    (∀ c : ℕ, c.Prime → c ≠ 2 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ 2 ^ m + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p') ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ 2 ^ m + 1 → ∀ p ∈ P, ¬ c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → ¬ c * c ∣ 2 ^ m + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → ∀ p ∈ P, ¬ c * c ∣ p + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hc2 p hp hd
    exact S_mem hP E hc hc2 ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hd
    exact S_mem hP E hc hc2 (hd.mul_right _)
  · intro c hc hc2 p hp p' hp' hd hd'
    by_contra hne
    apply S_sq hP E hc hc2
    have hsub : ({p, p'} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton.mp hx]; exact hp'
    have h1 : (p + 1) * (p' + 1) ∣ ∏ x ∈ P, (x + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hsub
      rwa [Finset.prod_pair hne] at this
    exact ((mul_dvd_mul hd hd').trans h1).mul_left _
  · intro c hc hc2 hd p hp hd'
    apply S_sq hP E hc hc2
    exact mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))
  · intro c hc hc2 hd
    exact S_sq hP E hc hc2 (hd.mul_right _)
  · intro c hc hc2 p hp hd
    exact S_sq hP E hc hc2 ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)

theorem S_sat {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    {A : Finset ℕ} (hA : A ⊆ P)
    (hEA : (2 ^ m + 1) * ∏ p ∈ A, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ A, p) : P = A := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  rw [← Finset.prod_sdiff hA, ← Finset.prod_sdiff hA (f := fun p => p)] at E
  have hK : 0 < 2 ^ (m + 1) * ∏ p ∈ A, p :=
    Nat.mul_pos (by positivity) (Finset.prod_pos fun p hp => hpos p (hA hp))
  have hD : ∏ p ∈ P \ A, (p + 1) = ∏ p ∈ P \ A, p := by
    have e : (∏ p ∈ P \ A, (p + 1)) * (2 ^ (m + 1) * ∏ p ∈ A, p) =
        (∏ p ∈ P \ A, p) * (2 ^ (m + 1) * ∏ p ∈ A, p) := by
      calc (∏ p ∈ P \ A, (p + 1)) * (2 ^ (m + 1) * ∏ p ∈ A, p)
          = (2 ^ m + 1) * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) := by rw [← hEA]; ring
        _ = 2 ^ (m + 1) * ((∏ p ∈ P \ A, p) * ∏ p ∈ A, p) := E
        _ = (∏ p ∈ P \ A, p) * (2 ^ (m + 1) * ∏ p ∈ A, p) := by ring
    exact Nat.eq_of_mul_eq_mul_right hK e
  have hempty : P \ A = ∅ := by
    by_contra hne
    have hlt : ∏ p ∈ P \ A, p < ∏ p ∈ P \ A, (p + 1) :=
      Finset.prod_lt_prod_of_nonempty (fun p hp => hpos p (Finset.mem_sdiff.mp hp).1)
        (fun p _ => Nat.lt_succ_self p) (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hempty) hA

theorem S_abund {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    {A : Finset ℕ} (hA : A ⊆ P) : ∏ p ∈ A, (p + 1) < 2 * ∏ p ∈ A, p := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  rw [← Finset.prod_sdiff hA, ← Finset.prod_sdiff hA (f := fun p => p)] at E
  have hle : ∏ p ∈ P \ A, p ≤ ∏ p ∈ P \ A, (p + 1) :=
    Finset.prod_le_prod' fun p _ => Nat.le_succ p
  have hYD : 0 < ∏ p ∈ P \ A, p :=
    Finset.prod_pos fun p hp => hpos p (Finset.mem_sdiff.mp hp).1
  by_contra hcon
  rw [not_lt] at hcon
  have hXA : 0 < ∏ p ∈ A, (p + 1) := Finset.prod_pos fun p _ => Nat.succ_pos p
  have h1 : 2 ^ (m + 1) * ((∏ p ∈ P \ A, p) * ∏ p ∈ A, p) ≤
      2 ^ m * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) := by
    rw [pow_succ]
    calc 2 ^ m * 2 * ((∏ p ∈ P \ A, p) * ∏ p ∈ A, p)
        = 2 ^ m * ((∏ p ∈ P \ A, p) * (2 * ∏ p ∈ A, p)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hle hcon)
  have h2 : 2 ^ m * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) <
      (2 ^ m + 1) * ((∏ p ∈ P \ A, (p + 1)) * ∏ p ∈ A, (p + 1)) :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos (lt_of_lt_of_le hYD hle) hXA)
  omega

end Graham1052

-- Section 3. The master inequality.

namespace Graham1052

theorem master {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p) (hm : 10 ≤ m)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 → (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hfin : 1025 / 1024 * (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) < 2) : False := by
  obtain ⟨S1, -, S2, -, -, -⟩ := facts hP E
  obtain ⟨g, hg⟩ := exists_child
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- leaves are Mersenne
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P), ∃ k, q + 1 = 2 ^ k := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  -- split leaves
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => q < 8191) β
  have hsmall : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter (fun q => q < 8191), β q ≤
      β 3 * β 7 * β 31 * β 127 := by
    have hsub : (P.filter (fun q => g q ∉ P)).filter (fun q => q < 8191) ⊆
        ({3, 7, 31, 127} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hleaf q hqL
      have := mersenne_small (hP q (hLP q hqL)).1 hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub (fun i hi => (hβpos i (hLP i (Finset.mem_filter.mp hi).1)).le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2)
    have e : ∏ q ∈ ({3, 7, 31, 127} : Finset ℕ), β q = β 3 * β 7 * β 31 * β 127 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      ring
    rwa [e] at h
  have htail : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter (fun q => ¬ q < 8191), β q ≤
      2048 / 2047 := by
    have hmemT : ∀ q ∈ (P.filter (fun q => g q ∉ P)).filter (fun q => ¬ q < 8191),
        q ∈ P.filter (fun q => g q ∉ P) ∧ 8191 ≤ q := fun q hq => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact ⟨h1, by omega⟩
    have hle : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter (fun q => ¬ q < 8191), β q ≤
        ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter (fun q => ¬ q < 8191),
          (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hβpos q (hLP q (hmemT q hq).1)).le)
        (fun q hq => (hB q (hLP q (hmemT q hq).1)).2)
    have htb := tail_bound _ _ 8191 rfl (by norm_num) (fun q hq => (hmemT q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hleaf q (hmemT q hq).1
        obtain ⟨k', hk'⟩ := hleaf q' (hmemT q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    rw [← hsplit]
    refine mul_le_mul hsmall htail ?_ ?_
    · exact Finset.prod_nonneg fun q hq =>
        (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
    · have := h1
      obtain ⟨a, b, c, d⟩ := this
      have h3 : (0 : ℚ) ≤ β 3 := by linarith
      have h7 : (0 : ℚ) ≤ β 7 := by linarith
      have h31 : (0 : ℚ) ≤ β 31 := by linarith
      have h127 : (0 : ℚ) ≤ β 127 := by linarith
      positivity
  -- the equation over ℚ
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hT0 : (0 : ℚ) ≤ 1 + 1 / (2 : ℚ) ^ m := by positivity
  have hprod0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  have : (2 : ℚ) ≤ 1025 / 1024 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) := by
    rw [← hEq]
    exact mul_le_mul hT (hpath.trans hprodL) (Finset.prod_nonneg fun p _ => by positivity) (by norm_num)
  linarith

end Graham1052

-- Section 4. Lower bounds for the parent of a least odd prime child; modular facts.

namespace Graham1052

theorem child_cases {N c : ℕ} (hN0 : N ≠ 0) (hN : 2 ∣ N) (hc : c.Prime) (hc2 : c ≠ 2)
    (hcN : c ∣ N) (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ N → c ≤ c') :
    (∃ i, N = c * 2 ^ i) ∨ 2 * c * c ≤ N := by
  obtain ⟨k, rfl⟩ := hcN
  have hk0 : k ≠ 0 := by rintro rfl; simp at hN0
  have hmul := Nat.ordProj_mul_ordCompl_eq_self k 2
  by_cases ho1 : k / 2 ^ k.factorization 2 = 1
  · left
    refine ⟨k.factorization 2, ?_⟩
    rw [ho1, mul_one] at hmul
    rw [hmul]
  · right
    have hq := Nat.minFac_prime ho1
    have hqo : (k / 2 ^ k.factorization 2).minFac ∣ k / 2 ^ k.factorization 2 := Nat.minFac_dvd _
    have hodd : ¬ 2 ∣ k / 2 ^ k.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hk0
    have hq2 : (k / 2 ^ k.factorization 2).minFac ≠ 2 := fun h => by
      have h' := hqo
      rw [h] at h'
      exact hodd h'
    have hok : k / 2 ^ k.factorization 2 ∣ k := Dvd.intro_left _ hmul
    have hopos : 0 < k / 2 ^ k.factorization 2 :=
      Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hk0 hmul.symm
    have hcq : c ≤ (k / 2 ^ k.factorization 2).minFac :=
      hmin _ hq hq2 ((hqo.trans hok).mul_left c)
    have hco : c ≤ k / 2 ^ k.factorization 2 := hcq.trans (Nat.minFac_le hopos)
    have hcop2c : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
    have h2k : 2 ∣ k := (Nat.Coprime.dvd_mul_left hcop2c).mp hN
    have hcop : Nat.Coprime 2 (k / 2 ^ k.factorization 2) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h2o : 2 * (k / 2 ^ k.factorization 2) ≤ k :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2k hok)
    calc 2 * c * c = c * (2 * c) := by ring
      _ ≤ c * (2 * (k / 2 ^ k.factorization 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hco)
      _ ≤ c * k := Nat.mul_le_mul_left _ h2o

theorem R127 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 127 ≤ c') : 32257 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 8 := by
      by_contra hcon
      have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> (obtain rfl : p = _ := Nat.succ_injective hi) <;> norm_num at hp
  · omega

theorem R103 {p : ℕ} (hp : p.Prime) (hd : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 103 ≤ c') : 823 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 3 := by
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> (obtain rfl : p = _ := Nat.succ_injective hi) <;> norm_num at hp
  · omega

theorem R7 {p : ℕ} (hp : p.Prime) (h7 : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1)
    (h13 : ¬ 13 ∣ p + 1) (h49 : ¬ 7 * 7 ∣ p + 1) (hne : p ≠ 13) : 223 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have h14 : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := h14
  have hj16 : j < 16 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem R13 {p : ℕ} (hp : p.Prime) (h13 : 13 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1)
    (h7 : ¬ 7 ∣ p + 1) (h11 : ¬ 11 ∣ p + 1) (h17 : ¬ 17 ∣ p + 1) (h43 : ¬ 43 ∣ p + 1)
    (h169 : ¬ 13 * 13 ∣ p + 1) (hne : p ≠ 103) : 1663 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have h26 : 26 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := h26
  have hj64 : j < 64 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 26 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem exists_prime_mod3 : ∀ N : ℕ, N % 3 = 2 → ∃ p, p.Prime ∧ p ∣ N ∧ p % 3 = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hN1 : N ≠ 1 := by omega
    have hq := Nat.minFac_prime hN1
    have hqd := Nat.minFac_dvd N
    have h3 : N.minFac % 3 ≠ 0 := by
      intro h
      have : 3 ∣ N := (Nat.dvd_of_mod_eq_zero h).trans hqd
      omega
    by_cases h2 : N.minFac % 3 = 2
    · exact ⟨_, hq, hqd, h2⟩
    · have h1 : N.minFac % 3 = 1 := by omega
      obtain ⟨k, hk⟩ := hqd
      have hk2 : k % 3 = 2 := by
        have : (N.minFac * k) % 3 = 2 := by rw [← hk]; exact hN
        rw [Nat.mul_mod, h1] at this
        omega
      have hklt : k < N := by
        have := hq.two_le
        have hk0 : 0 < k := by omega
        calc k < N.minFac * k := by nlinarith
          _ = N := hk.symm
      obtain ⟨p, hp, hpd, hp2⟩ := ih k hklt hk2
      exact ⟨p, hp, hpd.trans (Dvd.intro_left _ hk.symm), hp2⟩

theorem not_dvd_fourth_11 (x : ℕ) : ¬ 11 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 11).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 11, y ^ 4 + 1 ≠ 0) _ h'

theorem not_dvd_fourth_23 (x : ℕ) : ¬ 23 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 23).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 23, y ^ 4 + 1 ≠ 0) _ h'

theorem not_dvd_fourth_5 (x : ℕ) : ¬ 5 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 5).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 5, y ^ 4 + 1 ≠ 0) _ h'

end Graham1052

-- Section 5. The cases with m at least 10.

namespace Graham1052

theorem step_ge {c t p : ℕ} {x y : ℚ} (ht : 2 ≤ t) (hpt : t ≤ p)
    (hx : x ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (hy : (1 + 1 / (c : ℚ)) * (((t : ℚ) + 1) / ((t : ℚ) - 1)) ≤ y) :
    (1 + 1 / (c : ℚ)) * x ≤ y :=
  (mul_le_mul_of_nonneg_left (hx.trans (B_anti ht hpt)) (by positivity)).trans hy

theorem case_odd {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hodd : m % 2 = 1) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  have h3d : 3 ∣ 2 ^ m + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow 2 1 (Nat.odd_iff.mpr hodd)
    simpa using h
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 := by rw [hβ]; norm_num
  have b7 : β 7 = 4 / 3 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 => by
    rw [hβ, if_neg e3]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    rw [bd p e3]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3; exact absurd hd (S3 3 (by norm_num) (by norm_num) h3d p hp)
    exact absurd (bd c e3) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case_zero_mod_four {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 0) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  obtain ⟨k, rfl⟩ : ∃ k, m = k * 4 := ⟨m / 4, by omega⟩
  have hmod : (2 ^ (k * 4) + 1) % 3 = 2 := by
    rw [mul_comm, pow_mul, Nat.add_mod, Nat.pow_mod]; norm_num
  obtain ⟨p0, hp0, hp0d, hp03⟩ := exists_prime_mod3 _ hmod
  have hx : 2 ^ (k * 4) + 1 = (2 ^ k) ^ 4 + 1 := by rw [pow_mul]
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hp0d
    omega
  have hp0P : p0 ∈ P := S5 p0 hp0 hp02 hp0d
  have h3d : 3 ∣ p0 + 1 := by omega
  have h3P : 3 ∈ P := S1 3 (by norm_num) (by norm_num) p0 hp0P h3d
  have hp029 : 29 ≤ p0 := by
    by_contra hlt
    have hlt' : p0 < 29 := by omega
    have h2le := hp0.two_le
    rw [hx] at hp0d
    interval_cases p0 <;> first
      | omega
      | (norm_num at hp0; done)
      | exact not_dvd_fourth_5 _ hp0d
      | exact not_dvd_fourth_11 _ hp0d
      | exact not_dvd_fourth_23 _ hp0d
      | exact S4b 3 (by norm_num) (by norm_num) 17 hp0P (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 * (1 + 1 / (p0 : ℚ)) else
      if p = p0 then 1 + 1 / (p0 : ℚ) else ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hp0q : (29 : ℚ) ≤ p0 := by exact_mod_cast hp029
  have hinv0 : 0 < 1 / (p0 : ℚ) := by positivity
  have hinv : 1 / (p0 : ℚ) ≤ 1 / 29 := one_div_le_one_div_of_le (by norm_num) hp0q
  have hp0ne3 : p0 ≠ 3 := by omega
  have b3 : β 3 = 4 / 3 * (1 + 1 / (p0 : ℚ)) := by rw [hβ, if_pos rfl]
  have bp0 : β p0 = 1 + 1 / (p0 : ℚ) := by rw [hβ, if_neg hp0ne3, if_pos rfl]
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ p0 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 e0 => by
    rw [hβ, if_neg e3, if_neg e0]
  have b7 : β 7 = 4 / 3 := by rw [bd 7 (by norm_num) (by omega)]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [bd 31 (by norm_num) (by omega)]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [bd 127 (by norm_num) (by omega)]; norm_num
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [b3]
      have e1 : (1 : ℚ) + 1 / ((3 : ℕ) : ℚ) = 4 / 3 := by norm_num
      have e2 : (((3 : ℕ) : ℚ) + 1) / (((3 : ℕ) : ℚ) - 1) = 2 := by norm_num
      rw [e1, e2]
      constructor <;> linarith
    by_cases e0 : p = p0
    · subst e0; rw [bp0]; exact ⟨le_refl _, one_add_le_B hp0.two_le⟩
    rw [bd p e3 e0]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = p0 := S2 3 (by norm_num) (by norm_num) p hp p0 hp0P hd h3d
      rw [b3, bp0]; norm_num
    by_cases e0 : c = p0
    · subst e0; exact absurd hd (S3 c hp0 hp02 hp0d p hp)
    exact absurd (bd c e3 e0) hne
  · rw [b3, b7, b31, b127]
    refine ⟨by linarith, by norm_num, by norm_num, by norm_num⟩
  · rw [b3, b7, b31, b127]
    linarith

theorem case3_pre {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p) (h4 : m % 4 = 2) :
    5 ∈ P ∧ 3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → p = 5) ∧ (∀ p ∈ P, ¬ 5 ∣ p + 1) := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  have h5d : 5 ∣ 2 ^ m + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    apply Nat.dvd_of_mod_eq_zero
    rw [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]; norm_num
  have h5 : 5 ∈ P := S5 5 (by norm_num) (by norm_num) h5d
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) 5 h5 (by norm_num)
  exact ⟨h5, h3, fun p hp hd => S2 3 (by norm_num) (by norm_num) p hp 5 h5 hd (by norm_num),
    fun p hp => S3 5 (by norm_num) (by norm_num) h5d p hp⟩

theorem case3_ii {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h13 : 13 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (224 / 222) else if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e127 => by rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      have hge : 223 ≤ p := R7 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) h; omega)
        (fun h => h13 (S1 13 (by norm_num) (by norm_num) p hp h))
        (S4b 7 (by norm_num) (by norm_num) p hp)
        (fun h => h13 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd hmin
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_iii {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∉ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP E hsub
    revert h
    decide
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  have h17 : 17 ∉ P := fun h => by
    have := T3 17 h (by norm_num)
    omega
  have h43 : 43 ∉ P := fun h => h11 (S1 11 (by norm_num) (by norm_num) 43 h (by norm_num))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (1664 / 1662)) else
      if p = 13 then 14 / 13 * (1664 / 1662) else if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (1664 / 1662)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (1664 / 1662) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e13 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      have hge : 1663 ≤ p := R13 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) h; omega)
        (fun h => by have := hmin 11 (by norm_num) (by norm_num) h; omega)
        (fun h => h17 (S1 17 (by norm_num) (by norm_num) p hp h))
        (fun h => h43 (S1 43 (by norm_num) (by norm_num) p hp h))
        (S4b 13 (by norm_num) (by norm_num) p hp)
        (fun h => h103 (h ▸ hp))
      rw [b13]
      exact step_ge (t := 1663) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd hmin
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e13 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem case3_iv {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h4 : m % 4 = 2) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∈ P) : False := by
  obtain ⟨h5, h3, T3, T5⟩ := case3_pre hP E h4
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else
      if p = 103 then 104 / 103 * (824 / 822) else if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 822)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 822) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5; exact absurd hd (T5 p hp)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      have hge : 823 ≤ p := R103 (hP p hp).1 hd hmin
      rw [b103]
      exact step_ge (t := 823) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127; exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

theorem big {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p) (hm : 10 ≤ m) : False := by
  have h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h with h | h | h | h
  · exact case_zero_mod_four hP E hm h
  · exact case_odd hP E hm (by omega)
  · by_cases h13 : 13 ∈ P
    · have h7 : 7 ∈ P := (facts hP E).1 7 (by norm_num) (by norm_num) 13 h13 (by norm_num)
      by_cases h103 : 103 ∈ P
      · exact case3_iv hP E hm h h7 h13 h103
      · exact case3_iii hP E hm h h7 h13 h103
    · exact case3_ii hP E hm h h13
  · exact case_odd hP E hm (by omega)

end Graham1052

-- Section 6. Small m, the reduction to (E), and the theorem.

namespace Graham1052

theorem core {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p) (hm : 1 ≤ m) :
    (m = 1 ∧ P = {3}) ∨ (m = 2 ∧ P = {3, 5}) ∨ (m = 6 ∧ P = {3, 5, 7, 13}) := by
  by_cases h10 : 10 ≤ m
  · exact (big hP E h10).elim
  obtain ⟨S1, S5, S2, S3, S4a, S4b⟩ := facts hP E
  have hm9 : m ≤ 9 := by omega
  interval_cases m
  · left
    have h3 : 3 ∈ P := S5 3 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨rfl, S_sat hP E (A := {3}) (Finset.singleton_subset_iff.mpr h3) (by decide)⟩
  · right; left
    have h5 : 5 ∈ P := S5 5 (by norm_num) (by norm_num) (by norm_num)
    have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) 5 h5 (by norm_num)
    have hsub : ({3, 5} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h3
      · exact h5
    exact ⟨rfl, S_sat hP E hsub (by decide)⟩
  · exact absurd (by norm_num : 3 * 3 ∣ 2 ^ 3 + 1) (S4a 3 (by norm_num) (by norm_num))
  · have h17 : 17 ∈ P := S5 17 (by norm_num) (by norm_num) (by norm_num)
    exact absurd (by norm_num : 3 * 3 ∣ 17 + 1) (S4b 3 (by norm_num) (by norm_num) 17 h17)
  · have h11 : 11 ∈ P := S5 11 (by norm_num) (by norm_num) (by norm_num)
    exact absurd (by norm_num : 3 ∣ 11 + 1)
      (S3 3 (by norm_num) (by norm_num) (by norm_num) 11 h11)
  · right; right
    have h5 : 5 ∈ P := S5 5 (by norm_num) (by norm_num) (by norm_num)
    have h13 : 13 ∈ P := S5 13 (by norm_num) (by norm_num) (by norm_num)
    have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) 5 h5 (by norm_num)
    have h7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) 13 h13 (by norm_num)
    have hsub : ({3, 5, 7, 13} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
    exact ⟨rfl, S_sat hP E hsub (by decide)⟩
  · have h43 : 43 ∈ P := S5 43 (by norm_num) (by norm_num) (by norm_num)
    have h11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) 43 h43 (by norm_num)
    exact absurd (by norm_num : 3 ∣ 11 + 1)
      (S3 3 (by norm_num) (by norm_num) (by norm_num) 11 h11)
  · have h257 : 257 ∈ P := S5 257 (by norm_num) (by norm_num) (by norm_num)
    have h43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) 257 h257 (by norm_num)
    have h11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) 43 h43 (by norm_num)
    have h := S2 3 (by norm_num) (by norm_num) 257 h257 11 h11 (by norm_num) (by norm_num)
    omega
  · exact absurd (by norm_num : 3 * 3 ∣ 2 ^ 9 + 1) (S4a 3 (by norm_num) (by norm_num))

theorem balance_aux {n m s : ℕ}
    (hprod : ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n)
    (hmul : 2 ^ m * s = n) (hsodd : ¬ 2 ∣ s) (hs : Squarefree s) :
    1 ≤ m ∧ (2 ^ m + 1) * ∏ p ∈ s.primeFactors, (p + 1) =
      2 ^ (m + 1) * ∏ p ∈ s.primeFactors, p := by
  subst hmul
  have hs0 : s ≠ 0 := hs.ne_zero
  have h2m : (2 : ℕ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have hsprod : ∏ p ∈ s.primeFactors, p = s := Nat.prod_primeFactors_of_squarefree hs
  have hp2 : ∀ p ∈ s.primeFactors, p ≠ 2 := fun p hp h2 =>
    hsodd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hfp : ∀ p ∈ s.primeFactors, (2 ^ m * s).factorization p = 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_mul h2m hs0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_of_ne (hp2 p hp), zero_add]
    exact le_antisymm (Squarefree.natFactorization_le_one p hs)
      (hpp.factorization_pos_of_dvd hs0 (Nat.dvd_of_mem_primeFactors hp))
  have e2 : ∏ p ∈ s.primeFactors, (1 + p ^ (2 ^ m * s).factorization p) =
      ∏ p ∈ s.primeFactors, (p + 1) :=
    Finset.prod_congr rfl fun p hp => by rw [hfp p hp, pow_one, add_comm]
  by_cases hm0 : m = 0
  · exfalso
    subst hm0
    have hpf : (2 ^ 0 * s).primeFactors = s.primeFactors := by rw [pow_zero, one_mul]
    rw [hpf, e2, pow_zero, one_mul] at hprod
    by_cases hs1 : s = 1
    · rw [hs1] at hprod
      simp at hprod
    · have hne : s.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
      obtain ⟨q, hq, hqmax⟩ : ∃ q ∈ s.primeFactors, ∀ p ∈ s.primeFactors, p ≤ q :=
        ⟨s.primeFactors.max' hne, Finset.max'_mem _ hne, fun p hp => Finset.le_max' _ p hp⟩
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqd : q ∣ ∏ p ∈ s.primeFactors, (p + 1) := by
        rw [hprod]
        exact (Nat.dvd_of_mem_primeFactors hq).mul_left 2
      obtain ⟨p, hp, hqp1⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp hqd
      have h1 := two_mul_le hqp (hp2 q hq) (Nat.prime_of_mem_primeFactors hp) (hp2 p hp) hqp1
      have h2 := hqmax p hp
      have h3 := hqp.two_le
      omega
  · refine ⟨by omega, ?_⟩
    have h2notin : 2 ∉ s.primeFactors := fun h => hp2 2 h rfl
    have hf2 : (2 ^ m * s).factorization 2 = m := by
      rw [Nat.factorization_mul h2m hs0, Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hsodd, add_zero]
    rw [Nat.primeFactors_mul h2m hs0, Nat.primeFactors_prime_pow hm0 Nat.prime_two,
      Finset.prod_union (Finset.disjoint_singleton_left.mpr h2notin), Finset.prod_singleton,
      hf2, e2] at hprod
    rw [hsprod, pow_succ]
    linarith

end Graham1052

theorem graham_H1 : ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    Squarefree (n / 2 ^ padicValNat 2 n) → n = 6 ∨ n = 60 ∨ n = 87360 := by
  intro n h hs
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hs
  have hmul := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hsodd : ¬ 2 ∣ n / 2 ^ n.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hn0
  obtain ⟨hm, hE⟩ := Graham1052.balance_aux (Graham1052.prod_eq_two_mul h) hmul hsodd hs
  have hP : ∀ p ∈ (n / 2 ^ n.factorization 2).primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, fun h2 => by
      subst h2
      exact hsodd (Nat.dvd_of_mem_primeFactors hp)⟩
  have hsprod := Nat.prod_primeFactors_of_squarefree hs
  rcases Graham1052.core hP hE hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h2, h1] at hsprod
    rw [h1, ← hsprod] at hmul
    rw [← hmul]
    decide
  · right; left
    rw [h2, h1] at hsprod
    rw [h1, ← hsprod] at hmul
    rw [← hmul]
    decide
  · right; right
    rw [h2, h1] at hsprod
    rw [h1, ← hsprod] at hmul
    rw [← hmul]
    decide


theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1.H1 := graham_H1
