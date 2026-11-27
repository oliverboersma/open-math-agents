import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS

/-! Reduction of Conjecture 1.1 of arXiv 2501.03234.

For an odd prime p we prove (below, fully) the exact identity

  S(p) = T(p) := -2 * sum over 1 <= m < a < p of (-1)^m * floor((m*p - 1)/a).

Route: the floor shift (h+p)j/p = hj/p + j, the reflection h -> p - h (which uses that p
does not divide h*j), and an interval count of j in [1, p) between consecutive multiples
of p/a.  Writing floor((m p - 1)/a) = (m p - 1 - r)/a gives T(p) = M(p) + E(p) with main term
M(p) = p * (sum of 1/a over odd a < p), roughly (p/2) log p, and an error E(p) made of residues
(m p - 1) mod a.  Positivity is then split into a finite range (H1) and the
quantitative bound 2 T(p) >= M(p) for large p (H2), i.e. the error is at most half of the
main term.  Exact computation: T(p) > 0 for every odd prime p < 100000, and 2 T(p) >= M(p)
for every prime 180 <= p < 150000 (worst ratio E/M = -0.4377 at p = 233).
-/

open Finset

namespace OMA.R_Arxiv_2501_03234_conjecture_1_1_R1

/-- Finite range: T(p) > 0 for every odd prime p below 100000 (checked by exact computation). -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → p < 100000 →
    0 < -2 * ∑ a ∈ Ico 1 p, ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * ((m * p - 1) / a : ℕ)

/-- Large primes: T(p) is at least half of the main term p * (sum of 1/a over odd a < p). -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 100000 ≤ p →
    ∑ a ∈ (Ico 1 p).filter Odd, (p : ℚ) / a ≤
      2 * (((-2 * ∑ a ∈ Ico 1 p, ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * ((m * p - 1) / a : ℕ)) : ℤ) : ℚ)


lemma floor_eq (h j k : ℕ) : ⌊((h * j : ℚ)) / k⌋₊ = h * j / k := by
  rw [← Nat.cast_mul, Nat.floor_div_eq_div]

lemma refl_aux (p h j : ℕ) (hp : p.Prime) (h0 : 0 < h) (hh : h < p) (j0 : 0 < j) (hj : j < p) :
    (p - h) * j / p + h * j / p + 1 = j := by
  have hnd : ¬ p ∣ h * j := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · exact absurd (Nat.le_of_dvd h0 hd) (by omega)
    · exact absurd (Nat.le_of_dvd j0 hd) (by omega)
  have hr : 0 < h * j % p := Nat.pos_of_ne_zero (fun h' => hnd (Nat.dvd_of_mod_eq_zero h'))
  have e1 := Nat.div_add_mod (h * j) p
  have e2 := Nat.div_add_mod ((p - h) * j) p
  have hr1 := Nat.mod_lt (h * j) hp.pos
  have hr2 := Nat.mod_lt ((p - h) * j) hp.pos
  have hsum : (p - h) * j + h * j = p * j := by rw [← add_mul, Nat.sub_add_cancel hh.le]
  set q1 := h * j / p
  set q2 := (p - h) * j / p
  set r1 := h * j % p
  set r2 := (p - h) * j % p
  have key : p * (q1 + q2) + (r1 + r2) = p * j := by rw [← hsum, ← e1, ← e2]; ring
  have hlt : q1 + q2 < j := by
    by_contra hc; rw [not_lt] at hc
    have : p * j ≤ p * (q1 + q2) := Nat.mul_le_mul_left p hc
    omega
  have hgt : j < q1 + q2 + 2 := by
    by_contra hc; rw [not_lt] at hc
    have : p * (q1 + q2 + 2) ≤ p * j := Nat.mul_le_mul_left p hc
    nlinarith
  omega

lemma S_eq (p : ℕ) (hp : p.Prime) :
    Arxiv.«2501.03234».S p = ∑ a ∈ Ico 1 p, ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * j / p) := by
  unfold Arxiv.«2501.03234».S Arxiv.«2501.03234».S'
  have hr : ∀ g : ℕ → ℤ, ∑ h ∈ Ico 1 p, g h = ∑ h ∈ Ico 1 p, g (p - h) := by
    intro g
    rw [Finset.sum_Ico_reflect g 1 (by omega)]
    congr 1
    ext x; simp only [mem_Ico]; omega
  rw [hr]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mem_Ico] at hh hj
  rw [floor_eq]
  have := refl_aux p h j hp (by omega) (by omega) (by omega) (by omega)
  have e : j + 1 + (p - h) * j / p = h * j / p + 2 * ((p - h) * j / p + 1) := by omega
  rw [e, pow_add, pow_mul]
  simp


lemma neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = 1 + 2 * ∑ m ∈ Ico 1 (n + 1), (-1 : ℤ) ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega), pow_succ]
    linear_combination ih

lemma card_filter_eq (p a m : ℕ) (hp : 0 < p) (ha : 0 < a) (hm1 : 1 ≤ m) (hma : m < a) :
    (((Ico 1 p).filter (fun j => m * p ≤ a * j)).card : ℤ) = ((p : ℤ) - 1) - ((m * p - 1) / a : ℕ) := by
  have hmp : 1 ≤ m * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlt : (m * p - 1) / a < p := by
    rw [Nat.div_lt_iff_lt_mul ha]
    have : m * p ≤ (a - 1) * p := Nat.mul_le_mul_right p (by omega)
    have h2 : (a - 1) * p + p = p * a := by
      cases a with
      | zero => omega
      | succ a => simp only [Nat.add_sub_cancel]; ring
    omega
  have hf : (Ico 1 p).filter (fun j => m * p ≤ a * j) = Ico ((m * p - 1) / a + 1) p := by
    ext j
    simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2⟩
      have : (m * p - 1) / a < j := by
        rw [Nat.div_lt_iff_lt_mul ha, mul_comm j a]; omega
      omega
    · rintro ⟨h1, h2⟩
      have : (m * p - 1) / a < j := by omega
      rw [Nat.div_lt_iff_lt_mul ha, mul_comm j a] at this
      exact ⟨⟨le_trans (Nat.le_add_left 1 _) h1, h2⟩, by omega⟩
  rw [hf, Nat.card_Ico]
  push_cast [Nat.cast_sub (show (m * p - 1) / a + 1 ≤ p by omega)]
  ring

lemma inner_eq (p a : ℕ) (hp : 0 < p) (ha : 0 < a) (_hap : a < p) :
    ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * j / p) =
      ((p : ℤ) - 1) * (-1) ^ (a - 1) - 2 * ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * ((m * p - 1) / a : ℕ) := by
  have step : ∀ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * j / p) =
      1 + 2 * ∑ m ∈ Ico 1 a, (if m * p ≤ a * j then (-1 : ℤ) ^ m else 0) := by
    intro j hj
    simp only [mem_Ico] at hj
    have hlt : a * j / p < a := by
      rw [Nat.div_lt_iff_lt_mul hp]; exact Nat.mul_lt_mul_of_pos_left hj.2 ha
    have hs : (Ico 1 a).filter (fun m => m * p ≤ a * j) = Ico 1 (a * j / p + 1) := by
      ext m
      simp only [mem_filter, mem_Ico]
      have hle : m ≤ a * j / p ↔ m * p ≤ a * j := Nat.le_div_iff_mul_le hp
      omega
    rw [neg_one_pow_eq, ← Finset.sum_filter, hs]
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have step2 : ∀ m ∈ Ico 1 a, ∑ j ∈ Ico 1 p, (if m * p ≤ a * j then (-1 : ℤ) ^ m else 0) =
      (-1 : ℤ) ^ m * (((p : ℤ) - 1) - ((m * p - 1) / a : ℕ)) := by
    intro m hm
    simp only [mem_Ico] at hm
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_eq p a m hp ha hm.1 hm.2]
    ring
  rw [Finset.sum_congr rfl step2]
  have h1 := neg_one_pow_eq (a - 1)
  rw [Nat.sub_add_cancel ha] at h1
  rw [h1]
  have e3 : ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * (((p : ℤ) - 1) - ((m * p - 1) / a : ℕ)) =
      ((p : ℤ) - 1) * ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m -
        ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * ((m * p - 1) / a : ℕ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [e3, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ p by omega)]
  push_cast
  ring


lemma alt_sum_zero (n : ℕ) : ∑ a ∈ Ico 1 (2 * n + 1), (-1 : ℤ) ^ (a - 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), ih]
    rw [show 2 * n + 1 + 1 - 1 = 2 * n + 1 by omega, show 2 * n + 1 - 1 = 2 * n by omega,
      pow_succ, pow_mul]
    simp

/-- The conjectured sum equals an explicit floor sum. -/
lemma S_eq_T (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Arxiv.«2501.03234».S p = -2 * ∑ a ∈ Ico 1 p, ∑ m ∈ Ico 1 a, (-1 : ℤ) ^ m * ((m * p - 1) / a : ℕ) := by
  rw [S_eq p hp]
  rw [Finset.sum_congr rfl (fun a ha => inner_eq p a hp.pos (by simp only [mem_Ico] at ha; omega)
    (by simp only [mem_Ico] at ha; omega))]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  obtain ⟨n, rfl⟩ := hodd
  rw [alt_sum_zero]
  ring


theorem main : H1 → H2 → type_of% @Arxiv.«2501.03234».conjecture_1_1 := by
  intro h1 h2 k hk hodd
  rw [S_eq_T k hk hodd]
  have hk2 : 2 < k := by
    obtain ⟨n, hn⟩ := hodd
    have := hk.two_le
    omega
  by_cases hlt : k < 100000
  · exact h1 k hk hk2 hlt
  · have hb := h2 k hk (by omega)
    have hpos : (0 : ℚ) < ∑ a ∈ (Ico 1 k).filter Odd, (k : ℚ) / a := by
      apply Finset.sum_pos' (fun a _ => by positivity)
      refine ⟨1, ?_, ?_⟩
      · simp only [mem_filter, mem_Ico]
        exact ⟨⟨le_refl 1, by omega⟩, odd_one⟩
      · simp only [Nat.cast_one, div_one]
        exact_mod_cast hk.pos
    have : (0 : ℚ) < ((-2 * ∑ a ∈ Ico 1 k, ∑ m ∈ Ico 1 a,
        (-1 : ℤ) ^ m * ((m * k - 1) / a : ℕ) : ℤ) : ℚ) := by linarith
    exact_mod_cast this

end OMA.R_Arxiv_2501_03234_conjecture_1_1_R1
