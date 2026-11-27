import OMAStatements.S_oeis_a034178

-- Problem: A034178, Bryant's, Barrera's and Arndt's descriptions of the number of
-- representations n = a^2 - b^2 with a > b >= 0.
-- Credit: @ShoQo
-- Proof: three explicit bijections from {(a, b)}: (a, b) -> a - b (a divisor d with
-- n/d = a + b), (a, b) -> b^2 (sqrt k rational forces k and k + n to be squares), and
-- (m, j) -> (m + j, j).

open OMA.S_oeis_a034178

namespace OMA_A034178_Proof

lemma bryant (n : ℕ) (hn : 1 ≤ n) :
    a n = {d : ℕ | d ∣ n ∧ d * d ≤ n ∧ Even (d + n / d)}.ncard := by
  show {p : ℕ × ℕ | p.2 < p.1 ∧ p.1 ^ 2 = p.2 ^ 2 + n}.ncard = _
  refine Set.ncard_congr (fun p _ => p.1 - p.2) ?_ ?_ ?_
  · rintro ⟨x, y⟩ ⟨hlt, heq⟩
    obtain ⟨m, rfl⟩ : ∃ m, x = y + m := ⟨x - y, by omega⟩
    have hn' : n = m * (m + 2 * y) := by simp only at heq; nlinarith
    have hm : 0 < m := by simp only at hlt; omega
    simp only [show y + m - y = m by omega]
    refine ⟨⟨m + 2 * y, hn'⟩, by rw [hn']; nlinarith, ?_⟩
    rw [hn', Nat.mul_div_cancel_left _ hm]
    exact ⟨m + y, by ring⟩
  · rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨hlt, heq⟩ ⟨hlt', heq'⟩ h
    simp only at hlt heq hlt' heq' h
    obtain ⟨m, rfl⟩ : ∃ m, x = y + m := ⟨x - y, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', x' = y' + m' := ⟨x' - y', by omega⟩
    have hmm : m = m' := by omega
    subst hmm
    have : y = y' := by nlinarith
    subst this; rfl
  · rintro d ⟨hd, hdd, hev⟩
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
    obtain ⟨e, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ hd0] at hev
    have hde : d ≤ e := by nlinarith
    obtain ⟨r, hr⟩ := hev
    refine ⟨(e - r + d, e - r), ⟨by simp only; omega, ?_⟩, by simp only; omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, e = d + 2 * t := ⟨(e - d) / 2, by omega⟩
    simp only [show d + 2 * t - r = t by omega]
    ring

lemma arndt (n : ℕ) :
    a n = {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ^ 2 + 2 * p.1 * p.2 = n}.ncard := by
  show {p : ℕ × ℕ | p.2 < p.1 ∧ p.1 ^ 2 = p.2 ^ 2 + n}.ncard = _
  symm
  refine Set.ncard_congr (fun p _ => (p.1 + p.2, p.2)) ?_ ?_ ?_
  · rintro ⟨m, j⟩ ⟨hm, h⟩
    simp only at hm h ⊢
    exact ⟨by omega, by rw [← h]; ring⟩
  · rintro ⟨m, j⟩ ⟨m', j'⟩ _ _ h
    simp only [Prod.mk.injEq] at h ⊢; omega
  · rintro ⟨x, y⟩ ⟨hlt, heq⟩
    simp only at hlt heq
    obtain ⟨m, rfl⟩ : ∃ m, x = y + m := ⟨x - y, by omega⟩
    refine ⟨(m, y), ⟨show 1 ≤ m by omega, show m ^ 2 + 2 * m * y = n by nlinarith⟩, ?_⟩
    show (m + y, y) = (y + m, y)
    rw [add_comm]

lemma squares_of_sum (k n : ℕ) (hn : 1 ≤ n) (m : ℤ)
    (h : Real.sqrt k + Real.sqrt ((k + n : ℕ) : ℝ) = m) : IsSquare k ∧ IsSquare (k + n) := by
  set s := Real.sqrt k
  set t := Real.sqrt ((k + n : ℕ) : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = k := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = ((k + n : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have ht0 : 0 < t := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ k := by positivity
    exact Real.sqrt_pos.mpr (by push_cast; linarith)
  have hm0 : (0 : ℝ) < m := by rw [← h]; linarith
  push_cast at ht2
  have hsq : s = ((m : ℝ) ^ 2 - n) / (2 * m) := by
    field_simp
    have : t = m - s := by linarith
    rw [this] at ht2; nlinarith
  have htq : t = ((m : ℝ) ^ 2 + n) / (2 * m) := by
    field_simp
    have : s = m - t := by linarith
    rw [this] at hs2; nlinarith
  constructor
  · by_contra hk
    exact (irrational_sqrt_natCast_iff.mpr hk).ne_rat (((m : ℚ) ^ 2 - n) / (2 * m)) (by
      change s = _; rw [hsq]; push_cast; ring)
  · by_contra hk
    exact (irrational_sqrt_natCast_iff.mpr hk).ne_rat (((m : ℚ) ^ 2 + n) / (2 * m)) (by
      change t = _; rw [htq]; push_cast; ring)

lemma barrera (n : ℕ) (hn : 1 ≤ n) :
    a n = {k : ℕ | ∃ m : ℤ, Real.sqrt k + Real.sqrt ((k + n : ℕ) : ℝ) = m}.ncard := by
  show {p : ℕ × ℕ | p.2 < p.1 ∧ p.1 ^ 2 = p.2 ^ 2 + n}.ncard = _
  refine Set.ncard_congr (fun p _ => p.2 ^ 2) ?_ ?_ ?_
  · rintro ⟨x, y⟩ ⟨hlt, heq⟩
    simp only at hlt heq ⊢
    refine ⟨(x + y : ℕ), ?_⟩
    rw [← heq]; push_cast
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]; ring
  · rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨hlt, heq⟩ ⟨hlt', heq'⟩ h
    simp only at hlt heq hlt' heq' h
    have hy : y = y' := Nat.pow_left_injective (by norm_num) h
    subst hy
    have : x ^ 2 = x' ^ 2 := by omega
    have hx : x = x' := Nat.pow_left_injective (by norm_num) this
    subst hx; rfl
  · rintro k ⟨m, hm⟩
    obtain ⟨⟨y, hy⟩, ⟨x, hx⟩⟩ := squares_of_sum k n hn m hm
    refine ⟨(x, y), ⟨?_, ?_⟩, by simp only; rw [hy]; ring⟩
    · simp only; by_contra hc; push Not at hc; nlinarith [Nat.mul_le_mul hc hc]
    · simp only; nlinarith

end OMA_A034178_Proof

open OMA_A034178_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a034178.main :=
  fun n hn => ⟨bryant n hn, barrera n hn, arndt n⟩
