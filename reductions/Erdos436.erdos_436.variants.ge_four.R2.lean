import FormalConjectures.ErdosProblems.«436»

/-!
Reduction `Erdos436.erdos_436.variants.ge_four.R2` of Erdős Problem 436 — ge four.
-/

-- Reduction Erdos436.erdos_436.variants.ge_four.R2 of Erdős Problem 436 — ge four
-- Credit: @PEELY350
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos436_erdos_436_variants_ge_four_R2

open Filter Erdos436

private lemma isPowerResidue_of_dvd {q k p a : ℕ} (hqk : q ∣ k) (ha : IsPowerResidue k p a) :
    IsPowerResidue q p a := by
  rcases hqk with ⟨m, rfl⟩
  rcases ha with ⟨hne, x, hx⟩
  refine ⟨hne, x ^ m, ?_⟩
  rw [← pow_mul, mul_comm, hx]

private lemma isPowerResidue_one {q p : ℕ} (hp : 1 < p) : IsPowerResidue q p 1 := by
  have : Fact (1 < p) := ⟨hp⟩
  refine ⟨?_, 1, by simp⟩
  norm_num

private lemma isPowerResidue_mul {q p a b : ℕ} (hp : p.Prime) (ha : IsPowerResidue q p a)
    (hb : IsPowerResidue q p b) : IsPowerResidue q p (a * b) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases ha with ⟨hna, x, hx⟩
  rcases hb with ⟨hnb, y, hy⟩
  refine ⟨?_, x * y, ?_⟩
  · push_cast
    exact mul_ne_zero hna hnb
  · rw [mul_pow, hx, hy]
    push_cast
    rfl

private lemma not_isPowerResidue_mul_of_left_not_of_right {q p a b : ℕ}
    (hp : p.Prime) (hna : ¬ IsPowerResidue q p a) (hb : IsPowerResidue q p b) :
    ¬ IsPowerResidue q p (a * b) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hab
  apply hna
  rcases hb with ⟨hnb, y, hy⟩
  rcases hab with ⟨hnab, z, hz⟩
  refine ⟨?_, z * y⁻¹, ?_⟩
  · intro ha0
    apply hnab
    push_cast
    rw [ha0, zero_mul]
  · rw [mul_pow, hz, inv_pow, hy]
    push_cast
    rw [mul_assoc, mul_inv_cancel₀ hnb, mul_one]

private lemma isPowerResidue_of_odd_le {q p M : ℕ} (hp : p.Prime)
    (hodd : ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → IsPowerResidue q p r) :
    ∀ u : ℕ, 0 < u → Odd u → u ≤ M → IsPowerResidue q p u := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu_pos hu_odd hu_le
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hu_pos) with rfl | hu_gt1
    · exact isPowerResidue_one hp.one_lt
    · let r := u.minFac
      have hr_prime : r.Prime := Nat.minFac_prime (by omega)
      have hr_dvd : r ∣ u := Nat.minFac_dvd u
      have hr_ne2 : r ≠ 2 := by
        intro h2
        rw [h2] at hr_dvd
        exact (Nat.not_even_iff_odd.mpr hu_odd) (even_iff_two_dvd.mpr hr_dvd)
      have hr_gt2 : 2 < r := lt_of_le_of_ne hr_prime.two_le (Ne.symm hr_ne2)
      have hr_le : r ≤ u := Nat.minFac_le hu_pos
      have hr_res : IsPowerResidue q p r := hodd r hr_prime hr_gt2 (hr_le.trans hu_le)
      rcases hr_dvd with ⟨m, hm⟩
      rcases eq_or_lt_of_le (show 1 ≤ m by nlinarith) with rfl | hm_gt1
      · simpa [hm] using hr_res
      · have hm_lt : m < u := by nlinarith [hr_prime.two_le]
        have hm_odd : Odd m := by
          have : Odd (r * m) := hm ▸ hu_odd
          exact (Nat.odd_mul.mp this).2
        have hm_res : IsPowerResidue q p m := ih m hm_lt (by omega) hm_odd (hm_lt.le.trans hu_le)
        rw [hm]
        exact isPowerResidue_mul hp hr_res hm_res

private lemma exists_two_mul_odd_in_four_consec (n : ℕ) :
    ∃ i < 4, ∃ u : ℕ, Odd u ∧ n + i = 2 * u := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · refine ⟨2, by norm_num, 2 * m + 1, ⟨m, rfl⟩, by ring⟩
    · refine ⟨0, by norm_num, m + m + 1, ⟨m, by ring⟩, by ring⟩
  · rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · refine ⟨1, by norm_num, 2 * m + 1, ⟨m, rfl⟩, by ring⟩
    · refine ⟨3, by norm_num, 2 * m + 3, ⟨m + 1, by ring⟩, by ring⟩

def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 2 < q → ∀ M : ℕ,
    {p : ℕ | p.Prime ∧ ¬ IsPowerResidue q p 2 ∧
      ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → IsPowerResidue q p r}.Infinite

def H2 : Prop :=
  ∀ M : ℕ,
    {p : ℕ | p.Prime ∧ ¬ IsPowerResidue 2 p 2 ∧
      ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → IsPowerResidue 2 p r}.Infinite

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.ge_four := by
  intro h1 h2 k hk l hl
  have hmin : ∃ q : ℕ, q.Prime ∧ q ∣ k := ⟨k.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd k⟩
  rcases hmin with ⟨q, hq_prime, hqk⟩
  have hinf : ∀ M : ℕ,
      {p : ℕ | p.Prime ∧ ¬ IsPowerResidue q p 2 ∧
        ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → IsPowerResidue q p r}.Infinite := by
    rcases eq_or_lt_of_le hq_prime.two_le with rfl | hq2
    · exact h2
    · exact h1 q hq_prime hq2
  rw [runLimsup]
  by_contra hne
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hne
  have hle : ((M + 1 : ℕ) : ℕ∞) ≤ limsup (r k l) (atTop ⊓ 𝓟 {p | p.Prime}) := by
    refine Filter.le_limsup_of_frequently_le ?_ ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
    rw [Filter.frequently_iff]
    intro s hs
    rw [Filter.mem_inf_principal, Filter.mem_atTop_sets] at hs
    obtain ⟨N, hN⟩ := hs
    obtain ⟨p, hp_mem, hp_gt⟩ := (hinf (M + 5)).exists_gt (max N (M + 5))
    rcases hp_mem with ⟨hp_prime, h2_not, hodd⟩
    have hp_ge_N : N ≤ p := (le_max_left N (M + 5)).trans hp_gt.le
    have hp_in_s : p ∈ s := hN p hp_ge_N hp_prime
    refine ⟨p, hp_in_s, ?_⟩
    refine le_iInf₂ ?_
    rintro n ⟨hn1, hn_res⟩
    by_contra hlt
    push Not at hlt
    have hn_lt : n < M + 1 := by exact_mod_cast hlt
    obtain ⟨i, hi4, u, hu_odd, hi_eq⟩ := exists_two_mul_odd_in_four_consec n
    have hi_le : n + i ≤ M + 5 := by omega
    have hu_pos : 0 < u := by omega
    have hu_le : u ≤ M + 5 := by omega
    have hu_res : IsPowerResidue q p u := isPowerResidue_of_odd_le hp_prime hodd u hu_pos hu_odd hu_le
    have h2u_not : ¬ IsPowerResidue q p (2 * u) :=
      not_isPowerResidue_mul_of_left_not_of_right hp_prime h2_not hu_res
    rw [← hi_eq] at h2u_not
    exact h2u_not (isPowerResidue_of_dvd hqk (hn_res i (lt_of_lt_of_le hi4 hl)))
  rw [← hM] at hle
  have hle' : M + 1 ≤ M := Nat.cast_le.mp hle
  omega

end OMA.R_Erdos436_erdos_436_variants_ge_four_R2
