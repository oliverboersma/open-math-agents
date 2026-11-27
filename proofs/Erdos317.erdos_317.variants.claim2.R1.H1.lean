import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

-- Step Erdos317.erdos_317.variants.claim2.R1.H1: hypothesis H1 of reduction Erdos317.erdos_317.variants.claim2.R1
-- Credit: @NoahPuckett-IO
-- Take u the least prime power above n. Every k with n < k < u is not a prime power, so it is
-- a product of two coprime factors below k and divides lcm(1, ..., k - 1): the lcm never grows.

namespace OMA.E317

open Finset

/-- A number `k ≥ 2` that is not a prime power divides `lcm (1, ..., k - 1)`. -/
lemma dvd_lcm_pred (k : ℕ) (hk : 2 ≤ k) (hnp : ¬ IsPrimePow k) :
    k ∣ (Icc 1 (k - 1)).lcm id := by
  have hk0 : k ≠ 0 := by omega
  have hp : (Nat.minFac k).Prime := Nat.minFac_prime (by omega)
  set p := Nat.minFac k with hpdef
  have hab : ordProj[p] k * ordCompl[p] k = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hcop : Nat.Coprime (ordProj[p] k) (ordCompl[p] k) :=
    (Nat.coprime_ordCompl hp hk0).pow_left _
  have he : 0 < k.factorization p := hp.factorization_pos_of_dvd hk0 (Nat.minFac_dvd k)
  have ha1 : 1 < ordProj[p] k := Nat.one_lt_pow he.ne' hp.one_lt
  have hb0 : ordCompl[p] k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hab
    exact hk0 hab.symm
  have hb1 : 1 < ordCompl[p] k := by
    by_contra h
    have hb : ordCompl[p] k = 1 := Nat.le_antisymm (not_lt.1 h) (Nat.one_le_iff_ne_zero.2 hb0)
    apply hnp
    refine ⟨p, k.factorization p, hp.prime, he, ?_⟩
    rw [hb, mul_one] at hab
    exact hab
  have halt : ordProj[p] k < k := by
    have := lt_mul_of_one_lt_right (zero_lt_one.trans ha1) hb1
    rwa [hab] at this
  have hblt : ordCompl[p] k < k := by
    have := lt_mul_of_one_lt_left (zero_lt_one.trans hb1) ha1
    rwa [hab] at this
  have hda : ordProj[p] k ∣ (Icc 1 (k - 1)).lcm id :=
    Finset.dvd_lcm (s := Icc 1 (k - 1)) (f := id) (mem_Icc.2 ⟨ha1.le, Nat.le_sub_one_of_lt halt⟩)
  have hdb : ordCompl[p] k ∣ (Icc 1 (k - 1)).lcm id :=
    Finset.dvd_lcm (s := Icc 1 (k - 1)) (f := id) (mem_Icc.2 ⟨hb1.le, Nat.le_sub_one_of_lt hblt⟩)
  have := hcop.mul_dvd_of_dvd_of_dvd hda hdb
  rwa [hab] at this

end OMA.E317

open Finset in
theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  intro n hn
  classical
  have hex : ∃ u, n < u ∧ IsPrimePow u := by
    refine ⟨2 ^ (n + 1), ?_, ⟨2, n + 1, Nat.prime_two.prime, by omega, rfl⟩⟩
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hu := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ (n < m ∧ IsPrimePow m) := fun m hm => Nat.find_min hex hm
  refine ⟨Nat.find hex, hu.1, hu.2, ?_⟩
  have step : ∀ t, n + t ≤ Nat.find hex - 1 →
      (Icc 1 (n + t)).lcm id = (Icc 1 n).lcm id := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have hk : n + t + 1 < Nat.find hex := by omega
      have hnp : ¬ IsPrimePow (n + t + 1) := fun h => hmin _ hk ⟨by omega, h⟩
      have hdvd := OMA.E317.dvd_lcm_pred (n + t + 1) (by omega) hnp
      rw [show n + t + 1 - 1 = n + t by omega] at hdvd
      have hins : Icc 1 (n + (t + 1)) = insert (n + t + 1) (Icc 1 (n + t)) := by
        ext x
        simp only [mem_Icc, mem_insert]
        omega
      rw [hins, Finset.lcm_insert, ← ih (by omega)]
      exact Nat.dvd_antisymm (lcm_dvd hdvd dvd_rfl) (dvd_lcm_right _ _)
  have h := step (Nat.find hex - 1 - n) (by omega)
  rw [show n + (Nat.find hex - 1 - n) = Nat.find hex - 1 by omega] at h
  exact h.symm
