import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-! This step specializes the modular power-sum argument formalized by
@TheWaler in proof #449, AgohGiuga.isStrongGiuga_iff. The block sums and
finite-field lemmas below are adapted from that submission. -/

namespace OMA.GiugaSteps

open AgohGiuga
open scoped Nat

private lemma squarefree_of_forall_primeFactors_dvd_div_sub_one {n : ℕ} (hn0 : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have hdvd1 : p ∣ n / p - 1 := h p hmem
  rcases hpp with ⟨k, hk⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨k, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

private lemma sum_range_pow_zmod_mul (q d k : ℕ) :
    ((∑ i ∈ Finset.range (q * d), i ^ k : ℕ) : ZMod d) =
      (q : ZMod d) * ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, Nat.cast_add, ih]
    have hblock : ((∑ r ∈ Finset.range d, (q * d + r) ^ k : ℕ) : ZMod d) =
        ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
      push_cast
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
    rw [hblock]
    push_cast
    ring

private lemma sum_Ioo_eq_sum_range {n k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  by_cases hn : n = 0
  · subst hn; simp
  have hrange : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp), zero_pow hk.ne', zero_add]

private lemma sum_range_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} (hp : p.Prime)
    (hk_pos : 0 < k) (hdvd : p - 1 ∣ k) :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hdvd with ⟨c, hc⟩
  rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
  have h0 : ((0 : ℕ) : ZMod p) ^ k = 0 := by
    rw [Nat.cast_zero, zero_pow hk_pos.ne']
  rw [h0, zero_add]
  have hones : ∑ r ∈ Finset.Ico 1 p, (r : ZMod p) ^ k = ∑ _r ∈ Finset.Ico 1 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases Finset.mem_Ico.mp hr with ⟨hr1, hrp⟩
    have hr_ne : (r : ZMod p) ≠ 0 := by
      intro h0
      have hpr : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
      exact absurd (Nat.le_of_dvd (by omega) hpr) (by omega)
    rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hr_ne, one_pow]
  rw [hones, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
    Nat.cast_sub hp.pos, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_range_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} (hp : p.Prime)
    (hk : ¬ (p - 1) ∣ k) :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hrange : ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
    refine Finset.sum_nbij (fun r : ℕ => (r : ZMod p)) ?_ ?_ ?_ ?_
    · intro r _
      exact Finset.mem_univ _
    · intro r1 hr1 r2 hr2 heq
      have hval := congr_arg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hr1),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hr2)] at hval
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _
      rfl
  rw [hrange]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h1
    have hunit : g ^ k = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h1)
    exact hk (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr hunit)
  have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k :=
    Equiv.sum_comp (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero) (fun x : ZMod p => x ^ k)
  have hfactor : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k =
      (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k := by
    simp_rw [mul_pow, ← Finset.mul_sum]
  have hmul : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, ← hfactor, hbij, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hgk_ne)


private lemma divisor_conditions {a : ℕ} (h : IsStrongGiuga a) :
    ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ a / p - 1 := by
  have ha := h.1
  have ha1 : 1 < a := ha.1
  have ha_sub_pos : 0 < a - 1 := by omega
  have hp_iff : ∀ p ∈ a.primeFactors,
      p ∣ 1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) ↔ (p - 1) ∣ (a - 1) ∧ p ∣ a / p - 1 := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have : Fact p.Prime := ⟨hp⟩
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
    have hge1 : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    rw [sum_Ioo_eq_sum_range ha_sub_pos, ← ZMod.natCast_eq_zero_iff]
    have hsum_mod : ((∑ i ∈ Finset.range a, i ^ (a - 1) : ℕ) : ZMod p) =
        ((a / p : ℕ) : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
      have h := sum_range_pow_zmod_mul (a / p) p (a - 1)
      rwa [Nat.div_mul_cancel hpa] at h
    rw [Nat.cast_add, Nat.cast_one, hsum_mod]
    by_cases hdvd : p - 1 ∣ a - 1
    · rw [sum_range_pow_zmod_eq_neg_one_of_dvd hp ha_sub_pos hdvd, mul_neg_one,
        ← ZMod.natCast_eq_zero_iff (a / p - 1) p, Nat.cast_sub hge1, Nat.cast_one]
      constructor
      · intro h
        exact ⟨hdvd, by linear_combination -h⟩
      · rintro ⟨_, h⟩
        linear_combination -h
    · rw [sum_range_pow_zmod_eq_zero_of_not_dvd hp hdvd, mul_zero, add_zero]
      exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h.1 hdvd⟩
  intro p hp
  exact (hp_iff p hp).mp ((Nat.dvd_of_mem_primeFactors hp).trans h.2)

end OMA.GiugaSteps

open AgohGiuga OMA.GiugaSteps in
theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n hn
  have hn0 : n ≠ 0 := by have := hn.1.1; omega
  have hall := divisor_conditions hn
  refine (korselts_criterion n hn.1).2 ⟨?_, ?_⟩
  · exact squarefree_of_forall_primeFactors_dvd_div_sub_one hn0 fun p hp => (hall p hp).2
  · intro p hp hpn
    exact (hall p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)).1
