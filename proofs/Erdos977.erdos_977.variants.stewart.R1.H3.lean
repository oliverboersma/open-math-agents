import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1
import Mathlib

-- n / phi(n) = prod p/(p-1) over the distinct prime factors, and that product is at most
-- omega(n) + 1. Each prime is at least 2, so omega(n) is at most the base-two logarithm.
theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H3 := by
  intro n hn
  classical
  let s := n.primeFactors
  have hlog : s.card ≤ Nat.log 2 n := by
    have hpow : 2 ^ s.card ≤ ∏ p ∈ s, p := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    have hle : ∏ p ∈ s, p ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    exact Nat.le_log_of_pow_le (by decide) (hpow.trans hle)
  have aux : ∀ c : ℕ, ∀ t : Finset ℕ, t.card = c → (∀ p ∈ t, p.Prime) →
      ∏ p ∈ t, p ≤ (t.card + 1) * ∏ p ∈ t, (p - 1) := by
    intro c
    refine Nat.strongRecOn c ?_
    intro c ih t hc ht
    by_cases he : t.Nonempty
    · let p := t.max' he
      have hp_mem : p ∈ t := Finset.max'_mem t he
      have hp : p.Prime := ht p hp_mem
      have hle : t.card + 1 ≤ p := by
        have hp2 : 2 ≤ p := hp.two_le
        have hsub : t ⊆ Finset.Icc 2 p := by
          intro q hq
          exact Finset.mem_Icc.mpr ⟨(ht q hq).two_le, Finset.le_max' t q hq⟩
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Icc] at hcard
        have hsub2 : p + 1 - 2 = p - 1 := by omega
        rw [hsub2] at hcard
        omega
      let t' := t.erase p
      have ht' : ∀ q ∈ t', q.Prime := fun q hq => ht q (Finset.mem_of_mem_erase hq)
      have hc' : t'.card < c := by
        rw [Finset.card_erase_of_mem hp_mem, hc]
        have : 0 < t.card := Finset.card_pos.mpr he
        omega
      have ih' := ih t'.card hc' t' rfl ht'
      have hkey : p * t.card ≤ (t.card + 1) * (p - 1) := by
        have hc1 : t.card + 1 ≤ p := hle
        have hadd : p * t.card + (t.card + 1) ≤ (t.card + 1) * p := by
          calc
            p * t.card + (t.card + 1) ≤ p * t.card + p := Nat.add_le_add_left hc1 _
            _ = p * (t.card + 1) := by ring
            _ = (t.card + 1) * p := Nat.mul_comm _ _
        have happ : (t.card + 1) * (p - 1) + (t.card + 1) = (t.card + 1) * p := by
          have hmul := Nat.mul_add (t.card + 1) (p - 1) 1
          rw [Nat.mul_one, Nat.sub_add_cancel hp.one_lt.le] at hmul
          exact hmul.symm
        exact Nat.le_of_add_le_add_right (hadd.trans_eq happ.symm)
      have hc_eq : t'.card + 1 = t.card := by
        rw [Finset.card_erase_of_mem hp_mem]
        exact Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr he)
      calc
        ∏ q ∈ t, q = p * ∏ q ∈ t', q := by
          rw [← Finset.mul_prod_erase t (fun q => q) hp_mem]
        _ ≤ p * ((t'.card + 1) * ∏ q ∈ t', (q - 1)) :=
          Nat.mul_le_mul_left _ ih'
        _ = p * (t.card * ∏ q ∈ t', (q - 1)) := by rw [hc_eq]
        _ = (p * t.card) * ∏ q ∈ t', (q - 1) := by ring
        _ ≤ ((t.card + 1) * (p - 1)) * ∏ q ∈ t', (q - 1) :=
          Nat.mul_le_mul_right _ hkey
        _ = (t.card + 1) * ((p - 1) * ∏ q ∈ t', (q - 1)) := by ring
        _ = (t.card + 1) * ∏ q ∈ t, (q - 1) := by
          rw [← Finset.mul_prod_erase t (fun q => q - 1) hp_mem]
    · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp [hempty]
  have hprod := aux s.card s rfl fun p hp => Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < ∏ p ∈ s, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    exact Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have hmul := Nat.totient_mul_prod_primeFactors n
  have hcancel : n ≤ n.totient * (s.card + 1) := by
    have hle : n * ∏ p ∈ s, (p - 1) ≤ (n.totient * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by
      calc
        n * ∏ p ∈ s, (p - 1) = n.totient * ∏ p ∈ s, p := hmul.symm
        _ ≤ n.totient * ((s.card + 1) * ∏ p ∈ s, (p - 1)) := Nat.mul_le_mul_left _ hprod
        _ = (n.totient * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
    exact Nat.le_of_mul_le_mul_right hle hpos
  calc
    n ≤ n.totient * (s.card + 1) := hcancel
    _ ≤ n.totient * (Nat.log 2 n + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog _)
