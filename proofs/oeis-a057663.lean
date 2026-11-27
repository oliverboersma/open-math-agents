import OMAStatements.S_oeis_a057663
import Mathlib

/-! Gerasimov’s 2019 conjecture follows by bounding the totient gap of any
composite number below by its quotient by its least prime factor. -/

open Finset

/-- The multiples of p below pq leave at most pq-q coprime residues. -/
private theorem totient_gap {p q : ℕ} (hp : 1 < p) :
    (p*q).totient + q ≤ p*q := by
  let B := (range (p*q)).filter (fun i => ¬ (p*q).Coprime i)
  have hcard : q ≤ B.card := by
    rw [← card_range q]
    apply card_le_card_of_injOn (fun i : ℕ => p * i)
    · intro i hi
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hi) (by omega)),
        Nat.not_coprime_of_dvd_of_dvd hp (dvd_mul_right p q) (dvd_mul_right p i)⟩
    · intro i _ j _ h
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p) h
  have total := card_filter_add_card_filter_not (fun i : ℕ => (p*q).Coprime i) (s := range (p*q))
  change _ + B.card = _ at total
  rw [← Nat.totient_eq_card_coprime, card_range] at total
  omega

private theorem square_le_shift (k : ℕ) : k^2 ≤ k+2^k := by
  have aux (j : ℕ) : (j+3)^2 ≤ j+3 + 2^(j+3) := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show j+1+3 = (j+3)+1 by omega, pow_succ (2:ℕ)]
      nlinarith only [ih, Nat.zero_le (j^2)]
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · exact aux k

private theorem totient_shift_iff (k : ℕ) (hk : 1 ≤ k) :
    (Nat.totient (k + 2 ^ k) = Nat.totient k + 2 ^ k ↔ k.Prime ∧ (k + 2 ^ k).Prime) := by
  let m := k+2^k
  have hm : 1 < m := by dsimp [m]; have := Nat.two_pow_pos k; omega
  constructor
  · intro he
    have hp : m.Prime := by
      by_contra composite
      let p := m.minFac
      let q := m / p
      have prime : p.Prime := Nat.minFac_prime (by omega)
      have hpq : p*q=m := Nat.mul_div_cancel' (Nat.minFac_dvd m)
      have pleq : p ≤ q := Nat.minFac_le_div (by omega) composite
      have sq : k^2 ≤ q^2 := (square_le_shift k).trans (hpq ▸ Nat.mul_le_mul_right q pleq |>.trans_eq (sq q).symm)
      have kq : k ≤ q := by exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ) ≠ 0)).mp sq
      have gap := totient_gap (q := q) prime.one_lt
      rw [hpq] at gap
      change m.totient = k.totient + 2^k at he
      have positive : 0 < k.totient := Nat.totient_pos.mpr hk
      dsimp [m] at gap he
      omega
    refine ⟨(Nat.totient_eq_iff_prime hk).mp ?_, hp⟩
    change m.totient = _ at he
    rw [Nat.totient_prime hp] at he
    dsimp [m] at he
    omega
  · rintro ⟨hk', hm'⟩
    rw [Nat.totient_prime hk', Nat.totient_prime hm']
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a057663.main := totient_shift_iff
