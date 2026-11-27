import OMAReductions.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1_H2_R1
import Mathlib

/-! A congruence modulo 8 handles the prime 2. At odd primes choose a
square or nonsquare as required and use quadratic reciprocity, then combine
the local choices by the Chinese remainder theorem. -/
namespace Signs436
open Finset

lemma local_sign (q k : ℕ) (hq : q.Prime) (h2 : q ≠ 2) :
    ∃ v : ℕ, v.Coprime q ∧ (IsSquare (v : ZMod q) ↔ Even k) ∧ (Even k → v=1) := by
  letI : Fact q.Prime := ⟨hq⟩
  by_cases ev : Even k
  · refine ⟨1,Nat.coprime_one_left _,?_,fun _ => rfl⟩
    simp [ev]
  · obtain ⟨z,hz⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by simpa [ZMod.ringChar_zmod_n] using h2)
    have zn : z ≠ 0 := by rintro rfl; exact hz IsSquare.zero
    have cop : z.val.Coprime q := (hq.coprime_iff_not_dvd.mpr (fun h => zn (by
      rw [← ZMod.natCast_zmod_val z]; exact (ZMod.natCast_eq_zero_iff ..).mpr h))).symm
    exact ⟨z.val,cop,by simp [ZMod.natCast_zmod_val,hz,ev],fun h => (ev h).elim⟩

lemma signs (M : ℕ) (hM : 3 ≤ M) (w : ℕ → ℕ) (w2 : Odd (w 2)) (w3 : Even (w 3)) :
    ∃ m a C : ℕ, 0 < m ∧ a.Coprime m ∧ 3 ∣ m ∧ a%3=1 ∧
      ∀ p > C, p.Prime → p ≡ a [MOD m] → ∀ q : ℕ, q.Prime → q ≤ M →
        (q : ZMod p)^((p-1)/2) = (-1 : ZMod p)^(w q) := by
  classical
  let S := (Nat.primesLE M).erase 2
  have sm {q : ℕ} : q ∈ S ↔ q ≠ 2 ∧ q ≤ M ∧ q.Prime := by simp [S,Nat.mem_primesLE]
  have hv (q : ℕ) : ∃ z : ℕ, q ∈ S →
      z.Coprime q ∧ (IsSquare (z : ZMod q) ↔ Even (w q)) ∧ (Even (w q) → z=1) := by
    by_cases h : q∈S
    · obtain ⟨z,hz⟩ := local_sign q (w q) (sm.mp h).2.2 (sm.mp h).1
      exact ⟨z,fun _ => hz⟩
    · exact ⟨1,fun hh => (h hh).elim⟩
  choose v hv using hv
  let P := ∏ q ∈ S,q
  have Ppos : 0 < P := prod_pos fun q h => (sm.mp h).2.2.pos
  have divides {q : ℕ} (h : q∈S) : q ∣ P := dvd_prod_of_mem id h
  have twoP : Nat.Coprime 2 P := Nat.coprime_prod_right_iff.mpr
    (fun q h => (Nat.coprime_primes Nat.prime_two (sm.mp h).2.2).mpr (sm.mp h).1.symm)
  have eight : Nat.Coprime 8 P := twoP.pow_left 3
  obtain ⟨b,hb⟩ := Nat.chineseRemainderOfFinset v id S (fun q h => (sm.mp h).2.2.ne_zero)
    (fun p hp q hq ne => (Nat.coprime_primes (sm.mp hp).2.2 (sm.mp hq).2.2).mpr ne)
  obtain ⟨a,ha8,haP⟩ := Nat.chineseRemainder eight 5 b
  have atq {q : ℕ} (hq : q ∈ S) : a ≡ v q [MOD q] := (haP.of_dvd (divides hq)).trans (hb q hq)
  have acop : a.Coprime (8*P) := by
    apply Nat.Coprime.mul_right
    · change a.gcd 8 = 1
      rw [ha8.gcd_eq]; decide
    · apply Nat.coprime_prod_right_iff.mpr
      intro q h
      change a.gcd q = 1
      rw [(atq h).gcd_eq]
      exact (hv _ h).1
  have three : 3 ∈ S := sm.mpr ⟨by decide,hM,by decide⟩
  have a3 : a % 3=1 := by
    have h := atq three
    rw [(hv _ three).2.2 w3] at h
    exact h
  refine ⟨8*P,a,M,by positivity,acop,(divides three).mul_left 8,a3,?_⟩
  intro p hpM hp hpmod q hq hqM
  letI : Fact p.Prime := ⟨hp⟩
  have p8 : p%8=5 := (hpmod.of_dvd (dvd_mul_right ..)).trans ha8
  have p4 : p%4=1 := by omega
  have p2 : p ≠ 2 := by omega
  have ls : legendreSym p (q:ℤ) = (-1:ℤ)^(w q) := by
    by_cases he : q=2
    · subst q
      rw [w2.neg_one_pow]
      change legendreSym p 2 = -1
      rw [legendreSym.at_two p2,ZMod.χ₈_nat_eq_if_mod_eight]
      simp [p8,show p%2=1 by omega]
    · letI : Fact q.Prime := ⟨hq⟩
      have qs : q ∈ S := sm.mpr ⟨he,hqM,hq⟩
      have pv : p ≡ v q [MOD q] := (hpmod.of_dvd ((divides qs).mul_left 8)).trans (atq qs)
      have eqv := (ZMod.natCast_eq_natCast_iff ..).mpr pv
      have rel : IsSquare (p : ZMod q) ↔ Even (w q) := by rw [eqv]; exact (hv _ qs).2.1
      have nz : (p : ZMod q) ≠ 0 := by
        intro z
        have dv := (ZMod.natCast_eq_zero_iff ..).mp z
        exact (hq.coprime_iff_not_dvd.mp ((Nat.coprime_primes hq hp).mpr (by omega))) dv
      rw [← legendreSym.quadratic_reciprocity_one_mod_four p4 he]
      by_cases h : Even (w q)
      · rw [h.neg_one_pow]; exact (legendreSym.eq_one_iff' q nz).mpr (rel.mpr h)
      · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]; exact (legendreSym.eq_neg_one_iff' q).mpr (mt rel.mp h)
  have eval := legendreSym.eq_pow p (q:ℤ)
  rw [ls] at eval
  have half : (p-1)/2 = p/2 := by omega
  simpa only [half,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast] using eval.symm

end Signs436

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1_H2_R1.H1 := by
  let w (q : ℕ) : ℕ := if q ∈ ([3,43,61] : List ℕ) then 0 else
    if q ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 4 else 5
  exact Signs436.signs 202124 (by decide) w (by decide) (by decide)
