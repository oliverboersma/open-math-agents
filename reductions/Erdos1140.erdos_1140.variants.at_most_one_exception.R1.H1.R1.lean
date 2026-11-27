import OMAReductions.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1
import Mathlib

/-! Following Epure and Gica, Theorem 4.1, reduce to the class number of the
real quadratic field of radicand t²+1 and the classification of Byeon and Lee.
The sum-of-two-squares factorization, inertness at every smaller odd prime,
and the obstruction to a representation by x²+2y² are proved here. -/
namespace OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H1_R1
open Erdos1140 NumberField

def H1 : Prop := ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2*n=t^2+1 →
    (∀ q : ℕ, q.Prime → 2<q → q<t → ¬ IsSquare ((2*n : ℕ) : ZMod q)) →
    (∀ a b : ℕ, n ≠ a^2+2*b^2) →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (s : K),
      s^2 = ((t^2+1 : ℕ) : K) ∧ Algebra.adjoin ℚ ({s} : Set K) = ⊤ ∧ NumberField.classNumber K = 2

def H2 : Prop := ∀ (n t : ℕ), n.Prime → t.Prime → Odd t → 2*n=t^2+1 →
    ∀ (K : Type) [Field K] [NumberField K] (s : K), s^2 = ((t^2+1 : ℕ) : K) →
    Algebra.adjoin ℚ ({s} : Set K) = ⊤ → NumberField.classNumber K = 2 → t ≤ 19

lemma shape (n : ℕ) (hbig : 199<n) (hp : n.Prime) (hm : n%4 ≠ 3) (good : Erdos1140Prop n) :
    ∃ t : ℕ, t.Prime ∧ Odd t ∧ 2*n=t^2+1 := by
  letI : Fact n.Prime := ⟨hp⟩
  obtain ⟨a,b,h⟩ := Nat.Prime.sq_add_sq hm
  have go (a b : ℕ) (hle : b ≤ a) (eq : a^2+b^2=n) :
      ∃ t : ℕ, t.Prime ∧ Odd t ∧ 2*n=t^2+1 := by
    have hne : a ≠ b := by
      rintro rfl
      have dvd : 2 ∣ n := ⟨a^2,by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp dvd
      omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hle
    have dp : 0 < d := by omega
    have lt : 2*b^2<n := by nlinarith [Nat.pow_lt_pow_left (show b<a by omega) (by decide : 2≠0)]
    have diff : n-2*b^2 = d*(a+b) := by
      apply Nat.sub_eq_of_eq_add
      rw [← eq,hd]
      ring
    have pm := good.2 b lt
    rw [diff] at pm
    rcases Nat.prime_mul_iff.mp pm with ⟨_,one⟩|⟨pt,one⟩
    · have small : a = 1 ∧ b = 0 := by omega
      rw [small.1,small.2] at eq
      norm_num at eq
      omega
    · refine ⟨a+b,pt,pt.odd_of_ne_two (by omega),?_⟩
      rw [one] at hd
      rw [← eq,hd]
      ring
  rcases le_total a b with ab|ba
  · exact go b a ab (by rwa [add_comm])
  · exact go a b ba h

lemma inert (n t : ℕ) (shape : 2*n=t^2+1) (good : Erdos1140Prop n)
    (q : ℕ) (hq : q.Prime) (hodd : 2<q) (hlt : q<t) :
    ¬ IsSquare ((2*n : ℕ) : ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  rintro ⟨y,hy⟩
  have oddq := hq.odd_of_ne_two (by omega)
  have rep : ∃ r : ℕ, 2*r<q ∧ (((2*r : ℕ) : ZMod q) = y ∨ ((2*r : ℕ) : ZMod q) = -y) := by
    have yl := y.val_lt
    by_cases even : Even y.val
    · obtain ⟨r,hr⟩ := even
      exact ⟨r,by omega,Or.inl (by rw [show 2*r=y.val by omega,ZMod.natCast_zmod_val])⟩
    · have yn : y ≠ 0 := fun h => even (by simp [h])
      letI : NeZero y := ⟨yn⟩
      have ynv := ZMod.val_neg_of_ne_zero y
      obtain ⟨a,ha⟩ := oddq
      have yo : y.val % 2 ≠ 0 := fun eq => even (Nat.even_iff.mpr eq)
      have ev : Even (-y).val := by
        rw [ynv,Nat.even_iff]
        omega
      obtain ⟨r,hr⟩ := ev
      exact ⟨r,by have := (-y).val_lt; omega,Or.inr (by rw [show 2*r=(-y).val by omega,ZMod.natCast_zmod_val])⟩
  obtain ⟨r,hr,rep⟩ := rep
  have hs : (((2*r : ℕ) : ZMod q))^2 = ((2*n : ℕ) : ZMod q) := by
    rcases rep with h|h <;> rw [h,hy] <;> ring
  push_cast at hs
  have two : (2 : ZMod q) ≠ 0 := fun he =>
    (not_le_of_gt hodd) (Nat.le_of_dvd (by decide : 0<2) ((ZMod.natCast_eq_zero_iff 2 q).mp he))
  have eqm : (2*r^2 ≡ n [MOD q]) := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    push_cast
    apply mul_left_cancel₀ two
    linear_combination hs
  have nq : 2*r^2+q<n := by
    have h1 : (2*r+1)^2 ≤ q^2 := Nat.pow_le_pow_left (by omega) _
    have h2 : (q+1)^2 ≤ t^2 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have dv := (Nat.modEq_iff_dvd' (by omega : 2*r^2≤n)).mp eqm
  have eq := (Nat.prime_dvd_prime_iff_eq hq (good.2 r (by omega))).mp dv
  omega

theorem main : H1 → H2 → OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1.H1 := by
  intro class_two classification n big hp residue criterion
  have good := (OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1.sieve_iff n hp.pos).mpr criterion
  obtain ⟨t,ht,ho,form⟩ := shape n big hp (by omega) good
  have no (a b : ℕ) : n ≠ a^2+2*b^2 := by
    intro eqn
    by_cases ha : a=0
    · have hd : 2 ∣ n := ⟨b^2,by simpa [ha] using eqn⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
      omega
    have pa := good.2 b (by nlinarith [Nat.pos_of_ne_zero ha])
    have e : n-2*b^2=a^2 := by omega
    rw [e] at pa
    have := (pa.pow_eq_iff.mp (rfl : a^2=a^2)).2
    omega
  obtain ⟨K,_,_,s,hs,hgen,hnum⟩ := class_two n t hp ht ho form (inert n t form good) no
  have hle := classification n t hp ht ho form K s hs hgen hnum
  have bd := Nat.pow_le_pow_left hle 2
  norm_num at bd
  omega

end OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H1_R1
