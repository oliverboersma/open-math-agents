import OMAReductions.R_BealConjecture_beal_conjecture_R1_H1_R1
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas

-- Credit: @Hennyrick

namespace OMA.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1

/-- Remaining primitive solutions of the mixed signature after imposing the
six congruence classes when the fifth-power base is divisible by five. -/
def H1 : Prop :=
  ∀ {a b c p : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b → p.Prime →
    109 < p → b%2 = 1 → b.Coprime 15 → ¬3 ∣ c → 29 ∣ a*c →
    (11 ∣ c ∨ 19 ∣ a) →
    ((5 ∣ a ∧ p%4 = 3) → c%25 ∈ [1,4,11,14,21,24]) → a^5+b^p ≠ c^3

/-- CM local conditions at primes dividing the variable base. The first
conclusion treats the coefficient prime. The second compares the induced
trace with the multiplicative trace at an inert prime of residue degree two.
See Pacetti–Villagra Torcomian, formula (40), arXiv:2512.17845, and Jaswal,
"The equation x^5 + y^3 = z^p", sections 2.4, 6.2 and 6.4. -/
def H2 : Prop :=
  ∀ {a b c p : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b → p.Prime →
    109 < p → b%2 = 1 → b.Coprime 15 → ¬3 ∣ c → 29 ∣ a*c →
    (11 ∣ c ∨ 19 ∣ a) → a^5+b^p = c^3 → 5 ∣ a → p%4 = 3 →
    (¬p ∣ b ∨ p%5 = 1 ∨ p%5 = 4) ∧
    ∀ l : Nat, l.Prime → l ∣ b → 5 < l → l ≠ p →
      (l%5 = 2 ∨ l%5 = 3) → p ∣ l^2+1

/-- The eight classes of the cubic base excluded by Manvir Jaswal's
Theorem 6.15, under the inputs in his section 2.5. Set X=a, Y=-c, Z=-b.
https://manvirjaswal.github.io/papers/x5-y3-zp/jaswal-x5y3zp.pdf -/
def H3 : Prop :=
  ∀ {a b c p : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b → p.Prime →
    109 < p → b%2 = 1 → b.Coprime 15 → ¬3 ∣ c → 29 ∣ a*c →
    (11 ∣ c ∨ 19 ∣ a) → a^5+b^p = c^3 → 5 ∣ a →
    c%25 ∉ [6,8,9,12,13,16,17,19]

open scoped Fin.NatCast Fin.IntCast Fin.CommRing

private theorem never_square_minus_one {p l : ℕ} (hp : p.Prime) (hmod : p%4=3) :
    ¬ p ∣ l^2+1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  have frob (x : ℕ) : (x : Fin p)^p = (x : Fin p) := by
    induction x with
    | zero => simp [hp.ne_zero]
    | succ x ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]
  intro h
  have hz : ((l^2+1 : ℕ) : Fin p) = 0 := Fin.natCast_eq_zero.mpr h
  push_cast at hz
  have he : (l : Fin p)^2 = -1 := eq_neg_of_add_eq_zero_left hz
  let k := p/4
  have hp4 : p = 2*(2*k+1)+1 := by dsimp [k]; omega
  have hs : (l : Fin p) = -(l : Fin p) := by
    calc
      (l : Fin p) = (l : Fin p)^p := (frob l).symm
      _ = ((l : Fin p)^2)^(2*k+1)*(l : Fin p) := by
        conv_lhs => arg 2; rw [hp4]
        rw [pow_succ, pow_mul]
      _ = -(l : Fin p) := by rw [he, pow_succ, pow_mul, neg_one_sq]; simp
  have hh := congrArg (fun x : Fin p => x*l) hs
  change (l : Fin p)*l = (-(l : Fin p))*l at hh
  rw [neg_mul, ← pow_two, he, neg_neg] at hh
  have h2 : ((2 : ℕ) : Fin p) = 0 := by
    change (2 : Fin p) = 0
    rw [← one_add_one_eq_two]
    nth_rw 1 [← hh]
    exact neg_add_cancel _
  have hd := Fin.natCast_eq_zero.mp h2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega


private theorem nonresidue_factor (B : ℕ) (hB : B%5=2 ∨ B%5=3) :
    ∃ l : ℕ, l.Prime ∧ l ∣ B ∧ (l%5=2 ∨ l%5=3) := by
  induction B using Nat.strong_induction_on with
  | h B ih =>
    have hne : B ≠ 1 := by omega
    obtain ⟨l, hl, k, h⟩ := Nat.exists_prime_and_dvd hne
    by_cases hr : l%5=2 ∨ l%5=3
    · exact ⟨l, hl, ⟨k,h⟩, hr⟩
    · have ht : ∀ a b : Fin 5, (a.val*b.val%5=2 ∨ a.val*b.val%5=3) →
          ¬(a.val=2 ∨ a.val=3) → b.val=2 ∨ b.val=3 := by decide
      have hk : k%5=2 ∨ k%5=3 := by
        apply ht ⟨l%5, Nat.mod_lt _ (by decide)⟩ ⟨k%5, Nat.mod_lt _ (by decide)⟩ _ hr
        rwa [h,Nat.mul_mod] at hB
      have hkl : k < B := by
        have := hl.two_le
        have := Nat.mul_le_mul_right k this
        omega
      obtain ⟨m,hm,hd,hmr⟩ := ih k hkl hk
      exact ⟨m,hm,hd.trans (h ▸ dvd_mul_left k l),hmr⟩

/-- A prime divisor detected by the quadratic character modulo five also
violates the geometric congruence l² = -1 modulo p. -/
theorem exists_obstructing_prime_mod_four {p B : ℕ} (hp : p.Prime)
    (hr : p%4=3) (hexc : ¬p ∣ B ∨ p%5=1 ∨ p%5=4)
    (hc : B.Coprime 30) (h1 : B%5 ≠ 1) (h4 : B%5 ≠ 4) :
    ∃ l : ℕ, l.Prime ∧ l ∣ B ∧ 5 < l ∧ l ≠ p ∧
      (l%5=2 ∨ l%5=3) ∧ ¬p ∣ l^2+1 := by
  have h5 : B%5 ≠ 0 := by
    intro hz
    have := hc.coprime_dvd_left (Nat.dvd_of_mod_eq_zero hz)
    exact (by decide : ¬Nat.Coprime 5 30) this
  obtain ⟨l,hl,hd,hm⟩ := nonresidue_factor B (by omega)
  have hgt : 5 < l := by
    have hlc := hc.coprime_dvd_left hd
    have h2 : l ≠ 2 := by rintro rfl; exact (by decide : ¬Nat.Coprime 2 30) hlc
    have h3 : l ≠ 3 := by rintro rfl; exact (by decide : ¬Nat.Coprime 3 30) hlc
    omega
  have hne : l ≠ p := by
    rintro rfl
    rcases hexc with h | h | h
    · exact h hd
    · omega
    · omega
  exact ⟨l,hl,hd,hgt,hne,hm,never_square_minus_one hp hr⟩

/-- The inputs concerning CM representations are expressed as a condition on
the prime divisors of B. -/
theorem residue_of_prime_divisor_condition_mod_four {p B : ℕ} (hp : p.Prime)
    (hr : p%4=3) (hexc : ¬p ∣ B ∨ p%5=1 ∨ p%5=4) (hc : B.Coprime 30)
    (hcm : ∀ l : ℕ, l.Prime → l ∣ B → 5 < l → l ≠ p →
      (l%5=2 ∨ l%5=3) → p ∣ l^2+1) :
    B%5=1 ∨ B%5=4 := by
  by_contra! h
  obtain ⟨l,hl,hd,hgt,hne,hm,hnot⟩ := exists_obstructing_prime_mod_four hp hr hexc hc h.1 h.2
  exact hnot (hcm l hl hd hgt hne hm)

private theorem powers_of_zero_one_four {b : Nat}
    (hb : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 4) (n : Nat) :
    b ^ n % 5 = 0 ∨ b ^ n % 5 = 1 ∨ b ^ n % 5 = 4 := by
  induction n with
  | zero => exact Or.inr (Or.inl (by simp))
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;>
      rcases hb with k | k | k <;> rw [k] <;> decide

theorem equation_forces_residue {A B C p : Nat} (ha : 5 ∣ A)
    (hc : C % 5 = 2 ∨ C % 5 = 3) (he : A ^ 5 + B ^ p = C ^ 3) :
    B % 5 = 2 ∨ B % 5 = 3 := by
  have hm := congrArg (fun n : Nat => n % 5) he
  change (A ^ 5 + B ^ p) % 5 = C ^ 3 % 5 at hm
  rw [Nat.add_mod, Nat.pow_mod A, Nat.mod_eq_zero_of_dvd ha, Nat.pow_mod C] at hm
  have hres : B ^ p % 5 = 2 ∨ B ^ p % 5 = 3 := by
    rcases hc with h | h <;> rw [h] at hm <;> omega
  by_contra h
  have hb : B % 5 = 0 ∨ B % 5 = 1 ∨ B % 5 = 4 := by omega
  have := powers_of_zero_one_four hb p
  omega

/-- All and only the residues left by the two local restrictions. -/
theorem six_classes_iff : ∀ r : Fin 25,
    ((r.val%5=1 ∨ r.val%5=4) ∧ r.val ∉ [6,8,9,12,13,16,17,19]) ↔
    r.val ∈ [1,4,11,14,21,24] := by decide

/-- The two inputs are the variable-prime congruence and the eight
classes excluded under the hypotheses of Jaswal's Theorem 6.15. -/
theorem six_classes_of_equation {A B C p : ℕ} (hp : p.Prime) (hr : p%4=3)
    (hexc : ¬p ∣ B ∨ p%5=1 ∨ p%5=4) (hc : B.Coprime 30)
    (hcm : ∀ l : ℕ, l.Prime → l ∣ B → 5 < l → l ≠ p →
      (l%5=2 ∨ l%5=3) → p ∣ l^2+1)
    (ha : 5 ∣ A) (he : A^5+B^p = C^3)
    (hJ : C%25 ∉ [6,8,9,12,13,16,17,19]) :
    C%25 ∈ [1,4,11,14,21,24] := by
  have hB := residue_of_prime_divisor_condition_mod_four hp hr hexc hc hcm
  have hn : C%5 ≠ 0 := by
    intro hz
    have hC := Nat.dvd_of_mod_eq_zero hz
    have hA5 : 5 ∣ A^5 := by rw [pow_succ]; exact dvd_mul_of_dvd_right ha _
    have hC3 : 5 ∣ C^3 := by rw [pow_succ]; exact dvd_mul_of_dvd_right hC _
    have hBp := (Nat.dvd_add_right hA5).mp (he ▸ hC3)
    have h5 := (by decide : Nat.Prime 5).dvd_of_dvd_pow hBp
    have := Nat.mod_eq_zero_of_dvd h5
    omega
  have hC : C%5=1 ∨ C%5=4 := by
    by_contra h
    have := equation_forces_residue ha (show C%5=2 ∨ C%5=3 by omega) he
    omega
  apply (six_classes_iff ⟨C%25, Nat.mod_lt _ (by decide)⟩).mp
  exact ⟨by change C%25%5=1 ∨ C%25%5=4; omega, hJ⟩

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R1_H1_R1.H3 := by
  intro remaining localCM excluded a b c p ha hb hc hab hp h109 hodd h15 h3 h29 hsplit he
  apply remaining ha hb hc hab hp h109 hodd h15 h3 h29 hsplit _ he
  intro ⟨h5,h4⟩
  obtain ⟨hexc,hprimes⟩ := localCM ha hb hc hab hp h109 hodd h15 h3 h29 hsplit he h5 h4
  have h2 : b.Coprime 2 := by
    change Nat.gcd b 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec 2 b, hodd]
    decide
  exact six_classes_of_equation hp h4 hexc (h2.mul_right h15) hprimes h5 he
    (excluded ha hb hc hab hp h109 hodd h15 h3 h29 hsplit he h5)

end OMA.R_BealConjecture_beal_conjecture_R1_H1_R1_H3_R1
