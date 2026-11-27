import OMAReductions.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1

/-! Epure and Gica (2010), Remark 2, and the Mollin–Williams classification of
principal real quadratic orders of Richaud–Degert type. We prove the required
near-square shape by taking the nearest even integer to the square root of 2n.
A centered square root modulo a small odd prime rules out every nontrivial
prime divisor of the error. The sieve equivalence in the parent is by @TheWaler. -/

open Erdos1140
namespace OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H2_R1

private lemma square_mod (x : ℕ) : x^2%8=0 ∨ x^2%8=1 ∨ x^2%8=4 := by
  have h : ∀ a : Fin 8, a.val^2%8=0 ∨ a.val^2%8=1 ∨ a.val^2%8=4 := by decide
  simpa [Nat.pow_mod] using h ⟨x%8,Nat.mod_lt _ (by decide)⟩

private lemma no_root {n : ℕ} (res : n%4=3) (prop : Erdos1140Prop n)
    {p : ℕ} (hp : p.Prime) (odd : p ≠ 2) (le : p^2 ≤ 2*n) (a : ZMod p) :
    2*a^2 ≠ (n : ZMod p) := by
  intro eq
  let _ : Fact p.Prime := ⟨hp⟩
  let r := a.valMinAbs.natAbs
  have hr : r ≤ p/2 := ZMod.natAbs_valMinAbs_le a
  have oddp := hp.eq_two_or_odd.resolve_left odd
  have pr : 2*r+1 ≤ p := by omega
  have sp := square_mod p
  have gap : p^2+1 < 2*n := by omega
  have hsq := Nat.pow_le_pow_left pr 2
  have room : 2*r^2+p < n := by
    zify at pr gap ⊢
    nlinarith [mul_nonneg (show 0 ≤ (p:ℤ) - (2*r+1) by omega)
      (show 0 ≤ (p:ℤ) + (2*r+1) - 2 by omega)]
  have er : 2*(r:ZMod p)^2=(n:ZMod p) := by
    change 2*(a.valMinAbs.natAbs:ZMod p)^2 = _
    rw [ZMod.natCast_natAbs_valMinAbs]
    split <;> simpa using eq
  have hd : p ∣ n-2*r^2 := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [er,sub_self]
  have prime := prop.2 r (by omega)
  have e := (Nat.prime_dvd_prime_iff_eq hp prime).mp hd
  omega

private lemma nearest (n : ℕ) : ∃ k d : ℕ, d ≤ (2*n).sqrt ∧
    (n=2*k^2+d ∨ 2*k^2=n+d) := by
  let s := (2*n).sqrt
  let j := s/2
  have lo : s^2 ≤ 2*n := Nat.sqrt_le' _
  have hi : 2*n < (s+1)^2 := Nat.lt_succ_sqrt' _
  have cases : s=2*j ∨ s=2*j+1 := by dsimp [j]; omega
  rcases cases with e | e
  · rw [e] at lo hi
    have low : 2*j^2 ≤ n := by nlinarith
    refine ⟨j,n-2*j^2,?_,Or.inl (by omega)⟩
    change n-2*j^2 ≤ s
    rw [e]
    have up : n ≤ 2*j^2+2*j := by nlinarith
    omega
  · rw [e] at lo hi
    have up : n ≤ 2*(j+1)^2 := by nlinarith
    refine ⟨j+1,2*(j+1)^2-n,?_,Or.inr (by omega)⟩
    change 2*(j+1)^2-n ≤ s
    rw [e]
    have h : 2*(j+1)^2 ≤ n+(2*j+1) := by nlinarith
    omega

private lemma shape {n : ℕ} (res : n%4=3) (prop : Erdos1140Prop n)
    (one : ∀ x : ℕ, n ≠ 2*x^2+1) : ∃ y : ℕ, 2*n+2=(4*y)^2 := by
  obtain ⟨k,d,le,h⟩ := nearest n
  have odd : d%2=1 := by rcases h with h|h <;> omega
  have d1 : d=1 := by
    by_contra hn
    let p := d.minFac
    have hp : p.Prime := Nat.minFac_prime hn
    have pd : p ∣ d := Nat.minFac_dvd _
    have pn : p ≠ 2 := by intro e; rw [e] at pd; omega
    have small : p^2 ≤ 2*n := Nat.le_sqrt'.mp ((Nat.le_of_dvd (by omega) pd).trans le)
    apply no_root res prop hp pn small (k : ZMod p)
    have zero := (ZMod.natCast_eq_zero_iff d p).mpr pd
    rcases h with h | h
    · have e := congrArg (fun x : ℕ => (x : ZMod p)) h
      push_cast at e
      simpa [zero] using e.symm
    · have e := congrArg (fun x : ℕ => (x : ZMod p)) h
      push_cast at e
      simpa [zero] using e
  subst d
  rcases h with h | h
  · exact (one k h).elim
  have ke : k%2=0 := by
    have ks := square_mod k
    by_contra hn
    have : k^2%2=1 := by rw [Nat.pow_mod]; simp [show k%2=1 by omega]
    omega
  refine ⟨k/2,?_⟩
  have ek : k=2*(k/2) := by omega
  conv_lhs at h => rw [ek]
  nlinarith

/-- Minkowski's bound for this real quadratic order is sqrt(2n). The small
odd primes are inert and the displayed norm-two element handles the ramified prime. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Prime → n%4=3 → (∃ y : ℕ, 2*n+2=(4*y)^2) →
    (∀ p : ℕ, p.Prime → p ≠ 2 → p^2 ≤ 2*n → ∀ a : ZMod p, 2*a^2 ≠ (n:ZMod p)) →
    IsPrincipalIdealRing (Zsqrtd (2*(n:ℤ)))

/-- The class-number-one classification in the indicated Richaud–Degert family,
after removing the three known values 14, 62 and 398 of the radicand. -/
def H2 : Prop :=
  {m : ℕ | 398 < m ∧ (∃ y : ℕ, m+2=(4*y)^2) ∧ Squarefree m ∧
    IsPrincipalIdealRing (Zsqrtd (m:ℤ))}.Subsingleton

theorem main : H1 → H2 → OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1.H2 := by
  intro princip classify
  have lift {n : ℕ} (h : 199<n ∧ n.Prime ∧ (n%60=19 ∨ n%60=31) ∧
      (∀ x : ℕ, n ≠ 2*x^2+1) ∧ ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2*r^2+p<n → ¬ (2*r^2 ≡ n [MOD p])) :
      398<2*n ∧ (∃ y : ℕ, 2*n+2=(4*y)^2) ∧ Squarefree (2*n) ∧
        IsPrincipalIdealRing (Zsqrtd ((2*n:ℕ):ℤ)) := by
    obtain ⟨hn,hp,r,one,sieve⟩ := h
    have res : n%4=3 := by omega
    have prop := (OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1.sieve_iff n (by omega)).2 ⟨one,sieve⟩
    have e := shape res prop one
    have cop : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    refine ⟨by omega,e,?_,?_⟩
    · exact (Nat.squarefree_mul cop).mpr ⟨Nat.prime_two.squarefree,hp.squarefree⟩
    · simpa using princip n hp res e (fun _ hp hn le a => no_root res prop hp hn le a)
  intro a ha b hb
  have e := classify (lift ha) (lift hb)
  omega

end OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H2_R1

