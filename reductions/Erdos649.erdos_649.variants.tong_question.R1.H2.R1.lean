import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Squarefree

/-!
The Størmer transformation encodes consecutive smooth numbers n,n+1 by
x = 2n+1, y = 2w, where n(n+1) = D w² with D squarefree. Only divisors
of the primorial of p can occur as D. For each D there is at most one
positive fundamental unit. A primitive prime divisor of its kth Lucas
term has rank k and hence size at least k-1, giving the index cutoff.

H1 isolates this consequence of Bilu, Hanrot and Voutier, "Existence of
primitive divisors of Lucas and Lehmer numbers" (2001). H2 asks for
infinitely many primes passing a finite test of the individual halves.
-/

namespace OMA.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1

/-- The existence of a primitive prime divisor for large Pell powers. -/
def H1 : Prop := ∀ (D : ℕ) (u : Pell.Solution₁ (D:ℤ)), Pell.IsFundamental u →
  ∀ k : ℕ, 30 < k → ∃ r : ℕ, r.Prime ∧ r ∣ (u^k).y.natAbs ∧
    ∀ j : ℕ, 0 < j → j < k → ¬ r ∣ (u^j).y.natAbs

/-- For fixed p the radicands divide its primorial and the indices are bounded.
Fundamental solutions are unique when they exist. -/
def H2 : Prop := ∀ q : ℕ, q.Prime → Odd q →
  {p : ℕ | p.Prime ∧ q < p ∧ ∀ D : ℕ, D ∣ primorial p →
    ∀ u : Pell.Solution₁ (D:ℤ), Pell.IsFundamental u →
    ∀ k : ℕ, 0 < k → k ≤ max 30 (p+1) →
      let x := (u^k).x.natAbs
      Odd x → ((x-1)/2).maxPrimeFac ≠ p ∨ ((x+1)/2).maxPrimeFac ≠ q}.Infinite

section Proof

/-- Before the first vanishing y-coordinate modulo r, the powers have
distinct projective slopes. There are only r affine slopes and infinity. -/
private theorem first_prime_rank {D : ℤ} (u : Pell.Solution₁ D) {r k : ℕ} (hr : r.Prime)
    (hfirst : ∀ j : ℕ, 0 < j → j < k → ¬ r ∣ (u^j).y.natAbs) : k ≤ r+1 := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let X (i : ℕ) : ZMod r := (u^i).x
  let Y (i : ℕ) : ZMod r := (u^i).y
  let slope (i : ℕ) : Option (ZMod r) := if Y i = 0 then none else some (X i/Y i)
  have cross {i j : ℕ} (h : slope i = slope j) : X i*Y j = X j*Y i := by
    by_cases hi : Y i = 0 <;> by_cases hj : Y j = 0
    · simp [hi,hj]
    · simp [slope,hi,hj] at h
    · simp [slope,hi,hj] at h
    · have he : X i/Y i = X j/Y j := by simpa [slope,hi,hj] using h
      exact (div_eq_div_iff hi hj).mp he
  have separate {i j : ℕ} (hij : i < j) (hj : j < k) (he : slope i = slope j) : False := by
    have e := cross he
    have hz : ((u^(j-i)).y : ZMod r) = 0 := by
      rw [pow_sub u hij.le,Pell.Solution₁.y_mul,Pell.Solution₁.x_inv,Pell.Solution₁.y_inv]
      push_cast
      change X j * -Y i + Y j * X i = 0
      linear_combination e
    exact hfirst (j-i) (by omega) (by omega)
      (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
  have hinj : Function.Injective (fun i : Fin k => slope i.val) := by
    intro i j he
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact separate h j.isLt he
    · exact separate h i.isLt he.symm
  simpa using Fintype.card_le_of_injective _ hinj

private theorem squarefree_dvd_primorial {D p : ℕ} (hD : Squarefree D)
    (h : ∀ r : ℕ, r.Prime → r ∣ D → r ≤ p) : D ∣ primorial p := by
  rw [← Nat.prod_primeFactors_of_squarefree hD,primorial_eq_prod_primesLE]
  apply Finset.prod_dvd_prod_of_subset
  intro r hr
  exact Nat.mem_primesLE.mpr ⟨h r (Nat.prime_of_mem_primeFactors hr)
    (Nat.dvd_of_mem_primeFactors hr), Nat.prime_of_mem_primeFactors hr⟩

private theorem pell_witness (large : H1) {p q n : ℕ}
    (hp : p.Prime) (hqp : q < p)
    (hn : n.maxPrimeFac = p) (hn' : (n+1).maxPrimeFac = q) :
    ∃ D : ℕ, D ∣ primorial p ∧ ∃ u : Pell.Solution₁ (D:ℤ), Pell.IsFundamental u ∧
      ∃ k : ℕ, 0 < k ∧ k ≤ max 30 (p+1) ∧ (u^k).x.natAbs = 2*n+1 := by
  have hn1 : 1 < n := (Nat.one_lt_maxPrimeFac_iff n).mp (hn ▸ hp.one_lt)
  have hprod (r : ℕ) (hr : r.Prime) (h : r ∣ n*(n+1)) : r ≤ p := by
    rcases hr.dvd_mul.mp h with h | h
    · exact (Nat.le_maxPrimeFac (by omega) hr h).trans_eq hn
    · exact ((Nat.le_maxPrimeFac (by omega) hr h).trans_eq hn').trans hqp.le
  obtain ⟨D,w,hD,hw,hsq,hsf⟩ := Nat.sq_mul_squarefree_of_pos
    (show 0 < n*(n+1) by positivity)
  have hdvd : D ∣ n*(n+1) := hsq ▸ dvd_mul_left D (w^2)
  have hwdvd : w ∣ n*(n+1) := by rw [← hsq,pow_two]; exact dvd_mul_of_dvd_left (dvd_mul_right w w) D
  have hprim := squarefree_dvd_primorial hsf (fun r hr h => hprod r hr (h.trans hdvd))
  have hZ : (w:ℤ)^2 * D = (n:ℤ)*(n+1) := by exact_mod_cast hsq
  let a := @Pell.Solution₁.mk (D:ℤ) (2*(n:ℤ)+1) (2*(w:ℤ)) (by nlinarith only [hZ])
  have hx : 1 < a.x := by change 1 < 2*(n:ℤ)+1; omega
  have hy : 0 ≤ a.y := by change 0 ≤ 2*(w:ℤ); positivity
  obtain ⟨u,hu⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x hx) (Pell.Solution₁.d_nonsquare_of_one_lt_x hx)
  obtain ⟨k,hk⟩ := hu.eq_pow_of_nonneg (zero_lt_one.trans hx) hy
  have hkpos : 0 < k := by
    by_contra! h
    have h0 := hk.trans (show u^k = 1 by rw [Nat.eq_zero_of_le_zero h,pow_zero])
    rw [h0,Pell.Solution₁.x_one] at hx
    omega
  have hbound : k ≤ max 30 (p+1) := by
    by_cases h : k ≤ 30
    · exact h.trans (le_max_left _ _)
    obtain ⟨r,hr,hrd,hfirst⟩ := large D u hu k (by omega)
    have hrk := first_prime_rank u hr hfirst
    rw [← hk] at hrd
    change r ∣ (2*(w:ℤ)).natAbs at hrd
    have hwabs : (2*(w:ℤ)).natAbs = 2*w := by exact_mod_cast (Int.natAbs_natCast (2*w))
    have hrw : r ∣ 2*w := hwabs ▸ hrd
    have hrp : r ≤ p := by
      rcases hr.dvd_mul.mp hrw with h2 | hw'
      · exact (Nat.le_of_dvd (by decide : 0<2) h2).trans hp.two_le
      · exact hprod r hr (hw'.trans hwdvd)
    exact (show k ≤ p+1 by omega).trans (le_max_right _ _)
  refine ⟨D,hprim,u,hu,k,hkpos,hbound,?_⟩
  rw [← hk]
  change (2*(n:ℤ)+1).natAbs = 2*n+1
  exact_mod_cast (Int.natAbs_natCast (2*n+1))

theorem main : H1 → H2 → OMA.R_Erdos649_erdos_649_variants_tong_question_R1.H2 := by
  intro large sieve q hq hodd
  apply (sieve q hq hodd).mono
  rintro p ⟨hp,hqp,havoid⟩
  have exclude (n : ℕ) (hn : n.maxPrimeFac = p) (hn' : (n+1).maxPrimeFac = q) : False := by
    obtain ⟨D,hD,u,hu,k,hk,hb,hx⟩ := pell_witness large hp hqp hn hn'
    have htest := havoid D hD u hu k hk hb
    dsimp only at htest
    rw [hx] at htest
    rcases htest ⟨n,by omega⟩ with h | h
    · exact h (by simpa only [show (2*n+1-1)/2=n by omega] using hn)
    · exact h (by simpa only [show (2*n+1+1)/2=n+1 by omega] using hn')
  refine ⟨hp,hqp,?_,?_⟩
  · intro hpure
    let e := orderOf (q : ZMod p)
    change (q^e-1).maxPrimeFac = p at hpure
    have he : e ≠ 0 := by
      intro h
      rw [h,pow_zero,Nat.sub_self,Nat.maxPrimeFac_zero] at hpure
      exact hp.ne_zero hpure.symm
    have hpos := pow_pos hq.pos e
    apply exclude (q^e-1) hpure
    rw [show q^e-1+1 = q^e by omega,Nat.maxPrimeFac_pow he,hq.maxPrimeFac_eq_self]
  · intro m hm _mixed hbad
    have hm1 := (Nat.one_lt_maxPrimeFac_iff m).mp (hm ▸ hq.one_lt)
    exact exclude (m-1) hbad (by simpa only [show m-1+1=m by omega] using hm)

end Proof

end OMA.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1
