import FormalConjectures.ErdosProblems.«978»
import Mathlib

/-! For a primitive polynomial of degree d, a fixed divisor divides d!.
We use this to discharge all local obstructions and separate the sieve on
(N, 2N] at the prime cutoff N. -/

namespace OMA.R_Erdos978_erdos_978_variants_sub_one_R1

open Polynomial

/-- The top finite difference extracts the leading coefficient times the factorial. -/
lemma fixed_dvd_leading_factorial (f : ℤ[X]) (q : ℤ)
    (fixed : ∀ n : ℕ, q ∣ f.eval (n : ℤ)) :
    q ∣ f.leadingCoeff * (f.natDegree.factorial : ℤ) := by
  have h := congrFun f.fwdDiff_iter_degree_eq_factorial (0 : ℤ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  have divides : q ∣ ∑ k ∈ Finset.range (f.natDegree + 1),
      ((-1 : ℤ) ^ (f.natDegree - k) * f.natDegree.choose k) • f.eval (0 + k • (1 : ℤ)) := by
    apply Finset.dvd_sum
    intro k _
    simp only [nsmul_eq_mul, mul_one, zero_add, zsmul_eq_mul, Int.cast_id]
    exact
      dvd_mul_of_dvd_right (fixed k) ((-1 : ℤ) ^ (f.natDegree - k) * f.natDegree.choose k)
  rw [h] at divides
  exact divides

/-- Removing the leading falling factorial preserves the fixed divisor at every
natural input. Induction then clears the denominators of the Newton basis. -/
lemma fixed_dvd_scaled (f : ℤ[X]) (q : ℤ) (D : ℕ) (bound : f.natDegree ≤ D)
    (fixed : ∀ n : ℕ, q ∣ f.eval (n : ℤ)) :
    C q ∣ C (D.factorial : ℤ) * f := by
  by_cases hf : f = 0
  · simp [hf]
  let d := f.natDegree
  let head := C f.leadingCoeff * descPochhammer ℤ d
  let tail := f - head
  have top := fixed_dvd_leading_factorial f q fixed
  have hhead (n : ℕ) : q ∣ head.eval (n : ℤ) := by
    dsimp only [head]
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc]
    exact dvd_mul_of_dvd_left top _
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial bound
  have htop : q ∣ (D.factorial : ℤ) * f.leadingCoeff := by
    rw [hm, Nat.cast_mul]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using dvd_mul_of_dvd_left top (m : ℤ)
  have hscaled : C q ∣ C (D.factorial : ℤ) * head := by
    dsimp only [head]
    rw [← mul_assoc, ← map_mul]
    exact dvd_mul_of_dvd_left (map_dvd C htop) _
  have htail : C q ∣ C (D.factorial : ℤ) * tail := by
    by_cases ht : tail = 0
    · simp [ht]
    have hdeg : head.degree = f.degree := by
      rw [degree_eq_natDegree (show head ≠ 0 from mul_ne_zero
        (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)) (monic_descPochhammer ℤ d).ne_zero),
        degree_eq_natDegree hf]
      apply congrArg (fun n : ℕ => (n : WithBot ℕ))
      change (C f.leadingCoeff * descPochhammer ℤ d).natDegree = d
      rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hf), descPochhammer_natDegree]
    have hlc : head.leadingCoeff = f.leadingCoeff :=
      (monic_descPochhammer ℤ d).leadingCoeff_C_mul _
    have hlt : tail.natDegree < f.natDegree := (natDegree_lt_natDegree_iff ht).mpr
      (degree_sub_lt_left hdeg.symm hf hlc.symm)
    exact fixed_dvd_scaled tail q D (hlt.le.trans bound)
      (fun n => by simpa [tail] using dvd_sub (fixed n) (hhead n))
  simpa only [← mul_add, sub_add_cancel, tail] using dvd_add htail hscaled
termination_by f.natDegree

lemma fixed_dvd_factorial {f : ℤ[X]} (prim : f.IsPrimitive) (q : ℤ)
    (fixed : ∀ n : ℕ, q ∣ f.eval (n : ℤ)) : q ∣ (f.natDegree.factorial : ℤ) := by
  have h := dvd_content_iff_C_dvd.mpr (fixed_dvd_scaled f q f.natDegree le_rfl fixed)
  rw [content_C_mul, prim.content_eq_one, mul_one] at h
  simpa using h

/-- For binary factorial valuations equality with d-1 forces d to be a power of two. -/
lemma two_factorial_bound (d : ℕ) (hd : 2 < d) (hp : ∀ e : ℕ, d ≠ 2 ^ e) :
    padicValNat 2 d.factorial < d - 1 := by
  let m := d / 2
  have hm : 0 < m := by dsimp [m]; omega
  have decomp : d = 2 * m + d % 2 := by dsimp [m]; omega
  have v : padicValNat 2 d.factorial = padicValNat 2 m.factorial + m := by
    rw [← padicValNat_mul_div_factorial (p := 2) d, padicValNat_factorial_mul]
  rw [v]
  by_cases he : d % 2 = 0
  · have even : d = 2 * m := by omega
    have m_two : 2 < m := by have := hp 2; norm_num at this; omega
    have not_pow (e : ℕ) : m ≠ 2 ^ e := by
      intro h
      apply hp (e + 1)
      rw [even, h, pow_succ, mul_comm]
    have := two_factorial_bound m m_two not_pow
    omega
  · have := padicValNat_factorial_lt_of_ne_zero 2 hm.ne'
    omega
termination_by d
decreasing_by omega

lemma local_admissibility {f : ℤ[X]} (hi : Irreducible f) (hd : 2 < f.natDegree)
    (degrees : ∀ e : ℕ, f.natDegree ≠ 2 ^ e) (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ) := by
  by_contra! fixed
  have hj := fixed_dvd_factorial (hi.isPrimitive (by omega)) _ fixed
  have hnat : p ^ (f.natDegree - 1) ∣ f.natDegree.factorial := by exact_mod_cast hj
  have : Fact p.Prime := ⟨hp⟩
  have lower := (padicValNat_dvd_iff_le (p := p) (Nat.factorial_ne_zero _)).mp hnat
  by_cases he : p = 2
  · subst p
    exact (two_factorial_bound _ hd degrees).not_ge lower
  · have big : 2 ≤ p - 1 := by have := hp.two_le; omega
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : f.natDegree ≠ 0)
    have h' := Nat.mul_le_mul_right (padicValNat p f.natDegree.factorial) big
    omega

open scoped Classical

/-- After each prime has one allowed residue, the sieve up to N leaves a
positive proportion of the integers in (N, 2N]. -/
def H1 : Prop :=
  ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
    (∀ p : ℕ, p.Prime → ∃ a : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (a : ℤ)) →
    ∃ A : ℕ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      N ≤ A * ((Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ N → ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)).card

/-- The inputs lost to a prime larger than N have arbitrarily small relative
frequency along arbitrarily large dyadic intervals. -/
def H2 : Prop :=
  ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
    (∀ e : ℕ, f.natDegree ≠ 2 ^ e) → 0 < f.leadingCoeff →
    ∀ A : ℕ, 0 < A → ∀ L : ℕ, ∃ N ≥ L,
      A * ((Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)).card < N

theorem main : H1 → H2 → type_of% @Erdos978.erdos_978.variants.sub_one := by
  intro small large f hi hd hpow hlc
  obtain ⟨A, hA, N₀, hsmall⟩ := small f hi hd (local_admissibility hi hd hpow)
  apply Set.infinite_of_forall_exists_gt
  intro L
  obtain ⟨N, hN, hlarge⟩ := large f hi hd hpow hlc A hA (max L N₀)
  have hcard := hlarge.trans_le (hsmall N ((le_max_right L N₀).trans hN))
  obtain ⟨n, good, unmarked⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (Nat.lt_of_mul_lt_mul_left hcard)
  obtain ⟨inInterval, avoidsSmall⟩ := Finset.mem_filter.mp good
  refine ⟨n, ?_, ((le_max_left L N₀).trans hN).trans_lt (Finset.mem_Ioc.mp inInterval).1⟩
  intro x hx
  by_contra nonunit
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (mt Int.isUnit_iff_natAbs_eq.mpr nonunit)
  have hit := (pow_dvd_pow_of_dvd (Int.natCast_dvd.mpr hpx) _).trans hx
  rcases le_or_gt p N with h | h
  · exact avoidsSmall p hp h hit
  · exact unmarked (Finset.mem_filter.mpr ⟨inInterval, p, hp, h, hit⟩)

end OMA.R_Erdos978_erdos_978_variants_sub_one_R1
