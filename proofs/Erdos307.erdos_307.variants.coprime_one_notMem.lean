import FormalConjectures.ErdosProblems.«307»

-- Problem: Erdős Problem 307, coprime variant without 1.
-- Credit: @duggiephresh (Doug Phillips). The original solution: announced 26 November 2026 in
-- github.com/duggiephresh/unit-fraction-solutions and registered as PALOMAR-2026-11-26-000045
-- (Lean source: github.com/duggiephresh/palomar-unit-fractions, commit 27086794). This file is that
-- registered proof, with the module header removed and the namespace renamed to avoid clashing with
-- formal-conjectures. The solution, search and Lean proof were produced by AI agents (Claude, Anthropic)
-- in a project run by Doug Phillips.

-- ===== Erdos307/Forcing.lean =====

/-!
# Erdős Problem #307 — the forcing reduction

For a finite pairwise-coprime set `S` of positive integers put
`M S = ∏_{a ∈ S} a` and `A S = ∑_{a ∈ S} M S / a`.

* `coprime_A_M` / `gcd_A_M` : `gcd (A S) (M S) = 1`.
* `sum_inv_eq`, `sum_inv_num`, `sum_inv_den` : `∑ 1/a = A S / M S`, in lowest terms.
* `forcing` : `(∑_P 1/a) (∑_Q 1/b) = 1 ↔ A P = M Q ∧ A Q = M P`.
* `disjoint_of_solution` : with `1 ∉ P ∪ Q`, any solution has `P ∩ Q = ∅`.
* `prime_solution` : for sets of primes, `A P` is squarefree and `Q = (A P).primeFactors`.
* `two_cycle` : for sets of primes, a solution is exactly a 2-cycle `M P ↦ M Q ↦ M P`
  of the squarefree arithmetic derivative `sqfDeriv n = ∑_{p ∣ n} n / p`.
* `erdos_307_iff`, `coprime_one_notMem_iff` : the two open formal-conjectures statements
  (`docs/statement_307.md`) restated through the forcing reduction.
-/

namespace OMA.Phillips307

open Finset

/-- `M S = ∏_{a ∈ S} a`. -/
def M (S : Finset ℕ) : ℕ := ∏ a ∈ S, a

/-- `A S = ∑_{a ∈ S} M S / a`. -/
def A (S : Finset ℕ) : ℕ := ∑ a ∈ S, M S / a

/-- A finite set of positive, pairwise-coprime naturals. -/
def Admissible (S : Finset ℕ) : Prop :=
  (∀ a ∈ S, 0 < a) ∧ (S : Set ℕ).Pairwise Nat.Coprime

variable {S P Q : Finset ℕ}

lemma M_pos (h : ∀ a ∈ S, 0 < a) : 0 < M S := Finset.prod_pos h

lemma M_div_eq {a : ℕ} (ha : a ∈ S) (hpos : 0 < a) : M S / a = ∏ b ∈ S.erase a, b := by
  unfold M
  rw [← Finset.mul_prod_erase S (fun b => b) ha]
  exact Nat.mul_div_cancel_left _ hpos

lemma A_eq (h : ∀ a ∈ S, 0 < a) : A S = ∑ a ∈ S, ∏ b ∈ S.erase a, b := by
  unfold A
  exact Finset.sum_congr rfl fun a ha => M_div_eq ha (h a ha)

/-- `A S` is coprime to every element of `S`. -/
lemma coprime_A_mem (hS : Admissible S) {a : ℕ} (ha : a ∈ S) : Nat.Coprime (A S) a := by
  rw [A_eq hS.1, ← Finset.add_sum_erase S _ ha]
  have hdvd : a ∣ ∑ c ∈ S.erase a, ∏ b ∈ S.erase c, b := by
    refine Finset.dvd_sum fun c hc => ?_
    exact Finset.dvd_prod_of_mem (fun b => b)
      (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hc).symm, ha⟩)
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.coprime_add_mul_left_left]
  exact Nat.Coprime.prod_left fun b hb =>
    hS.2 (Finset.mem_of_mem_erase hb) ha (Finset.ne_of_mem_erase hb)

/-- **Lowest terms:** `A S` and `M S` are coprime. -/
theorem coprime_A_M (hS : Admissible S) : Nat.Coprime (A S) (M S) :=
  Nat.Coprime.prod_right fun _ ha => coprime_A_mem hS ha

theorem gcd_A_M (hS : Admissible S) : Nat.gcd (A S) (M S) = 1 := coprime_A_M hS

/-- `∑_{a ∈ S} 1/a = A S / M S` (positivity suffices). -/
theorem sum_inv_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, (a : ℚ)⁻¹) = (A S : ℚ) / (M S : ℚ) := by
  rw [A_eq hpos, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hM : (M S : ℚ) = (a : ℚ) * ∏ b ∈ S.erase a, (b : ℚ) := by
    unfold M
    rw [Nat.cast_prod, Finset.mul_prod_erase S (fun b : ℕ => (b : ℚ)) ha]
  rw [hM, Nat.cast_prod]
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
  have hP0 : ∏ b ∈ S.erase a, (b : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => by
      exact_mod_cast (hpos b (Finset.mem_of_mem_erase hb)).ne'
  field_simp

theorem sum_one_div_eq (hpos : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, 1 / (a : ℚ)) = (A S : ℚ) / (M S : ℚ) := by
  simpa only [one_div] using sum_inv_eq hpos

/-- The reduced numerator of `∑ 1/a` is `A S`. -/
theorem sum_inv_num (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).num = A S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.num_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  simpa using this

/-- The reduced denominator of `∑ 1/a` is `M S`. -/
theorem sum_inv_den (hS : Admissible S) : (∑ a ∈ S, (a : ℚ)⁻¹).den = M S := by
  rw [sum_inv_eq hS.1]
  have hb : (0 : ℤ) < (M S : ℤ) := by exact_mod_cast M_pos hS.1
  have := Rat.den_div_eq_of_coprime (a := (A S : ℤ)) (b := (M S : ℤ)) hb
    (by simpa using coprime_A_M hS)
  exact_mod_cast (by simpa using this)

/-- **Forcing theorem.** -/
theorem forcing (hP : Admissible P) (hQ : Admissible Q) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔ A P = M Q ∧ A Q = M P := by
  rw [sum_inv_eq hP.1, sum_inv_eq hQ.1]
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP.1).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ.1).ne'
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hMP hMQ)]
  norm_cast
  constructor
  · intro h
    have cP := coprime_A_M hP
    have cQ := coprime_A_M hQ
    have h1 : A P ∣ M Q := cP.dvd_of_dvd_mul_left ⟨A Q, h.symm⟩
    have h2 : M Q ∣ A P := cQ.symm.dvd_of_dvd_mul_right (h ▸ dvd_mul_left (M Q) (M P))
    have e1 : A P = M Q := Nat.dvd_antisymm h1 h2
    refine ⟨e1, ?_⟩
    rw [e1, mul_comm (M P)] at h
    exact Nat.eq_of_mul_eq_mul_left (M_pos hQ.1) h
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_comm]

/-- Same statement in the `1 = …` orientation and `⁻¹` notation used by formal-conjectures. -/
theorem forcing' (hP : Admissible P) (hQ : Admissible Q) :
    1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) ↔ A P = M Q ∧ A Q = M P := by
  rw [eq_comm]; exact forcing hP hQ

/-- With `1 ∉ P ∪ Q`, a solution has `P` and `Q` disjoint. -/
theorem disjoint_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  have e := ((forcing hP hQ).1 heq).1
  have hx1 : x ∣ A P := e ▸ Finset.dvd_prod_of_mem (fun b => b) hxQ
  have hx2 : x ∣ M P := Finset.dvd_prod_of_mem (fun b => b) hxP
  have : x ∣ 1 := gcd_A_M hP ▸ Nat.dvd_gcd hx1 hx2
  exact h1 (Finset.mem_union_left _ (Nat.dvd_one.1 this ▸ hxP))

theorem inter_eq_empty_of_solution (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : P ∩ Q = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.1 (disjoint_of_solution hP hQ h1 heq)

/-! ## Sets of primes -/

lemma admissible_of_primes (h : ∀ p ∈ S, p.Prime) : Admissible S :=
  ⟨fun p hp => (h p hp).pos, fun p hp q hq hpq => (Nat.coprime_primes (h p hp) (h q hq)).2 hpq⟩

lemma squarefree_M_of_primes (h : ∀ p ∈ S, p.Prime) : Squarefree (M S) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (h p hp) (h q hq)).2 hpq)
    fun p hp => (h p hp).prime.squarefree

lemma primeFactors_M (h : ∀ p ∈ S, p.Prime) : (M S).primeFactors = S :=
  Nat.primeFactors_prod h

/-- For prime sets: `A P` is squarefree, `Q = (A P).primeFactors`, `P = (A Q).primeFactors`,
and `P ∩ Q = ∅`. -/
theorem prime_solution (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    Squarefree (A P) ∧ Q = (A P).primeFactors ∧ P = (A Q).primeFactors ∧ Disjoint P Q := by
  obtain ⟨e1, e2⟩ := (forcing (admissible_of_primes hP) (admissible_of_primes hQ)).1 heq
  refine ⟨e1 ▸ squarefree_M_of_primes hQ, ?_, ?_, ?_⟩
  · rw [e1, primeFactors_M hQ]
  · rw [e2, primeFactors_M hP]
  · refine disjoint_of_solution (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
    intro h1
    rcases Finset.mem_union.1 h1 with h | h
    · exact Nat.not_prime_one (hP 1 h)
    · exact Nat.not_prime_one (hQ 1 h)

/-- The arithmetic derivative restricted to squarefree arguments: for squarefree `n`,
`n' = ∑_{p ∣ n} n / p`. (On non-squarefree `n` this is *not* the arithmetic derivative.) -/
def sqfDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n / p

lemma sqfDeriv_M (h : ∀ p ∈ S, p.Prime) : sqfDeriv (M S) = A S := by
  unfold sqfDeriv A
  rw [primeFactors_M h]

/-- **2-cycle equivalence.** For prime sets, `(∑_P 1/p)(∑_Q 1/q) = 1` iff the squarefree numbers
`M P`, `M Q` form a 2-cycle of the arithmetic derivative. -/
theorem two_cycle (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) :
    (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1 ↔
      sqfDeriv (M P) = M Q ∧ sqfDeriv (M Q) = M P := by
  rw [sqfDeriv_M hP, sqfDeriv_M hQ]
  exact forcing (admissible_of_primes hP) (admissible_of_primes hQ)

/-! ## The formal-conjectures statements, restated -/

/-- `erdos_307` (formal-conjectures) is equivalent to the integer system `A P = M Q, A Q = M P`
over sets of primes. -/
theorem erdos_307_iff :
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧ A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h⟩
    exact ⟨P, Q, hP, hQ, (forcing' (admissible_of_primes hP) (admissible_of_primes hQ)).2 h⟩

/-- Under the side conditions of the open variant, every element is positive. -/
lemma pos_of_variant {S : Finset ℕ} (h1 : 1 ∉ S) (hcard : 1 < S.card)
    (hcop : (S : Set ℕ).Pairwise Nat.Coprime) : ∀ a ∈ S, 0 < a := by
  intro a ha
  rcases Nat.eq_zero_or_pos a with h0 | h
  · exfalso
    subst h0
    obtain ⟨b, hb, hb0⟩ := Finset.exists_mem_ne hcard 0
    have := hcop ha hb (Ne.symm hb0)
    rw [Nat.coprime_zero_left] at this
    exact h1 (this ▸ hb)
  · exact h

/-- `erdos_307.variants.coprime_one_notMem` (formal-conjectures) restated through forcing. -/
theorem coprime_one_notMem_iff :
    (∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) ↔
    (∃ P Q : Finset ℕ, Admissible P ∧ Admissible Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      A P = M Q ∧ A Q = M P) := by
  constructor
  · rintro ⟨P, Q, -, h1, hcP, hcQ, cP, cQ, h⟩
    have hP : Admissible P :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    have hQ : Admissible Q :=
      ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩
    exact ⟨P, Q, hP, hQ, h1, hcP, hcQ, (forcing' hP hQ).1 h⟩
  · rintro ⟨P, Q, hP, hQ, h1, hcP, hcQ, h⟩
    refine ⟨P, Q, ?_, h1, hcP, hcQ, hP.2, hQ.2, (forcing' hP hQ).2 h⟩
    intro h0
    exact (hP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl

end OMA.Phillips307

-- ===== Erdos307/Floor.lean =====

/-!
# Erdős #307 — the 59-element floor for the coprime variant (E6)

Any solution with `P`, `Q` positive, pairwise coprime and `1 ∉ P ∪ Q` has `59 ≤ #(P ∪ Q)`.

1. Forcing gives `gcd (M P) (M Q) = 1`, so `P ∪ Q` is pairwise coprime (and `P`, `Q` disjoint).
2. AM-GM: `Σ_P · Σ_Q = 1` gives `Σ_P + Σ_Q ≥ 2`.
3. `x ↦ minFac x` is injective on `P ∪ Q`, and `1/x ≤ 1/minFac x`.
4. A set `V` of at most 58 primes has `Σ_V 1/p ≤ Σ_F 1/p`, where `F` lists the 58 primes below
   277: a prime of `V \ F` is `≥ 277`, every entry of `F` is `< 277`, and `|V \ F| ≤ |F \ V|`.
5. `Σ_F 1/p < 2` (≈ 1.99874).

Only the finite facts `#F = 58`, `Σ_F 1/p < 2` and "every prime below 277 lies in `F`" are
computed; the primality of the entries of `F` is never used.
-/

namespace OMA.Phillips307

open Finset

/-- The 58 primes below 277. -/
def F58 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271}

set_option maxRecDepth 100000 in
lemma F58_card : F58.card = 58 := by decide

set_option maxRecDepth 100000 in
lemma F58_bounds : ∀ p ∈ F58, 0 < p ∧ p < 277 := by decide

lemma F58_sum : (∑ p ∈ F58, (p : ℚ)⁻¹) < 2 := by
  simp only [F58]
  norm_num

set_option maxRecDepth 100000 in
/-- Every prime outside `F58` is at least 277. -/
lemma le_of_prime_notMem_F58 {p : ℕ} (hp : p.Prime) (h : p ∉ F58) : 277 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | exact h (by decide) | exact absurd hp (by norm_num)

/-- Comparison against any set `F` of `k` numbers in `(0, B)` containing every prime `< B`. -/
lemma sum_inv_primes_le_of {F V : Finset ℕ} {k B : ℕ} (hB : 0 < B) (hFcard : F.card = k)
    (hFb : ∀ p ∈ F, 0 < p ∧ p < B) (hFp : ∀ p, p.Prime → p ∉ F → B ≤ p)
    (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ k) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F, (p : ℚ)⁻¹ := by
  rw [← Finset.sum_inter_add_sum_sdiff V F, ← Finset.sum_inter_add_sum_sdiff F V,
    Finset.inter_comm F V]
  have h1 : (∑ p ∈ V \ F, (p : ℚ)⁻¹) ≤ (V \ F).card • (B : ℚ)⁻¹ := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    obtain ⟨hpV, hpF⟩ := Finset.mem_sdiff.1 hp
    have h277 : (B : ℚ) ≤ p := by exact_mod_cast hFp p (hV p hpV) hpF
    exact inv_anti₀ (by exact_mod_cast hB) h277
  have h2 : (F \ V).card • (B : ℚ)⁻¹ ≤ ∑ p ∈ F \ V, (p : ℚ)⁻¹ := by
    refine Finset.card_nsmul_le_sum _ _ _ fun p hp => ?_
    obtain ⟨hpos, hlt⟩ := hFb p (Finset.mem_sdiff.1 hp).1
    exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hlt.le)
  have hc : (V \ F).card ≤ (F \ V).card := by
    have a := Finset.card_sdiff_add_card_inter V F
    have b := Finset.card_sdiff_add_card_inter F V
    rw [Finset.inter_comm, hFcard] at b
    omega
  have h3 : (V \ F).card • (B : ℚ)⁻¹ ≤ (F \ V).card • (B : ℚ)⁻¹ := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  linarith

/-- At most 58 primes have reciprocal sum at most that of the 58 primes below 277. -/
lemma sum_inv_primes_le {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) (hcard : V.card ≤ 58) :
    (∑ p ∈ V, (p : ℚ)⁻¹) ≤ ∑ p ∈ F58, (p : ℚ)⁻¹ :=
  sum_inv_primes_le_of (by norm_num) F58_card F58_bounds (fun _ hp h => le_of_prime_notMem_F58 hp h) hV hcard

/-- On a pairwise-coprime set of integers `> 1`, `minFac` is injective onto primes and
`1/x ≤ 1/minFac x`. -/
lemma sum_inv_le_minFac {U : Finset ℕ} (hgt : ∀ x ∈ U, 1 < x)
    (hcop : (U : Set ℕ).Pairwise Nat.Coprime) :
    (∑ x ∈ U, (x : ℚ)⁻¹) ≤ ∑ p ∈ U.image Nat.minFac, (p : ℚ)⁻¹ ∧
      (U.image Nat.minFac).card = U.card ∧ ∀ p ∈ U.image Nat.minFac, p.Prime := by
  have hinj : Set.InjOn Nat.minFac (U : Set ℕ) := by
    intro x hx y hy hxy
    by_contra hne
    have c := hcop hx hy hne
    have hdx : x.minFac ∣ x := Nat.minFac_dvd x
    have hdy : x.minFac ∣ y := hxy ▸ Nat.minFac_dvd y
    have h1 : x.minFac ∣ 1 := c ▸ Nat.dvd_gcd hdx hdy
    have : x = 1 := Nat.minFac_eq_one_iff.1 (Nat.dvd_one.1 h1)
    exact absurd (hgt x hx) (by omega)
  refine ⟨?_, Finset.card_image_of_injOn hinj, ?_⟩
  · rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum fun x hx => ?_
    have hx0 : 0 < x := by have := hgt x hx; omega
    exact inv_anti₀ (by exact_mod_cast Nat.minFac_pos x)
      (by exact_mod_cast Nat.minFac_le hx0)
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    exact Nat.minFac_prime (by have := hgt x hx; omega)

/-- In a solution, elements of `P` and `Q` are coprime. -/
lemma cross_coprime {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) {a b : ℕ} (ha : a ∈ P)
    (hb : b ∈ Q) : Nat.Coprime a b := by
  have e := ((forcing hP hQ).1 heq).1
  have c : Nat.Coprime (M P) (M Q) := e ▸ (coprime_A_M hP).symm
  exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hb)
    (Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem (fun x => x) ha) c)

/-- AM-GM for a product equal to one. -/
lemma two_le_add_of_mul_eq_one {s t : ℚ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s * t = 1) :
    2 ≤ s + t := by
  nlinarith [sq_nonneg (s - t)]

/-- **E6: the floor.** Any solution of the coprime variant with `1 ∉ P ∪ Q` uses at least
59 numbers. -/
theorem card_floor {P Q : Finset ℕ} (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) : 59 ≤ (P ∪ Q).card := by
  by_contra hlt
  push Not at hlt
  have hgt : ∀ x ∈ P ∪ Q, 1 < x := by
    intro x hx
    have hpos : 0 < x := by
      rcases Finset.mem_union.1 hx with h | h
      · exact hP.1 x h
      · exact hQ.1 x h
    have hne : x ≠ 1 := fun e => h1 (e ▸ hx)
    omega
  have hcop : ((P ∪ Q : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hne
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hP.2 hx hy hne
    · exact cross_coprime hP hQ heq hx hy
    · exact (cross_coprime hP hQ heq hy hx).symm
    · exact hQ.2 hx hy hne
  obtain ⟨hle, hcard, hprime⟩ := sum_inv_le_minFac hgt hcop
  have hV := sum_inv_primes_le hprime (by omega)
  have hsum : (∑ x ∈ P ∪ Q, (x : ℚ)⁻¹) = (∑ a ∈ P, (a : ℚ)⁻¹) + ∑ b ∈ Q, (b : ℚ)⁻¹ :=
    Finset.sum_union (disjoint_of_solution hP hQ h1 heq)
  have hamgm := two_le_add_of_mul_eq_one
    (Finset.sum_nonneg fun a _ => inv_nonneg.2 (Nat.cast_nonneg a))
    (Finset.sum_nonneg fun b _ => inv_nonneg.2 (Nat.cast_nonneg b)) heq
  linarith [F58_sum]

/-- The floor in the exact form of formal-conjectures' `erdos_307.variants.coprime_one_notMem`
hypotheses. -/
theorem coprime_one_notMem_card_floor {P Q : Finset ℕ} (h1 : 1 ∉ P ∪ Q) (hcP : 1 < P.card)
    (hcQ : 1 < Q.card) (cP : (P : Set ℕ).Pairwise Nat.Coprime)
    (cQ : (Q : Set ℕ).Pairwise Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card :=
  card_floor ⟨pos_of_variant (fun h => h1 (Finset.mem_union_left _ h)) hcP cP, cP⟩
    ⟨pos_of_variant (fun h => h1 (Finset.mem_union_right _ h)) hcQ cQ, cQ⟩ h1 heq.symm

/-- Cross-check: the same argument gives the 59-prime half of the upstream `erdos_307.barrier`
(Bonfioli), with no `Q.Nonempty` hypothesis. -/
theorem prime_card_floor {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) : 59 ≤ (P ∪ Q).card := by
  refine card_floor (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq.symm
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact Nat.not_prime_one (hP 1 h)
  · exact Nat.not_prime_one (hQ 1 h)

end OMA.Phillips307

-- ===== Erdos307/Square.lean =====

/-!
# Erdős #307 — the square criterion and the closing lemma (E7)

* `A_union` : for disjoint positive `P`, `Q` : `A (P ∪ Q) = A P * M Q + A Q * M P`.
* `square_criterion` : in a solution with `P`, `Q` disjoint,
  `A (P ∪ Q) = M P ^ 2 + M Q ^ 2` and `M (P ∪ Q) = M P * M Q`; hence (`square_pm`)
  `A U + 2 M U = (M P + M Q)²` and `A U − 2 M U = (M P − M Q)²`.
* `prime_square` : for prime sets, `n = ∏ (P ∪ Q)` has `n' + 2n` and `n' − 2n` both squares
  (`n'` the arithmetic derivative, `sqfDeriv`).
* `closing` : if `P0`, `Q0` are admissible, cross-coprime and `M Q0 · M P0 = A Q0 · A P0 + 1`,
  then `P0 ∪ {M Q0² + A Q0 · M P0}` and `Q0 ∪ {M Q0 · A P0 + M P0²}` solve the equation, with
  everything pairwise coprime. `coprime_one_notMem_of_closing` : such a pair with
  `1 ∉ P0 ∪ Q0`, both nonempty, proves the open variant `erdos_307.variants.coprime_one_notMem`.
-/

namespace OMA.Phillips307

open Finset

variable {P Q : Finset ℕ}

lemma M_union (h : Disjoint P Q) : M (P ∪ Q) = M P * M Q := Finset.prod_union h

lemma pos_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) : ∀ x ∈ P ∪ Q, 0 < x := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hP x h
  · exact hQ x h

lemma A_union (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ b ∈ Q, 0 < b) (h : Disjoint P Q) :
    A (P ∪ Q) = A P * M Q + A Q * M P := by
  have e := sum_inv_eq (pos_union hP hQ)
  rw [Finset.sum_union h, sum_inv_eq hP, sum_inv_eq hQ, M_union h] at e
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ).ne'
  have key : (A (P ∪ Q) : ℚ) = A P * M Q + A Q * M P := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- **Square criterion.** -/
theorem square_criterion (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) = M P ^ 2 + M Q ^ 2 ∧ M (P ∪ Q) = M P * M Q := by
  obtain ⟨e1, e2⟩ := (forcing hP hQ).1 heq
  refine ⟨?_, M_union hd⟩
  rw [A_union hP.1 hQ.1 hd, e1, e2]
  ring

theorem square_pm (hP : Admissible P) (hQ : Admissible Q) (hd : Disjoint P Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    A (P ∪ Q) + 2 * M (P ∪ Q) = (M P + M Q) ^ 2 ∧
      (A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q) = ((M P : ℤ) - M Q) ^ 2 := by
  obtain ⟨h1, h2⟩ := square_criterion hP hQ hd heq
  refine ⟨by rw [h1, h2]; ring, ?_⟩
  rw [h1, h2]
  push_cast
  ring

/-- For the open variant (`1 ∉ P ∪ Q`) disjointness is automatic. -/
theorem square_pm_of_one_notMem (hP : Admissible P) (hQ : Admissible Q) (h1 : 1 ∉ P ∪ Q)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (A (P ∪ Q) + 2 * M (P ∪ Q)) ∧ IsSquare ((A (P ∪ Q) : ℤ) - 2 * M (P ∪ Q)) := by
  obtain ⟨h1', h2'⟩ := square_pm hP hQ (disjoint_of_solution hP hQ h1 heq) heq
  exact ⟨⟨M P + M Q, by rw [h1']; ring⟩, ⟨(M P : ℤ) - M Q, by rw [h2']; ring⟩⟩

/-- **Prime form:** for a solution in primes and `n = ∏ (P ∪ Q)`, both `n' + 2n` and `n' − 2n` are
perfect squares, `n'` the arithmetic derivative. -/
theorem prime_square (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) = 1) :
    IsSquare (sqfDeriv (M (P ∪ Q)) + 2 * M (P ∪ Q)) ∧
      IsSquare ((sqfDeriv (M (P ∪ Q)) : ℤ) - 2 * M (P ∪ Q)) := by
  have hU : ∀ x ∈ P ∪ Q, x.Prime := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hP x h
    · exact hQ x h
  rw [sqfDeriv_M hU]
  refine square_pm_of_one_notMem (admissible_of_primes hP) (admissible_of_primes hQ) ?_ heq
  intro h
  exact Nat.not_prime_one (hU 1 h)

/-! ## The closing lemma -/

section closing

variable {P0 Q0 : Finset ℕ}

/-- **Closing lemma.** A pair with `M Q0 · M P0 = A Q0 · A P0 + 1` closes to a solution. -/
theorem closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    Admissible (insert (M Q0 ^ 2 + A Q0 * M P0) P0) ∧
    Admissible (insert (M Q0 * A P0 + M P0 ^ 2) Q0) ∧
    (M Q0 ^ 2 + A Q0 * M P0) ∉ P0 ∧ (M Q0 * A P0 + M P0 ^ 2) ∉ Q0 ∧
    (∀ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, ∀ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0,
      Nat.Coprime x y) ∧
    (∑ x ∈ insert (M Q0 ^ 2 + A Q0 * M P0) P0, (x : ℚ)⁻¹) *
      (∑ y ∈ insert (M Q0 * A P0 + M P0 ^ 2) Q0, (y : ℚ)⁻¹) = 1 := by
  set MP := M P0 with hMPdef
  set AP := A P0 with hAPdef
  set MQ := M Q0 with hMQdef
  set AQ := A Q0 with hAQdef
  set a := MQ ^ 2 + AQ * MP with ha
  set b := MQ * AP + MP ^ 2 with hb
  -- basic coprimality
  have cPQ : Nat.Coprime MP MQ :=
    Nat.Coprime.prod_left fun x hx => Nat.Coprime.prod_right fun y hy => hcross x hx y hy
  have cAP : Nat.Coprime AP MP := coprime_A_M hP
  have cAQ : Nat.Coprime AQ MQ := coprime_A_M hQ
  have ha_MP : Nat.Coprime a MP := by
    rw [ha, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ.symm
  have ha_MQ : Nat.Coprime a MQ := by
    have : a = AQ * MP + MQ * MQ := by rw [ha]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cAQ cPQ
  have hb_MQ : Nat.Coprime b MQ := by
    have : b = MP ^ 2 + AP * MQ := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_right_left]
    exact Nat.Coprime.pow_left 2 cPQ
  have hb_MP : Nat.Coprime b MP := by
    have : b = MQ * AP + MP * MP := by rw [hb]; ring
    rw [this, Nat.coprime_add_mul_left_left]
    exact Nat.Coprime.mul_left cPQ.symm cAP
  -- the two linear relations, from hD
  have hDz : (MQ : ℤ) * MP = AQ * AP + 1 := by exact_mod_cast hD
  have E1 : MQ * b = MP + AP * a := by
    have : (MQ : ℤ) * b = MP + AP * a := by
      rw [hb, ha]; push_cast; linear_combination (MP : ℤ) * hDz
    exact_mod_cast this
  have E2 : MP * a = MQ + AQ * b := by
    have : (MP : ℤ) * a = MQ + AQ * b := by
      rw [hb, ha]; push_cast; linear_combination (MQ : ℤ) * hDz
    exact_mod_cast this
  have hab : Nat.Coprime a b := by
    have h' : Nat.Coprime (MP + AP * a) a := by
      rw [Nat.coprime_add_mul_right_left]; exact ha_MP.symm
    rw [← E1] at h'
    exact Nat.Coprime.coprime_mul_left_right h'.symm
  -- sizes
  have hMQ2 : 2 ≤ MQ := by
    obtain ⟨y, hy⟩ := hQne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
    have hy0 := hQ.1 y hy
    have : y ≤ MQ := Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have hMP2 : 2 ≤ MP := by
    obtain ⟨y, hy⟩ := hPne
    have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
    have hy0 := hP.1 y hy
    have : y ≤ MP := Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
    omega
  have ha2 : 2 ≤ a := by rw [ha]; nlinarith
  have hb2 : 2 ≤ b := by rw [hb]; nlinarith
  have haP : a ∉ P0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd ha_MP (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  have hbQ : b ∉ Q0 := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd hb_MQ (Finset.dvd_prod_of_mem (fun x => x) h)
    omega
  -- admissibility
  have adP : Admissible (insert a P0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hP.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hP.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime a y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MP
      exact ⟨c, c.symm⟩
  have adQ : Admissible (insert b Q0) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | h
      · omega
      · exact hQ.1 x h
    · rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hQ.2, fun y hy _ => ?_⟩
      have c : Nat.Coprime b y :=
        Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) hb_MQ
      exact ⟨c, c.symm⟩
  refine ⟨adP, adQ, haP, hbQ, ?_, ?_⟩
  · intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx <;> rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hab
    · exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hy) ha_MQ
    · exact (Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun x => x) hx) hb_MP).symm
    · exact hcross x hx y hy
  · rw [Finset.sum_insert haP, Finset.sum_insert hbQ, sum_inv_eq hP.1, sum_inv_eq hQ.1]
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hP0 : (MP : ℚ) ≠ 0 := by exact_mod_cast (show MP ≠ 0 by omega)
    have hQ0 : (MQ : ℚ) ≠ 0 := by exact_mod_cast (show MQ ≠ 0 by omega)
    have E1q : (MQ : ℚ) * b = MP + AP * a := by exact_mod_cast E1
    have E2q : (MP : ℚ) * a = MQ + AQ * b := by exact_mod_cast E2
    have s1 : (a : ℚ)⁻¹ + AP / MP = (MQ * b) / (a * MP) := by
      rw [E1q]; field_simp
    have s2 : (b : ℚ)⁻¹ + AQ / MQ = (MP * a) / (b * MQ) := by
      rw [E2q]; field_simp
    rw [s1, s2]
    field_simp

/-- **Sufficient condition for the open variant.** A cross-coprime admissible pair `P0`, `Q0`,
both nonempty, without `1`, with `M Q0 · M P0 = A Q0 · A P0 + 1`, proves
`erdos_307.variants.coprime_one_notMem` (stated exactly as in formal-conjectures). -/
theorem coprime_one_notMem_of_closing (hP : Admissible P0) (hQ : Admissible Q0)
    (hcross : ∀ a ∈ P0, ∀ b ∈ Q0, Nat.Coprime a b) (hQne : Q0.Nonempty) (hPne : P0.Nonempty)
    (h1 : 1 ∉ P0 ∪ Q0) (hD : M Q0 * M P0 = A Q0 * A P0 + 1) :
    ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
      (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
      1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) := by
  obtain ⟨adP, adQ, haP, hbQ, -, heq⟩ := closing hP hQ hcross hQne hPne h1 hD
  refine ⟨_, _, ?_, ?_, ?_, ?_, adP.2, adQ.2, heq.symm⟩
  · intro h0
    exact (adP.1 0 (Finset.mem_inter.1 h0).1).ne' rfl
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · -- the new element `a` is ≥ 2
        have : 2 ≤ M Q0 ^ 2 + A Q0 * M P0 := by
          obtain ⟨y, hy⟩ := hQne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_right _ (e ▸ hy))
          have : y ≤ M Q0 :=
            Nat.le_of_dvd (M_pos hQ.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hQ.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_left _ h)
    · rcases Finset.mem_insert.1 h with e | h
      · have : 2 ≤ M Q0 * A P0 + M P0 ^ 2 := by
          obtain ⟨y, hy⟩ := hPne
          have hy1 : y ≠ 1 := fun e => h1 (Finset.mem_union_left _ (e ▸ hy))
          have : y ≤ M P0 :=
            Nat.le_of_dvd (M_pos hP.1) (Finset.dvd_prod_of_mem (fun x => x) hy)
          have hy2 : 2 ≤ y := by have := hP.1 y hy; omega
          nlinarith
        omega
      · exact h1 (Finset.mem_union_right _ h)
  · rw [Finset.card_insert_of_notMem haP]
    have := Finset.card_pos.2 hPne
    omega
  · rw [Finset.card_insert_of_notMem hbQ]
    have := Finset.card_pos.2 hQne
    omega

end closing

end OMA.Phillips307

-- ===== Erdos307/Descent.lean =====

/-!
# Erdős #307, coprime variant: existence conditional on a descent hypothesis

Write `Dev P Q = M(Q)·M(P) − A(Q)·A(P)` (an integer). By the closing lemma (`Square.lean`), an
admissible, cross-coprime pair with `Dev = 1` and no `1` closes to a solution of the open variant
`erdos_307.variants.coprime_one_notMem`.

`DescentHyp` says: every such "good" state with `Dev > 1` extends, by appending two new pairwise
coprime elements `x, y > 1` (coprime to everything present) to `P`, to a state with
`0 < Dev′ < Dev`. Gemini's two-element hyperbola descent (sprint lens R3-E) predicts such
extensions, even with `Dev′ < Dev / 2`, with an expected count that grows at every step; proving it
is an open thin-strip equidistribution problem.

Proved here (standard axioms):
- the descent machinery: `dev_insert2` (step formula), `dev_mul_dev_insert2` (the strip identity
  `Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²`, `E = A(Q)·M(P)`), `good_extend` (good states are
  closed under coprime extension), and `closes_of_dev_one`;
- `coprime_one_notMem_of_descent` and `coprime_one_notMem_of_descentBelow` (descent ⇒ the open variant).

**Honest status of the hypotheses (2026-11-24).**
- `DescentHyp` is FALSE (`not_descentHyp`, proved), so the first theorem is vacuous.
- `DescentHypBelow K` restricts to near-solution states. It is not known to be false, but it is
  universal over infinitely many states, while the halving heuristic gives each state a failure
  chance of about q0^(−c²/2) > 0. Ford-type exceptional sets make the universal form *heuristically
  false*. The heuristic supports only "some descent path survives" (a branching-process statement),
  which no ∀-state hypothesis captures.
- `DescentHypDeep M₀` (Gemini's refinement; the main result `coprime_one_notMem_of_descentDeep`)
  addresses both problems:
  - it adds `Coprime (M P) (A Q)`, which removes the local obstruction `dvd_dev_of_dvd`;
  - it requires `Dev² ≤ M(P)M(Q)`, so the halving start point is `q₀ ≥ √M`;
  - it allows **arbitrary finite** extensions `S`.

  Heuristically (Gemini, reported; not re-checked by Claude) the number of descending extensions
  per state grows fast enough that a union bound over all deep states converges, so the universal
  hypothesis is *plausible* under a Poisson model. Ford-type correlations are not ruled out.
  **It is a conjecture, not a theorem.**
- A deep seed exists: `scripts/deep_seed.py` builds one, with 69 elements, log₁₀ Dev = 115.5 and
  log₁₀ M(P)M(Q) = 4595.4. It is verified with exact integers in Python, not yet in Lean.
- Net: a genuine conditional reduction of the open variant to `DescentHypDeep`, a natural
  thin-strip / equidistribution conjecture, with the vacuous versions proved false and the local
  obstruction explicit.
-/

namespace OMA.Phillips307

open Finset

/-- The closing-lemma deviation `M(Q)·M(P) − A(Q)·A(P)`. -/
def Dev (P Q : Finset ℕ) : ℤ := (M Q : ℤ) * M P - (A Q : ℤ) * A P

/-- A state from which the closing lemma / descent can proceed. -/
def Good (P Q : Finset ℕ) : Prop :=
  Admissible P ∧ Admissible Q ∧ (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) ∧ P.Nonempty ∧
    Q.Nonempty ∧ 1 ∉ P ∪ Q ∧ 0 < Dev P Q

/-- **Descent hypothesis.** Every good state with `Dev > 1` admits a two-element extension of `P`
by new coprime elements that strictly lowers the (still positive) deviation. -/
def DescentHyp : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

lemma M_insert {S : Finset ℕ} {x : ℕ} (hxS : x ∉ S) : M (insert x S) = x * M S := by
  unfold M
  rw [Finset.prod_insert hxS]

lemma A_insert {S : Finset ℕ} {x : ℕ} (hS : ∀ a ∈ S, 0 < a) (hx : 0 < x) (hxS : x ∉ S) :
    A (insert x S) = x * A S + M S := by
  have hpos : ∀ a ∈ insert x S, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hx
    · exact hS a h
  have e := sum_inv_eq hpos
  rw [Finset.sum_insert hxS, sum_inv_eq hS, M_insert hxS] at e
  have hMS : (M S : ℚ) ≠ 0 := by exact_mod_cast (M_pos hS).ne'
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have key : (A (insert x S) : ℚ) = x * A S + M S := by
    rw [Nat.cast_mul] at e
    field_simp at e
    linarith
  exact_mod_cast key

/-- The deviation after appending two new elements to `P`. -/
lemma dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev (insert x (insert y P)) Q =
      (x : ℤ) * y * Dev P Q - ((A Q : ℤ) * M P) * ((x : ℤ) + y) := by
  have hyP' : ∀ a ∈ insert y P, 0 < a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | h
    · exact hy
    · exact hP a h
  have hxyP : x ∉ insert y P := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, hxP⟩
  unfold Dev
  rw [A_insert hyP' hx hxyP, M_insert hxyP, A_insert hP hy hyP, M_insert hyP]
  push_cast
  ring

/-- The thin-strip identity behind the halving mechanism:
`Dev·Dev′ = (Dev·x − E)(Dev·y − E) − E²` with `E = A(Q)·M(P)`. -/
lemma dev_mul_dev_insert2 {P Q : Finset ℕ} {x y : ℕ} (hP : ∀ a ∈ P, 0 < a) (hx : 0 < x)
    (hy : 0 < y) (hxy : x ≠ y) (hxP : x ∉ P) (hyP : y ∉ P) :
    Dev P Q * Dev (insert x (insert y P)) Q =
      (Dev P Q * x - (A Q : ℤ) * M P) * (Dev P Q * y - (A Q : ℤ) * M P) -
        ((A Q : ℤ) * M P) ^ 2 := by
  rw [dev_insert2 hP hx hy hxy hxP hyP]
  ring

lemma not_mem_of_coprime_M {S : Finset ℕ} {x : ℕ} (hx1 : 1 < x) (h : Nat.Coprime x (M S)) :
    x ∉ S := by
  intro hx
  have := Nat.Coprime.eq_one_of_dvd h (Finset.dvd_prod_of_mem (fun a => a) hx)
  omega

lemma coprime_of_mem_of_coprime_M {S : Finset ℕ} {x a : ℕ} (ha : a ∈ S)
    (h : Nat.Coprime x (M S)) : Nat.Coprime x a :=
  Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun b => b) ha) h

/-- A two-element extension of a good state by new coprime elements is good again. -/
lemma good_extend {P Q : Finset ℕ} {x y : ℕ} (hG : Good P Q) (hx1 : 1 < x) (hy1 : 1 < y)
    (hxy : x ≠ y) (hxM : Nat.Coprime x (M P * M Q)) (hyM : Nat.Coprime y (M P * M Q))
    (hcxy : Nat.Coprime x y) (hpos : 0 < Dev (insert x (insert y P)) Q) :
    Good (insert x (insert y P)) Q := by
  obtain ⟨hP, hQ, hc, hPne, hQne, h1, -⟩ := hG
  have hxP : Nat.Coprime x (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM
  have hxQ : Nat.Coprime x (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hxM
  have hyP : Nat.Coprime y (M P) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM
  have hyQ : Nat.Coprime y (M Q) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hyM
  refine ⟨⟨?_, ?_⟩, hQ, ?_, ⟨x, Finset.mem_insert_self _ _⟩, hQne, ?_, hpos⟩
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    rcases Finset.mem_insert.1 ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert, Finset.coe_insert, Set.pairwise_insert, Set.pairwise_insert]
    refine ⟨⟨hP.2, fun b hb _ => ?_⟩, fun b hb hne => ?_⟩
    · have c := coprime_of_mem_of_coprime_M hb hyP
      exact ⟨c, c.symm⟩
    · rcases hb with rfl | hb
      · exact ⟨hcxy, hcxy.symm⟩
      · have c := coprime_of_mem_of_coprime_M hb hxP
        exact ⟨c, c.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hxQ
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact coprime_of_mem_of_coprime_M hb hyQ
    · exact hc a ha b hb
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 h with e | h
      · omega
      rcases Finset.mem_insert.1 h with e | h
      · omega
      · exact h1 (Finset.mem_union_left _ h)
    · exact h1 (Finset.mem_union_right _ h)

/-- The open variant, exactly as stated in formal-conjectures (`coprime_one_notMem`). -/
def CoprimeOneNotMem : Prop :=
  ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧ 1 < P.card ∧ 1 < Q.card ∧
    (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

lemma closes_of_dev_one {P Q : Finset ℕ} (hG : Good P Q) (h1 : Dev P Q = 1) :
    CoprimeOneNotMem := by
  obtain ⟨hP, hQ, hc, hPne, hQne, hone, -⟩ := hG
  have hD : M Q * M P = A Q * A P + 1 := by
    unfold Dev at h1
    have : ((M Q * M P : ℕ) : ℤ) = ((A Q * A P + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  exact coprime_one_notMem_of_closing hP hQ hc hQne hPne hone hD

/-- The starting state `({2}, {3})`, with `Dev = 3·2 − 1·1 = 5`. -/
lemma good_two_three : Good {2} {3} := by
  refine ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ?_, by simp, by simp, by simp, ?_⟩
  · intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    decide
  · simp [Dev, M, A]

/-- **Main theorem.** The descent hypothesis implies the open coprime / 1-excluded variant of
Erdős #307. -/
theorem coprime_one_notMem_of_descent (H : DescentHyp) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hnat.symm
        omega
  exact key _ {2} {3} good_two_three (Int.toNat_of_nonneg good_two_three.2.2.2.2.2.2.le).symm

/-- **Sanity check: the unrestricted `DescentHyp` is FALSE**, so `coprime_one_notMem_of_descent`
is vacuous. At `({2}, {3})` (`Dev = 5`), new elements must be coprime to 6, so they are ≥ 5 and
`Dev′ = 5xy − 2(x + y) ≥ 105`. The halving mechanism only operates near a solution; see
`DescentHypBelow`. -/
theorem not_descentHyp : ¬ DescentHyp := by
  intro H
  have hgt : 1 < Dev {2} {3} := by simp [Dev, M, A]
  obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, -, -, hlt⟩ := H {2} {3} good_two_three hgt
  have hxP : x ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hx1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
  have hyP : y ∉ ({2} : Finset ℕ) := not_mem_of_coprime_M hy1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
  rw [dev_insert2 (by simp) (by omega) (by omega) hxy hxP hyP] at hlt
  have h5 : Dev {2} {3} = 5 := by simp [Dev, M, A]
  have hA : (A {3} : ℤ) * M {2} = 2 := by simp [M, A]
  rw [h5, hA] at hlt
  have hx2 : (2 : ℤ) ≤ x := by exact_mod_cast hx1
  have hy2 : (2 : ℤ) ≤ y := by exact_mod_cast hy1
  nlinarith

/-- **Near-solution descent hypothesis.** Restricted to good states with deviation ratio
`Dev / (M(P)·M(Q)) ≤ 1/K`, a class closed under the descent step (`Dev′ < Dev` while the
products grow). This is where Gemini's halving mechanism lives. -/
def DescentHypBelow (K : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
      Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
      0 < Dev (insert x (insert y P)) Q ∧ Dev (insert x (insert y P)) Q < Dev P Q

/-- **Conditional existence (non-vacuous form).** If some good state lies in the near-solution
class `Dev·K ≤ M(P)M(Q)`, and every state of that class descends, then the open coprime variant
of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentBelow (K : ℕ) (H : DescentHypBelow K)
    (P0 Q0 : Finset ℕ) (hG0 : Good P0 Q0) (hK0 : Dev P0 Q0 * K ≤ (M P0 : ℤ) * M Q0) :
    CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Good P Q → Dev P Q * K ≤ (M P : ℤ) * M Q →
      Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hG hK hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hG (by rw [hn, hn1]; norm_num)
      · have hD := hG.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hD ⊢; omega
        obtain ⟨x, y, hx1, hy1, hxy, hxM, hyM, hcxy, hpos, hlt⟩ := H P Q hG hgt hK
        have hG' := good_extend hG hx1 hy1 hxy hxM hyM hcxy hpos
        -- the class is closed: Dev′·K < Dev·K ≤ M(P)M(Q) ≤ M(P′)M(Q)
        have hxP : x ∉ P := not_mem_of_coprime_M hx1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hxM)
        have hyP : y ∉ P := not_mem_of_coprime_M hy1
          (Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hyM)
        have hxyP : x ∉ insert y P := by
          simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hxP⟩
        have hM' : M (insert x (insert y P)) = x * (y * M P) := by
          rw [M_insert hxyP, M_insert hyP]
        have hMP : 0 < M P := M_pos hG.1.1
        have hMQ : 0 < M Q := M_pos hG.2.1.1
        have hgrow : (M P : ℤ) * M Q ≤ (M (insert x (insert y P)) : ℤ) * M Q := by
          rw [hM']
          have h1 : (M P : ℤ) ≤ (x : ℤ) * (y * M P) := by
            have : (1 : ℤ) ≤ (x : ℤ) * y := by
              have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx1.le
              have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy1.le
              nlinarith
            have hm : (0 : ℤ) ≤ M P := by exact_mod_cast hMP.le
            nlinarith
          push_cast
          exact mul_le_mul_of_nonneg_right h1 (by exact_mod_cast hMQ.le)
        have hK' : Dev (insert x (insert y P)) Q * K ≤
            (M (insert x (insert y P)) : ℤ) * M Q := by
          have hk : (0 : ℤ) ≤ K := by exact_mod_cast Nat.zero_le K
          nlinarith
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (insert x (insert y P)) Q).toNat ?_ _ Q hG' hK' hnat.symm
        omega
  exact key _ P0 Q0 hG0 hK0 (Int.toNat_of_nonneg hG0.2.2.2.2.2.2.le).symm

/-! ## The `Deep` class (Gemini's refinement) and arbitrary finite extensions -/

/-- **Local obstruction (Gemini, 2026-11-24).** If a prime `p` divides both `M(P)` and `A(Q)`, it
divides `Dev` for every extension of `P`, so one-sided descent can never reach `Dev = 1`. `Deep`
therefore requires `Coprime (M P) (A Q)`. -/
lemma dvd_dev_of_dvd {P Q : Finset ℕ} {p : ℕ} (hP : p ∣ M P) (hQ : p ∣ A Q) :
    (p : ℤ) ∣ Dev P Q := by
  unfold Dev
  exact dvd_sub (Dvd.dvd.mul_left (by exact_mod_cast hP) _)
    (Dvd.dvd.mul_right (by exact_mod_cast hQ) _)

/-- Deep near-solution states: good, `σ(Q) ≥ 1`, no local obstruction, large, and
`Dev² ≤ M(P)M(Q)`, so the halving start point `q₀ ≥ √M`. Closed under descent. -/
def Deep (M₀ : ℕ) (P Q : Finset ℕ) : Prop :=
  Good P Q ∧ M Q ≤ A Q ∧ Nat.Coprime (M P) (A Q) ∧ M₀ ≤ M P * M Q ∧
    Dev P Q ^ 2 ≤ (M P : ℤ) * M Q

/-- **Deep descent hypothesis.** Every deep state with `Dev > 1` admits a finite extension `S` of
`P` by new elements, pairwise coprime and coprime to `M(P)·M(Q)·A(Q)`, that lowers the
(positive) deviation. Gemini's two- and three-element halving pairs are special cases.
Heuristic support (Gemini, reported, not checked by Claude): with arbitrary finite `S`, the expected
number of descending extensions grows fast enough that a union bound over all deep states
converges (Poisson model); Ford-type correlations are not ruled out. -/
def DescentHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

lemma deep_extend {M₀ : ℕ} {P Q S : Finset ℕ} (hD : Deep M₀ P Q)
    (hS : ∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q))
    (hSc : (S : Set ℕ).Pairwise Nat.Coprime) (hpos : 0 < Dev (P ∪ S) Q)
    (hlt : Dev (P ∪ S) Q < Dev P Q) : Deep M₀ (P ∪ S) Q := by
  obtain ⟨⟨hP, hQ, hc, hPne, hQne, h1, hDpos⟩, hMQ, hcop, hM0, hsq⟩ := hD
  have hsP : ∀ s ∈ S, Nat.Coprime s (M P) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M Q * A Q) (by ring)) (hS s hs).2
  have hsQ : ∀ s ∈ S, Nat.Coprime s (M Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro (M P * A Q) (by ring)) (hS s hs).2
  have hsA : ∀ s ∈ S, Nat.Coprime s (A Q) := fun s hs =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (hS s hs).2
  have hdisj : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro a haP haS
    have := Nat.Coprime.eq_one_of_dvd (hsP a haS) (Finset.dvd_prod_of_mem (fun b => b) haP)
    have := (hS a haS).1
    omega
  have hMU : M (P ∪ S) = M P * M S := Finset.prod_union hdisj
  have hMS : 0 < M S := Finset.prod_pos fun s hs => by have := (hS s hs).1; omega
  have hMP : 0 < M P := M_pos hP.1
  have hMQpos : 0 < M Q := M_pos hQ.1
  have hgrow : M P * M Q ≤ M (P ∪ S) * M Q := by
    rw [hMU]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hMS)
  refine ⟨⟨⟨fun a ha => ?_, ?_⟩, hQ, ?_, ?_, hQne, ?_, hpos⟩, hMQ, ?_, ?_, ?_⟩
  · rcases Finset.mem_union.1 ha with h | h
    · exact hP.1 a h
    · have := (hS a h).1; omega
  · intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hP.2 ha hb hab
    · exact (coprime_of_mem_of_coprime_M ha (hsP b hb)).symm
    · exact coprime_of_mem_of_coprime_M hb (hsP a ha)
    · exact hSc ha hb hab
  · intro a ha b hb
    rcases Finset.mem_union.1 ha with h | h
    · exact hc a h b hb
    · exact coprime_of_mem_of_coprime_M hb (hsQ a h)
  · obtain ⟨a, ha⟩ := hPne; exact ⟨a, Finset.mem_union_left _ ha⟩
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact h1 (Finset.mem_union_left _ h)
      · have := (hS 1 h).1; omega
    · exact h1 (Finset.mem_union_right _ h)
  · rw [hMU]
    exact Nat.Coprime.mul_left hcop (Nat.Coprime.prod_left fun s hs => hsA s hs)
  · exact le_trans hM0 hgrow
  · have h0 : (0 : ℤ) < Dev (P ∪ S) Q := hpos
    have hsq' : Dev (P ∪ S) Q ^ 2 < Dev P Q ^ 2 := by nlinarith
    have : ((M P * M Q : ℕ) : ℤ) ≤ ((M (P ∪ S) * M Q : ℕ) : ℤ) := by exact_mod_cast hgrow
    push_cast at this
    linarith

/-- **Conditional existence (Deep form).** If the deep descent hypothesis holds at level `M₀`, and
some deep state exists at that level, the open coprime / 1-excluded variant of Erdős #307 holds. -/
theorem coprime_one_notMem_of_descentDeep (M₀ : ℕ) (H : DescentHypDeep M₀)
    (P0 Q0 : Finset ℕ) (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem := by
  have key : ∀ n : ℕ, ∀ P Q : Finset ℕ, Deep M₀ P Q → Dev P Q = n → CoprimeOneNotMem := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P Q hD hn
      by_cases hn1 : n = 1
      · exact closes_of_dev_one hD.1 (by rw [hn, hn1]; norm_num)
      · have hDp := hD.1.2.2.2.2.2.2
        have hgt : 1 < Dev P Q := by rw [hn] at hDp ⊢; omega
        obtain ⟨S, hS, hSc, hpos, hlt⟩ := H P Q hD hgt
        have hD' := deep_extend hD hS hSc hpos hlt
        have hnat := Int.toNat_of_nonneg hpos.le
        refine ih (Dev (P ∪ S) Q).toNat ?_ _ Q hD' hnat.symm
        omega
  exact key _ P0 Q0 h0 (Int.toNat_of_nonneg h0.1.2.2.2.2.2.2.le).symm

/-! ## Egyptian-fraction reformulation -/

/-- **Extension formula.** For a disjoint positive extension `S` of `P`:
`Dev(P ∪ S, Q) = M(S)·Dev(P, Q) − E·A(S)` with `E = A(Q)·M(P)`. So descent is the statement
`σ(S) ∈ (t − t/M(S), t)` with `t = Dev/E`: an Egyptian underapproximation of `t` with relative
error below `1/∏S` (`σ(S) = t` exactly would be a solution of #307). -/
lemma dev_union {P Q S : Finset ℕ} (hP : ∀ a ∈ P, 0 < a) (hS : ∀ s ∈ S, 0 < s)
    (hd : Disjoint P S) :
    Dev (P ∪ S) Q = (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S := by
  unfold Dev
  rw [A_union hP hS hd, M_union hd]
  push_cast
  ring

/-- The descent hypothesis in Egyptian-fraction form (same conclusion, stated through
`M(S)·Dev − E·A(S)`); it implies `DescentHypDeep`. -/
def EgyptHypDeep (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧
      0 < (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S ∧
      (M S : ℤ) * Dev P Q - ((A Q : ℤ) * M P) * A S < Dev P Q

theorem descentHypDeep_of_egypt {M₀ : ℕ} (H : EgyptHypDeep M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  obtain ⟨S, hS, hSc, h1, h2⟩ := H P Q hD hgt
  refine ⟨S, hS, hSc, ?_, ?_⟩ <;>
  · have hdisj : Disjoint P S := by
      rw [Finset.disjoint_left]
      intro a haP haS
      have hc : Nat.Coprime a (M P) := Nat.Coprime.coprime_dvd_right
        (Dvd.intro (M Q * A Q) (by ring)) (hS a haS).2
      have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) haP)
      have := (hS a haS).1
      omega
    rwa [dev_union hD.1.1.1 (fun s hs => by have := (hS s hs).1; omega) hdisj]

/-! ## A proved special case: the greedy element -/

/-- In a deep state, `Dev` and `E = A(Q)·M(P)` share no prime factor. -/
lemma not_dvd_dev_and_E {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) {p : ℕ} (hp : p.Prime)
    (h1 : (p : ℤ) ∣ Dev P Q) (h2 : p ∣ A Q * M P) : False := by
  obtain ⟨⟨hP, hQ, -, -, -, -, -⟩, -, hcop, -, -⟩ := hD
  have cAP := coprime_A_M hP
  have cAQ := coprime_A_M hQ
  have bad : ∀ {a b : ℕ}, Nat.Coprime a b → p ∣ a → p ∣ b → False := fun hab ha hb => by
    have : p ∣ Nat.gcd _ _ := Nat.dvd_gcd ha hb
    rw [hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  unfold Dev at h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with hA | hM
  · -- p ∣ A Q ⇒ p ∣ M Q · M P
    have : (p : ℤ) ∣ (M Q : ℤ) * M P := by
      have hAA : (p : ℤ) ∣ (A Q : ℤ) * A P := Dvd.dvd.mul_right (by exact_mod_cast hA) _
      have := dvd_add h1 hAA
      simpa using this
    have : p ∣ M Q * M P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad cAQ hA h
    · exact bad hcop h hA
  · -- p ∣ M P ⇒ p ∣ A Q · A P
    have : (p : ℤ) ∣ (A Q : ℤ) * A P := by
      have hMM : (p : ℤ) ∣ (M Q : ℤ) * M P := Dvd.dvd.mul_left (by exact_mod_cast hM) _
      have := dvd_sub hMM h1
      simpa using this
    have : p ∣ A Q * A P := by exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact bad hcop hM h
    · exact bad cAP h hM

/-- **Greedy descent (proved).** In a deep state with `Dev > 1`, if the greedy element
`s = ⌊E/Dev⌋ + 1` (`E = A(Q)·M(P)`) is `> 1` and coprime to `M(P)·M(Q)·A(Q)`, then `S = {s}`
descends: `Dev′ = Dev − (E mod Dev) ∈ (0, Dev)`. -/
theorem greedy_descends {M₀ : ℕ} {P Q : Finset ℕ} (hD : Deep M₀ P Q) (hgt : 1 < Dev P Q)
    (hs1 : 1 < A Q * M P / (Dev P Q).toNat + 1)
    (hsc : Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) :
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q := by
  obtain ⟨d, hdD⟩ : ∃ d : ℕ, (d : ℤ) = Dev P Q := ⟨(Dev P Q).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdt : (Dev P Q).toNat = d := by rw [← hdD]; simp
  rw [hdt] at hs1 hsc
  have hd1 : 1 < d := by omega
  -- d does not divide E = A(Q)·M(P) (coprime, d > 1)
  have hmod : A Q * M P % d ≠ 0 := by
    intro h0
    have hdvd : d ∣ A Q * M P := Nat.dvd_of_mod_eq_zero h0
    have hp := Nat.minFac_prime (show d ≠ 1 by omega)
    exact not_dvd_dev_and_E hD hp (by rw [← hdD]; exact_mod_cast Nat.minFac_dvd d)
      ((Nat.minFac_dvd d).trans hdvd)
  have hlt : A Q * M P % d < d := Nat.mod_lt _ (by omega)
  have hdiv := Nat.div_add_mod (A Q * M P) d
  have hsP : A Q * M P / d + 1 ∉ P := by
    intro hm
    have hc : Nat.Coprime (A Q * M P / d + 1) (M P) := Nat.Coprime.coprime_dvd_right
      (Dvd.intro (M Q * A Q) (by ring)) hsc
    have := Nat.Coprime.eq_one_of_dvd hc (Finset.dvd_prod_of_mem (fun b => b) hm)
    omega
  have hdisj : Disjoint P {A Q * M P / d + 1} := Finset.disjoint_singleton_right.2 hsP
  have hform := dev_union (Q := Q) hD.1.1.1
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; omega) hdisj
  have hMs : M {A Q * M P / d + 1} = A Q * M P / d + 1 := by simp [M]
  have hAs : A {A Q * M P / d + 1} = 1 := by simp [A, M]
  rw [hMs, hAs] at hform
  have key : Dev (P ∪ {A Q * M P / d + 1}) Q = (d : ℤ) - ((A Q * M P % d : ℕ) : ℤ) := by
    rw [hform, ← hdD]
    have h' : ((A Q * M P : ℕ) : ℤ) =
        (d : ℤ) * ((A Q * M P / d : ℕ) : ℤ) + ((A Q * M P % d : ℕ) : ℤ) := by
      exact_mod_cast hdiv.symm
    push_cast at h' ⊢
    linear_combination (-1 : ℤ) * h'
  have hr : 0 < A Q * M P % d := Nat.pos_of_ne_zero hmod
  refine ⟨{A Q * M P / d + 1}, ?_, by simp, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.1 ht]
    exact ⟨hs1, hsc⟩
  · rw [key]; omega
  · rw [key, ← hdD]; omega

/-- So the hypothesis only needs assuming at **hard** states, where the greedy element is not
admissible. -/
def EgyptHypHard (M₀ : ℕ) : Prop :=
  ∀ P Q : Finset ℕ, Deep M₀ P Q → 1 < Dev P Q →
    ¬ (1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)) →
    ∃ S : Finset ℕ, (∀ s ∈ S, 1 < s ∧ Nat.Coprime s (M P * M Q * A Q)) ∧
      (S : Set ℕ).Pairwise Nat.Coprime ∧ 0 < Dev (P ∪ S) Q ∧ Dev (P ∪ S) Q < Dev P Q

theorem descentHypDeep_of_hard {M₀ : ℕ} (H : EgyptHypHard M₀) : DescentHypDeep M₀ := by
  intro P Q hD hgt
  by_cases hg : 1 < A Q * M P / (Dev P Q).toNat + 1 ∧
      Nat.Coprime (A Q * M P / (Dev P Q).toNat + 1) (M P * M Q * A Q)
  · exact greedy_descends hD hgt hg.1 hg.2
  · exact H P Q hD hgt hg

/-- **Headline.** The open coprime / 1-excluded variant of Erdős #307 follows from the descent
hypothesis at *hard* deep states only (those whose greedy element is not admissible), given one
deep seed. Easy states are handled unconditionally by `greedy_descends`. -/
theorem coprime_one_notMem_of_hard (M₀ : ℕ) (H : EgyptHypHard M₀) (P0 Q0 : Finset ℕ)
    (h0 : Deep M₀ P0 Q0) : CoprimeOneNotMem :=
  coprime_one_notMem_of_descentDeep M₀ (descentHypDeep_of_hard H) P0 Q0 h0

/-- Gemini's halving form (`Dev′ < Dev/2`) is a special case of the descent hypothesis. -/
theorem descentHyp_of_halving
    (H : ∀ P Q : Finset ℕ, Good P Q → 1 < Dev P Q →
      ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ Nat.Coprime x (M P * M Q) ∧
        Nat.Coprime y (M P * M Q) ∧ Nat.Coprime x y ∧
        0 < Dev (insert x (insert y P)) Q ∧ 2 * Dev (insert x (insert y P)) Q < Dev P Q) :
    DescentHyp := by
  intro P Q hG hgt
  obtain ⟨x, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H P Q hG hgt
  exact ⟨x, y, h1, h2, h3, h4, h5, h6, h7, by linarith⟩

end OMA.Phillips307

-- ===== Erdos307/ImplicitChain.lean =====

/-!
# Kernel check of implicit descent chains (Claude, 2026-11-25)

A chain is given by `Q`, a seed `P₀` and deviations `d₀, d₁, …, dₙ`. The elements are
`sⱼ = (Eⱼ + dⱼ₊₁)/dⱼ` with `E₀ = A(Q)·M(P₀)` and `Eⱼ₊₁ = Eⱼ·sⱼ`. They are never computed: a Bool checker
works with residues only, and `chain_sound` turns a `true` answer into the hypotheses of `closing`.

* `implicit_step`: one step preserves admissibility, cross-coprimality and `1 ∉ P`, and moves `Dev` from
  `d` to `d'`.
* `stepCheck`, `stepCheck_sound`: the residue checker and its soundness.
-/

namespace OMA.Phillips307

open Finset

/-- **One implicit step.** If `s·d = E + d'` with `E = A(Q)·M(P)`, `d'` coprime to `E`, `s` coprime to
every element of `Q` and `s > 1`, then `insert s P` is again admissible, cross-coprime with `Q`, free
of `1`, and has deviation `d'`. -/
theorem implicit_step {P Q : Finset ℕ} {d d' s : ℕ}
    (hP : Admissible P) (hcross : ∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) (h1 : 1 ∉ P)
    (hdev : Dev P Q = d)
    (hs : s * d = A Q * M P + d') (hcop : Nat.Coprime d' (A Q * M P))
    (hsQ : ∀ q ∈ Q, Nat.Coprime s q) (hs1 : 1 < s) :
    s ∉ P ∧ Admissible (insert s P) ∧ (∀ a ∈ insert s P, ∀ b ∈ Q, Nat.Coprime a b) ∧
      1 ∉ insert s P ∧ Dev (insert s P) Q = d' ∧ A Q * M (insert s P) = (A Q * M P) * s := by
  set E := A Q * M P with hE
  -- s is coprime to E: a common prime would divide s·d − E = d'
  have hsE : Nat.Coprime s E := by
    apply Nat.coprime_of_dvd
    intro l hl hls hlE
    have h1' : l ∣ E + d' := hs ▸ Dvd.dvd.mul_right hls d
    have hld' : l ∣ d' := (Nat.dvd_add_right hlE).mp h1'
    have : l ∣ Nat.gcd d' E := Nat.dvd_gcd hld' hlE
    rw [hcop] at this
    exact hl.one_lt.ne' (Nat.dvd_one.mp this)
  have hMdvd : ∀ p ∈ P, p ∣ E := fun p hp =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hp) _
  have hsP : s ∉ P := by
    intro hsP
    have : Nat.gcd s E = s := Nat.gcd_eq_left (hMdvd s hsP)
    rw [hsE] at this
    omega
  refine ⟨hsP, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · omega
    · exact hP.1 a ha
  · rw [Finset.coe_insert]
    refine Set.Pairwise.insert hP.2 fun p hp _ => ?_
    have hc : Nat.Coprime s p := Nat.Coprime.coprime_dvd_right (hMdvd p hp) hsE
    exact ⟨hc, hc.symm⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hsQ b hb
    · exact hcross a ha b hb
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact h1 h
  · have hS : ∀ x ∈ ({s} : Finset ℕ), 0 < x := by
      intro x hx; rw [Finset.mem_singleton] at hx; omega
    have hdisj : Disjoint P {s} := Finset.disjoint_singleton_right.mpr hsP
    have hform := dev_union (Q := Q) hP.1 hS hdisj
    have hMs : M ({s} : Finset ℕ) = s := by simp [M]
    have hAs : A ({s} : Finset ℕ) = 1 := by
      simp only [A, hMs, Finset.sum_singleton]; exact Nat.div_self (by omega)
    rw [show insert s P = P ∪ {s} by rw [Finset.insert_eq, Finset.union_comm], hform, hMs, hAs, hdev]
    have : ((s * d : ℕ) : ℤ) = ((E + d' : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    simp only [hE] at this ⊢
    push_cast
    linarith
  · rw [M, Finset.prod_insert hsP]
    simp only [hE, M]
    ring

/-- Cap for the running lower bound on `E` (any value ≥ 2·max dⱼ works). -/
def capLB : ℕ := 10 ^ 200

/-- **The residue checker.** `R` is the current modulus, `Em` the residue of the implicit `E`, `lb` a lower
bound for `E`, `d` the current deviation; the list holds the remaining deviations. -/
def stepCheck (qs : List ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | _, _, _, d, [] => d == 1
  | R, Em, lb, d, d' :: rest =>
    ((Em + d') % d == 0) && (Nat.gcd (Em % d') d' == 1) && (d' != 0) &&
      qs.all (fun q => Nat.gcd ((((Em + d') % R) / d) % q) q == 1) && Nat.ble (2 * d) (lb + d') &&
      stepCheck qs (R / d) ((Em % (R / d)) * (((Em + d') % R) / d) % (R / d))
        (min capLB (lb * ((lb + d') / d))) d' rest

/-- **Soundness of the residue checker.** -/
theorem stepCheck_sound {Q : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs) :
    ∀ (rest : List ℕ) (P : Finset ℕ) (d R Em lb : ℕ),
      Admissible P → (∀ a ∈ P, ∀ b ∈ Q, Nat.Coprime a b) → 1 ∉ P → P.Nonempty →
      Dev P Q = d → 0 < d → R = M Q * (d :: rest).prod → Em ≡ A Q * M P [MOD R] →
      lb ≤ A Q * M P → stepCheck qs R Em lb d rest = true →
      ∃ P' : Finset ℕ, Admissible P' ∧ (∀ a ∈ P', ∀ b ∈ Q, Nat.Coprime a b) ∧ 1 ∉ P' ∧
        P'.Nonempty ∧ Dev P' Q = 1 := by
  intro rest
  induction rest with
  | nil =>
    intro P d R Em lb hP hcross h1 hne hdev _ _ _ _ hchk
    simp only [stepCheck, beq_iff_eq] at hchk
    exact ⟨P, hP, hcross, h1, hne, by rw [hdev, hchk]; rfl⟩
  | cons d' rest ih =>
    intro P d R Em lb hP hcross h1 hne hdev hd hR hEm hlb hchk
    simp only [stepCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
      Nat.ble_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hi, hii⟩, hd'0⟩, hiii⟩, hiv⟩, hnext⟩ := hchk
    set E := A Q * M P with hE
    set Rn := M Q * (d' :: rest).prod with hRn
    have hRdRn : R = d * Rn := by rw [hR, hRn, List.prod_cons]; ring
    have hRdiv : R / d = Rn := by rw [hRdRn, Nat.mul_div_cancel_left _ hd]
    have hdR : d ∣ R := ⟨Rn, hRdRn⟩
    have hRnR : Rn ∣ R := ⟨d, by rw [hRdRn]; ring⟩
    have hd'R : d' ∣ R := by
      rw [hRdRn, hRn, List.prod_cons]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right d' _) _) _
    -- (i) integrality
    have hEmd : Em ≡ E [MOD d] := Nat.ModEq.of_dvd hdR hEm
    have hdiv : d ∣ E + d' := by
      apply Nat.dvd_of_mod_eq_zero
      have := (hEmd.add_right d').symm
      unfold Nat.ModEq at this; rw [this]; exact hi
    set s := (E + d') / d with hsdef
    have hs : s * d = E + d' := Nat.div_mul_cancel hdiv
    -- (ii) coprimality with E
    have hcop : Nat.Coprime d' E := by
      have h' : Em % d' = E % d' := Nat.ModEq.of_dvd hd'R hEm
      rw [h'] at hii
      unfold Nat.Coprime; rw [Nat.gcd_rec]; exact hii
    -- s modulo Rn
    have hsm : ((Em + d') % R) / d ≡ s [MOD Rn] := by
      have ht : (Em + d') % R ≡ E + d' [MOD R] := (Nat.mod_modEq _ _).trans (hEm.add_right d')
      have htd : d ∣ (Em + d') % R := by
        apply Nat.dvd_of_mod_eq_zero
        have := Nat.ModEq.of_dvd hdR ht
        unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_zero_of_dvd hdiv
      have e1 : (Em + d') % R = d * (((Em + d') % R) / d) := (Nat.mul_div_cancel' htd).symm
      have e2 : E + d' = d * s := by rw [mul_comm]; exact hs.symm
      rw [e1, e2] at ht
      rw [hRdRn] at ht ⊢
      exact Nat.ModEq.mul_left_cancel' (c := d) (by omega) ht
    -- (iii) s coprime to Q
    have hsQ : ∀ q ∈ Q, Nat.Coprime s q := by
      intro q hq
      have hqRn : q ∣ Rn := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hq) _
      have h3 := hiii q (hqs q hq)
      have h' : (((Em + d') % R) / d) % q = s % q := Nat.ModEq.of_dvd hqRn hsm
      rw [h'] at h3
      have : Nat.gcd q s = 1 := by rw [Nat.gcd_rec]; exact h3
      exact Nat.Coprime.symm this
    -- (iv) s > 1
    have hs1 : 1 < s := by
      have h2 : 2 * d ≤ E + d' := le_trans hiv (by omega)
      rw [← hs] at h2
      have : 2 ≤ s := Nat.le_of_mul_le_mul_right (by rw [mul_comm] at h2; linarith [h2]) hd
      omega
    obtain ⟨hsP, hP', hcross', h1', hdev', hE'⟩ :=
      implicit_step hP hcross h1 hdev hs hcop hsQ hs1
    refine ih (insert s P) d' Rn ((Em % Rn) * (((Em + d') % R) / d) % Rn)
      (min capLB (lb * ((lb + d') / d))) hP' hcross' h1' (Finset.insert_nonempty _ _) hdev'
      (by omega) hRn ?_ ?_ ?_
    · rw [hE']
      have hEmRn : Em % Rn ≡ E [MOD Rn] := (Nat.mod_modEq _ _).trans (Nat.ModEq.of_dvd hRnR hEm)
      exact (Nat.mod_modEq _ _).trans (hEmRn.mul hsm)
    · rw [hE']
      refine le_trans (min_le_right _ _) (Nat.mul_le_mul hlb ?_)
      exact Nat.div_le_div_right (by omega)
    · rw [hRdiv] at hnext; exact hnext

/-- **From a passing check to the open statement.** -/
theorem coprime_one_notMem_of_stepCheck {Q P0 : Finset ℕ} {qs : List ℕ} (hqs : ∀ q ∈ Q, q ∈ qs)
    (hQ : Admissible Q) (hQne : Q.Nonempty) (h1Q : 1 ∉ Q)
    (hP0 : Admissible P0) (hcross : ∀ a ∈ P0, ∀ b ∈ Q, Nat.Coprime a b) (h1P : 1 ∉ P0)
    (hP0ne : P0.Nonempty) {d0 : ℕ} (hdev : Dev P0 Q = d0) (hd0 : 0 < d0) (rest : List ℕ)
    (hchk : stepCheck qs (M Q * (d0 :: rest).prod) ((A Q * M P0) % (M Q * (d0 :: rest).prod))
      (A Q * M P0) d0 rest = true) : CoprimeOneNotMem := by
  obtain ⟨P, hP, hc, h1, hne, hdev1⟩ := stepCheck_sound hqs rest P0 d0 _ _ _ hP0 hcross h1P hP0ne
    hdev hd0 rfl (Nat.mod_modEq _ _) le_rfl hchk
  refine closes_of_dev_one ⟨hP, hQ, hc, hne, hQne, ?_, by rw [hdev1]; norm_num⟩ hdev1
  intro h
  rcases Finset.mem_union.mp h with h | h
  · exact h1 h
  · exact h1Q h

end OMA.Phillips307

-- ===== Erdos307/CoprimeSolution.lean =====
/-!
# Kernel-checked certificate: a solution of the coprime, 1-excluded variant of Erdős #307

Certificate `erdos307-coprime/certificate.txt` (sha256 ecb1397a93bd72bd3ecc628416c6225fcb34c4f2a080579c45f59c4014473119),
found by a residue-only beam descent (Fable session, 2026-11-25). The deviations below define 913 implicit
elements; the kernel runs `stepCheck` on them, and `coprime_one_notMem_of_stepCheck` concludes.
-/
namespace OMA.Phillips307

set_option maxRecDepth 1000000 in
def solQ : List ℕ := [2, 3, 7, 41]
set_option maxRecDepth 1000000 in
def solP0 : List ℕ := [5, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]
set_option maxRecDepth 1000000 in
def solD0 : ℕ := 399317102181519648748531027788408430645554284720114800883959866918778551945838634066041627720822282576341734
set_option maxRecDepth 1000000 in
def solRest : List ℕ := [
  291315515032578698547627281349027580188918159068555993733480972770382438888049618962413739555302424865009698377,
  155739097602172039423328334888486273907861355444896092898947255568659847618647263904221080210522788711474915574,
  60868962831075758074997787551184262051560784739233579950184806884133103711739045665653548511020048212967043,
  29665721728531691195632533803920577900115642959339981753906110258875984862068500828272374220927514479406716934,
  3832913704332285662784221895296087342015877180994326681629985217582282334524964819097862276174383942955617,
  214721035420708383343768027523517867334520326587161393543076088854370777210005444122126255015410693449696865024,
  62888689099488841821676100515743207301012358137041007789621849200955824521441630228938780341007422155871,
  395675869305603355333915946579281394657161325335523789766627715004026686208113238822312728562020863020803338,
  4028070703028965276034018103317493017314973093188565806550455174983025864396673001518628359555564867789669,
  22544004482827607956405162579754146171449000402867438945941159414553936902162243850307406719912497480792802,
  1151812493813150083532608916405371584846990160769693839880805435283132096173561264657777168341359886793271783,
  55342192405685314967477090123311330543642148615855030903399808907601770777674077202866159344283198669618,
  96755996166846631016476125113102350375205687756074098590394643296849267559364562046443637458682576788867021,
  6129772801106899429908731162719384104834857532488082704532550539202974941488001947967709598959950349940102,
  7820405325634027196043681425949398246055545624904628590794948189544962681451214089452565063296338380104763,
  1237941239094119440920445255196948988229783508476283483176643337507119537818742436356286573286664542342412,
  60146982777909211203009871566648431978499046418570399820557378701901111433670051014534051329085292177237,
  16160850186151552802791807106500962460703640367690328397854874935346467043196341731640695416736511813320142,
  304954132171933666611419788791637284664275373752574273483238634174296046637167293674208694313542475898441207,
  14552518049811626093297424075950137767302456906967140004335732358677864986183910276498576087175359825744,
  1799461494883496723974430780033249512215099109153760058829625204159810398078075641709759781641052708691561,
  295645115141398306250641133019298709688704924169559763617663836636160079923395646940506453323873057136050004,
  6066434307951992688810258833604281967651103020533855315453191922807459242605744862530975081143042389007,
  1114660706628169564503230771705443244545284524870642328868147270353768148431917775353678829373501842742442,
  7163697140198347968716776937526167001565373778447681129338315666221403227332329596500033338895879911577,
  31630598605116228751531371726879658775134509829925430722580569021168098056829664843038978076611248964,
  14836233249613057450477643594808715393505212383424077470624682666517846292436886821890513753174645631,
  188033291992076640190836091605720567312593772942976149109655625723446643703943045352162801089509471064,
  80915967584803830790608201817818582450627690121095994303267632665209666072785544406938019490239833410953,
  40102114615510058123288116892922588373773874545034027190239554748447661288573550310545227693581206448,
  289924180178625247203965113032104838753299829327779472956712702532169581614865416395635388676168681506751,
  7828276836312638105161534948290649450540111459280221189503055578027880864862733117884950687533933578,
  2522778586715199581983119509875913143430752534747145613127853778786480266178075644570436253732646374122533,
  28236598858233611877081602307840143257435740047866742415278416225749006298635215345133165675793100785468,
  15547186996484253495037338120581878317682454077613163488463751523749609961132398033519566041891730435787,
  10461391785516171476333527642016227640233447715360708292543384803436911864734678907963872414159758719196,
  828018484294037666484993009162371540600320005724966604919513472723162814004782767751599764119201235130397,
  9965957223220601570153040514422336195567264452158310859794850869293890480934011813571430942849910916314,
  353337714472205670026754146624933532209430328798955538592477985558857296936544308878824045489907112723439,
  392160738911507275540929022443276815057563399200681807939290818577156510567897310464304935851422205916744,
  1789542977273363856375749513678401131943190882964099008935957915944364154354860872413686184958681625697,
  25820638629950371893182720440434201254308441502261316127693599770957174126503288583472650670472239618,
  3976919069661198376146525714236343115707142160461483678943143123144897671421259528670694950603440491,
  280245487584027563250963937608233894058383282133229107217406816997067157303468295007519568526909548224068,
  132942070126797561330324480021006488593250503468536107214348913375542379198130125866777947626352240741,
  7145692527439856851985462657662866707076585123840065314220325431652361771187545462028915406073854285336,
  19790548713861660126917101405842042631083934971367227382604710699931811495612511425222224614254685932667,
  2327615595627581669405124949304699521736399563886940043305261659087322648746423742654871857278101392628,
  12622150303016150258703839557780009363693756599816019593827551045722731302049052649228262259692059797,
  1415715024212006030028356068565205774485095581805434961715717303762012964477454844163956678725267826,
  55327831601786998303021075923720840999982621108941748335458372855336656096577227786395104204507488297323,
  173101261267097776656782714870957366783114705917872552229934977238261974215226871874996240192869132614,
  11624149641384491952573013437760056535725186330175840709878895024656713933865639838020306427724438669,
  52386694214468235220383394306400230971108016679033820678032903420289380367245553286925488027636845008,
  31724352865131912306812476571422618875641353846675976032381731814592277885586867662249412498093961059523,
  3122603823966527134485530255857214256040789813245892761285494521131929127023181900561842215088377063264,
  40219923763572496763663985200656268766119860070322344256292276601994705203025430514817492586081901053,
  566494703403999053174645198620959033946278746607474392987456989987670059810533818804684944367268614,
  171586546679752447721250675812476841159919381610672224103696377501227828023034911428529361838153011,
  2312922950120297138474101937942376942439124606673881697422522144216105742252030421913496041176014666708,
  556878968766425192264694610494414702613434304757079305798983523063008624144738676796453109796024461,
  1013440570909703268542536128977100718016980151405206896509532351889218713280859136662461483069659712,
  174709007910486094722741122090082678890130935485386280821133356905191416879527416179111729503271371,
  5900640365450856417562368317990043377011931874026713214561565255810559552973022421991927847307227966,
  74645146784463269545434182355000314579915205428551880105585991057887595179010897177161728829075189989,
  40197425334706261809870038257039699749037893072291498944658677510450642752653932400269691388042092678,
  34184022912649320171673961734693681804520913583696267884742068685548394792787937212466512902173563,
  156076286518397277466980319057294638158931415175260374482492721618964076344905684965680538718618730626,
  4235953956698971947851371660510879605439280635979694556857894501300660692428719869143181268703933,
  83128348375433640627830181233164432494407688690170420801740187434608576921643538870297130855220623584,
  50104110731637983374694458693884641443149556975282022565686180142025884666281854226781776892684152867,
  2698620375743490600298690242600491511455420047005433950602237955582886927859322998021609059209972,
  90249697633145369758110065547451426355521630911613534384046133324419295083564334098786057009509,
  687094587768024736989212546724048576879241480867338261449562379955558685311118852259236633542915344,
  58031798866427129101310131970899189914771180830173997866960141572556038882180761473917207383185019,
  14732027020893762066384982749001224867709477365744528654039171357255955534345374474879383528832,
  16356931940727925130949774129930299931269853237373537191196158274285640962934088977747289168287581,
  1784531071425488432749110387198138772635826865508450646358386019717882423287404792847710563130829406,
  142948764068386103704969295956244858724755284955075143544405085720185611472893107553484446515948351,
  264770512751553398550867951443595074816930116378606836388109158256926403550265658211540918240811054,
  7703654809470132478867592873630565938745274580493102053276434700251606314554524478375819999961,
  45578083567809736762654883431616444461005216367958402714027444284350612458549185400066728464836,
  44811502449852497631166984910143494885150352792453143177676667206698615558109117150940856581135719,
  2952438172611717645940459845705461734895454879507800892414881186775362831425641140968016597574,
  281372192042494473972013492880224842722057748055865443499811836636089473454071946326343081193,
  5835563642279286936689805216327558378473635294760907549479156735700621354709735185897504989986674,
  37228462439553357640517120501373469763475839787875116047685354560234003146378197973168019883,
  3829559799155856032735961428550060295322680698686026929238639967183620071629353467127637931716,
  1269719321946192561488261237097158064780487161357363841692346345230378905977894423804929859026749,
  288297741169912035196754635307880864309491893521187574955551824552246033319315758170350240012842,
  739004546275410314817084405421799279184870224719947691492772889374310757547715688251180518611,
  1429397090616488461190583497991732550036132765499436584118377743910393050700299060175990501742,
  856938756965338354597987368417674387468715836109329756189584461095182486171805345052450979006361,
  1885433927898219107758067305418754081598460050413588401092969244447883582477334406495779519328,
  110383684267307559794514571373241328929357682367612898437606372780028192085976982996023112415759,
  75175137111536528403942266055303333659190570668878440211388254686759083818051484724240046673046,
  24251094626645706395060718196156604101184468020931765341574603897023406001211707681306012062057,
  982525823513264451191918638341483987560791349538823093813264102184362931562241332597347028744,
  434117276351391235388518329947635339571099779544533369686904941926661878044431036748059087727,
  1338273816898962472850798302145008284966817525831901160904078202926544550318941813933710546876,
  28046015764833415749723081625325882298888737135423116754219300768257657475445533354225775774713,
  228605617330645986516992714743200530144738206035711902914637729528700301677624167938022402931528,
  416421125885244961138415475413558635105521604368974271326534231727359579944273286513303471158471,
  903870417162812272988538619639216402575538666184665371397808756324244796667597408285077873598,
  315913019719521049491774810475166406345080063006141546765371711865697803965316306254706810302241,
  280346504010160088392651999275421298226933602122648615891362513859839814416057517210522032622654,
  85545524635316175909205944557009431559129382018366053681307758372336742296495728887655911,
  54847471399956854470082528215514146872501409083225469026176740426737608769264542184064142564,
  2374895560693589693886700134291076767956481783207473688072637632898892277304926147617294361,
  344217283528539639824835483386057680231744012621814710980862355533215881095130055282358003936,
  742172837526169434058295388173887158939423164250951925767366188447401091122851482006579887,
  319322257771445445141478344461325417293515775777903786021120831836422932379871220700658023396,
  16718523699045485450683425652044269478046519965819856652665301858982359194231539661556602163393,
  63018982266002760658176908414032459705521629202989321017658218032257853709061497696395213918,
  2019550558654479374130198896846196871708422508245921520210441893829159997882505507213288343,
  2705306351793113214638635526593483116142205468461986836550215681095931951973058025926133214,
  42081459512072209394575328466290657588390521415278856002069864143336808445590263336385757,
  182536090775047693707646233785541638701472619521090555851387474265026323903335971682617142052,
  12124525697303838521798586815028486544929539587272231176434134842250224263559188470413139643,
  195504347705261603700888543225332032941940583726947557109735262158989157064517710476412745416,
  11344974925647143294801583945642562375508188141012097997803687780868519827212129355500943021,
  130448937881291799624622323456470775133962020895792956894665044763115818823814688904062962,
  13556367892181243525122996333861603096379064004733473475586972509691464246083267499731051,
  7847250004827610560098450392954512963481624329789952048905249764630345873973942885904732,
  13671609442382822207430284104883839474495067134466041793933012696486105855636296484995337637,
  3790170834289223293219212654421866712907359133148583413453229913618659965188968811017814,
  19457695975613894694897689544661718520371638695419225780904998261156362933539547830654069971,
  53766440160588283573810389799197399777698682716351130389050690490295063621177410646893722,
  141689467180160608773063689427855520584360488245484237485168117109032208070405254709215473,
  2805831786970308220454301140035630057102084171132412280275868431870495025847260728612418,
  6289490871822417102812239680505640177483291699763399951773717965133112905472091432531702427,
  3384037191381884981492834977381210003386708330351173417746562559664299227374109713402765018,
  25649551614903866539825691475122581488145277364721394245398595897758379873226055878908761,
  210436236744957230948252701243452593657420267883348606892490739551515589298148649022352448,
  2082711197386553300271134825024520413879748062129355138803160862614507442357080307913800023,
  4161622934692673679836672794272206258247967652928044286758775062098441079164704010437748,
  103470829366647155994241997493200738307307544110281439528893443467860052373506236518036145369,
  29108155748389761199329598434211042245922893364372578821002027218605406891978259391384042,
  58776984839258958781575424808492286236326776387131444401792020673689062574828740941959,
  16796460069391676147944932523312229581889163324024285481733039084953854340593185344790015926,
  138315759226580171555538977551917532991923408132933091401823788719612423232072022130341101,
  1594264926897115446483899599854248243758123835562398992192274513088368807705589917695272,
  438728797245799474111880810231993797979277519460379145711201571939250468063792005349459,
  618144400476147872390478685526286789600907513086258088660085818454765278878878165431308,
  29396938084652937461316289016880811525227767035461121646744998996511619849519274331960581,
  2825605441809406634332884320296827268963451846448911056441139169789976116686941595778,
  54853273824875462188022618735388175883000358081410656576144293738255928574959293478799,
  576064981249136146237894493052097640650205967207052064092843380705445919038239802129075818,
  402936606910232679813132543442125686616544829251393765690283806073261303324990485579837,
  25906827253912545741202696961016020421698662893859455091492155522910406398033048049286,
  15727283831920458598461673003129168378931866695134335219848173996197198834762240939211,
  3426797742624633774663917382126227704672977223803952095148317986333939190326814759191316,
  501296323965474942264995975298868472125586719245483710361667486662271932098416827733,
  10429807464008700812466849158760028432386567938856876293449740989805427199236494086944,
  2952125720644315404720688271669705951256100933142165816152827594276930628977490599882443,
  793075587266023237144442598971101163579162945405898402171346101141055061806980564366018,
  6278395023623075754221478981677054180756940171332004394821309365012629317185016222349,
  18439894774818650983311420184174118371386567304606371251339966055443792336868876105978,
  1718738629073104648260317703852189592080476160846594181510288943284173767622289267331,
  4730155081525758476908575918037398890474873666242154026927709496710102159919189780054,
  89244008168697703239454295904695742581756332758586189319709746877400929209364701857,
  283544531573917758496871406240796508387684263684693307046996686891885519169225406902956,
  30828348234096431910297760851250206547980298098224419610539107741078707785149458321823,
  1404988130211731257588894688908081485439111941898885667417358757163479826882256672124,
  5410287618663618154127404850379929186597053521219622299847992061345483455819319880578257,
  1871787659066939185193343569605705323715913055834182685859477975163144353416716377316,
  190734133017572089493235313966490602051573683632239753439012474164994314050333155431,
  790354930586583398734482848598165338162619942088829983064302368804357644218038873985152,
  4696377724329438396539548217981190724952355305871149604505026344602358869381761041,
  32952389645522772320811364027432740764304526527606846269409302486958906507224345874,
  1784713816752137124259073173965741220099909471871938301319175795380987755842462842355579,
  522566990405013596011198020241540325899789275095358731463915109354903968427848927694,
  9951668634022009795229440283750892697024728262132622207736504902228128772198950442237,
  2170957911953769803021389314632953267706078010054132257029283602640267030979074344663892,
  5893220757153292423890332433915914945108835031537198135378300161462635384786227191363,
  1536566044401312423228869140027916339147320752011604057341921334819603300109649802544,
  185910648562970073369288661320083091566844284155099617075899881432946301834472471677,
  60306435593123055500747216119226400480608996972375361627302153005511296762423942022,
  3981887409422494751024731452686459951632283175770823647327551194291854055197695116959,
  17961348807236157668984942332146724814271052014039604940539964681376590677521349756,
  20458262808502566393665743458528288477845202771149275803970289621329799917445396649,
  19602250258294291976299946119957487486337644661416746849926123183620482012690399756268,
  12547430440449674454475187928645519390850668263184036603552994636686270756829943511,
  3901350426300922100131667944725999943618420206469357293854101894302458365871130244,
  2132904056801232905911130134530914930754226795835640813974177211716923693015756956657,
  118539433578593004127481426151578765991349008729898676665205555220778515446769971882,
  986389768894008546178481412555645124232612496244777515331666188242698107897354487787,
  51580840911235655793426203255603605480060544027196755180829197585314506890790816,
  2355207049500501565184111569896050365560125707896012806676116106596475435003500605477,
  9891512971653686924040008414676420463281781693324573317327896706357767874359324,
  490397395913676500618001768054656714921803436149160105929643556310458481776343659,
  6208806191620589319501361931177898465707049164337617202968495355543286970208941272,
  2183984932394984335846732663791017383906552841538417518606546635343826588254029479117,
  14135647461268488737789828573947743383012921306393266116694744738574889401060990972,
  251838033395817390666480853497609798396927714389384658221502279938161340701897011,
  362739380765987778247349068605844532552398005142789663739473850789757891395643882556,
  1827089539095030927234072292833214593142071378368259690587447976329567623277628019773,
  735956356427858664307337213910044139734692235311045258493424730249237239259597955588,
  1989721389437413947862320599122718665044952481390924783463156778782622797839846304427,
  553115459416731740219629344390325959983996686115916147387696853703638435908792289584,
  93940824984365828282815299736372513063424226100672805973925713920998490293834301,
  102434986473450730987164540428340562213363191593558885648381550470214600118541258394,
  308845667285570391610882678314660154548569119095625404944537187451307954475465703,
  68224685102943831709081435080762338904899163010708333283835801171220866482006306,
  63166980771493478714128618639251239296592883206154352893509328646819881119893049,
  60052995710397856836216489040892953026077304689926575547522164942914283988474255768,
  420589124453863408860776925446466446065214924157698562076975765453564564273231,
  145220345257647823062089670473088155156963290381077343159267685945457299219988521382,
  365253783078358066615485922816242621485205117171005829171436308897465229464833,
  7131490415491114915250793393630802376577811136330774646925852170015743081036182,
  2534665616071486336551127831308689336243810522015336103366356473119036177815051079,
  13067891161960822396128354348515148981324162271275773502522166025577149865452,
  898523655315655007479683560745924962859671975636867621333145932569109075331256809,
  1727097767069891155357366253017076321296871071519129191511510695818471259703398862,
  195572394540823368319300699459024213928417334767578251586984122466917799751915287,
  47329692369327318496996557147695344907545530395337996198184866403207429973068152,
  13434686804930080968451217597351085831902903973090306763020257246507023751830457,
  414405518719009419332073542852111169398096709495999577429463488007916812032432,
  150566311609019361015428215102956466750139868462649165907102703784183542672061399,
  24115356113665394708772421420916937151346589400944088561244692887127237807705238,
  13694853484123133644136590455115301549969650995939155315834879131218000964220933,
  191315114420489310117112305443096749921584750106998431557042560975828914976,
  2567673684141080873902300265358990335106355070188735966520068539008726610979,
  84495040592402259772174173671649672113700010139939878259247061814027960922,
  61643897853220946333519688029986156852774897288034074154683285728940535342870693,
  82471013971088391019620300891045835657241778064472395879599118577980079932,
  30410242655879768274582192550537785934552914472361078224236755997258845226619,
  20313944565583228257700377278055189239328511412172129774462574340058886915104,
  622541177520530898453968164445188672372368557664975331381827549462443252661149,
  18919665517565089260760237719620144403565823203360422565403190199003113858,
  35003326544747488876823631206912323312826646804655038023375810005409360084563,
  6984970821228620316406453158298196254488325535373977403726698324806734341758,
  16815220551443526679683245421195554822497026938484168918598102762623758300709,
  562732939205189742992024511268954385014844469896191823629591368002140405890014,
  598635620086675242522317521837754682791072483995937061532520764664291159856651,
  537842692551104335050468748092443017690323858237885393934304417571262792114804,
  136409409827764663877734349747097006229787434151526563098884425760229868013,
  541441014467259730314096648795232021215398221100833342382159622747370197248,
  1990258877095965219691180878445215015163438193893356232275077009463508651,
  24373359956385483779535830803289307630837670281409233017816569226542201926,
  24436215255953756347138681018648639401940259849226990488160209080302202277,
  6594977661855085960566528475138440616723504967938890646838709725986586478,
  48705902034206655813522613819769056591530875530870682951565358210617734023,
  64520110729433748611572570320436004250582334600869526921074181551294797926722,
  3484074862957361988424853654866719945016015147851271012532912096381042342873,
  992054999286286946651888918537011223234228137831208711200468851874918933696,
  2538251831489533724549141296270631874195018578800057696445812005401205471,
  1834207554171271538694904826861860518284807423531170486253453619473713622246,
  13188079993721508113460102504377804807274262056759529163650546912441189737,
  976703127468772546284038583388127119208281236823086108177600408394442116,
  28331655666085909370077229400551819828323731697625624353972608614531907951,
  11094238713893806290433290505408907656436919600820085937846888044492074895012,
  24035686986877957252483789156495329579266176602886496462315775873693291009,
  19238390249019926989823479736562745544136744186322281346301073347513359066624,
  3607477483585097611675236115395495973525650558835507599314603427358893807,
  42436293552332282666200577054298117662584620235998179697388814025133073864,
  14438432999841379681744171899302060644053910813623946406647995636144016521,
  75325322725202490956121028512292062910797627298513416305968753885983978238,
  27257488463287075223290776171272695683444025692220874234947902795873987,
  460644792526037439173882240737092234465785585441196768642074563366742198,
  410282365139066838834661084991240736731777570871739861299241727550850689,
  34993973756073778587273520387850556335389128906174036787971442185526354612,
  1425953383033421060109790045911298038351077959366395438899625611556403806799,
  8638273161684707858503242169854021759171021091740066102683504671882434133532,
  530281490955736155875430090060983406218686698531283245928837720482371001113,
  4725942654744203519566130271888970219846866826972689456055364522689360624,
  659102283569513622074961457288461522896689610430480355232291180236228678671,
  54693604798077375229854301891483081816301797065821725413991053663805328,
  125480596624878795571364398926101111206060678487167785020445195438801,
  3783141882118523849955213351387364570216883656799476645976172992741418712,
  18301301245431032872995590765856366135603512134092480950920788959746132887,
  415766406378403917324001256974618418037909964950343665610408429360982408,
  868026624330255731952889448223699916300645834796401064997732145023976953,
  8063639346692102912755889399262089462083070577374156203432086057814,
  4019921925034190369550755828850921389010005781571974493320450970139237571,
  1690906937417704748698911135579410357775705520074780630263859153743973476,
  34727612927891461645469614641878423835877074964094834397371230175781,
  1212349640301952763721323658852243777129971650837665651929134185224864068,
  1277856988868494700935223985916262688402349714066099993262645174571,
  24716832525418953480300251956957574468151680211961391554020414850962878,
  1664306899479305746918352996664117435591621080758747640634770216118593,
  227004211297683636393134905072272044345968885263683668215064050271302,
  261781072458227126753107738611151889820396528179614427331053080652383,
  285238092617950350783401976601352404051148898101105485410875788059515088,
  5098160300411623634481760721670453810832564676293673216374539338681,
  22325414797003565739432485457388951372274908892039312555998279281592,
  87303814043382118146404699912951280770782690071832710812239975741423,
  562486956949451329283891237522361471591759814186107746915722087404,
  75033505908201077354236799686413122176820395248009770922467839907977649,
  191724511414931604397191713272956533261822361655121809222574875256606,
  827453256049905088488377463146174160235199602116974060086421780030947,
  5528553098051280188525782578806184128899499760873319793715578645442,
  885467492951355832821154366483464378962649090477931430680680629,
  20593840831682794766672919558943489901948343385005115273421633026,
  4014783129093991927583979502801847642170774352521791937516561723447,
  6061802604309907254013908709898590264961034198590906032377685872,
  167899789696750888077940770172477550816069865373988457913980871136153,
  2402970326468401720185700420337502330587898819201065987265650260932,
  86166286743455722648172211544649930884406914156390240607634668920999,
  14097081502174095351401785317133523911286478123819316460484775185054,
  414409494902805319708124079472777461354311752204646096030370089,
  3373451451811410512864396596887449779479385783707463443388743456,
  43878618195772207455413729390037215557954380611643635434288304638711,
  335120410576817320656935538780674345629577968622028338730347275622,
  1570352392139577601782705892104653742711683976090341322848280137201,
  178421792725910431600416685918089057716075373891859838785726638,
  4258459481018157453424594884319632650900717347619354312283436651,
  436989951757901090853981616432651356863554245380086703133538924,
  42572193135120401437340985148693406643747715274458659605889981693,
  79774050673352404655985622812920760562920283082866147102117388,
  350910133485290589874569455439506544486143786636397878376344331,
  9755965987505572431963632302958166498818439323697692429176574505634,
  235220989616169896616416673205988691231081325204911386466090523581,
  1176196825889305511687835817718614539744306617314372520127774086,
  4923028232377161238495542175200031767230031338430841459249195107,
  108676459490585011112584663395601830292744482976444022777147566,
  7784167985524730209615502329755149809684786019091751198238529,
  3346172358525510856522881950416383025164627716815112892126918098,
  2262887496083196967119134659506003711723783779001426723117993568191,
  175377713980610852442949184722434905015192628634525150782758314,
  74236339296082718873785370120891311333018928856868406411168625121,
  25801232196860991296485570327130367166836427220933956668521918,
  19481334523885294652693170118345055457996794785462556391047515243,
  2480966647413207078011271514782069784686657669236593494728706,
  485276306469200035985396276672479586428053219423509228221417,
  161468128784967445271079451740845048408294272526838220287504004,
  62667587831950862928730160478250903420391459983168662870295151,
  2556923638451906520971109548909728360791220727988323533228311636,
  18824341575458021800730075823189757598390020029814383464279490793,
  9859675285836706326225970379330069468510632851177122134459996576,
  17734290353197345949262497932318396774469515070653991002599,
  16710871739072660372913203358865413554326699117768026677342,
  508303911031352914074054133828880741109741877677825266459010657,
  1776235697018199039887330403275238485187906910845227597913795262,
  3327689485538914919320670386948456537349344373920191614390987,
  3949650928040210680708893630519742119638439819136606331689752,
  181389501809683698351865314516549419793235812816095408124172837,
  64892194654390665962036031257718492616156744671661369463562852,
  118074916144041839183108815623111352015602873251393922619807739,
  116458889689091280109583240416932323191696397689748786264016,
  1191607197836922285693452782181162119549696680037277427293344501,
  68025906480315189983544028869712643707217582187814945998902,
  2217123645955842522250372525373835942672799263213256086337947,
  296300472423588374996901873016582865671609789411521414923758,
  52713897098198418388569772433201339841321271977804985652177,
  31248192404270513179710441381146251671949863728979949017151146,
  931464509894839846437425820487836319808776169070431756020183,
  201388077907758234196981846505943870243302800124683941337038,
  3067655454388884903249274711845424132827654442485174318167884589,
  33227340561079279709095889795466881846922902170622886572959678,
  337625782093410238791856209848497028945898959286171124627351,
  2112049248457317952154566427259266795172796899887127724019220944,
  5409445217223345283007548234987539202239941654765727550582097,
  1300115470236614948528172990426754410684038867933053141065249948,
  354625148530555037363280004412880230519336796220586271286266871,
  12530255483863442208606568697400006364095625676535401650796,
  278338992861669987484804293870237685687405303994210701423633673,
  188775954153097543419598717846133592611685617429158274608812,
  97861635925786435191056497255406235496359993520014471002624407,
  106031455871838954841045511875716068037160176998262476354948,
  249540274316875906949873869323381283011642474279671508809,
  23911274553878926852127797146100681880985848330921450487768,
  3547481350094912452815436116859980420341378643980248960792111,
  19099370820541770571929535421191803118093701735968881291086,
  1736150133223410333356313707675069408489787235430737197341,
  61806869835618221216944818448844755041975303208128844831836,
  149754903490687331478965045271753851783851792994307685891,
  5964424809286953836927188329984410442156711395606176773517998,
  1152675576462944275874497331341998412854647977506911420391941,
  1594325795843719082229852206092546211462858641133837678360746,
  8452958561948684852101867831706181257789984780068729567,
  8061723646430440300550648357936220444665861618040819177084,
  371559413536482490240957482414988788896268737642577636641,
  833508793952322877659817181996729963281482681198580472592,
  887991392569132814416448212869892515480159588895567269751,
  80765952041576208106120331943345194408836474150853035324666,
  1267396973935768541921157617589329857033048007017949090553,
  16986216957376258336065403920919155603136155677005879214,
  124414104752184449660787393544108239788212366894620200367,
  857028815135044176762322470291690007200447375846816720206218,
  4804885561871064858081553878194943915118054442935088609829,
  537660758511597223434434210868593016982285344336205129664,
  310967471804776351423316887391021139597284567117085632001147,
  181729327321215527851390639328604256845060501487936632616,
  509451383203602131089424617002319032672804875757154069,
  64097184464345206264984729408470821645694613209527311098,
  1772166830691325949840866107422449898053238330042194931,
  356518791556905468547056930286988323907205873182594422236,
  29970312973687457535114299997094560870589211198142592837,
  1187248613318775531855271302625915613755639331582415038,
  8086394942950433509545897071198830970582171932239912063,
  2987091934303340533400230387812665585017794226473227806,
  2062596278690756714442773078144828607191727982553381,
  76525954151838171895363735371564315209260529086997704034,
  983572706461401100009693508786162280886526292856879,
  2349190368233516391463262652030113188884607951797222,
  207817250672769173768070865321463492618926633885889,
  2059630779082905808124529037641510590816997489773924,
  233641760704175390227045410741721528374098836876660663,
  13922307329297295890052332146563900746557586659520897502,
  68070468606522571057763917967546894016407032422280352609,
  343877442527405756701174061926934258325443952718478084,
  1309438561244431758761191576799261063540815227657559,
  1380104302828516930572031662881750614937853204896866,
  185645256331037751838906924129848297019249727120365697,
  938950023051363856471449637232922343644086253108014018,
  1210246953804687860756806471477695873314640135184327,
  30835832343908753890109860866540980050998782214662335024,
  37573521803765232554554557900662735656054579304073,
  23344530929206536360491998802168431121707391184806,
  810432576665766296001579314785328149185792163571775779,
  1658305680561064485216590616191507223784618027007752,
  31281346462313424653517086031369434572779873554920557,
  59178764206727640837816804784369521181928446286174,
  1711477041061372030118489178294855594582566076128011,
  108249972057413281571371444613450723395997639882630392,
  66171723167493011161428085872305457933258194419320269,
  177701594012316499927085514875933065178075133665332026,
  1335937360098497375840260743486727633767680458846790587,
  3706160864688474878434773150162292892347076357142158746,
  1133541863352860752349576161953815785088585211348304989,
  73381477163860430560052897938060084896571319313837206,
  4235792108236742245363120003538827202338898111499,
  4109721993544734576316866422223751191623126379144508,
  110140941882199993108300637086268802291641846558197,
  27089663212090356674368262600371635852482781123728,
  43024247483017452944169022771887351028050924404891,
  738024227120741359937617266693526271114514487792199778,
  356653125189783441716200794819415555655821086334813,
  220334065419051596447142201598990675806909559465449426,
  1415738141892301863401103098301003363492616000865699,
  258198763140690669989487618577551715735966175038,
  979765137545666280789946047639569817934455355555989,
  106012528524934866230737262151973136650424596304,
  12872356529614349634002284534382714393963067052405059,
  29144853028153996152607135087907802201218472306412,
  1548104175597236491222377713175207774800639448027349,
  3623083089029395516722898775306465607533790770286648,
  352075646659775244514194618793095459061347218747,
  30156972164120288054250911297210965656685606529696,
  76307144965629135132045678744316777243474773261,
  739601578310714148899766704035137911495583591682,
  761274960854133291876434039118935014665051740480239,
  69637178217941598081559120991698482935603732286,
  15933607326937094843980917110508846538721842894375013,
  869055055747899654217642019790529340401370025292164,
  6094121207420521611413783376766185982768743909667,
  191200605317538088147846129352132812894549550504,
  198484323801806144499182977638980232967792173837,
  6947436696351865793835151974369053427763890039214,
  1334542904917991925803450026178537035961680702498979,
  5112170679714796053849604545032653100226165176684,
  579284657318361132527303435994765891592920039141,
  38579662043322478620267882430151418907342792852,
  324611339677789734594657468902663312733486209683,
  83317114250296997970823779386168305776803427573818,
  1561264314766310157593097571158240359279623955313,
  222587476824221530892483541916456320438806613409486,
  99216566582881291327143429821544555001253282583,
  749723346783408912985706846610544067282133578,
  419231024704357806520705234148943659534212276956593,
  5927198983329416133332910810070023448562206299514,
  260710065568476298949875756889951361899097585623271,
  218969188313018962577099427223824344577484321180982,
  2296553289148162186068309740635037853241442989,
  111540768236333378652073652906207512412495578,
  4300050992143697919322630615511632297243761531,
  17878859276099530109074359996829675377392764400708,
  2100682342406395041358525059960844616301133813,
  3471804800713333858343346103063323828167230018524,
  16136303106602056276896326578294179629322994551443,
  228711791414961651430931936686845547700102321724,
  33458757324488131181949028321688496820213669,
  16752050514377252655477998972126546676960782802326,
  1844575142515490470596596284744147806787268039,
  6471374841136285792645510194447449807493172,
  1184054267162027481724944302562297229868193,
  62427563008962773200459983989900599935013088,
  42449231442896572967495630342805404517833207,
  6466800573982365257840912989574299323471371062,
  2899963661979981049878864807699040842115789981,
  5831979483942188391150244661251756542844718,
  81338023319172255113015293104459614987411403,
  867052646479416766796380841235355012225474,
  991638395474111595591607591663599392749261,
  2516630347541913601923078841820841634387223358,
  130452640580749393314860501607598960611843779,
  100170444539042216052668301135048929923594,
  1289576859217590787505679068296376865335941,
  29384448017503836318050451564226592948957238,
  10558067014319818749263763860521092607931,
  1675399940865770242196038019592447045716202076,
  41829170539197488614991936374406342788687893,
  2187486406190761404410282388797149427852,
  52689715577295758660475747196027760773075491,
  12447204544942379226767249253615902087581522,
  2905435691243820020361991750769891297232253,
  40854504871367201624343144141379825384122186,
  1343909922087796433914102613474115972023639,
  537966369926693343053782022179937495706474,
  623847327602575427082681394627599940249,
  82462147743887278759598057076015851638869484,
  36178070575306274923465283854397645120753183,
  61209402997530101663027497960606665574141998,
  27375183890772563430628424356212902249701,
  170221906307327118562041725588260995088182,
  5658498739137978773890406315287188973152371,
  44359891757459684314499627248181321826,
  348821928968210829513432700821828036539209,
  10447424179576798217936344286530055565908,
  615539830864145171521833193814737247887431,
  211496132134814828037592007570203290118,
  20666293347694621150941815580723335958753,
  30988811482537748705229842347131698257124,
  143367810287981115659757393596753210103,
  3539136783107491215261668232287995198,
  30174421401367889968837474704941581449,
  10908012337922400460987237189532912345528,
  796558826084157464779436466800283103,
  30855817280010648052971771125881892173396,
  12220776628640528056737909625773062849,
  456438859589274379801393436435081191694304,
  108021345375004050611421382405638606103,
  18032758348201838991143378570448058782518,
  118030277803929830610058171562706537509,
  501687106338158613916807042824485740614,
  354762638285220150521274016723003670598739,
  478561588524416701245951102302919966,
  18137094882245246811802928585853159052193,
  141003185232782753382886431973346791413834,
  36317748460045980281357474184325082452447,
  1673525193627301070000594577978791778,
  169020582040560552285104779954257115457,
  4166648901580757933570467759815946038,
  491605543087893711513022397881013179,
  7212311773336423131439686264303226212618,
  2911499542571042504419198653876603341,
  388542379080199130356759309654489403574,
  21793639750397767110178479614991912610831,
  666991543742070225883429750546331694668,
  2827939841723952616533840813729879092657,
  16486488561419159441632036923590706706,
  14881258245763656006325109559370386579,
  68119446210966329762898719196499755044,
  214503025105488374427265038650532517,
  41752832056289710638848602821897815304114,
  1281321509587440155584827172845210947,
  36931914044167268469911063728040184,
  2537834022332745853785030643560315493,
  196880335069741705091375571826096854,
  549859614763512762099092257696946423,
  361394367986120057243620185418579594,
  913393145932054737583166412750737389,
  1650357225255978210508364820469501784,
  196194243611564073649460126194180227,
  224502075942567773607783176373310756,
  591189725741984347610250676451350981,
  1013726866277269702366961157316254852492,
  1103399335635029022728792406819767891,
  1205414695161755955977700211520808,
  1956263757670275454567546631257741,
  527651893393772524155986088164200364,
  2975353701102886507283830727406477923,
  60317816634017333515871744205056452,
  3297410482152572948666101373348120389,
  244934515098712104359623778474730074,
  48009369238457057393723141713240743,
  12209089796864049932986852420739572,
  24596361282671864310462970737156193201,
  1154417602828199707776572953344803934,
  118113956143990599218946895687113966143,
  1998440987792128460132953960909314,
  1439864111029748633345330371958342521,
  1796597694138540644288775915234037962,
  1138904627102869506533068879106917379,
  71389376714839991964408931316197474,
  1153527488440373591457350290087177,
  4801016571498208366617089458450960496,
  1606728537686861743850993806938863,
  2759960919359465050597227068587337122,
  1025107833049831072304674111647201637,
  1028810097874137662504290979970586692,
  15265619275228785554142791339243,
  547185227028673930613243495456365514,
  8676028773005429914428422373813,
  300127940303517040067003736380391394,
  3389762483312755692726197740167887,
  35068839042524749350428961258366,
  346025128213394360011864998214818517,
  104135394143105981785249648824792,
  33599702108774215139237100298809947,
  13684677689649628878366348567024,
  268206588684280046653558184156173741,
  184828601149165053626873132234384,
  58101343892738591518780035411,
  65681953276387045894352236461496,
  3020059653742179368986513236914861,
  412051193291368356351054385729746,
  7967774610114527803410690571,
  71317584735441245931932166442,
  15818124232855553843024613015909,
  490793512979111861867362356956,
  3279039718851865055590700946335667,
  274510467108966271698150680206,
  88358453191612048301037009029,
  471380321184078134845913939924,
  275292322253901703513194750668379,
  890432793812139590490989149108,
  59648426701202688651795980173,
  339535059288194380230661972934,
  397693948696881438050183343,
  102479305246988315680194194224,
  17779530352223755670557826016081,
  1015371438795097117756266770462,
  133706760081578095642782049347,
  136430281011634601372446110609832,
  54399670929803355718359727109,
  22542201176952130751306924,
  78281899095366853888034998531,
  787659355615839362744063842,
  11660761559527271532579125289,
  20836871088951952622839574,
  364835722695333513774012243,
  567071623062722498732756482,
  2669197143654907394630007389853,
  187539296610423886171727726,
  3844053976100351716796749366167,
  8816391527976732837869062,
  2687684578151078461275226681381,
  4367631420372442063989582,
  19379114243143731334123689563,
  83411902221524113236734004982,
  1214806212942051551975031576873,
  550758700644644138783858,
  100218746684711519238464643,
  6282958462619759831956036,
  456349456242371383756781,
  2325860311665934552124948,
  13172478021227584165017521043,
  132323814782842646178946254724,
  291036919383484530569850093,
  8578759356888132782334158,
  1510010808719810214444043,
  27039835128991885954297098,
  9823094311134155005971761,
  125773737922467824713253008878,
  2918050464975932228733564487,
  42031484014584635854489358,
  10836422496289278310994539053,
  14743076654443229927686715992,
  3219984455107011501950590051,
  7185693566246244197015258,
  383389987378179845639493,
  710992765173936794382742,
  1331665374445549495897911,
  139193273497523762083866584,
  279163190639604366078287401,
  34135559424983575152474,
  3896204622048457458199523,
  1236779573991023942130192,
  572909119405974825523789,
  118190614462371017235031306,
  4810219594965298173802617939,
  1632962961436841294319054794,
  19623215994195262395869193,
  112240306370507939382724,
  6793475391829683692305952863,
  10129820594208118659345062,
  42325493750742694580638353,
  1439024530475850334500346,
  286879308736300643290687,
  18212385538848873777561584,
  2433826112786940761601,
  72161809149036798056692,
  1203044390191599389101758591,
  2033670698135859033272,
  32957628356196354360028881,
  65002103239204107953888992,
  648382345022258836270439,
  318925533627392724957552,
  538477834476093188412169,
  255291676668111294656,
  3733623603237542498807,
  898592883963148458334,
  6355693752877024581009,
  987451359726835325702,
  729077774330247704114691,
  1471908211289144707786,
  23859947546512843676271261,
  1974295726379316173828972,
  314252895882612227011563,
  26364276720588874698766,
  413820028980527844313,
  571432091669357806249682,
  20964291993487216261607,
  5426261800050507557623354,
  27768687384447426495321189,
  11711625426955761513809618,
  1753369929616500181167,
  4059205041410449216705906,
  9330769977765354564504249,
  5115901743127271489888114,
  4433515366188709027655551,
  2350602497238040605384004,
  299258812207088142919241,
  9519153681412190484,
  33265771859070700063,
  350629773782860994,
  14278146508633039976553,
  813708171868511432878,
  21817358433418909128139,
  4551455047923260739332,
  1780306914895025692661,
  3552090250291087983538,
  481660736023068219,
  4957764983572843526,
  730039010146918858137,
  29396353373081142112,
  957120099053370743,
  304842675894654395336,
  36307104697273581049,
  53162584865746009449922,
  1859263738670477583,
  18302443872062222,
  63939573108828421,
  10119802861760306855346,
  212203887797315411,
  84330859524994438,
  122828888187555909,
  120284564952621885932,
  1986390539093741761179,
  20786564026517704,
  88329553227267549,
  1271211609842143196,
  64042772606483514939,
  54795544042070217526,
  3843609643359719973,
  6497190163452027704,
  122368584821164579,
  8309312491390305484,
  78402450509603157,
  2665282283986352,
  379114765650959931,
  11739856163040374806,
  3929337583003850813,
  29556693626519814,
  40876086568000575691,
  702606304772755480624,
  24233273568234701,
  260458297781760516,
  1797150944112859,
  6553497442591733016,
  225791494263293,
  3116743815080158064,
  176653885683083329867,
  564167042862264,
  6771703592793638093,
  916722358428014,
  2015145946321853187,
  25777046628685294,
  8363236720049883361,
  7274570614572636,
  11137942057902551,
  132586370133656,
  18880423540255393,
  9818302252518187228,
  673609662191639,
  939533766694272326,
  141068429183181,
  8347782301252,
  718108988906019,
  1289915225685104,
  487540040436833541,
  4747342155032188,
  331587581569613571,
  4879858574479742,
  581836293529540029,
  180778027964692,
  259835993185444803,
  2302031603217305294,
  10247900342777,
  13095845598360724,
  642319816231,
  5965823806172216,
  2555459090273,
  5534561643953986,
  398933563603,
  125896057838,
  115919740429617,
  657608563486,
  19914238423,
  3605278751852,
  17361383116769,
  44132984664,
  835348399,
  1137414724846,
  10204053213,
  97310966756,
  278456645707,
  1469475246808,
  8136277051269,
  2105724337484,
  1168300123083,
  259319542,
  9228952797,
  4247257963898,
  8877424226007,
  13548167137138,
  939034573981,
  26569914932354,
  34475223719,
  21191884,
  2127529844113,
  2955942484094,
  34701000023,
  119959157628,
  394030441,
  836920572,
  284981759,
  14196186,
  261768613,
  216101664,
  25636041323,
  163274,
  1234521,
  386572,
  8674191,
  30458456,
  5021609,
  63864761736,
  8941663,
  56594306436,
  2288657,
  532562,
  3032383,
  674712358,
  48773949,
  3302277332,
  2313259867,
  248352802,
  105981,
  2413058,
  172366607,
  14318432866,
  28641,
  592292,
  299043687,
  11025712,
  77513,
  4835966,
  1962451,
  2621548,
  2214830837,
  505639674,
  1830298963,
  11333908,
  52467981,
  8063380766,
  1625843,
  3008844,
  34526917,
  2284752,
  515963,
  228856,
  9470629,
  1187064,
  635935691,
  6137388,
  136717,
  88302,
  752771,
  958494858,
  1462119157,
  1652022,
  60611,
  19204,
  20029,
  783090042,
  198047,
  3563475832,
  397041,
  25736,
  100992927,
  122632,
  1016601,
  16076,
  1991247,
  256,
  4776769,
  588,
  123203351,
  3342986,
  11821,
  4425636,
  141587,
  212492,
  20320197,
  62368,
  374740947,
  18473534,
  27337,
  75995586,
  129198587,
  588243606,
  49,
  162,
  2938607,
  111698,
  21,
  4,
  3,
  2,
  1]

set_option maxRecDepth 1000000 in
/-- A list of positive, pairwise coprime numbers gives an admissible finset. -/
lemma admissible_toFinset (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x)
    (hpw : l.Pairwise (fun a b => Nat.gcd a b = 1)) : Admissible l.toFinset := by
  refine ⟨fun a ha => hpos a (List.mem_toFinset.mp ha), ?_⟩
  intro a ha b hb hab
  have : Std.Symm (fun a b : ℕ => Nat.gcd a b = 1) := ⟨fun x y h => by simpa [Nat.gcd_comm] using h⟩
  exact hpw.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab

set_option maxRecDepth 1000000 in
lemma solQ_adm : Admissible solQ.toFinset :=
  admissible_toFinset _ (by decide) (by decide)

set_option maxRecDepth 1000000 in
lemma solP0_adm : Admissible solP0.toFinset :=
  admissible_toFinset _ (by decide) (by decide +kernel)

set_option maxRecDepth 1000000 in
lemma sol_cross : ∀ a ∈ solP0.toFinset, ∀ b ∈ solQ.toFinset, Nat.Coprime a b := by
  have h : ∀ a ∈ solP0, ∀ b ∈ solQ, Nat.gcd a b = 1 := by decide +kernel
  intro a ha b hb
  exact h a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb)

set_option maxRecDepth 1000000 in
lemma sol_dev : Dev solP0.toFinset solQ.toFinset = solD0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The kernel runs the residue checker on the certificate.** -/
lemma sol_check : stepCheck solQ (M solQ.toFinset * (solD0 :: solRest).prod)
    ((A solQ.toFinset * M solP0.toFinset) % (M solQ.toFinset * (solD0 :: solRest).prod))
    (A solQ.toFinset * M solP0.toFinset) solD0 solRest = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The open coprime, 1-excluded variant of Erdős #307 has a solution** (kernel-checked certificate). -/
theorem coprime_one_notMem_solved : CoprimeOneNotMem :=
  coprime_one_notMem_of_stepCheck (qs := solQ) (fun q hq => List.mem_toFinset.mp hq)
    solQ_adm (by decide) (by decide) solP0_adm sol_cross (by decide +kernel) (by decide +kernel)
    sol_dev (by decide) solRest sol_check

end OMA.Phillips307

/-- The coprime, 1-excluded variant of Erdős #307 has a solution. -/
theorem OMA.solution : type_of% @Erdos307.erdos_307.variants.coprime_one_notMem :=
  OMA.Phillips307.coprime_one_notMem_solved
