import FormalConjectures.OEIS.«51903»

/-!
# Ordowski's maximum-exponent congruence and Lehmer's totient problem

The catalogue asks whether a composite integer n > 4 satisfies φ(n) ∣ n − e,
where e is the largest prime-factor exponent of n. A prime power p^e ∣ n forces
p^(e−1) ∣ e under this congruence. For e > 1 this forces p = e = 2. But 4 divides
the totient of every multiple of four greater than four, excluding that case.
Thus every witness also answers Lehmer's problem. Conversely the Lehmer congruence
forces e = 1, which is the independent first step below.

The equivalence is described in the Formal Conjectures statement for A051903.
Lean proof by @Deldor14.
-/

namespace OMA.R_OeisA51903_conjecture1_R1

open OeisA51903

private lemma max_mem (l : List ℕ) (hl : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => contradiction
  | cons h t ih =>
    cases t with
    | nil => simp
    | cons x xs =>
      simp only [List.foldr_cons, List.mem_cons] at *
      rcases le_total h (max x (xs.foldr max 0)) with hle | hle
      · rw [max_eq_right hle]
        exact Or.inr (ih (by simp))
      · simp [max_eq_left hle]

/-- The maximum multiplicity is positive, and its witnessing prime power divides n. -/
lemma attains {n : ℕ} (hn : 1 < n) :
    ∃ p k : ℕ, p.Prime ∧ a n = k+1 ∧ p^(k+1) ∣ n := by
  obtain ⟨p,hp,he⟩ := List.mem_map.mp (max_mem
    (n.primeFactorsList.map (n.primeFactorsList.count ·))
    (by simpa using (Nat.primeFactorsList_ne_nil n).2 hn))
  have hp' := Nat.prime_of_mem_primeFactorsList hp
  change n.primeFactorsList.count p = a n at he
  have hpos := List.count_pos_iff.mpr hp
  cases h : n.primeFactorsList.count p with
  | zero => omega
  | succ k =>
    refine ⟨p,k,hp',by omega,?_⟩
    apply (hp'.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mpr
    rw [← Nat.primeFactorsList_count_eq, h]

/-- Stripping the prime power from a totient congruence. -/
lemma strip {n z p k : ℕ} (hz : z ≤ n) (hp : p.Prime)
    (hpk : p^(k+1) ∣ n) (hφ : n.totient ∣ n-z) : p^k ∣ z := by
  have hpkn : p^k ∣ n := (pow_dvd_pow p (Nat.le_succ k)).trans hpk
  have hpt : p^k ∣ n.totient := by
    apply Dvd.dvd.trans _ (Nat.totient_dvd_of_dvd hpk)
    rw [Nat.totient_prime_pow_succ hp]
    exact dvd_mul_right _ _
  have hh := Nat.dvd_sub hpkn (hpt.trans hφ)
  rwa [Nat.sub_sub_self hz] at hh

private lemma pow_bound (k : ℕ) : k+3 < 2^(k+2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.succ_add, pow_succ]
    omega

lemma ordowski_max {n : ℕ} (hn : 4 < n) (hφ : n.totient ∣ n-a n) : a n = 1 := by
  obtain ⟨p,k,hp,he,hpk⟩ := attains (show 1 < n by omega)
  have hp2 := hp.two_le
  have hpown := Nat.le_of_dvd (show 0<n by omega) hpk
  have hlower := Nat.pow_le_pow_left hp2 (k+1)
  have hle : k+1 ≤ n := by have := Nat.lt_two_pow_self (n:=k+1); omega
  rw [he] at hφ
  have hbound := Nat.le_of_dvd (show 0<k+1 by omega) (strip hle hp hpk hφ)
  rcases k with _ | k
  · exact he
  rcases k with _ | k
  · simp at hbound he hφ hpk
    have heqp : p=2 := by omega
    subst p
    obtain ⟨m,hm⟩ := hpk
    have hm' : 2 < 2*m := by omega
    have ht : n.totient = 2*(2*m).totient := by
      rw [show n=2*(2*m) by omega, Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right _ _)]
    obtain ⟨u,hu⟩ := Nat.totient_even hm'
    obtain ⟨v,hv⟩ := hφ
    have hd : 4 ∣ n-2 := by
      refine ⟨u*v, ?_⟩
      rw [hv, ht, hu]
      ring
    omega
  · have pp := Nat.pow_le_pow_left hp2 (k+2)
    change p^(k+2) ≤ k+3 at hbound
    exact False.elim ((pow_bound k).not_ge (pp.trans hbound))


/-- The maximal prime exponent of a Lehmer witness is one. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n.totient ∣ n-1 → OeisA51903.a n = 1

/-- Lehmer's original question, with the same natural number witness. -/
def H2 : Prop := ∃ n : ℕ, 1 < n ∧ ¬ Prime n ∧ n.totient ∣ n-1

/-- Ordowski's congruence implies Lehmer's congruence for the very same integer. -/
theorem lehmer_of_ordowski {n : ℕ} (hn : 4 < n) (hc : n.totient ∣ n-a n) :
    n.totient ∣ n-1 := by
  rwa [ordowski_max hn hc] at hc

theorem main : H1 → H2 → type_of% @OeisA51903.conjecture1 := by
  rintro h₁ ⟨n, hn, hnp, hc⟩
  have hnp' : ¬ n.Prime := fun h => hnp h.prime
  have h4 : 4 < n := by
    by_contra! h
    interval_cases n <;> first | exact hnp' (by decide) | exact (by decide +kernel : ¬ (4:ℕ).totient ∣ 4-1) hc
  refine ⟨n,h4,hnp',?_⟩
  rwa [h₁ n hn hc]

end OMA.R_OeisA51903_conjecture1_R1
