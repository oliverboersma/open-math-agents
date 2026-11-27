import Mathlib

/-!
# Inverse totients of the form 2^s q

Source: https://arxiv.org/abs/2610.34808, Tian-Xiao He, Open Problem 16
Credit: @rleshner

The explicit prime-adjoining construction below characterizes every member
of the inverse fiber X_(2^s q). Part (a) asks for a congruence condition
giving zero or two preimages for all s. We display an infinite prime
progression of this kind and distinguish empty fibers from any proposed
nonempty dichotomy. Part (b) asks whether the fiber can be a singleton.
-/

namespace OMA.S_arxiv_2610_34808

/-- Generate a preimage using the powers of 2 and of q available in a
totient. A new prime spends (a,b) exactly when it is 2^a q^b + 1.
An existing prime may be repeated only if it is 2 or q. For the requested
index (s,1), the new primes are therefore of the two explicit forms
2^a + 1 and 2^a q + 1 with a ≤ s, and at most one factor spends q. -/
inductive Generated (q : ℕ) : ℕ → ℕ → ℕ → Prop
  | one : Generated q 0 0 1
  | newPrime {m u v a b : ℕ} (p : ℕ) (hp : p.Prime)
      (form : p = 2^a * q^b + 1) (fresh : ¬ p ∣ m) (old : Generated q u v m) :
      Generated q (a+u) (b+v) (p*m)
  | moreTwo {m u v : ℕ} (already : 2 ∣ m) (old : Generated q u v m) :
      Generated q (u+1) v (2*m)
  | moreQ {m u v : ℕ} (already : q ∣ m) (old : Generated q u v m) :
      Generated q u (v+1) (q*m)

/-- Open Problem 16: characterize the fiber, rule out singletons, and
determine whether a congruence condition can give the proposed 0-or-2
dichotomy uniformly in s. The specified reduced progression has empty
fibers; the three-preimage conclusion shows why this is unavoidable. -/
theorem main :
    (∀ q : ℕ, q.Prime → q ≠ 2 → ∀ s ≥ 3,
      (∀ n : ℕ, n.totient = 2^s*q ↔ Generated q s 1 n) ∧
      (∀ n : ℕ, n.totient = 2^s*q →
        ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient) ∧
      (∀ n : ℕ, n.totient = 2^s*q → ∃ t ≥ 3, ∃ x y z : ℕ,
        x<y ∧ y<z ∧ x.totient=2^t*q ∧ y.totient=2^t*q ∧ z.totient=2^t*q)) ∧
    {q : ℕ | q.Prime ∧ q % 560403480 = 420381167}.Infinite ∧
    (∀ q : ℕ, q.Prime → q % 560403480 = 420381167 → ∀ s ≥ 3,
      ∀ n : ℕ, n.totient ≠ 2^s*q) := by
  sorry

end OMA.S_arxiv_2610_34808
