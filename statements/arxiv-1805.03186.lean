import Mathlib

/-!
# Recovering a hidden forest by the quasiprime CRT algorithm

Goodrich, Mbirika and Nielsen, Definition 4.6 and Question 1,
https://arxiv.org/abs/1805.03186. Credit: @rleshner.

We index a forest from its first coordinates x,y with zero-based offsets.
In the paper's CRT systems the unknowns are the predecessors x-1,y-1.
These conventions give the same row and column divisibilities.
-/

namespace OMA.S_arxiv_1805_03186

abbrev Cell (n : ℕ) := Fin n × Fin n

def grid {n : ℕ} (x y : ℕ) (c : Cell n) : ℕ :=
  Nat.gcd (x + c.1.val) (y + c.2.val)

/-- The union of the prime supports of all gcd entries. -/
def primes {n : ℕ} (g : Cell n → ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun c => (g c).primeFactors

def exponent {n : ℕ} (g : Cell n → ℕ) (p : ℕ) : ℕ :=
  Finset.univ.sup fun c => (g c).factorization p

/-- For each grid prime the QP algorithm retains precisely one location at
which its exponent is maximal. Locations outside the prime support are unused. -/
def Valid {n : ℕ} (g : Cell n → ℕ) (place : ℕ → Cell n) : Prop :=
  ∀ p ∈ primes g, (g (place p)).factorization p = exponent g p

/-- The product of the retained prime powers in a row or column of the QP
matrix. Taking the first or second coordinate of the retained cell specifies
the row or column containing each factor. -/
def block {n : ℕ} (g : Cell n → ℕ) (group : ℕ → Fin n) (i : Fin n) : ℕ :=
  ∏ p ∈ (primes g).filter (fun p => group p = i), p ^ exponent g p

/-- The common product of the row moduli, equivalently of the column moduli.
It retains each prime once with its maximal exponent. -/
def period {n : ℕ} (g : Cell n → ℕ) : ℕ :=
  ∏ p ∈ primes g, p ^ exponent g p

/-- Every hidden forest gives a quasiprime matrix. For every permitted choice
at tied maxima, the CRT solution classes consist precisely of the translates
of the two original coordinates by multiples of the common period. -/
theorem main : ∀ {n : ℕ}, 0 < n → ∀ x y : ℕ, 0 < x → 0 < y →
    (∀ c : Cell n, 1 < grid x y c) →
    let g : Cell n → ℕ := grid x y
    (∃ place, Valid g place) ∧
    ∀ place, Valid g place → ∀ u v : ℕ,
      ((∀ i : Fin n, block g (fun p => (place p).1) i ∣ u + i.val) ∧
       (∀ j : Fin n, block g (fun p => (place p).2) j ∣ v + j.val)) ↔
      (Nat.ModEq (period g) u x ∧ Nat.ModEq (period g) v y) := by
  sorry

end OMA.S_arxiv_1805_03186
