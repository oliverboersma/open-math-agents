import Mathlib

/-!
# A208494: Least integer m>1 such that those k! mod m with k=1,...,n are pairwise distinct

Source: https://oeis.org/A208494
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, Feb 27 2012, in the comments of A208494): a(n) is a prime with the only
exception a(5)=10, and a(n) does not exceed n^2/2 for all n=2,3,4,...

(The same comment records further conjectures of Sun: an asymptotic one and variants with
(-1)^k*k!, (2k)! and (-1)^k*(2k)!; only the two statements above are formalized here.)

Conventions:
* The sequence has offset 1: a(n) is the least m > 1 such that 1!, 2!, ..., n! are pairwise
  distinct modulo m, i.e. k -> k! mod m is injective on {1, ..., n}. Such m exist (any m > n!), so
  the infimum `sInf` is attained.
* "a(n) does not exceed n^2/2" is written without division as 2 * a(n) <= n^2.
-/

namespace OMA.S_oeis_a208494

/-- A208494: the least `m > 1` such that `k! mod m` (`k = 1, ..., n`) are pairwise distinct. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ Set.InjOn (fun k => k.factorial % m) (Set.Icc 1 n)}

/-- Sun's conjectures on A208494: `a n` is prime for every `n >= 1` except `a 5 = 10`, and
`a n <= n^2 / 2` for every `n >= 2`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ≠ 5 → (a n).Prime) ∧ a 5 = 10 ∧ (∀ n : ℕ, 2 ≤ n → 2 * a n ≤ n ^ 2) := by
  sorry

end OMA.S_oeis_a208494
