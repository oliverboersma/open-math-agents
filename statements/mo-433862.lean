import Mathlib

/-!
# Do primes of the form $4k+1$ ever lead the greatest prime factor race?

Source: https://mathoverflow.net/questions/433862/do-primes-of-the-form-4k1-ever-lead-the-greatest-prime-factor-race
Credit: @mgv27

Let $f_1(n)$ and $f_3(n)$ be the number of natural numbers $\le n$ whose greatest prime factor
(GPF) is of the form $4k+1$ and $4k+3$ respectively. For $n \le 3 \times 10^{10}$ there is not
a single instance where primes of the form $4k+1$ equal or take the lead in the race.

Question 1: Does the GPF race ever become equal or change the lead, i.e. is there an $n$ such
that $f_1(n) = f_3(n)$?

Question 2: What is the true growth rate of $f_3(n) - f_1(n)$?

Formalization notes:
* `main` states Question 1 in its natural "yes" reading. Equality holds trivially for tiny `n`
  (e.g. `n = 5`: GPFs `5` and `3`), and a quick computation shows `f₁(n) < f₃(n)` for all
  `6 ≤ n ≤ 2·10⁵`; so the question is whether `f₁(n) ≥ f₃(n)` happens again for arbitrarily
  large `n`. Since `f₃ - f₁` changes by at most `1` at each step, this is the same as
  `f₁(n) = f₃(n)` for arbitrarily large `n`.
* The GPF of `m ≥ 2` is `m.primeFactors.sup id`; for `m = 1` this is `0`, which is in neither
  class, as is the GPF `2`.
* Question 2 (the growth rate) is not formalized.
-/

namespace OMA.S_mo_433862

/-- The greatest prime factor of `m` (`0` for `m ≤ 1`). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- `f r n`: the number of `m ∈ [1, n]` whose greatest prime factor is `≡ r (mod 4)`. -/
def f (r n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun m => gpf m % 4 = r)).card

/-- Question 1: the `4k+1` primes catch up with (or lead) the `4k+3` primes in the GPF race
for arbitrarily large `n`. -/
theorem main : ∀ N : ℕ, ∃ n ≥ N, f 3 n ≤ f 1 n := by
  sorry

end OMA.S_mo_433862
