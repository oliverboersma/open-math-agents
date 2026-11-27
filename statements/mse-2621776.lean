import Mathlib

/-!
# The sequence $\,a_n=\lfloor \mathrm{e}^n\rfloor$ contains infinitely many odd and infinitely many even terms

Source: https://math.stackexchange.com/questions/2621776/the-sequence-a-n-lfloor-mathrmen-rfloor-contains-infinitely-many-odd-an
Credit: @mgv27

Show that the sequence $a_n=\lfloor \mathrm{e}^n\rfloor$ contains infinitely many odd and
infinitely many even terms.

It suffices to show that the terms of the sequence $b_n = \mathrm{e}^n \bmod 2$ are dense in
$[0,2]$; but (as noted in the comments) this density claim is open, since it would imply that
$\mathrm{e}^n$ is dense modulo $1$.

Formalization notes:
* `a n = ⌊exp n⌋₊` as a natural number (OEIS A000149: 1, 2, 7, 20, 54, 148, 403, …).
* `main` states that both `{n | a n odd}` and `{n | a n even}` are infinite.
* A quick high-precision computation for `n ≤ 39` shows both parities occur often.
-/

namespace OMA.S_mse_2621776

/-- `a n = ⌊e^n⌋`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊Real.exp (n : ℝ)⌋₊

/-- `⌊e^n⌋` is odd for infinitely many `n` and even for infinitely many `n`. -/
theorem main : {n : ℕ | Odd (a n)}.Infinite ∧ {n : ℕ | Even (a n)}.Infinite := by
  sorry

end OMA.S_mse_2621776
