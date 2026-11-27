import Mathlib

/-!
# OEIS A058764: the smallest x with cototient 2^n is 3*2^(n-1) for n > 1

Source: https://oeis.org/A058764 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A058764 (Labos Elemer, Jan 02 2001), offset 0: Smallest number x such that cototient(x) =
2^n. Formula: a(n) = min { x | A051953(x) = 2^n }. Formula (M. F. Hasler, Nov 10 2016):
a(n) = (if n>1 then 3 else 4)*2^(n-1) = A007283(n-1) for n>1. (Conjectured.)
A051953(x) is the cototient x - phi(x) and A007283(n) = 3*2^n.

Formalization notes:
* The condition n>1 is read as applying to the whole formula, so the statement is a(n) =
  3*2^(n-1) for every n > 1. For n = 1 the formula gives 4 = a(1), and for n = 0 it gives
  4*2^(-1) = 2 = a(0); both are listed terms, and the definition reproduces them (controls).
* The cototient is `x - Nat.totient x`; a(n) is the infimum of the x with cototient 2^n.
* Controls from the entry: the definition gives a(0) = 2 and a(1) = 4.
-/

namespace OMA.S_oeis_a058764

/-- The cototient x - phi(x) (A051953). -/
def cototient (x : ℕ) : ℕ := x - Nat.totient x

/-- A058764(n): the smallest x with cototient(x) = 2^n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {x | cototient x = 2 ^ n}

/-- Hasler's conjecture: a(n) = 3*2^(n-1) = A007283(n-1) for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → a n = 3 * 2 ^ (n - 1) := by
  sorry

end OMA.S_oeis_a058764
