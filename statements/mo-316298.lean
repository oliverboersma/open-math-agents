import Mathlib

/-!
# Can we write each positive integer as $x^2+y^2+\varphi(z^2)$?

Source: https://mathoverflow.net/questions/316298
Credit: @LordMike

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

Zhi-Wei Sun asked on MathOverflow: QUESTION: Can we write each n in Z^+ as
x^2+y^2+phi(z^2) with x, y in N and z in Z^+? (Here phi is Euler's totient function,
N = {0,1,2,...}, Z^+ = {1,2,3,...}.) Sun also stated a stronger conjecture (any n > 1 can be
written this way with x <= y and y or z prime), verified for n up to 10^6; the stronger
conjecture is not formalized here, only the question itself. Related OEIS entries: A262311
(counts of the stronger representation) and A262747 (a variant with 2 | xyz, verified by Sun for
n <= 10^7). formal-conjectures has only the different variant OEIS/262781
(x^2 + phi(y^2) + phi(z^2)).

Modelling choices:
* The question is open with a conjectured affirmative answer, so the theorem states that every
  positive integer has such a representation. No `answer(...)` is used.
* `Nat.totient (z ^ 2)` is Euler's phi applied to z^2. Since Mathlib sets `Nat.totient 0 = 0`,
  the requirement `0 < z` is essential (z = 0 would allow plain sums of two squares), and it is
  imposed as in the source.
* `x` and `y` range over all natural numbers including 0, as in the source.
-/

namespace OMA.S_mo_316298

theorem main : ∀ n : ℕ, 0 < n →
    ∃ x y z : ℕ, 0 < z ∧ n = x ^ 2 + y ^ 2 + Nat.totient (z ^ 2) := by
  sorry

end OMA.S_mo_316298
