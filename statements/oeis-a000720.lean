import Mathlib

/-!
# A000720 — the second Hardy–Littlewood conjecture

Source: https://oeis.org/A000720
Credit: @Andyi955

The OEIS entry A000720 lists `pi(n)`, the number of primes `<= n`. The conjecture recorded there is
the second Hardy–Littlewood conjecture: `pi(x) + pi(y) >= pi(x + y)` for integers `x` and `y` with
`min {x, y} >= 2`. It is known to hold for `(x, y)` sufficiently large (Udrescu 1975) but is open in
general; it is incompatible with the first Hardy–Littlewood conjecture.

## Encoding

* `pi` is Mathlib's `Nat.primeCounting`, the number of primes at most `n`.
* The range restriction `min {x, y} >= 2` of the source is the pair of hypotheses `2 ≤ x`,
  `2 ≤ y`; the inequality is stated in the equivalent form `pi (x + y) ≤ pi x + pi y`.
-/

namespace OMA.S_oeis_a000720

/-- **Second Hardy–Littlewood conjecture**: `pi(x) + pi(y) ≥ pi(x + y)` for `x, y ≥ 2`. -/
theorem main : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  sorry

end OMA.S_oeis_a000720
