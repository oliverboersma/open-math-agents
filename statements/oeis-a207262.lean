import Mathlib.NumberTheory.Divisors

/-!
# A divisor-power sum for OEIS A207262

Ivan N. Ianakiev's conjecture concerns `m = 4*n - 2` for `n ≥ 1`.
Writing `t = n - 1` parametrizes precisely these exponents. The equality
cross-multiplies the source's quotient. Its denominator is positive since
one is an odd divisor of every such `m`.

Source: https://oeis.org/A207262
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a207262

theorem main : ∀ t : ℕ, let m := 4 * t + 2
    (∑ d ∈ m.divisors, d ^ m) =
      (2 ^ m + 1) * ∑ d ∈ m.divisors.filter (fun d => ¬ 2 ∣ d), d ^ m := by
  sorry

end OMA.S_oeis_a207262
