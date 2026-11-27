import Mathlib

/-!
# Mathar's Vatalan recurrence recorded in OEIS A025756

Source: https://oeis.org/A025756
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A025/A025756.seq
Credit: @Heart-galaxy

A025756 is the zero-indexed sequence of third-order Vatalan numbers.
We use Tani Akinari's January 19, 2026 finite formula:
a(n)=(4+Sum_{k=0..n}(C(2/3,k)-2*C(1/3,k))*(-9)^k)/3.
Ring.choose is the generalized binomial coefficient over the rationals.
The auxiliary term and d definitions merely distribute the common factor
(-9)^k; they do not assume the recurrence being stated. The source's integer
sequence values are represented exactly in the rationals.

Mathar conjectured the order-three recurrence on November 14, 2011. We
retain every n>=3 so all previous indices are in the original offset-zero
sequence. The OEIS source still labels this recurrence a conjecture; no
claim of a previously published proof is made here.
-/

namespace OMA.S_oeis_a025756

noncomputable def term (r : ℚ) (n : ℕ) : ℚ := Ring.choose r n * (-9 : ℚ)^n
noncomputable def d (n : ℕ) : ℚ := term (2/3) n - 2*term (1/3) n
noncomputable def a (n : ℕ) : ℚ := (4 + ∑ k ∈ Finset.range (n+1), d k) / 3

theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℚ)*((n : ℚ)-1)*a n - ((n : ℚ)-1)*(19*(n : ℚ)-36)*a (n-1) +
      9*(11*(n : ℚ)^2-51*(n : ℚ)+60)*a (n-2) -
      9*(3*(n : ℚ)-7)*(3*(n : ℚ)-8)*a (n-3) = 0 := by
  sorry

end OMA.S_oeis_a025756
