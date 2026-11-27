import Mathlib

/-!
# A256587: Number of ways to write n = r + s + t, where r,s,t are elements of the set {floor(k*(k+1)/4): k = 1,2,3,...} with s odd and r <= s <= t.

Source: https://oeis.org/A256587
Credit: @divmxnd0x

Let `S = {floor(k(k+1)/4) : k = 1, 2, 3, ...}`.

Conjecture (Zhi-Wei Sun, stated in A256587):
(i) `a(n) > 0` for all `n > 1`, i.e. every `n > 1` is `r + s + t` with `r, s, t ∈ S`, `s` odd and
`r ≤ s ≤ t`.
(ii) If the ordered pair `(b, c)` is among (1,2), (1,3), (1,4), (1,5), (1,6), (1,8), (1,9), (2,2)
and (2,3), then each nonnegative integer can be written as `r + b s + c t` with `r, s, t ∈ S`.

Formalization notes:
* Part (i) keeps exactly the conditions of the counting function (`s` odd, `r ≤ s ≤ t`).
* `floor(k(k+1)/4)` is natural-number division in `ℕ`.
* With these definitions the counts for `n = 1, ..., 20` are 0, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 4,
  2, 5, 3, 4, 3, 3, 5 (data of A256587), and part (ii) holds for all `n < 300` and all nine pairs.
-/

namespace OMA.S_oeis_a256587

/-- The set `{floor(k(k+1)/4) : k ≥ 1}`. -/
def S : Set ℕ :=
  {s | ∃ k : ℕ, 1 ≤ k ∧ s = k * (k + 1) / 4}

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, Odd s ∧ r ≤ s ∧ s ≤ t ∧ n = r + s + t) ∧
      ∀ bc ∈ ({(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (2, 2), (2, 3)} :
          Finset (ℕ × ℕ)),
        ∀ n : ℕ, ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, n = r + bc.1 * s + bc.2 * t := by
  sorry

end OMA.S_oeis_a256587
