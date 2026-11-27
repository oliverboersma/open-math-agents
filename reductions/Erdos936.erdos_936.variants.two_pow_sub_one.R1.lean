import FormalConjectures.ErdosProblems.«936»

-- Reduction Erdos936.erdos_936.variants.two_pow_sub_one.R1 of Erdős Problem 936 (2^n - 1 case)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# 2^n - 1 is powerful only finitely often, from an abc estimate

The conditional argument for the Mersenne case of Erdős Problem 936. Under the abc conjecture
the answer is yes (CrowdMath, see erdosproblems.com/936; compare Cushing and Pascoe,
*Powerful numbers and the ABC-conjecture*, arXiv:1611.01192, for the factorial case).

* `H1` (elementary): the square of the radical divides each positive powerful number. This is
  word for word `H1` of `Erdos936.erdos_936.variants.factorial_add_one.R1`.
* `H2` (open core): the abc inequality with exponent 3/2 for the triples `(1, 2^n - 1, 2^n)`,
  whose radical is `2 * rad (2^n - 1)`. It is a special case of the abc conjecture with
  `ε = 1/2`, written with integer powers.

`main`: if `c = 2^n - 1` is powerful then `rad c ^ 2 ≤ c < 2^n` by `H1`. Squaring `H2` gives
`(2^n)^4 ≤ 64 C^2 (rad c)^6 ≤ 64 C^2 (2^n)^3`, so `2^n ≤ 64 C^2`, which fails for large `n`.
-/

open Finset Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R1

/-- The square of the radical divides each positive powerful number. -/
def H1 : Prop :=
  ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c

/-- The abc estimate with exponent 3/2 for the triples `(1, 2^n - 1, 2^n)`, written with
integer powers. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    let c := 2 ^ n - 1
    (2 ^ n) ^ 2 ≤ C * (2 * ∏ p ∈ c.primeFactors, p) ^ 3

theorem main : H1 → H2 → type_of% @Erdos936.erdos_936.variants.two_pow_sub_one := by
  intro radicalSquare ⟨C, hABC⟩
  change ∀ᶠ n : ℕ in atTop, ¬ (2 ^ n - 1).Powerful
  filter_upwards [eventually_gt_atTop (64 * C ^ 2)] with n hn
  intro hpower
  let m := 2 ^ n
  let c := 2 ^ n - 1
  let r := ∏ p ∈ c.primeFactors, p
  have hm : 0 < m := Nat.pow_pos (by norm_num)
  have hnm : n < m := Nat.lt_two_pow_self
  have hc : 0 < c := by dsimp [c]; omega
  have hcm : c ≤ m := Nat.sub_le _ _
  have hr : r ^ 2 ≤ m := (Nat.le_of_dvd hc (radicalSquare c hc hpower)).trans hcm
  have hABCn : m ^ 2 ≤ C * (2 * r) ^ 3 := hABC n
  have hbound : m * m ^ 3 ≤ (64 * C ^ 2) * m ^ 3 := by
    calc
      m * m ^ 3 = (m ^ 2) ^ 2 := by ring
      _ ≤ (C * (2 * r) ^ 3) ^ 2 := Nat.pow_le_pow_left hABCn 2
      _ = (64 * C ^ 2) * (r ^ 2) ^ 3 := by ring
      _ ≤ (64 * C ^ 2) * m ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 3)
  have hcancel := Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos hm)
  omega

end OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R1
