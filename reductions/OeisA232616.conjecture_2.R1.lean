import FormalConjectures.OEIS.«232616»

-- Reduction OeisA232616.conjecture_2.R1 of Complete residue systems of 2^k - k — conjecture2
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is an iff: the only solutions of `x ^ n - n = y ^ m` in integers `> 1` are the two
-- exceptional ones. The forward direction is the deep half (a Diophantine finiteness statement);
-- the backward direction is a finite check on the two explicit witnesses.

namespace OMA.R_OeisA232616_conjecture_2_R1

/-- Forward direction: every solution in integers `> 1` of `x ^ n - n = y ^ m` is one of the two
exceptional tuples `(2, 5, 3, 3)` and `(2, 7, 11, 2)`. -/
def H1 : Prop :=
  ∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m → x ^ n - n = y ^ m →
    (x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)

/-- Backward direction: the two exceptional tuples really are solutions, i.e. they satisfy
`x ^ n - n = y ^ m`. -/
def H2 : Prop :=
  ∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m →
    ((x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)) →
    x ^ n - n = y ^ m

theorem main : H1 → H2 → type_of% @OeisA232616.conjecture_2 := by
  intro h1 h2 x y n m hx hy hn hm
  exact ⟨fun h => h1 x y n m hx hy hn hm h, fun h => h2 x y n m hx hy hn hm h⟩

end OMA.R_OeisA232616_conjecture_2_R1
