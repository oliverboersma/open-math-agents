import Mathlib

/-!
# The golden-ratio conjecture in OEIS A294532

Clark Kimberling's guide gives 34 pairs of increasing complementary
sequences, A294532 through A294565. Their first terms are `a(0) = 1`,
`a(1) = 2`, and `b(0) = 3`. Each recurrence adds to `a(j-1) + a(j-2)`
an expression `p*b(j-1) + q*b(j-2) + r*j + s`. The guide conjectures
that all 34 consecutive-term ratios tend to the golden ratio. The guide
prints `s = -3` for its last entry, while A294565 itself prints `s = -2`.
The list below includes both versions of that last recurrence.

Sources: https://oeis.org/A294532 and https://oeis.org/A294565
-/

namespace OMA.S_oeis_a294532

abbrev Profile := ℤ × ℤ × ℤ × ℤ

def profiles : List Profile :=
  [(0,1,0,0), (0,1,0,1), (0,1,0,2), (0,1,0,3), (0,1,0,-1),
   (0,1,1,0), (0,1,2,0), (0,1,1,-1), (0,1,2,-1),
   (1,0,0,0), (1,0,0,1), (1,0,0,2), (1,0,0,3), (1,0,0,-1),
   (1,0,1,0), (1,0,2,0), (1,0,1,-1), (1,0,1,1),
   (1,1,0,0), (1,1,0,1), (1,1,1,0), (1,1,-1,0), (1,1,0,2),
   (1,1,0,3), (1,1,1,1), (1,1,1,-1), (1,1,2,0),
   (1,2,0,0), (2,2,0,0), (2,1,0,0), (1,-1,0,1), (1,-1,1,0),
   (2,-1,0,-1), (2,-1,0,-3), (2,-1,0,-2)]

def correction : Profile → ℕ → ℕ → ℕ → ℤ
  | (p,q,r,s), j, x, y => p*x + q*y + r*j + s

def complementary (a b : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → (m ∈ Set.range b ↔ m ∉ Set.range a)

theorem main : ∀ v ∈ profiles, ∀ a b : ℕ → ℕ,
    StrictMono a → StrictMono b → a 0 = 1 → a 1 = 2 → b 0 = 3 → complementary a b →
    (∀ n : ℕ, (a (n+2) : ℤ) = a (n+1) + a n + correction v (n+2) (b (n+1)) (b n)) →
    Filter.Tendsto (fun n : ℕ => (a (n+1) : ℝ) / a n) Filter.atTop (nhds ((1 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a294532
