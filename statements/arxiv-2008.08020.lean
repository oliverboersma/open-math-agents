import Mathlib

/-!
# Vielhaber's binary question mark function at rational points

Source: https://arxiv.org/abs/2008.08020, Definition 2 and Conjecture 23
Credit: @rleshner

The real-valued function agrees on rational inputs with the numerical
binary fraction obtained by alternating codes I and II for an even-length
continued fraction. The suffix deletion in the address notation and the
subsequent addition of the terminal 1 in the address-to-dyadic conversion
cancel in the numerical binary value (Appendix 2). We state
nondifferentiability for every real extension of these prescribed values.
This includes the paper's continuous extension. The points p/q with
0 < p < q run through all rationals in the open unit interval.
-/

namespace OMA.S_arxiv_2008_08020

/-- A pair (a,b) stores the positive partial denominators (a+1,b+1).
The real argument is the unevaluated continued-fraction tail. -/
noncomputable def cf : List (ℕ × ℕ) → ℝ → ℝ
  | [], x => x
  | (a,b)::ds, x => 1 / ((a:ℝ)+1 + 1 / ((b:ℝ)+1 + cf ds x))

/-- Binary place-value denominator of either code for a positive digit d. -/
def denom (d : ℕ) : ℕ := 2^(2 * Nat.log 2 d + 1)

/-- The bits of code I, read as an unsigned binary integer. The low bits
of d are complemented (Definition 1, Table 1). -/
def bitsI (d : ℕ) : ℕ := 3*2^(Nat.log 2 d) - 1 - d

/-- Code II is the bitwise complement of code I at its specified length. -/
def bitsII (d : ℕ) : ℕ := denom d - 1 - bitsI d

/-- The binary real given by the concatenated alternating codewords,
followed by a binary tail whose value is y. -/
noncomputable def code : List (ℕ × ℕ) → ℝ → ℝ
  | [], y => y
  | (a,b)::ds, y =>
    ((bitsI (a+1) : ℝ) + ((bitsII (b+1) : ℝ) + code ds y) / denom (b+1)) / denom (a+1)

/-- The rational values in Definition 2 specify Vielhaber's function on
a dense set. Its continuous extension, as well as any other extension,
meets this condition. The empty word assigns zero to zero. -/
def Encodes (F : ℝ → ℝ) : Prop := ∀ ds : List (ℕ × ℕ), F (cf ds 0) = code ds 0

theorem main : ∀ F : ℝ → ℝ, Encodes F → ∀ p q : ℕ, 0 < p → p < q →
    ¬ DifferentiableAt ℝ F ((p:ℝ)/q) := by
  sorry

end OMA.S_arxiv_2008_08020
