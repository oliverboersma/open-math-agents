import Mathlib

/-!
# The Primal Conjecture in the modulo-nine matrix

Source: P. Marrero and E. Acuña, https://arxiv.org/abs/2205.09212, §§3.3, 8.1, 11, 12.3.
Credit: @rleshner

Section 11 quantifies the two input representatives in its displayed implication,
leaving the prescribed integer output fixed. Its surrounding prose also considers
allowing the output to vary within a residue class. The class labels below include the
positive and negative columns displayed in the paper. Division means exact
division, as in the multiplication relation under Table 7.
-/

namespace OMA.S_arxiv_2205_09212

inductive Operation where
  | add | sub | mul | div

/-- A column of the matrix, with label between −9 and 9, including its zero column. -/
def label (r : ℤ) : Prop := -9 ≤ r ∧ r ≤ 9

/-- The signed modulo-nine column containing an integer. -/
def inColumn (r x : ℤ) : Prop := Int.sign x = Int.sign r ∧ x ≡ r [ZMOD 9]

def compatible : Operation → ℤ → ℤ → ℤ → Prop
  | .add, a, b, c => a + b ≡ c [ZMOD 9]
  | .sub, a, b, c => a - b ≡ c [ZMOD 9]
  | .mul, a, b, c => a * b ≡ c [ZMOD 9]
  | .div, a, b, c => b ≠ 0 ∧ a ≡ b * c [ZMOD 9]

def exactAt : Operation → ℤ → ℤ → ℤ → Prop
  | .add, x, y, z => x + y = z
  | .sub, x, y, z => x - y = z
  | .mul, x, y, z => x * y = z
  | .div, x, y, z => y ≠ 0 ∧ x = y * z

/-- The signs of a proposed entry in the signed tables must be realizable
by the operation; this check only concerns signs, with no modulus involved. -/
def signsCompatible (op : Operation) (a b c : ℤ) : Prop :=
  ∃ u v w : ℤ, u.sign = a.sign ∧ v.sign = b.sign ∧ w.sign = c.sign ∧ exactAt op u v w

theorem main : ∀ (op : Operation) (a b c z : ℤ),
    label a → label b → label c → compatible op a b c → signsCompatible op a b c → inColumn c z →
    ∃ x y : ℤ, inColumn a x ∧ inColumn b y ∧ exactAt op x y z := by
  sorry

end OMA.S_arxiv_2205_09212
