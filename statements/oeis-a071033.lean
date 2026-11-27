import Mathlib.Data.Nat.Bitwise

/-!
# The decimal words of Rule 94

The initial row is a single ON cell. A neighborhood with left, center and
right bits has index 4*left + 2*center + right. Bit number i of 94 is the
next state of neighborhood i. The cells outside the displayed row are OFF;
each update includes one new cell at each end. The resulting binary word
is read in base ten, as in the source values 1, 111 and 11011.

Source: https://oeis.org/A071033 (conjecture by Karl V. Keller, Jr.)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a071033

def cell (left center right : Bool) : Bool :=
  (94 : ℕ).testBit (4 * left.toNat + 2 * center.toNat + right.toNat)

def scan (left center : Bool) : List Bool → List Bool
  | [] => [cell left center false, cell center false false]
  | right :: rest => cell left center right :: scan center right rest

def row : ℕ → List Bool
  | 0 => [true]
  | n + 1 => scan false false (row n)

def readWord (acc : ℕ) : List Bool → ℕ
  | [] => acc
  | b :: rest => readWord (acc * 10 + b.toNat) rest

theorem main : ∀ n : ℕ, 1 < n → readWord 0 (row n) =
    if n % 2 = 1 then (1099 * 100^n + 9090) / 990 + 1
    else (1090 * 100^n + 10) / 990 + 1 := by
  sorry

end OMA.S_oeis_a071033
