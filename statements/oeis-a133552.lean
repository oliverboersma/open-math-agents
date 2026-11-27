import Mathlib.Init

/-!
# OEIS A133552

R. H. Hardin counts binary words with at most four ones in each window of
six consecutive bits. His list starts 1, 2, 4, 8, 16, 31. Thus a five-bit
word of all ones is excluded. We use five initial zero bits, which gives
these short-word counts and enforces the six-bit rule on longer words.

The two conjectures are due to Colin Barker, February 22, 2018.
Source: https://oeis.org/A133552
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a133552

/-- The number of ones among the five remembered bits. -/
def weight (s : Fin 32) : Nat :=
  ((List.range 5).filter (fun j => s.val.testBit j)).length

/-- Append one bit and retain the most recent five bits. -/
def shift (s : Fin 32) (b : Nat) : Fin 32 :=
  ⟨(2 * s.val + b) % 32, Nat.mod_lt _ (by decide)⟩

/-- Count completions by their next bit. A zero is allowed if the suffix
has at most four ones. A one is allowed if the suffix has at most three. -/
def step (v : Fin 32 → Int) (s : Fin 32) : Int :=
  if weight s ≤ 4 then
    v (shift s 0) + (if weight s < 4 then v (shift s 1) else 0)
  else 0

/-- Number of allowed n-bit continuations. State 31 already contains five
ones and is unreachable from the initial all-zero suffix. -/
def count : Nat → Fin 32 → Int
  | 0, s => if s.val = 31 then 0 else 1
  | n + 1, s => step (count n) s

def a (n : Nat) : Int := count n 0

/-- The conjectured recurrence with every term moved to the left. The
argument f supplies consecutive terms from index n through n+15. -/
def deviation (f : Nat → Int) : Int :=
  f 15 - f 14 - f 13 - f 12 - f 10 - 2 * f 9 + 2 * f 7 + 2 * f 6 + f 3 - f 0

/-- Coefficient of the product of a polynomial and an ordinary power series.
The list gives the polynomial coefficients in ascending degree. -/
def productCoeff (f : Nat → Int) : List Int → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c * f 0
  | c :: cs, n + 1 => c * f (n + 1) + productCoeff f cs n

def denominator : List Int := [1,-1,-1,-1,0,-1,-2,0,2,2,0,0,1,0,0,-1]

def numeratorCoeff : Nat → Int
  | 0 | 1 | 2 | 3 | 13 | 14 => 1
  | 4 | 5 => 2
  | 6 | 8 => -2
  | 7 => -3
  | 10 | 11 => -1
  | _ => 0

/-- Barker's recurrence for all indices ≥ 15 and his generating function
after multiplication by its denominator, stated coefficient by coefficient. -/
theorem main :
    (∀ n : Nat, deviation (fun j => a (n + j)) = 0) ∧
    (∀ n : Nat, productCoeff a denominator n = numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a133552
