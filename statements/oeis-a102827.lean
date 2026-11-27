import Mathlib.Data.Nat.Digits.Defs

/-!
# The count of the last digit in the previously written terms

The OEIS definition and the decimal Maple program search positive integers
from one at each step. For last digit d and its count c, the unique candidate
is b*c+d. The least positive candidate is therefore precisely the first
successful integer in that search. The first stored term is 1, and the counts
include each digit of every stored term in its usual base-b representation.

Source: https://oeis.org/A102827
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a102827

def addDigits (b v : ℕ) (counts : List ℕ) : List ℕ :=
  let digits := b.digits v
  counts.mapIdx (fun d c => c + digits.count d)

def nextValue (b : ℕ) (counts : List ℕ) : ℕ :=
  let candidates := counts.mapIdx (fun d c => b*c+d)
  ((candidates.filter (fun x => x > 0)).min?).getD 1

def state (b : ℕ) : ℕ → ℕ × List ℕ
  | 0 => (1, addDigits b 1 (List.replicate b 0))
  | n+1 =>
    let previous := state b n
    let v := nextValue b previous.2
    (v, addDigits b v previous.2)

theorem main : ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, ¬ b ∣ (state b n).1 := by
  sorry

end OMA.S_oeis_a102827
