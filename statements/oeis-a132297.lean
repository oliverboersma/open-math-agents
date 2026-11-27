import Mathlib

/-!
# OEIS A132297

A binary word is specified by its first symbol and the sequence of decisions
to stay at the current symbol (false) or switch to the other symbol (true).
These decisions are in bijection with the remaining symbols of the word.
The four adjacent-pair counts (00, 01, 10, 11) determine its order-two Markov
type. Count distinct types among all words of length n, starting at n=2.

Colin Barker proposed the closed formula, fourth-order recurrence, and
ordinary generating function below. The rational generating function is
given after multiplication by its denominator, whose constant term is one.

Source: https://oeis.org/A132297
-/

namespace OMA.S_oeis_a132297

structure Profile where
  zz : ℕ
  zo : ℕ
  oz : ℕ
  oo : ℕ
deriving DecidableEq

def walk : Bool → List Bool → Profile
  | _, [] => ⟨0,0,0,0⟩
  | false, false::w => let p := walk false w; {p with zz := p.zz+1}
  | false, true::w => let p := walk true w; {p with zo := p.zo+1}
  | true, false::w => let p := walk true w; {p with oo := p.oo+1}
  | true, true::w => let p := walk false w; {p with oz := p.oz+1}

def profiles (m : ℕ) : Finset Profile :=
  (Finset.univ : Finset (Bool × (Fin m → Bool))).image (fun z => walk z.1 (List.ofFn z.2))

def term (n : ℕ) := if 2 ≤ n then (profiles (n-1)).card else 0

noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => term n)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 ≤ n → 8*(term n : ℤ) = 15+(-1)^n-4*(n:ℤ)+6*(n:ℤ)^2) ∧
    (∀ k : ℕ, term (k+6)+2*term (k+3) = 2*term (k+5)+term (k+2)) ∧
    (1-2*X+2*X^3-X^4)*series = 4*X^2-X^3-2*X^4+2*X^5 := by
  sorry

end OMA.S_oeis_a132297
