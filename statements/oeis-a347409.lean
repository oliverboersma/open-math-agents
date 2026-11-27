import Mathlib.Data.Set.Finite.Basic

/-!
# The longest halving run in a Collatz trajectory (OEIS A347409)

A347409(n) is the longest run of halving steps before the first visit to
1, or -1 if there is no such visit. The entry conjectures that every
integer k ≥ 4 occurs infinitely often.

Source: https://oeis.org/A347409 (OEIS Foundation, CC BY-SA 4.0).

A finite trace records individual, unaccelerated Collatz steps: true is
a halving and false is an odd step. Only 1 has the empty trace, and no
step may leave 1. The two coordinates of runStats count the leading
halving run and the longest halving run, respectively. Since k ≥ 4,
a nonterminating trajectory cannot contribute an occurrence.
-/

namespace OMA.S_oeis_a347409

inductive Trace : ℕ → List Bool → Prop
  | stop : Trace 1 []
  | half {n : ℕ} {s : List Bool} (hn : 1 < n) (he : n % 2 = 0)
      (next : Trace (n / 2) s) : Trace n (true :: s)
  | triple {n : ℕ} {s : List Bool} (hn : 1 < n) (ho : n % 2 = 1)
      (next : Trace (3 * n + 1) s) : Trace n (false :: s)

def runStats : List Bool → ℕ × ℕ
  | [] => (0, 0)
  | false :: s => (0, (runStats s).2)
  | true :: s =>
      let t := runStats s
      (t.1 + 1, max (t.1 + 1) t.2)

theorem main : ∀ k : ℕ, 4 ≤ k →
    Set.Infinite {n : ℕ | ∃ s : List Bool, Trace n s ∧ (runStats s).2 = k} := by
  sorry

end OMA.S_oeis_a347409
