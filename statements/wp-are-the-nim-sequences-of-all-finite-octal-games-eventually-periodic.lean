import Mathlib

/-!
# Are the nim-sequences of all finite octal games eventually periodic?

Source: https://en.wikipedia.org/wiki/octal_game
Credit: @LAPRAI

*Reference:* R. K. Guy, *Unsolved problems in combinatorial games*, Games of No Chance (1996),
cited by the source as the place where Guy lists this question.

## The source's definitions, as encoded here

An octal game is given by its code `0 . d₁ d₂ d₃ …` (optionally with a digit `d₀ = 4` before the
point). A move picks one heap and, for some `k`, removes `k` tokens from it; the digit `d k` is a sum of
* `1`: leaving zero heaps is permitted (the heap had exactly `k` tokens, `k ≥ 1`);
* `2`: leaving one heap is permitted (the heap had more than `k` tokens, `k ≥ 1`);
* `4`: leaving two nonempty heaps is permitted (the heap had at least `k + 2` tokens).
Zero tokens are not counted as a heap. Here `d : ℕ → ℕ` with `d k < 8` is the digit sequence and
`d 0` is the digit before the point. For `k = 0` only the bit `4` describes a move (splitting a heap
without removing tokens); bits `1` and `2` of `d 0` would describe no move or a null move, and the
source never uses them, so they are ignored. A *finite* octal game is one with finitely many
nonzero digits.

The nim-sequence `G 0, G 1, G 2, …` gives the nim-value of a single heap of `n` tokens (via the
Sprague–Grundy theorem). It is computed by the standard recursion: `G n` is the minimum excluded
value (mex) of the nim-values of the positions reachable in one move from a heap of `n`, where the
empty position has value `0`, one heap of `a` tokens has value `G a`, and two heaps of `a` and `b`
tokens have value `G a xor G b`.

## The statement

The source: all finite octal games analyzed so far have an ultimately periodic nim-sequence, and
whether all finite octal games are ultimately periodic is an open question. `main` states the
expected (positive) answer, Guy's conjecture; a disproof would establish the negative answer.
-/

namespace OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic

/-- The minimum excluded value of a finite set of natural numbers. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (p := fun m => m ∉ s)
    ⟨s.sup id + 1, fun h => Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)⟩

/-- The nim-value `G n` of a single heap of `n` tokens in the octal game with digits `d`. -/
def nimValue (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  let g : ℕ → ℕ := fun a => if a < n then nimValue d a else 0
  -- remove `k = n ≥ 1` tokens, leaving no heap (value `0`)
  let zeroHeaps : Finset ℕ :=
    if 1 ≤ n ∧ (d n).testBit 0 then {0} else ∅
  -- remove `k` tokens with `1 ≤ k < n`, leaving one heap of `n - k` tokens
  let oneHeap : Finset ℕ :=
    ((Finset.Ico 1 n).filter (fun k => (d k).testBit 1)).image (fun k => g (n - k))
  -- remove `k ≥ 0` tokens and split the rest into heaps of `a ≥ 1` and `n - k - a ≥ 1` tokens
  let twoHeaps : Finset ℕ :=
    ((Finset.range n ×ˢ Finset.range n).filter
      (fun p => (d p.1).testBit 2 ∧ 1 ≤ p.2 ∧ p.1 + p.2 < n)).image
      (fun p => g p.2 ^^^ g (n - p.1 - p.2))
  mex (zeroHeaps ∪ oneHeap ∪ twoHeaps)

/-- An octal code: every digit is an octal digit. -/
def IsOctal (d : ℕ → ℕ) : Prop := ∀ k, d k < 8

/-- A finite octal game: an octal code with only finitely many nonzero digits. -/
def IsFiniteOctal (d : ℕ → ℕ) : Prop := IsOctal d ∧ {k | d k ≠ 0}.Finite

/-- **Guy's question on octal games.** The nim-sequence of every finite octal game is ultimately
periodic. -/
theorem main : ∀ d : ℕ → ℕ, IsFiniteOctal d →
    ∃ p, 0 < p ∧ ∃ N, ∀ n, N ≤ n → nimValue d (n + p) = nimValue d n := by
  sorry

end OMA.S_wp_are_the_nim_sequences_of_all_finite_octal_games_eventually_periodic
