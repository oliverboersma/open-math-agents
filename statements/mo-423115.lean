import Mathlib

/-!
# Two-player item picking game

Source: https://mathoverflow.net/questions/423115
Credit: @tatashbar

This statement follows the text of the question as reproduced on
https://lefttosolve.com/p/mo-423115.

The question. There are `n` items; item `i` is worth `a i` to player `A` and `b i` to player
`B`. The players take turns picking items, an item can be picked only once, and the game lasts
`k` rounds with `2 * k ≤ n`, so each player makes `k` picks and `n - 2 * k` items are left
over. Each player seeks to maximise the sum of the values of his/her picked items minus the sum
of the values of the opponent's picked items. What is the outcome of the game under optimal
play, and is there an efficient algorithm for it? (The source notes that for `2 * k = n` both
players should take the item with the largest `a i + b i`, and that this fails for general `k`.)

Conventions chosen here, each stated because the source leaves it implicit.

* Objective. The payoff to `A` is (sum of `a` over `A`'s items) - (sum of `b` over `B`'s items)
  and the payoff to `B` is its negative: each player's items are valued by their owner, and the
  game is zero-sum. This is the reading under which the source's remark about `2 * k = n` is
  correct. Under the other reading (`A` gets `a(A's items) - a(B's items)`, `B` gets
  `b(B's items) - b(A's items)`, a general-sum game) that remark already fails for two items,
  so that reading is not the one formalised.
* Order of play. `A` picks first and the players alternate, so `B` makes the last pick.
* Outcome. The outcome is the minimax value of the game: `A` maximises the payoff above and
  `B` minimises it. `value a b t s` is the value of the position in which `s` is the set of
  items not yet picked and `t` picks remain; the game of the source has value
  `value a b (2 * k) Finset.univ`.
* Efficient algorithm. The values are rational numbers and an instance is the number of rounds
  `k` together with the list of pairs `(a i, b i)`. `main` asks for a deterministic Turing
  machine that computes the value in time polynomial in the bit length of the instance.
  Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`. The bit-string encodings below
  are the ones used by formal-conjectures (`BitstringEncoding`: binary naturals, an integer as
  the pair of its positive and negative parts, a rational as numerator and denominator, a pair
  as a self-delimiting block followed by the second component, a list as a concatenation of
  self-delimiting blocks), written out here because a statement file imports Mathlib only.
  The shape of `main` is that of `Arxiv.«2610.08796».exists_isPolyTime_bayesNash` there.

`main` is the affirmative answer to the source's question. Whether it is true is open.
-/

namespace OMA.S_mo_423115

/-- `value a b t s` is the payoff to `A` (sum of `a` over the items `A` picks minus the sum of
`b` over the items `B` picks) from the rest of the play under optimal play, when `s` is the set
of items not yet picked and `t` picks remain. The players alternate and `B` makes the last
pick, so `A` is to move exactly when `t` is even. `A` maximises the payoff, `B` minimises it. -/
def value {n : ℕ} (a b : Fin n → ℚ) : ℕ → Finset (Fin n) → ℚ
  | 0, _ => 0
  | t + 1, s =>
      if h : s.Nonempty then
        if Even (t + 1) then s.sup' h fun i => a i + value a b t (s.erase i)
        else s.inf' h fun i => value a b t (s.erase i) - b i
      else 0

/-- An instance of the game: the number of rounds `k`, and the list of the items, item `i`
being given by the pair `(a i, b i)` of its values to `A` and to `B`. -/
abbrev Instance := ℕ × List (ℚ × ℚ)

/-- The value of the game for an instance: `A` picks first, `2 * k` picks are made in total,
all items are available at the start. -/
def gameValue (g : Instance) : ℚ :=
  value (fun i : Fin g.2.length => (g.2.get i).1) (fun i : Fin g.2.length => (g.2.get i).2)
    (2 * g.1) Finset.univ

/-- Make a bit string self-delimiting: each payload bit `b` becomes the two bits `true, b`,
and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- An integer is encoded as the pair of naturals `(z.toNat, (-z).toNat)`, in binary. -/
def encodeInt (z : ℤ) : List Bool :=
  delimit (Computability.encodeNat z.toNat) ++ Computability.encodeNat (-z).toNat

/-- A rational is encoded as the pair of its reduced numerator and its denominator. -/
def encodeRat (q : ℚ) : List Bool :=
  delimit (encodeInt q.num) ++ Computability.encodeNat q.den

/-- An item is encoded as the pair of its two values. -/
def encodeItem (p : ℚ × ℚ) : List Bool :=
  delimit (encodeRat p.1) ++ encodeRat p.2

/-- An instance is encoded as the pair of `k` (in binary) and the list of its items, the list
being the concatenation of the self-delimiting encodings of the items. -/
def encodeInstance (g : Instance) : List Bool :=
  delimit (Computability.encodeNat g.1) ++ ((g.2.map encodeItem).map delimit).flatten

theorem main : ∃ solve : Instance → ℚ,
    Nonempty (Turing.TM2ComputableInPolyTime encodeInstance encodeRat solve) ∧
    ∀ g : Instance, 2 * g.1 ≤ g.2.length → solve g = gameValue g := by
  sorry

end OMA.S_mo_423115
