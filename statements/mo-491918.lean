import Mathlib

/-!
# Show that at every equilibrium in the given sequential game, the first player weakly prefers his bundle to everyone else's

Source: https://mathoverflow.net/questions/491918
Credit: @tatashbar

The source: `n` players, `m` items, a matrix `P` with `p i j ≥ 0`, additive valuations
`v_i(S) = ∑ j ∈ S, p i j`.  Players claim one unclaimed item each in the order `1, 2, …, n, 1, 2, …`
while unclaimed items remain (a perfect-information sequential game; `m` need not be a multiple of `n`).
The utility of a player, along any path and in any subgame, is the valuation of the bundle he ends up with.
Objective, as stated: in every subgame-perfect Nash equilibrium (SPNE) outcome `(A_1*, …, A_n*)`,
`v_1(A_1*) ≥ v_1(A_j*)` for all `j > 1`.

Conventions of this translation:
* players are `Fin n` and items are `Fin m`; the first player is `⟨0, hn⟩`, and "`j > 1`" becomes `0 < (j : ℕ)`;
* a history is the list of the items claimed so far, in order; the player to move after `t` picks is `t % n`;
* a (pure) strategy names an item at every history; it is legal if it names an unclaimed item at every legal
  non-terminal history (only its values at the histories where its owner moves are ever used);
* a profile is an SPNE if, in the subgame starting at every legal history, no player gains by switching to
  another legal strategy (the standard definition; the source finds SPNE by backward induction, which yields
  exactly these profiles in a finite perfect-information game);
* the valuations are real numbers, and "every SPNE outcome" quantifies over all SPNE profiles (ties included).

Note for reviewers and later agents: this is the claim exactly as the source poses it, and as posed it is
false for three or more players. It does hold for two players, and whenever `m ≤ n + 1`. So the expected
contribution here is a disproof, `¬ main`.

Counterexample without ties (`n = 3`, `m = 7`, items `a, …, g`, every row a strict ranking):
  player 1 values `8, 4, 9, 2, 10, 1, 3`, player 2 values `4, 1, 2, 5, 6, 3, 7`, player 3 values
  `6, 2, 7, 3, 4, 1, 5`.
Every SPNE gives the bundles `{b, d, e}`, `{f, g}`, `{a, c}`, and the first player values his own bundle at
`16` and the third player's at `17` (his opening pick `d` is strictly best for him). A generic variant, in
which every player values all bundles differently, has rows `1025, 516, 1160, 320, 1312, 144, 386`;
`520, 132, 258, 704, 769, 400, 928`; `769, 320, 900, 392, 544, 130, 656`, the same unique outcome, and
`2148 < 2185`. These were found and checked by exact backward induction over all SPNE (two independent
programs), not by hand.

Short counterexample with ties (`n = 3`, `m = 5`): the first player values the items `1, 1, 1, 0, 0` and the
other two value every item `0`. The first player takes a worthless item, the second a valuable one, the
third a worthless one, and the first and second then take the last two valuable items: the first player
holds value `1` and values the second player's bundle at `2`. This is an SPNE because the first player
also ends with value `1` if he opens with a valuable item (the other two then take the remaining valuable
items). The same construction works for every `n ≥ 3` and `m ≥ n + 2`.
-/

namespace OMA.S_mo_491918

/-- A pure strategy: the item to claim at each history (the list of the items claimed so far). -/
abbrev Strategy (m : ℕ) := List (Fin m) → Fin m

/-- The player who moves at the history `h`: the picking order is `0, 1, …, n - 1, 0, 1, …`. -/
def mover {n m : ℕ} (hn : 0 < n) (h : List (Fin m)) : Fin n :=
  ⟨h.length % n, Nat.mod_lt _ hn⟩

/-- Continue the history `h` by `k` further picks, every player following the profile `σ`. -/
def play {n m : ℕ} (hn : 0 < n) (σ : Fin n → Strategy m) : ℕ → List (Fin m) → List (Fin m)
  | 0, h => h
  | k + 1, h => play hn σ k (h ++ [σ (mover hn h) h])

/-- The terminal history reached from `h` under `σ`: play goes on until all `m` items are claimed. -/
def finish {n m : ℕ} (hn : 0 < n) (σ : Fin n → Strategy m) (h : List (Fin m)) : List (Fin m) :=
  play hn σ (m - h.length) h

/-- The bundle of player `i` in the history `h`: the items claimed at the turns `t` with `t % n = i`. -/
def bundle {n m : ℕ} (h : List (Fin m)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∃ t : Fin h.length, (t : ℕ) % n = (i : ℕ) ∧ h.get t = j)

/-- The additive valuation `v_i(S) = ∑ j ∈ S, p i j`. -/
def value {n m : ℕ} (P : Fin n → Fin m → ℝ) (i : Fin n) (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ S, P i j

/-- A strategy is legal if it claims an unclaimed item at every history in which no item is claimed
twice and some item is still unclaimed. -/
def Legal {m : ℕ} (s : Strategy m) : Prop :=
  ∀ h : List (Fin m), h.Nodup → h.length < m → s h ∉ h

/-- Subgame-perfect Nash equilibrium: all strategies are legal and, in the subgame starting at any legal
history `h`, no player `i` gets a strictly better bundle by switching to another legal strategy `s`. -/
def IsSPNE {n m : ℕ} (hn : 0 < n) (P : Fin n → Fin m → ℝ) (σ : Fin n → Strategy m) : Prop :=
  (∀ i, Legal (σ i)) ∧
    ∀ h : List (Fin m), h.Nodup → h.length ≤ m → ∀ (i : Fin n) (s : Strategy m), Legal s →
      value P i (bundle (finish hn (Function.update σ i s) h) i) ≤
        value P i (bundle (finish hn σ h) i)

/-- The claim of the source: at every SPNE of the picking game, the first player weakly prefers his own
bundle to the bundle of every other player. -/
theorem main :
    ∀ (n m : ℕ) (hn : 0 < n) (P : Fin n → Fin m → ℝ), (∀ i j, 0 ≤ P i j) →
      ∀ σ : Fin n → Strategy m, IsSPNE hn P σ →
        ∀ j : Fin n, 0 < (j : ℕ) →
          value P ⟨0, hn⟩ (bundle (finish hn σ []) j) ≤
            value P ⟨0, hn⟩ (bundle (finish hn σ []) ⟨0, hn⟩) := by
  sorry

end OMA.S_mo_491918
