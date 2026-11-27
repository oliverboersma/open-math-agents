import Mathlib

/-!
# Erdős Problem 689

Source: https://www.erdosproblems.com/689
Credit: @YourFriendPollux

## The problem

Let $n$ be sufficiently large. Is there some choice of congruence class $a_p$ for all
primes $2 \le p \le n$ such that every integer in $[1,n]$ satisfies at least two of the
congruences $\equiv a_p \pmod p$?

## Formalization notes

* "sufficiently large" is stated as `∀ᶠ n : ℕ in atTop`.
* The congruences are indexed by the primes $p \le n$: `p.Prime` already forces $p \ge 2$,
  and the range `Finset.range (n + 1)` restricts to $p \le n$.
* A congruence class modulo $p$ is an element of `ZMod p`, and an integer $m$ satisfies
  $m \equiv a_p \pmod p$ exactly when its image in `ZMod p` equals `a p`.
* The problem asks a yes/no question ("is there some choice ..."), so the statement
  asserts that such a choice exists for all sufficiently large $n$. No bound on the
  number of congruences is imposed, matching the source.
-/

namespace OMA.S_erdos_689

/-- There is a choice of a residue class `a p : ZMod p` for every prime `p ≤ n` such that
every integer `m` with `1 ≤ m ≤ n` satisfies `m ≡ a p [MOD p]` for at least two primes
`p ≤ n`. -/
def TwoCoveringResidues (n : ℕ) : Prop :=
  ∃ a : (p : ℕ) → ZMod p,
    ∀ m ∈ Finset.Icc 1 n,
      2 ≤ ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ (m : ZMod p) = a p)).card

theorem main : ∀ᶠ n : ℕ in atTop, TwoCoveringResidues n := by
  sorry

end OMA.S_erdos_689
