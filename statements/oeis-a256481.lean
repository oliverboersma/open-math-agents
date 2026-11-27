import Mathlib

/-!
# OEIS A256481: if no prime arises by appending a repdigit to n, then 3 divides n

Source: https://oeis.org/A256481 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry (Chai Wah Wu, 2015), offset 0: Smallest prime obtained by appending a number with identical
digits to n or 0 if no such prime exists. Comment: For n <= 15392, a(n) = 0 if and only if n = 6930.
Conjecture: if a(n) = 0, then n is divisible by 3. Conjecture verified for n <= 10^6. a(n) = 0 for
n = 6930, 50358, 56574, 72975. The conjecture is also stated in arXiv:1503.08883 by the same author.

Formalization notes:
* Appending i >= 1 copies of the digit d to n gives n * 10^i + d * (10^i - 1)/9; `R i` is the
  repunit (10^i - 1)/9, defined by R 0 = 0 and R (i+1) = 10 * R i + 1.
* a(n) = 0 means that none of these numbers is prime, for every digit d from 0 to 9 and every
  length i >= 1 (the digit 0 never gives a prime, so including it changes nothing). A prime is
  never 0, so this is exactly the condition a(n) = 0.
* Controls from the entry: a(20) = 2011 (append 11), and a(6930) = 0.
-/

namespace OMA.S_oeis_a256481

/-- The repunit with i digits. -/
def R : ℕ → ℕ
  | 0 => 0
  | i + 1 => 10 * R i + 1

/-- n followed by i copies of the digit d. -/
def app (n d i : ℕ) : ℕ := n * 10 ^ i + d * R i

/-- a(n) = 0: no prime is obtained by appending a number with identical digits to n. -/
def ZeroTerm (n : ℕ) : Prop := ∀ d ≤ 9, ∀ i ≥ 1, ¬ (app n d i).Prime

/-- Wu's conjecture: if a(n) = 0, then n is divisible by 3. -/
theorem main : ∀ n : ℕ, ZeroTerm n → 3 ∣ n := by
  sorry

end OMA.S_oeis_a256481
