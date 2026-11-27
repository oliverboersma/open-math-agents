import Mathlib

/-!
# OEIS A230044: the numbers k with k + square triangular are the distinct values of A064784

Source: https://oeis.org/A230044 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A230044 (Ralf Stephan, Oct 06 2013), offset 1: Nonnegative numbers k such that k plus a
perfect square is a triangular number. Comment: Conjecture: these are the sorted distinct terms of
A064784.
Entry A064784 (Jonathan Ayres, Oct 20 2001), offset 1: Difference between n-th triangular number
t(n) and the largest square <= t(n). Formula: a(n) = n*(n+1)/2 - floor(sqrt(n*(n+1)/2))^2.

Formalization notes:
* Triangular numbers are t(m) = m(m+1)/2 and perfect squares are s^2, for m, s >= 0; k is a term
  of A230044 when k + s^2 = t(m) for some s and m.
* A230044 lists its terms in increasing order, so it is the sorted list of distinct terms of
  A064784 exactly when its set of terms equals the set of values A064784(n), n >= 1; the
  statement is that equality of sets.
* Controls from the entry A064784: the definition gives 0, 2, 2, 1, 6, 5, 3, 0, 9, 6 for
  n = 1..10.
-/

namespace OMA.S_oeis_a230044

/-- The triangular number t(m) = m(m+1)/2. -/
def T (m : ℕ) : ℕ := m * (m + 1) / 2

/-- A064784(n): t(n) minus the largest square <= t(n). -/
def A064784 (n : ℕ) : ℕ := T n - Nat.sqrt (T n) ^ 2

/-- Membership in A230044: k plus a perfect square is a triangular number. -/
def InA230044 (k : ℕ) : Prop := ∃ s m : ℕ, k + s ^ 2 = T m

/-- Stephan's conjecture: the terms of A230044 are the distinct terms of A064784. -/
theorem main : {k | InA230044 k} = {k | ∃ n, 1 ≤ n ∧ A064784 n = k} := by
  sorry

end OMA.S_oeis_a230044
