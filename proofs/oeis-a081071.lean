import OMAStatements.S_oeis_a081071
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: Lucas(m+1) = F(m) + F(m+2) by strong induction, and the even-index
-- Fibonacci sum satisfies F(0) + F(2) + ... + F(2m) + 1 = F(2m+1). Hence the sum over
-- k in [2, 2n] equals F(4n+1) - 2, and the right side is F(4n+3) + F(4n+1) - 2 = L(4n+2) - 2.

namespace OMA.A081071Proof

open OMA.S_oeis_a081071

theorem lucas_succ : ∀ m : ℕ, lucas (m + 1) = Nat.fib m + Nat.fib (m + 2)
  | 0 => by simp [lucas, Nat.fib_two]
  | 1 => by
      simp [lucas, Nat.fib_add_two]
  | (m + 2) => by
      have h1 := lucas_succ m
      have h2 := lucas_succ (m + 1)
      show lucas (m + 2) + lucas (m + 1) = _
      rw [h2, h1]
      have e1 : Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      have e2 : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 1 + 2) := by
        rw [show m + 2 + 2 = (m + 2) + 2 from rfl, Nat.fib_add_two]
      have e3 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      rw [e2, e1, e3]
      ring

theorem even_sum : ∀ m : ℕ,
    (∑ k ∈ Finset.range (m + 1), Nat.fib (2 * k)) + 1 = Nat.fib (2 * m + 1)
  | 0 => by simp
  | (m + 1) => by
      rw [Finset.sum_range_succ, add_right_comm, even_sum m]
      have : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
      rw [this, Nat.fib_add_two]
      have h2 : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [h2, show 2 * m + 1 + 1 = 2 * m + 2 from rfl]

theorem icc_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 2 (2 * n), Nat.fib (2 * k)) + 2 = Nat.fib (4 * n + 1) := by
  have hsplit : Finset.range (2 * n + 1) = {0, 1} ∪ Finset.Icc 2 (2 * n) := by
    ext x; simp [Finset.mem_Icc]; omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 (2 * n)) := by
    rw [Finset.disjoint_left]; intro x hx; simp at hx; simp [Finset.mem_Icc]; omega
  have h := even_sum (2 * n)
  rw [hsplit, Finset.sum_union hdisj] at h
  simp [Nat.fib_two] at h
  rw [show 4 * n + 1 = 2 * (2 * n) + 1 by ring, ← h]
  ring

end OMA.A081071Proof

open OMA.A081071Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081071.main := by
  intro n hn
  unfold OMA.S_oeis_a081071.a
  have hL : OMA.S_oeis_a081071.lucas (4 * n + 2) = Nat.fib (4 * n + 1) + Nat.fib (4 * n + 3) :=
    lucas_succ (4 * n + 1)
  have hs := icc_sum n hn
  have h2 : 2 ≤ Nat.fib (4 * n + 1) := by omega
  omega
