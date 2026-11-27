import FormalConjectures.ErdosProblems.«454»
import Mathlib.Tactic

/-!
Reduction Erdos454.erdos_454.R1 of Erdős Problem 454.

The problem asks whether limsup (f n - 2 * p n) = ⊤, where
f n = min over 0 < i < n of (p (n + i) + p (n - i)) and p is Nat.nth Prime.
Writing S n i = p (n + i) + p (n - i) - 2 * p n, the target needs, for every
bound B, infinitely many centres n at which EVERY symmetric chord satisfies
S n i ≥ B. This reduction splits the chords by length at i ≈ n / (log₂ n)²:

* H1 (long chords, known mathematics): for every B, eventually in n, every i
  with 0 < i < n and n ≤ i * (Nat.log 2 n)² has p (n+i) + p (n-i) ≥ 2 p n + B.
  By the prime number theorem with the classical error term, for i in this
  range the convexity main term of S n i is of order at least n / (log n)⁴,
  which dominates the PNT error O(n · exp(-c (log n)^(3/5 - ε))). This is a
  genuine but realistic formalization target, not an open question.

* H2 (short chords, the open core): for every B there are infinitely many n
  such that every i with 0 < i and i * (Nat.log 2 n)² < n has
  p (n+i) + p (n-i) ≥ 2 p n + B. This carries the real difficulty of
  Erdős 454: simultaneous lower bounds on all short paired gap sums
  S n i = Σ_{r ≤ i} (g (n+r-1) - g (n-r)) at a single centre n.
  Pomerance (Math. Comp. 33 (1979), 399-408) proved the limsup is ≥ 2;
  McNew (The Convex Hull of the Prime Number Graph, 2018) verified growth
  of the records for n < 1.6 × 10⁸.

main combines them: at a centre n provided by H2 that also lies in the
eventual set of H1 (and with n ≥ 2 so the infimum in f is over a nonempty
type), every chord is covered by one of the two cases, so f n ≥ 2 p n + B,
hence B ≤ limsup; since B is arbitrary, the limsup is ⊤.
-/

namespace OMA.R_Erdos454_erdos_454_R1

/-- Long chords are eventually uniformly convex by at least any fixed margin:
for every margin, all chords with n ≤ i * (Nat.log 2 n) ^ 2 at centre n
eventually clear twice the central prime by that margin. Known mathematics
(prime number theorem with error term), not part of the open core. -/
def H1 : Prop := ∀ B : ℕ, ∀ᶠ n in Filter.atTop, ∀ i : ℕ, 0 < i → i < n →
    n ≤ i * (Nat.log 2 n) ^ 2 →
    2 * Nat.nth Prime n + B ≤ Nat.nth Prime (n + i) + Nat.nth Prime (n - i)

/-- Short chords clear any fixed margin at infinitely many centres:
for every margin there are infinitely many n at which all chords with
i * (Nat.log 2 n) ^ 2 < n clear twice the central prime by that margin.
This is the open core of Erdős Problem 454. -/
def H2 : Prop := ∀ B : ℕ, ∃ᶠ n in Filter.atTop, ∀ i : ℕ, 0 < i →
    i * (Nat.log 2 n) ^ 2 < n →
    2 * Nat.nth Prime n + B ≤ Nat.nth Prime (n + i) + Nat.nth Prime (n - i)

theorem main : H1 → H2 → type_of% @Erdos454.erdos_454 := by
  intro h1 h2
  have key : ∀ B : ℕ, (B : ℕ∞) ≤
      Filter.limsup (fun n => ((Erdos454.f n : ℕ∞) - 2 * (Nat.nth Prime n : ℕ∞)))
        Filter.atTop := by
    intro B
    refine Filter.le_limsup_of_frequently_le ?_ ⟨⊤, by simp⟩
    have freq := (h2 B).and_eventually ((h1 B).and (Filter.eventually_ge_atTop 2))
    refine freq.mono ?_
    rintro n ⟨hshort, hlong, hn2⟩
    have hf : 2 * Nat.nth Prime n + B ≤ Erdos454.f n := by
      unfold Erdos454.f
      rw [if_neg (by omega)]
      have hne : Nonempty {i : Fin n // 0 < (i : ℕ)} :=
        ⟨⟨⟨1, by omega⟩, by simp⟩⟩
      refine le_ciInf ?_
      rintro ⟨⟨i, hilt⟩, hipos⟩
      by_cases hcase : n ≤ i * (Nat.log 2 n) ^ 2
      · exact hlong i hipos hilt hcase
      · exact hshort i hipos (by omega)
    have hB : B ≤ Erdos454.f n - 2 * Nat.nth Prime n := by omega
    calc (B : ℕ∞) ≤ ((Erdos454.f n - 2 * Nat.nth Prime n : ℕ) : ℕ∞) := by
          exact_mod_cast hB
      _ = (Erdos454.f n : ℕ∞) - 2 * (Nat.nth Prime n : ℕ∞) := by
          push_cast [ENat.natCast_sub]
          ring_nf
  by_contra hne
  lift Filter.limsup (fun n => ((Erdos454.f n : ℕ∞) - 2 * (Nat.nth Prime n : ℕ∞)))
      Filter.atTop to ℕ using hne with m hm
  exact absurd (key (m + 1)) (by exact_mod_cast Nat.not_succ_le_self m)

end OMA.R_Erdos454_erdos_454_R1
