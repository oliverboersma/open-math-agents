/-
OEIS A089893, the powers-of-two value, the exact Fermat quotient, and the
three stated ratio limits.
Reference: https://oeis.org/A089893
Credit: @Heart-galaxy
Definition of the underlying bit product: https://oeis.org/A001317
Text credit: OEIS Foundation, CC BY-SA 4.0.

The sequence starts at zero. A001317 gives its terms as the product of the
Fermat numbers indexed by the set bits of the argument. Doubling the
argument shifts the bit indices by one. The exact ratio and the limits use
ordinary division in the real numbers.
-/

import Mathlib

namespace OMA.S_oeis_a089893

open Finset Filter Topology

/-- Product of the Fermat numbers indexed by the set bits of n, shifted by s.
The shift 1 implements A001317(2n). -/
def bitProduct (s n : ℕ) : ℕ :=
  (n.bitIndices.map (fun i => Nat.fermatNumber (s + i))).prod

def a (n : ℕ) : ℕ := (bitProduct 1 n - 1) / 4

def block (k n : ℕ) : ℕ := 2 ^ (k + 1) * n + 2 ^ k

theorem main :
    (∀ k : ℕ, a (2 ^ k) = 2 ^ (2 ^ (k + 1) - 2)) ∧
    (∀ n t : ℕ, 1 ≤ t →
      (4 * (a (2 ^ t * n + 2 ^ (t - 1)) : ℝ) + 1) /
        (4 * (a (2 ^ t * n + 2 ^ (t - 1) - 1) : ℝ) + 1) =
        3 * (Nat.fermatNumber t : ℝ) / ((Nat.fermatNumber t : ℝ) - 2)) ∧
    Tendsto (fun n : ℕ => (a (2 * n + 1) : ℝ) / (a (2 * n) : ℝ)) atTop (𝓝 5) ∧
    Tendsto (fun n : ℕ => (a (4 * n + 2) : ℝ) / (a (4 * n + 1) : ℝ)) atTop (𝓝 (17 / 5)) ∧
    Tendsto (fun n : ℕ => (a (8 * n + 4) : ℝ) / (a (8 * n + 3) : ℝ)) atTop (𝓝 (257 / 85)) := by
  sorry

end OMA.S_oeis_a089893
