import Mathlib

/-!
# Minimum number of equipartitions forcing a pair to occur together half the time

Arun, MathOverflow question 407245, October 28, 2021.
Source: https://mathoverflow.net/questions/407245
Formalization: Codex Linden (OpenAI Codex).

The ground set has n*k distinct elements. Each partition labels its n blocks
by Fin n. Permuting the labels preserves all tests. The indexed list of
partitions may repeat a partition. The two elements in a pair are distinct.

The proposed answer tests only lists of length three and four. The value
none means that no length at least three forces a pair to occur together in
at least half of the partitions. Peter Taylor's comment on the original
question gives an example from Kirkman's schoolgirl problem.
-/

namespace OMA.S_mo_407245

abbrev Point (k n : ℕ) := Fin n × Fin k
abbrev Family (k n r : ℕ) := Fin r → Point k n → Fin n

/-- Each block of every listed partition contains exactly k elements. -/
def valid {k n r : ℕ} (P : Family k n r) : Prop :=
  ∀ i b, (Finset.univ.filter (fun x => P i x = b)).card = k

instance {k n r : ℕ} (P : Family k n r) : Decidable (valid P) := by
  unfold valid
  infer_instance

/-- Indices of the partitions in which the two given elements share a block. -/
def meetings {k n r : ℕ} (P : Family k n r) (x y : Point k n) : Finset (Fin r) :=
  Finset.univ.filter (fun i => P i x = P i y)

/-- Every indexed list of r equipartitions places some pair together at least half the time. -/
def forces (k n r : ℕ) : Prop :=
  ∀ P : Family k n r, valid P → ∃ x y, x ≠ y ∧ r ≤ 2 * (meetings P x y).card

/-- Finite search for r equipartitions in which each distinct pair meets at most once. -/
def hasOrthogonal (k n r : ℕ) : Bool :=
  decide (∃ P : Family k n r,
    valid P ∧ ∀ x y, x ≠ y → (meetings P x y).card ≤ 1)

/-- The two finite tests compute the minimum length, or detect its nonexistence. -/
def threshold (k n : ℕ) : Option ℕ :=
  if hasOrthogonal k n 3 then
    if hasOrthogonal k n 4 then none else some 4
  else some 3

theorem main : ∀ k n : ℕ, 0 < k → 0 < n →
    match threshold k n with
    | none => ∀ r : ℕ, 3 ≤ r → ¬ forces k n r
    | some t => IsLeast {r : ℕ | 3 ≤ r ∧ forces k n r} t := by
  sorry

end OMA.S_mo_407245
