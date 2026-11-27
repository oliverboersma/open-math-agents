import Mathlib

/-!
# The odd-index recurrence recorded in OEIS A067281

Source: https://oeis.org/A067281
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A067/A067281.seq
Credit: @Heart-galaxy

A067281 counts permutations of {1,...,n} whose elements are indistinguishable
when their ratio is a power of 2. The odd part ordCompl[2] gives a canonical
label for each equivalence class. Thus classes(n) is the multiset of those
labels, and Mathlib's Multiset.countPerms counts exactly the distinct
permutations required by the source.

Rothbach confirmed the conjecture a(2*n+1)=(2*n+1)*a(2*n) on September 15,
2004: the newly added odd number starts a new equivalence class.
The source now has offset 0, with a(0)=1 prepended in 2023. Our empty multiset
has one permutation, so the theorem retains all current indices n>=0.
-/

namespace OMA.S_oeis_a067281

noncomputable def classes (n : ℕ) : Multiset ℕ :=
  ((List.range n).map (fun k => ordCompl[2] (k+1)) : Multiset ℕ)

noncomputable def a (n : ℕ) : ℕ := (classes n).countPerms

theorem main : ∀ n : ℕ, a (2*n+1) = (2*n+1)*a (2*n) := by
  sorry

end OMA.S_oeis_a067281
