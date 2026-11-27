import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1
import Mathlib

/-! Blocks of prime indices in which the primes that are 1 mod q dominate, from Shiu's theorem.
Shiu, Strings of congruent primes, J. London Math. Soc. 61 (2000): for coprime a and q and
every k there are infinitely many strings of k consecutive primes all congruent to a mod q.
This is the catalogue's Erdos427.erdos_427.variants.shiu. A string of k consecutive good
indices is already a block with no bad index and k good ones, and (k - 1) (0 + 1) < k. -/

namespace OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1

/-- Shiu's theorem on strings of consecutive primes in a residue class. -/
def H1 : Prop := ∀ (k a q : ℕ), 1 ≤ k → 1 ≤ q → a.gcd q = 1 →
  {m : ℕ | ∀ p ∈ (Finset.Ico m (m + k)).image (Nat.nth Nat.Prime), p ≡ a [MOD q]}.Infinite

/-- A string of k consecutive good indices is a block in which the good indices outnumber
k - 1 times one more than the bad ones. -/
def H2 : Prop := ∀ (good : ℕ → Bool) (k : ℕ), 0 < k →
  (∃ m, ∀ i ∈ Finset.Ico m (m + k), good i = true) →
  ∃ l r : ℕ,
    (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <
      ((Finset.Ico l r).filter (fun i => good i = true)).card

theorem main : H1 → H2 → OMA.R_Erdos997_erdos_997_variants_irrational_R1.H1 := by
  intro h1 h2 q k hq hk
  intro good
  obtain ⟨m, hm⟩ := (h1 k 1 q hk hq (Nat.gcd_one_left q)).nonempty
  refine h2 good k hk ⟨m, fun i hi => ?_⟩
  exact decide_eq_true (hm _ (Finset.mem_image_of_mem _ hi))

end OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1
