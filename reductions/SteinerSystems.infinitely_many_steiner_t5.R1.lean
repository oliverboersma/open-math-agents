import FormalConjectures.Wikipedia.SteinerSystem
import Mathlib

/-! Infinitely many Steiner systems with t = 5 from Keevash's theorem. Keevash, The existence
of designs (2014), Theorem 1.1: for fixed t and k, a Steiner system S(t, k, n) exists for
every sufficiently large n satisfying the divisibility conditions that the binomial
coefficient C(k - i, t - i) divides C(n - i, t - i) for 0 ≤ i < t. Here t = 5 and k = 6. The
divisibility conditions hold for infinitely many n, which is an elementary statement about
binomial coefficients, and distinct n give distinct systems. -/

namespace OMA.R_SteinerSystems_infinitely_many_steiner_t5_R1

/-- Keevash's existence theorem for t = 5 and block size 6. -/
def H1 : Prop := ∃ N₀ : ℕ, ∀ n ≥ N₀,
  (∀ i < 5, Nat.choose (6 - i) (5 - i) ∣ Nat.choose (n - i) (5 - i)) →
    Nonempty (SteinerSystems.SteinerSystem 5 6 n)

/-- The divisibility conditions hold for arbitrarily large n. -/
def H2 : Prop := ∀ N : ℕ, ∃ n ≥ N,
  ∀ i < 5, Nat.choose (6 - i) (5 - i) ∣ Nat.choose (n - i) (5 - i)

theorem main : H1 → H2 → type_of% @SteinerSystems.infinitely_many_steiner_t5 := by
  rintro ⟨N₀, hK⟩ hadm
  apply Set.Infinite.of_image
    (fun s : Σ k n : ℕ, SteinerSystems.SteinerSystem 5 k n => s.2.1)
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, hdiv⟩ := hadm (max N₀ (max (M + 1) 7))
  have h1 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have h2 : M + 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h3 : 7 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨sys⟩ := hK n h1 hdiv
  have hmem : n ∈ (fun s : Σ k n : ℕ, SteinerSystems.SteinerSystem 5 k n => s.2.1) ''
      {s | 5 < s.1 ∧ s.1 < s.2.1} :=
    ⟨⟨6, n, sys⟩, ⟨by norm_num, by show 6 < n; omega⟩, rfl⟩
  have h4 := hM hmem
  omega

end OMA.R_SteinerSystems_infinitely_many_steiner_t5_R1
