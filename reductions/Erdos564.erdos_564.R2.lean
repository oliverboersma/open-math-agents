import FormalConjectures.ErdosProblems.«564»

-- Reduction Erdos564.erdos_564.R2 of Erdős Problem 564
-- Credit: @tamoghnokandar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- H1 is a KNOWN theorem (Erdős–Hajnal stepping-up lemma; Erdős, Hajnal, Máté, Rado 1984):
-- with FOUR colours the 3-uniform Ramsey number is doubly exponential. It is a formalisation
-- task, not an open problem (the three-colour analogue used in R1 is itself open).
-- H2 carries the whole open difficulty: at the two-colour threshold R_3(n), four colours still
-- force a monochromatic set of linear size. Since the four-colour number is at most doubly
-- exponential (Erdős–Rado), H2 is equivalent to the conjecture, so nothing is lost.

namespace OMA.R_Erdos564_erdos_564_R2

open Filter Combinatorics

/-- Four-colour tower lower bound: if every 4-colouring of the triples of `Fin m` has a
monochromatic `k`-set, then `m ≥ 2 ^ 2 ^ (a k)` (for all large `k`). Known. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ᶠ k : ℕ in atTop, ∀ m : ℕ,
    (∀ f : Finset (Fin m) → Fin 4, ∃ S : Finset (Fin m), S.card = k ∧
      ∃ b : Fin 4, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b) →
    (2 : ℝ) ^ (2 : ℝ) ^ (a * k) ≤ m

/-- Two colours versus four: on `R_3(n)` vertices every 4-colouring of the triples has a
monochromatic set of size at least `d n`. Open; equivalent to the conjecture. -/
def H2 : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, d * n ≤ k ∧
    ∀ f : Finset (Fin (hypergraphRamsey 3 n)) → Fin 4,
      ∃ S : Finset (Fin (hypergraphRamsey 3 n)), S.card = k ∧
        ∃ b : Fin 4, ∀ e : Finset (Fin (hypergraphRamsey 3 n)),
          e ⊆ S → e.card = 3 → f e = b

theorem main : H1 → H2 → type_of% @Erdos564.erdos_564 := by
  rintro ⟨a, ha, h1⟩ ⟨d, hd, h2⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 h1
  refine ⟨a * d, mul_pos ha hd, ?_⟩
  filter_upwards [h2, eventually_ge_atTop ⌈(k₀ : ℝ) / d⌉₊] with n hn hlarge
  obtain ⟨k, hdk, hforce⟩ := hn
  have h3 : (k₀ : ℝ) / d ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hlarge)
  have h4 : (k₀ : ℝ) ≤ k := by
    have h5 : (k₀ : ℝ) ≤ d * n := by
      have := (div_le_iff₀ hd).1 h3
      linarith
    linarith
  have h6 : a * d * n ≤ a * k := by
    have := mul_le_mul_of_nonneg_left hdk ha.le
    linarith
  have h7 := hk₀ k (by exact_mod_cast h4) (hypergraphRamsey 3 n) hforce
  have h8 : (2 : ℝ) ^ (a * d * n) ≤ (2 : ℝ) ^ (a * k) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h6
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) h8).trans h7

end OMA.R_Erdos564_erdos_564_R2
