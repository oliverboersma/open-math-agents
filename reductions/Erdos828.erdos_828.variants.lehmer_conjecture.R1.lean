import FormalConjectures.ErdosProblems.«828»

-- Reduction Erdos828.erdos_828.variants.lehmer_conjecture.R1 of Erdős Problem 828 — Lehmer's
-- totient conjecture in the form phi n | n - 1 iff n is prime.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a biconditional under `n > 1` and the two directions differ in weight: forward
-- says no composite n > 1 has phi n | n - 1 (a Lehmer number would refute it, none is known),
-- backward is the elementary phi p = p - 1 for a prime p.

namespace OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

/-- Forward direction (the deep one): if `phi n` divides `n - 1`, then `n` is prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Nat.totient n ∣ n - 1 → Prime n

/-- Backward direction: for a prime `n > 1`, `phi n = n - 1` divides `n - 1`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Prime n → Nat.totient n ∣ n - 1

theorem main : H1 → H2 → type_of% @Erdos828.erdos_828.variants.lehmer_conjecture := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1
