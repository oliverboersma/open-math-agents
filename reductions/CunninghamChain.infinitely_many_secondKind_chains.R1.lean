import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

-- Reduction CunninghamChain.infinitely_many_secondKind_chains.R1 of Jones's conjecture on Cunningham chains of exact length k (second kind)
-- Credit: @marcusbuffett

/-!
# Cunningham chains of exact length `k` (second kind): length one, and the open rest

A prime `p` starts a chain of exact length `k` for the recurrence `q ↦ 2q - 1` if the first `k`
terms are prime and the next one is composite. The conjecture asks for infinitely many such `p`
for every `k ≥ 1`.

* `H1` (classical, by Dirichlet's theorem): exact length one. Every prime `p > 3` with
  `p ≡ 2 (mod 3)` has `3 ∣ 2p - 1`, so `2p - 1` is composite, and there are infinitely
  many such primes.
* `H2`: exact length `k` for every `k ≥ 2`. This is open (already `k = 2` needs infinitely many
  primes `p` with `2p - 1` prime).
-/

namespace OMA.R_CunninghamChain_infinitely_many_secondKind_chains_R1

/-- Infinitely many chains of exact length one. -/
def H1 : Prop :=
  Set.Infinite {p : ℕ | CunninghamChain.IsSecondKindChainOfLength p 1}

/-- The open part: exact length `k ≥ 2`. -/
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k → Set.Infinite {p : ℕ | CunninghamChain.IsSecondKindChainOfLength p k}

theorem main : H1 → H2 → type_of% @CunninghamChain.infinitely_many_secondKind_chains := by
  intro h1 h2 k hk
  by_cases hk1 : k = 1
  · subst hk1
    exact h1
  · exact h2 k (by omega)

end OMA.R_CunninghamChain_infinitely_many_secondKind_chains_R1
