import FormalConjectures.OEIS.«38771»

/-!
Reduction `OeisA38771.conjecture1.R1`.

`a n` is the least composite `c` with `primorial(n) + c` prime, where `primorial(n)` is the
product of the first `n` primes, and `p_{n+1} = Nat.nth Nat.Prime n` is the next prime. The
conjecture asks that `a(n) / p_{n+1}^2` has `liminf = 1` and `limsup = 2`.

* `H1` (proved as a step): `p_{n+1}^2 ≤ a(n)` for every `n`. A composite `c` with
  `primorial(n) + c` prime is coprime to `primorial(n)`, so its least prime factor is at least
  `p_{n+1}`, and a composite number is at least the square of its least prime factor. The set
  defining `a(n)` is nonempty by Dirichlet's theorem (`OeisA38771.a_n_exists`). So `H1` gives
  `liminf ≥ 1`.
* `H2` (the open part): `liminf ≤ 1` and `limsup = 2`.

`main` combines them; `limsup = 2` makes the ratio eventually bounded, which is what lets the
pointwise bound of `H1` pass to the `liminf`.
-/

-- Credit: @ivillar

namespace OMA.R_OeisA38771_conjecture1_R1

open Filter

/-- The known lower bound: `a(n)` is at least the square of the next prime `p_{n+1}`.
It gives `liminf a(n) / p_{n+1}^2 ≥ 1`. -/
def H1 : Prop := ∀ n : ℕ, (Nat.nth Nat.Prime n) ^ 2 ≤ OeisA38771.a n

/-- The open part: `liminf a(n) / p_{n+1}^2 ≤ 1` and `limsup a(n) / p_{n+1}^2 = 2`. -/
def H2 : Prop :=
  let p_next_sq (n : ℕ) : ℝ := ((Nat.nth Nat.Prime n : ℝ)) ^ 2
  let seq (n : ℕ) : ℝ := (OeisA38771.a n : ℝ) / p_next_sq n
  liminf seq atTop ≤ 1 ∧ limsup seq atTop = 2

theorem main : H1 → H2 → type_of% @OeisA38771.conjecture1 := by
  intro h1 h2
  dsimp only [H2] at h2
  obtain ⟨hle, hsup⟩ := h2
  intro p_next_sq seq
  change liminf seq atTop ≤ 1 at hle
  change limsup seq atTop = 2 at hsup
  refine ⟨le_antisymm hle ?_, hsup⟩
  have hge : ∀ n, 1 ≤ seq n := by
    intro n
    have hp : (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) ^ 2 := by
      have := (Nat.prime_nth_prime n).pos
      positivity
    have hb : ((Nat.nth Nat.Prime n : ℝ)) ^ 2 ≤ (OeisA38771.a n : ℝ) := by
      exact_mod_cast h1 n
    change 1 ≤ (OeisA38771.a n : ℝ) / ((Nat.nth Nat.Prime n : ℝ)) ^ 2
    rw [le_div_iff₀ hp, one_mul]
    exact hb
  have hbdd : IsBoundedUnder (· ≤ ·) atTop seq := by
    by_contra hnb
    have hempty : {a : ℝ | ∀ᶠ n in atTop, seq n ≤ a} = ∅ := by
      ext a
      constructor
      · intro ha
        exact absurd ⟨a, ha⟩ hnb
      · intro h
        exact h.elim
    rw [limsup_eq, hempty, Real.sInf_empty] at hsup
    norm_num at hsup
  exact le_liminf_of_le hbdd.isCoboundedUnder_ge (Eventually.of_forall hge)

end OMA.R_OeisA38771_conjecture1_R1
