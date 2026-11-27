import Mathlib

/-!
# VP versus VNP (Valiant's conjecture)

Source: https://en.wikipedia.org/wiki/VP_vs._VNP_problem
Credit: @my-other-github-account (statement adaptation, not a claimed proof).

Definitions adapted from OpenAI, math, lean/ComparatorChallenges/VPVNP.lean,
commit 3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0.
Copyright OpenAI. License: https://www.apache.org/licenses/LICENSE-2.0
Changes: namespace and conjecture phrasing; arbitrary finite variable types
rather than the source theorem's fixed Fin n × Bool variable types.

We use the nonuniform exact-circuit reading over any fixed field. A family
has polynomially bounded arity and degree; its VNP verifier has polynomially
many Boolean witness variables. The conclusion exhibits a VNP family not
in VP. No permanent-completeness equivalence is asserted, so the restriction
to characteristic different from two needed for that equivalence is absent.
Subtraction and free scalar/variable inputs do not change polynomial-size
circuit classes. Arbitrary finite variable types allow renaming variables
without committing to a particular arity function.
-/

namespace OMA.S_wpc_vp_vs_vnp

open scoped Classical

/-- A table of `s` binary gates computes `p`. Variables and scalars are free, and the
output and later gates may reuse any previously available value. -/
def Computes {F σ : Type*} [Field F] (s : ℕ) (p : MvPolynomial σ F) : Prop :=
  ∃ v : Fin s → MvPolynomial σ F,
    let available (k : ℕ) (x : MvPolynomial σ F) :=
      (∃ j : σ, MvPolynomial.X j = x) ∨ (∃ a : F, MvPolynomial.C a = x) ∨
        ∃ j : Fin s, j.val < k ∧ v j = x
    available s p ∧ ∀ i : Fin s, ∃ a b, available i.val a ∧ available i.val b ∧
      (v i = a + b ∨ v i = a - b ∨ v i = a * b)

/-- A polynomial bound uniform in all sufficiently large indices. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop := ∃ A d N : ℕ, ∀ n ≥ N, f n ≤ A * n ^ d

/-- At each index a family has its own finite type of indeterminates. -/
abbrev Family (F : Type*) [Field F] (σ : ℕ → Type) := (n : ℕ) → MvPolynomial (σ n) F

variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- Arity and total degree grow at most polynomially with the index. -/
def PFamily (p : Family F σ) : Prop :=
  PolynomiallyBounded (fun n => Fintype.card (σ n)) ∧
    PolynomiallyBounded (fun n => (p n).totalDegree)

/-- VP consists of polynomial families computed by polynomial-size exact circuits. -/
def IsVP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, Computes (s n) (p n)

/-- A VNP family sums a VP verifier over all Boolean assignments to its witness variables. -/
def IsVNP (p : Family F σ) : Prop :=
  PFamily p ∧ ∃ (W : ℕ → Type) (inst : ∀ n, Fintype (W n)) (g : Family F (fun n => σ n ⊕ W n)),
    PolynomiallyBounded (fun n => @Fintype.card _ (inst n)) ∧ IsVP g ∧ ∀ n,
      p n = ∑ y : W n → Bool, MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (if y i then 1 else 0))) (g n)


/-- Valiant's conjecture over every fixed field. -/
theorem main : ∀ (F : Type) [Field F],
    ∃ (σ : ℕ → Type) (inst : ∀ n, Fintype (σ n)) (p : Family F σ),
      @IsVNP F _ σ inst p ∧ ¬ @IsVP F _ σ inst p := by
  sorry

end OMA.S_wpc_vp_vs_vnp
