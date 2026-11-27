import Mathlib

/-!
# Kung–Traub conjecture

Source: https://en.wikipedia.org/wiki/Kung–Traub_conjecture
Credit: @ZenimXD

Wikipedia has no article at this title; its lists of conjectures and of unsolved problems give
the conjecture as the one on the optimal order of a multipoint iteration without memory, citing
H. T. Kung and J. F. Traub, Optimal order of one-point and multipoint iteration, J. ACM 21 (1974),
643–651, Conjecture 8.1:

  A multipoint iteration without memory based on n evaluations of the function or its
  derivatives has order at most 2^(n-1).

Reading of the source (the standard precise version of this information model, as in
M. J. Colbrook, Adversarial Wronskians: A proof of the Kung–Traub conjecture, arXiv:2610.40660,
Section 1, which also reports a Lean verification; the problem is stated here as listed, open):
* One iteration starts from the current point x. Evaluation j chooses a point z_j and a derivative
  order ν_j ≥ 0 from x and the earlier answers only, and receives f^(ν_j)(z_j). After at most n
  evaluations the method returns the next iterate from x and the answers. No memory: nothing but
  x is kept from earlier iterations. Deterministic and stationary: the rules are the same for every
  function and every iteration. No continuity or other regularity is imposed on the rules.
  A method stopping early is padded with unused slots (`none`).
* Order at least p means: for every function f analytic at every real point and every simple zero
  α of f, |T(x) - α| ≤ C |x - α|^p for all x ≠ α close to α, with C and the neighbourhood allowed to
  depend on f. Kung and Traub's order (J. ACM 1974, Section 2) implies this estimate, so the
  statement below rules out their notion of order as well.
* The conjecture: for n ≥ 1, no such method has order at least p for any real p > 2^(n-1).
-/

namespace OMA.S_wp_kung_traub_conjecture

/-- The answer to one evaluation: `some (z, ν)` returns the `ν`-th derivative of `f` at `z`
(`ν = 0` is the value `f z`); `none` is an unused slot and returns `0`. -/
noncomputable def answer (q : Option (ℝ × ℕ)) (f : ℝ → ℝ) : ℝ :=
  match q with
  | some (z, ν) => iteratedDeriv ν f z
  | none => 0

/-- A deterministic stationary multipoint iteration without memory using at most `n` evaluations.
Evaluation `j` is chosen from the current point and the `j` earlier answers; the output is computed
from the current point and all answers. Neither rule sees the function itself. -/
structure Method (n : ℕ) where
  query : (j : Fin n) → ℝ → (Fin j.val → ℝ) → Option (ℝ × ℕ)
  output : ℝ → (Fin n → ℝ) → ℝ

/-- The answers to the first `j` evaluations of one iteration started at `x`. -/
noncomputable def Method.answers {n : ℕ} (M : Method n) (f : ℝ → ℝ) (x : ℝ) :
    (j : ℕ) → j ≤ n → (Fin j → ℝ)
  | 0, _ => Fin.elim0
  | j + 1, hj =>
      let prev := M.answers f x j (Nat.le_of_succ_le hj)
      Fin.snoc prev (answer (M.query ⟨j, hj⟩ x prev) f)

/-- One iteration: the next iterate computed from the current point `x`. -/
noncomputable def Method.step {n : ℕ} (M : Method n) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  M.output x (M.answers f x n le_rfl)

/-- `M` has order at least `p` on every function analytic on `ℝ`, at every simple zero. -/
def HasOrderAtLeast {n : ℕ} (M : Method n) (p : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, (∀ t : ℝ, AnalyticAt ℝ f t) →
    ∀ α : ℝ, f α = 0 → deriv f α ≠ 0 →
      ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
        ∀ x : ℝ, 0 < |x - α| → |x - α| < δ → |M.step f x - α| ≤ C * |x - α| ^ p

/-- Kung–Traub conjecture: an iteration without memory using at most `n` evaluations of the
function or its derivatives has order at most `2^(n-1)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ M : Method n, ∀ p : ℝ, (2 : ℝ) ^ (n - 1) < p → ¬ HasOrderAtLeast M p := by
  sorry

end OMA.S_wp_kung_traub_conjecture
