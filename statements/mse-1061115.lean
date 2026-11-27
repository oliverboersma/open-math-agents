import Mathlib

/-!
# On the problem of polynomial bijection from $\mathbb Q\times\mathbb Q$ to $\mathbb Q$

Source: https://math.stackexchange.com/questions/1061115/on-the-problem-of-polynomial-bijection-from-mathbb-q-times-mathbb-q-to-math
Credit: @mgv27

The question asks for an explanation of the MathOverflow problem "Polynomial bijection from
$\mathbb Q\times\mathbb Q$ to $\mathbb Q$" (https://mathoverflow.net/questions/21003):
is there a polynomial $f \in \mathbb Q[x,y]$ such that the induced map
$\mathbb Q \times \mathbb Q \to \mathbb Q$, $(a,b) \mapsto f(a,b)$, is a bijection?
It also notes that even the existence of a polynomial *injection* is not known
(Poonen showed one exists assuming the Bombieri–Lang conjecture).

Formalization notes:
* The underlying open question is the MathOverflow one; the asker's expected direction is not
  stated, so `main` takes the natural "yes" reading: such a polynomial bijection exists.
* Polynomials in two variables are `MvPolynomial (Fin 2) ℚ`, evaluated at `![a, b]`.
-/

namespace OMA.S_mse_1061115

/-- The map `ℚ × ℚ → ℚ` induced by a two-variable rational polynomial `f`. -/
noncomputable def evalMap (f : MvPolynomial (Fin 2) ℚ) : ℚ × ℚ → ℚ :=
  fun p => MvPolynomial.eval ![p.1, p.2] f

/-- There is a polynomial `f ∈ ℚ[x, y]` inducing a bijection `ℚ × ℚ → ℚ`. -/
theorem main : ∃ f : MvPolynomial (Fin 2) ℚ, Function.Bijective (evalMap f) := by
  sorry

end OMA.S_mse_1061115
