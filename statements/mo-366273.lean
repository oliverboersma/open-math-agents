import Mathlib

/-!
# Numbers of the form $x^2(x-1) + y^2(y-1) + z^2(z-1)$ with $x,y,z\in\mathbb Z$

Source: https://mathoverflow.net/questions/366273/numbers-of-the-form-x2x-1-y2y-1-z2z-1-with-x-y-z-in-mathbb-z
Credit: @mgv27

I conjecture that any even integer can be represented as $x^2(x-1) + y^2(y-1) + z^2(z-1)$
with $x, y, z\in\mathbb Z$. I also conjecture that this is possible in infinitely many
different ways for any even integer. (Related: OEIS A336205.) Equivalently, every integer is
of the form $xT_x + yT_y + zT_z$ with $x,y,z\in\mathbb Z$, where $T_n = n(n+1)/2$.
Is this known, or can someone prove it?

Formalization notes:
* `main` states the first (weaker) conjecture: every even integer `n` equals
  `x²(x-1) + y²(y-1) + z²(z-1)` for some integers `x, y, z`.
* Evenness is necessary: `x²(x-1)` is always even, so odd integers are never represented.
* The stronger "infinitely many representations" conjecture is not formalized.
* Numerically, every even integer in `[-200, 200]` is represented (e.g. `-166` needs
  `x = -2160, y = -265`).
-/

namespace OMA.S_mo_366273

/-- The cubic `w²(w-1)` appearing in the representation. -/
def g (w : ℤ) : ℤ := w ^ 2 * (w - 1)

/-- Every even integer is a sum `g x + g y + g z` with `x, y, z ∈ ℤ`. -/
theorem main : ∀ n : ℤ, Even n → ∃ x y z : ℤ, n = g x + g y + g z := by
  sorry

end OMA.S_mo_366273
