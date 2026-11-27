import OMAStatements.S_oeis_a377109
import Mathlib

/-!
Disproof of the prime-divisibility conjecture in OEIS A377109.
The four residues modulo 241 return to the initial state after 240 steps.
Their first coordinate stays nonzero throughout the period.
-/

namespace OMA

open S_oeis_a377109

private abbrev Quad := ℕ × ℕ × ℕ × ℕ

private def reduce241 (v : Quad) : Quad :=
  (v.1 % 241, v.2.1 % 241, v.2.2.1 % 241, v.2.2.2 % 241)

private def advance241 : Quad → Quad
  | (a, b, c, d) =>
    ((2*a+2*b+3*c) % 241, (a+2*b+3*d) % 241,
      (a+2*c+2*d) % 241, (b+c+2*d) % 241)

private def orbit241 : ℕ → Quad
  | 0 => (1, 0, 0, 0)
  | n+1 => advance241 (orbit241 n)

private theorem orbit241_correct (n : ℕ) : orbit241 n = reduce241 (coords n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [orbit241, ih, coords]
    obtain ⟨a, b, c, d⟩ := coords n
    simp only [advance241, reduce241, Prod.mk.injEq]
    repeat' apply And.intro
    all_goals simp [Nat.add_mod, Nat.mul_mod]

private theorem orbit241_period (n : ℕ) : orbit241 (240+n) = orbit241 n := by
  induction n with
  | zero => decide +kernel
  | succ n ih => exact congrArg advance241 ih

private theorem nonzero241 (n : ℕ) : (orbit241 n).1 ≠ 0 := by
  have finiteCheck : ∀ i : Fin 240, (orbit241 i.val).1 ≠ 0 := by decide +kernel
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 240
    · exact finiteCheck ⟨n, hn⟩
    · rw [show n = 240+(n-240) by omega, orbit241_period]
      exact ih (n-240) (by omega)

end OMA

open OMA OMA.S_oeis_a377109

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377109.main) := by
  intro claim
  obtain ⟨k, _, hits, _⟩ := claim 241 (by norm_num)
  have hd := (hits (k 0)).2 ⟨0, rfl⟩
  have bad := nonzero241 (k 0)
  rw [orbit241_correct] at bad
  exact bad (Nat.mod_eq_zero_of_dvd hd)
