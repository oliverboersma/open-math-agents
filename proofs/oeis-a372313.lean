import OMAStatements.S_oeis_a372313
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Rows of A372313 that end in 33

Source: OEIS A372313, conjectured by Ali Sada.
Proof by @DomTheDeveloper.
-/

open OMA.S_oeis_a372313

private lemma transform_mod {x : ℕ} (hx : x % 100 = 66) :
    transform x % 100 = 33 := by
  have hn : x ≠ 0 := by omega
  have htwo : 1 ≤ x.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp (by change 2 ∣ x; omega)
  have hfour : ¬ 2 ≤ x.factorization 2 := by
    intro h
    have hd : 2 ^ 2 ∣ x := (Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr h
    change 4 ∣ x at hd
    omega
  have he : x.factorization 2 = 1 := by omega
  simp only [transform, he, pow_one]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a372313.main := by
  intro n _ hrow k
  cases k with
  | zero => omega
  | succ k =>
    intro _
    induction k with
    | zero => exact hrow
    | succ k ih =>
      change transform (entry n (k + 1) + (2 * n - 1)) % 100 = 33
      apply transform_mod
      change (2 * n - 1) % 100 = 33 at hrow
      omega
