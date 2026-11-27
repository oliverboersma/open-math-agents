import OMAStatements.S_oeis_a071282
import Mathlib.Tactic

/-!
At expansion level three the denominator occupies an even stream index.
The values at the odd denominator positions are 3. At the even ones,
level two supplies the three-periodic list 2, 1, 2.
-/
-- Credit: @dk8827

namespace OMA.A071282

open OMA.S_oeis_a071282 hiding peirce

private theorem second_expansion (q : ℕ) :
    OMA.S_oeis_a071282.peirce 2 (2 * q) =
      if q % 3 = 1 then Symbol.den 1 else Symbol.den 2 := by
  have residues : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases residues with h | h | h
  · have hr : 2 * q % 3 = 0 := by omega
    have hj : (2 * q / 3 + 1) % 2 = 1 := by omega
    simp [OMA.S_oeis_a071282.peirce, expandStream, hr, hj, h]
  · have hr : 2 * q % 3 = 2 := by omega
    have hj : (2 * q / 3) % 2 = 0 := by omega
    simp [OMA.S_oeis_a071282.peirce, expandStream, hr, hj, h]
  · have hr : 2 * q % 3 = 1 := by omega
    have hj : (2 * q / 3 + 1) % 2 = 0 := by omega
    simp [OMA.S_oeis_a071282.peirce, expandStream, hr, hj, h]

private theorem even_position (q : ℕ) :
    denominatorAt 3 (2 * q) = if q % 3 = 1 then 1 else 2 := by
  have hr : 2 * (2 * q) % 4 = 0 := by omega
  have hq : 2 * (2 * q) / 4 = q := by omega
  have he : OMA.S_oeis_a071282.peirce 3 (2 * (2 * q)) = OMA.S_oeis_a071282.peirce 2 (2 * q) := by
    change expandStream 2 (OMA.S_oeis_a071282.peirce 2) (2 * (2 * q)) = _
    simp [expandStream, hr, hq, Nat.mul_comm q 2]
  rw [denominatorAt, he, second_expansion]
  split_ifs <;> rfl

private theorem odd_position (q : ℕ) : denominatorAt 3 (2 * q + 1) = 3 := by
  have hr : 2 * (2 * q + 1) % 4 = 2 := by omega
  have he (j : ℕ) : (j + 1) * 2 % 2 = 0 := Nat.mul_mod_left _ _
  have hpeirce : OMA.S_oeis_a071282.peirce 3 (2 * (2 * q + 1)) = Symbol.den 3 := by
    change expandStream 2 (OMA.S_oeis_a071282.peirce 2) (2 * (2 * q + 1)) = _
    simp [expandStream, hr, he]
  rw [denominatorAt, hpeirce]

theorem period (i : ℕ) : denominatorAt 3 i = ([2, 3, 1, 3, 2, 3] : List ℕ)[i % 6]! := by
  have hcases : i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 2 ∨
      i % 6 = 3 ∨ i % 6 = 4 ∨ i % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h | h
  · have hi : i = 2 * (i / 2) := by omega
    have hj : i / 2 % 3 ≠ 1 := by omega
    rw [h, hi, even_position]
    simp [hj]
  · have hi : i = 2 * (i / 2) + 1 := by omega
    rw [h, hi, odd_position]
    rfl
  · have hi : i = 2 * (i / 2) := by omega
    have hj : i / 2 % 3 = 1 := by omega
    rw [h, hi, even_position]
    simp [hj]
  · have hi : i = 2 * (i / 2) + 1 := by omega
    rw [h, hi, odd_position]
    rfl
  · have hi : i = 2 * (i / 2) := by omega
    have hj : i / 2 % 3 ≠ 1 := by omega
    rw [h, hi, even_position]
    simp [hj]
  · have hi : i = 2 * (i / 2) + 1 := by omega
    rw [h, hi, odd_position]
    rfl

end OMA.A071282

theorem OMA.solution : type_of% @OMA.S_oeis_a071282.main := OMA.A071282.period
