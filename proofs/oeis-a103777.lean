import OMAStatements.S_oeis_a103777

/-! The obstruction is primality at residues 3 and 4 modulo 5.  Unlike
  the original proof in PR 7257, reduce the polynomial modulo 5 directly,
  using the fact that congruence is preserved by addition and multiplication. -/

open OMA.S_oeis_a103777

private theorem composite {j : ℕ} (hj : 3 ≤ j % 5) : ¬ (f j).Prime := by
  intro hp
  have h := (Nat.mod_modEq j 5).symm
  have hc : f j ≡ f (j % 5) [MOD 5] :=
    (((h.pow 2).mul_left 8).add (h.mul_left 4)).add_right 1
  have hr : j % 5 = 3 ∨ j % 5 = 4 := by omega
  have hz : f (j % 5) ≡ 0 [MOD 5] := by rcases hr with hm | hm <;> rw [hm] <;> decide
  have hd : 5 ∣ f j := Nat.dvd_of_mod_eq_zero (hc.trans hz)
  have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp hd
  have hj' : 3 ≤ j := hj.trans (Nat.mod_le _ _)
  unfold f at he
  nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a103777.main := by
  intro n ⟨h₀, h₁, h₂, h₃⟩
  rcases (by omega : 3 ≤ n % 5 ∨ 3 ≤ (n + 1) % 5 ∨ 3 ≤ (n + 2) % 5 ∨ 3 ≤ (n + 3) % 5) with
    h | h | h | h
  · exact composite h h₀
  · exact composite h h₁
  · exact composite h h₂
  · exact composite h h₃
