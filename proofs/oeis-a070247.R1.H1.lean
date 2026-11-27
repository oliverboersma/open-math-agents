import OMAReductions.R_oeis_a070247_R1

-- Proper divisors from OEIS A102050, indexed by the exponent parameter k.
private def divisor : Fin 15 → ℕ :=
  ![1, 1, 73, 17, 353, 19841, 1265011073, 257, 10753, 1514497, 1856104284667693057,
    106907803649, 458924033, 3635898263938497962802538435084289,
    1702047085242613845984907230501142529]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem certificate : ∀ j : Fin 15, 2 ≤ j.val →
    let n := 10 ^ (2 ^ j.val) + 1
    divisor j ∣ n ∧ divisor j ≠ 1 ∧ divisor j ≠ n := by
  decide +kernel

theorem OMA.solution : OMA.R_oeis_a070247_R1.H1 := by
  intro k hk hk'
  obtain ⟨hd, h₁, h₂⟩ := certificate ⟨k, by omega⟩ hk
  exact Nat.not_prime_of_dvd_of_ne hd h₁ h₂
