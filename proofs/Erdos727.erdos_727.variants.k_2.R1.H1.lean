import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1

-- Step Erdos727.erdos_727.variants.k_2.R1.H1: hypothesis H1 of reduction Erdos727.erdos_727.variants.k_2.R1
-- Credit: @NoahPuckett-IO
-- (2n)! = C(2n, n) * (n!)^2 and (n+2)! = (n+1)(n+2) * n!, so cancel the positive factor (n!)^2.

theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H1 := by
  intro n
  have h1 : (2 * n).factorial = (2 * n).choose n * n.factorial ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [← h]
    ring
  have h2 : (n + 2).factorial ^ 2 = ((n + 1) * (n + 2)) ^ 2 * n.factorial ^ 2 := by
    rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [h1, h2]
  exact Nat.mul_dvd_mul_iff_right (by positivity)
