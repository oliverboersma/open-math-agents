import OMAStatements.S_oeis_a169597

-- The product of twin primes determines their midpoint by its square.
-- Original proof: @LAPRAI, PR #6708. Shorter proof: @dwilfand-sys.
theorem OMA.solution : type_of% @OMA.S_oeis_a169597.main := by
  intro n hn hmod p hp hp2 h
  have hs : (p + 1) * (p + 1) = (6 * n + 6) * (6 * n + 6) := by nlinarith
  have eq := Nat.mul_self_inj.mp hs
  obtain rfl : p = 6 * n + 5 := by omega
  rcases hmod with hmod | hmod
  · have := hp2.eq_one_or_self_of_dvd 19 (by omega)
    omega
  · have := hp.eq_one_or_self_of_dvd 19 (by omega)
    omega
