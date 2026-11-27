import OMAStatements.S_oeis_a056142

-- Problem: A056142: Concatenate n, floor[n/10], floor[n/100] ... (but do not continue if floor[.]=0).
-- Upstream: formal-conjectures statements/oeis-a056142.lean:0 (declaration OMA.S_oeis_a056142.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Counterexample n = 101: the concatenation 101, 10, 1 is 101101, a palindrome,
yet the digits of 101 are not all equal. This matches the OEIS comment of
David Wasserman (2005): for three-digit n, a(n) is a palindrome iff n is.
So the conjecture as literally stated (3 or more digits) is false; the
intended form is presumably for 4 or more digits.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a056142.main) := by
  intro h
  have hw : OMA.S_oeis_a056142.decimalWord 101 = [1, 0, 1] := by
    norm_num [OMA.S_oeis_a056142.decimalWord]
  have h10 : (1 : ℕ) = 0 :=
    h 101 (by rw [hw]; decide) (by rw [hw]; decide) 1 (by rw [hw]; decide) 0
      (by rw [hw]; decide)
  exact absurd h10 (by decide)
