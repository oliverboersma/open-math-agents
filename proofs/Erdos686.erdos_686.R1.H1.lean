import OMAReductions.R_Erdos686_erdos_686_R1

-- Step Erdos686.erdos_686.R1.H1: hypothesis H1 of reduction Erdos686.erdos_686.R1
-- Credit: @anmolspace
-- Proof: the upstream Pell-equation proof of Erdos686.erdos_686.variants.non_square (k = 2), with the
-- two small-case native_decide searches (N = 2, N = 3) replaced by decide +kernel, so that only the
-- standard axioms are used.

open Erdos686

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  intro N hN_ge_2 hN_not_square

  have hN_not_square' : ¬ ∃ s, s * s = N := fun ⟨s, hs⟩ => hN_not_square ⟨s, hs.symm⟩

  -- 1. Setup the existence for k = 2 and simplify the products
  exists 2, by valid
  field_simp
  simp [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]

  -- 2. Case split on the existence of solutions for small bounds
  by_cases h : {n | ∃ k, N * ((n + 1) * (n + 2)) = (k + 1) * (k + 2)}.Nonempty
  · obtain rfl | hN_lt := hN_ge_2.eq_or_lt
    · exact mod_cast
        if a : ∃ a ∈ Finset.range 30, ∃ n ∈ Finset.range 30, _ then
          a.imp fun a s => s.2.imp fun and => And.right
        else
          by exact (a (by decide +kernel)).elim

    obtain rfl | hN_ne_3 := eq_or_ne N 3
    · exact mod_cast
        if a : ∃ a ∈ Finset.range 30, ∃ n ∈ Finset.range 30, _ then
          a.imp fun and μ => μ.2.imp fun and => And.right
        else
          by exact (a (by decide +kernel)).elim

    exact h.mono fun and =>
      .imp fun a s =>
        mod_cast (by refine ⟨by
            nlinarith only [pow_three and, s, show N > 3 by valid], ?_⟩; push_cast [s.symm]; field_simp)

  -- 3. Reduce the general case to Pell's Equation
  convert (Pell.exists_of_not_isSquare _)
  show @@_ ↔ ¬ IsSquare (N * 4 : ℤ) → _
  · use
      mod_cast h.elim ∘ .imp (fun n ⟨m, hle, heq⟩ => ⟨m, by
        push_cast at heq; rw [eq_div_iff (by positivity : ((n : ℚ) + 1) * (↑n + 2) ≠ 0)] at heq
        exact_mod_cast heq⟩),
      (. (mod_cast hN_not_square' ∘ .rec (by
          use . / 2
          norm_num [←., true, Nat.div_mul_div_comm _, ((2).pow_dvd_pow_iff two_ne_zero).1, false, sq]))
        |>.elim ↑? _)

    use fun and ⟨A, B, _⟩ =>
      absurd
        (eq_add_of_sub_eq B)
        (A.natAbs_sq ▸ and.natAbs_sq ▸ mod_cast fun and => h ?_)

    -- Parity analysis
    obtain ⟨l, hl⟩ | ⟨a, ha⟩ := ((by · bound : ℤ)).natAbs.even_or_odd
    · exact absurd
        (and.trans (by rw [mul_right_comm]) |>.symm.trans (by rw [(by valid :), sq, add_mul]))
        (by valid)

    match a with
    | 0 => simp_all
    | S + 1 =>
        use A.natAbs + S, N * A.natAbs + S, by nlinarith only [‹_› ▸ and]

  omega
