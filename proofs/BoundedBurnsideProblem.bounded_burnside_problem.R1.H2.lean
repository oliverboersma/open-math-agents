import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

/-! Step H2: a quotient of the free group on two generators is finitely generated, and in the
quotient by the normal closure of all n-th powers every element has n-th power one. -/

-- Step BoundedBurnsideProblem.bounded_burnside_problem.R1.H2: hypothesis H2 of reduction BoundedBurnsideProblem.bounded_burnside_problem.R1
-- Credit: @ivillar

theorem OMA.solution : OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1.H2 := by
  intro n
  refine ⟨Group.fg_of_surjective (QuotientGroup.mk'_surjective _), fun g => ?_⟩
  induction g using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩
