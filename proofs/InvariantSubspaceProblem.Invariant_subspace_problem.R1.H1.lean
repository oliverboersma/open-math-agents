import OMAReductions.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1

-- Step InvariantSubspaceProblem.Invariant_subspace_problem.R1.H1
-- Credit: @caa1982

open scoped lp

private lemma span_singleton_ne_top (v : ℓ²(ℕ, ℂ)) :
    Submodule.span ℂ ({v} : Set ℓ²(ℕ, ℂ)) ≠ ⊤ := by
  intro htop
  let e0 : ℓ²(ℕ, ℂ) := lp.single 2 (0 : ℕ) (1 : ℂ)
  let e1 : ℓ²(ℕ, ℂ) := lp.single 2 (1 : ℕ) (1 : ℂ)
  have he0 : e0 ∈ Submodule.span ℂ ({v} : Set ℓ²(ℕ, ℂ)) := by rw [htop]; trivial
  have he1 : e1 ∈ Submodule.span ℂ ({v} : Set ℓ²(ℕ, ℂ)) := by rw [htop]; trivial
  obtain ⟨c0, hc0⟩ := Submodule.mem_span_singleton.mp he0
  obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp he1
  have h00 : c0 * v 0 = 1 := by
    have := congr_arg (fun f : ℓ²(ℕ, ℂ) => f 0) hc0
    simpa [e0] using this
  have h01 : c0 * v 1 = 0 := by
    have := congr_arg (fun f : ℓ²(ℕ, ℂ) => f 1) hc0
    simpa [e0] using this
  have h10 : c1 * v 0 = 0 := by
    have := congr_arg (fun f : ℓ²(ℕ, ℂ) => f 0) hc1
    simpa [e1] using this
  have h11 : c1 * v 1 = 1 := by
    have := congr_arg (fun f : ℓ²(ℕ, ℂ) => f 1) hc1
    simpa [e1] using this
  have hcontra : (1 : ℂ) = 0 := by
    calc (1 : ℂ) = (c0 * v 0) * (c1 * v 1) := by rw [h00, h11, mul_one]
      _ = (c0 * v 1) * (c1 * v 0) := by ring
      _ = 0 := by rw [h01, zero_mul]
  exact one_ne_zero hcontra

private lemma eigenline_invariant (T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) (z : ℂ) (v : ℓ²(ℕ, ℂ))
    (hv0 : v ≠ 0) (hv : T v = z • v) :
    Nonempty (InvariantSubspaceProblem.ClosedInvariantSubspace T) := by
  refine ⟨⟨Submodule.span ℂ {v}, ?_, span_singleton_ne_top v, Submodule.closed_of_finiteDimensional _, ?_⟩⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    exact hv0
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change T v ∈ Submodule.span ℂ {v}
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem OMA.solution : OMA.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1.H1 := by
  intro T z h
  let S : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) := T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)
  rcases h with hni | hnd
  · have hker : ∃ v : ℓ²(ℕ, ℂ), v ≠ 0 ∧ S v = 0 := by
      unfold Function.Injective at hni
      push Not at hni
      obtain ⟨x, y, hxy, hne⟩ := hni
      exact ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
    obtain ⟨v, hv0, hSv⟩ := hker
    have hTv : T v = z • v := by
      have : T v - z • v = 0 := by simpa [S] using hSv
      exact sub_eq_zero.mp this
    exact eigenline_invariant T z v hv0 hTv
  · by_cases hS0 : S = 0
    · let e0 : ℓ²(ℕ, ℂ) := lp.single 2 (0 : ℕ) (1 : ℂ)
      have he0 : e0 ≠ 0 := by
        intro h0
        have := congr_arg (fun f : ℓ²(ℕ, ℂ) => f 0) h0
        simp [e0] at this
      have hTe0 : T e0 = z • e0 := by
        have hSe0 : S e0 = 0 := by rw [hS0]; rfl
        have : T e0 - z • e0 = 0 := by simpa [S] using hSe0
        exact sub_eq_zero.mp this
      exact eigenline_invariant T z e0 he0 hTe0
    · let W : Submodule ℂ ℓ²(ℕ, ℂ) := (LinearMap.range S.toLinearMap).topologicalClosure
      refine ⟨⟨W, ?_, ?_, isClosed_closure, ?_⟩⟩
      · intro hbot
        apply hS0
        apply ContinuousLinearMap.ext
        intro x
        have hx : S x ∈ W := Submodule.le_topologicalClosure _ ⟨x, rfl⟩
        rw [hbot, Submodule.mem_bot] at hx
        exact hx
      · intro htop
        apply hnd
        rw [DenseRange, dense_iff_closure_eq]
        have hset : (W : Set ℓ²(ℕ, ℂ)) = Set.univ := by rw [htop]; rfl
        have hcoe : (W : Set ℓ²(ℕ, ℂ)) = closure (Set.range (T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ))) := rfl
        rw [← hcoe]
        exact hset
      · calc Submodule.map T.toLinearMap (LinearMap.range S.toLinearMap).topologicalClosure
            ≤ (Submodule.map T.toLinearMap (LinearMap.range S.toLinearMap)).topologicalClosure :=
              Submodule.topologicalClosure_map T _
          _ ≤ (LinearMap.range S.toLinearMap).topologicalClosure := by
              apply Submodule.topologicalClosure_mono
              rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
              refine ⟨T x, ?_⟩
              change S (T x) = T (S x)
              simp [S, map_sub, map_smul]
