import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H1_R1

-- Step Green100.green_100.variants.operator_norm.R1.H1.R1.H3
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1.H3 := by
  intro L _ a
  let φ : (Multiplicative (Fin 3 → ℤ) ⋊[a] L) →* (Multiplicative (Fin 3 → ℤ) ⋊[a] L) :=
    { toFun := fun x => ⟨x.left * x.left, x.right⟩
      map_one' := by
        apply SemidirectProduct.ext <;> simp
      map_mul' := fun x y => by
        apply SemidirectProduct.ext
        · simp only [SemidirectProduct.mul_left, map_mul]
          ac_rfl
        · simp only [SemidirectProduct.mul_right] }
  refine ⟨φ, ?_, ?_⟩
  · intro x y hxy
    have hL : x.left * x.left = y.left * y.left := congrArg SemidirectProduct.left hxy
    have hR : x.right = y.right := by simpa [φ] using congrArg SemidirectProduct.right hxy
    apply SemidirectProduct.ext _ hR
    apply Multiplicative.toAdd.injective
    ext i
    have hadd : Multiplicative.toAdd (x.left * x.left) i =
        Multiplicative.toAdd (y.left * y.left) i :=
      congrArg (fun (z : Multiplicative (Fin 3 → ℤ)) => Multiplicative.toAdd z i) hL
    simp only [toAdd_mul, Pi.add_apply] at hadd
    omega
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj ⟨Multiplicative.ofAdd (fun _ => (1 : ℤ)), 1⟩
    have hL : x.left * x.left = Multiplicative.ofAdd (fun _ => (1 : ℤ)) :=
      congrArg SemidirectProduct.left hx
    have h0 : Multiplicative.toAdd (x.left * x.left) 0 = (1 : ℤ) := by
      have := congrArg (fun (z : Multiplicative (Fin 3 → ℤ)) => Multiplicative.toAdd z 0) hL
      simpa using this
    simp only [toAdd_mul, Pi.add_apply] at h0
    omega
