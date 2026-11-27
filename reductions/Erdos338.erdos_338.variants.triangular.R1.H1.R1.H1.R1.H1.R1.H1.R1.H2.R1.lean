import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-! The ideal asymptotic for an imaginary quadratic field, the coefficients
of its Dedekind zeta function, and Dirichlet's hyperbola method.
The regulator is one and the unit torsion has order at least two. -/

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
open Finset Polynomial NumberField NumberField.InfinitePlace NumberField.Units Real Filter
open scoped NumberField Topology

theorem quad_irred {s:ℕ} (hs:0<s) : Irreducible (X^2+C (s:ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_X_pow_add_C]; decide)
  intro x hx
  simp only [IsRoot.def,eval_add,eval_pow,eval_X,eval_C] at hx
  have := Nat.cast_pos (α:=ℚ).mpr hs
  nlinarith [sq_nonneg x]

private theorem abs_det_empty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] (M : Matrix ι ι ℝ) :
    |M.det|=1 := by rw [Matrix.det_isEmpty,abs_one]

private theorem factors (s:ℕ) (hs:0<s) [Fact (Irreducible (X^2+C (s:ℚ)))] :
    let K := AdjoinRoot (X^2+C (s:ℚ))
    nrRealPlaces K=0 ∧ nrComplexPlaces K=1 ∧ regulator K=1 ∧ 2≤torsionOrder K := by
  classical
  intro K
  let δ := AdjoinRoot.root (X^2+C (s:ℚ))
  have ds : δ^2=-(s:K) := by
    have h := AdjoinRoot.eval₂_root (X^2+C (s:ℚ))
    rw [eval₂_add,eval₂_pow,eval₂_X,eval₂_C] at h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [δ,map_natCast] using h
  have nr : nrRealPlaces K=0 := by
    apply nrRealPlaces_eq_zero_iff.mpr
    constructor
    intro v
    apply not_isReal_iff_isComplex.mp
    intro hv
    let e := embedding_of_isReal hv
    have hh : (e δ)^2 = -(s:ℝ) := calc
      _ = e (δ^2) := (map_pow e δ 2).symm
      _ = e (-(s:K)) := congrArg e ds
      _ = _ := by rw [map_neg,map_natCast]
    have := (Nat.cast_pos (α:=ℝ)).mpr hs
    nlinarith [sq_nonneg (e δ)]
  have rank : Module.finrank ℚ K=2 := by
    let f : ℚ[X] := X^2+C (s:ℚ)
    have nz : f ≠ 0 := (quad_irred hs).ne_zero
    change Module.finrank ℚ (AdjoinRoot f)=2
    rw [(AdjoinRoot.powerBasis nz).finrank,AdjoinRoot.powerBasis_dim]
    exact natDegree_X_pow_add_C
  have card := card_add_two_mul_card_eq_rank (K:=K)
  have nc : nrComplexPlaces K=1 := by omega
  have one : Units.rank K=0 := by
    rw [Units.rank,card_eq_nrRealPlaces_add_nrComplexPlaces,nr,nc]
  haveI : IsEmpty (Fin (Units.rank K)) := by rw [one]; infer_instance
  letI := (equivFinRank K).symm.isEmpty
  have reg : regulator K=1 := by rw [regulator_eq_det']; apply abs_det_empty
  have two := torsionOrder_pos K
  obtain ⟨j,hj⟩ := even_torsionOrder K
  exact ⟨nr,nc,reg,by omega⟩

-- Count ideals by norm via the quadratic Euler factors.
def H1 : Prop := ∀ s : ℕ, ∀ hs : 0<s, Squarefree s → s%8=3 →
  letI : Fact (Irreducible (X^2+C (s:ℚ))) := ⟨quad_irred hs⟩
  let K := AdjoinRoot (X^2+C (s:ℚ))
  ∀ n : ℕ, 0<n → (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I=n}:ℤ) =
    ∑ a∈n.divisors,jacobiSym a s

-- The integral basis of the maximal quadratic order has discriminant minus s.
def H2 : Prop := ∀ s : ℕ, ∀ hs : 0<s, Squarefree s → s%8=3 →
  letI : Fact (Irreducible (X^2+C (s:ℚ))) := ⟨quad_irred hs⟩
  let K := AdjoinRoot (X^2+C (s:ℚ))
  NumberField.discr K=-(s:ℤ)

-- Averaging the divisor convolution recovers L(1) by Dirichlet's hyperbola method.
def H3 : Prop := ∀ s:ℕ, 0<s → s%8=3 → ∀ L:ℝ,
  Tendsto (fun n:ℕ => ∑ a∈Icc 1 n,(jacobiSym a s:ℝ)/(a:ℝ)) atTop (𝓝 L) →
  Tendsto (fun n:ℕ => (∑ k∈Icc 1 n,∑ a∈k.divisors,(jacobiSym a s:ℝ))/(n:ℝ)) atTop (𝓝 L)

-- Gauss reduction counts ideal classes by reduced forms.
def H4 : Prop := ∀ s : ℕ, ∀ hs : 0<s, Squarefree s → s%8=3 →
  letI : Fact (Irreducible (X^2+C (s:ℚ))) := ⟨quad_irred hs⟩
  let K := AdjoinRoot (X^2+C (s:ℚ))
  classNumber K ≤ {v : ℤ×ℤ×ℤ | v.1>0 ∧ |v.2.1|≤v.1 ∧ v.1≤v.2.2 ∧ 4*v.1*v.2.2=(s:ℤ)+v.2.1^2}.ncard

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro coefficients discriminant averages classes s hs hsq hm L hlim
  letI : Fact (Irreducible (X^2+C (s:ℚ))) := ⟨quad_irred hs⟩
  let K := AdjoinRoot (X^2+C (s:ℚ))
  let a (n:ℕ) := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I=n}:ℝ)
  have lim : Tendsto (fun n:ℕ => (∑ k∈Icc 1 n,a k)/(n:ℝ)) atTop (𝓝 L) := by
    refine (averages s hs hm L hlim).congr (fun n => ?_)
    congr 1
    apply sum_congr rfl
    intro k hk
    have eq := coefficients s hs hsq hm k (mem_Icc.mp hk).1
    dsimp only [a]
    exact_mod_cast eq.symm
  have hl := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg a lim
    (fun n => Nat.cast_nonneg _)
  have hr := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hfun : (fun s:ℝ => (s-1)*LSeries (fun n => (a n:ℂ)) s) =
      (fun s:ℝ => (s-1)*dedekindZeta K s) := by
    funext x
    simp only [dedekindZeta,a,Complex.ofReal_natCast]
  rw [hfun] at hl
  have eq : L=dedekindZeta_residue K := Complex.ofReal_injective (tendsto_nhds_unique hl hr)
  obtain ⟨r,c,reg,u⟩ := factors s hs
  have disc := discriminant s hs hsq hm
  have cl := classes s hs hsq hm
  change NumberField.discr K=-(s:ℤ) at disc
  change classNumber K ≤ {v : ℤ×ℤ×ℤ | v.1>0 ∧ |v.2.1|≤v.1 ∧ v.1≤v.2.2 ∧ 4*v.1*v.2.2=(s:ℤ)+v.2.1^2}.ncard at cl
  rw [eq,dedekindZeta_residue_def,r,c,reg,disc]
  have pos : 0 < (s:ℝ) := by exact_mod_cast hs
  have un : (2:ℝ)≤torsionOrder K := by exact_mod_cast u
  have sr := sqrt_pos.mpr pos
  simp only [pow_zero,pow_one,one_mul,mul_one,Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_pos pos]
  have sqp := Real.sqrt_pos.mpr pos
  rw [←mul_div_assoc,div_le_iff₀ (mul_pos (by positivity) sqp)]
  have v : ((classNumber K):ℝ) ≤ _ := Nat.cast_le.mpr cl
  calc _ = (π*(classNumber K))*2*sqrt (s:ℝ) := by ring
       _ ≤ _ := by rw [←mul_assoc]; gcongr

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
