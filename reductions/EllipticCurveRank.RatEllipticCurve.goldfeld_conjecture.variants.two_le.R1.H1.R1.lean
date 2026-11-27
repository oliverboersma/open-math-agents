import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1
import Mathlib

/-! Reduction from integral twists to positive squarefree twist parameters.
The square classes with a fixed square multiplier have limiting density zero.
The summable majorant 1/b² justifies summing those densities. -/
namespace OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1
open EllipticCurveRank Finset Filter
open scoped Topology Classical

/-- Squarefree positive twists of Mordell–Weil rank at least two, the
density-zero consequence of Smith's theorem for squarefree parameters. -/
def H1 : Prop := ∀ E : RatEllipticCurve,
  Tendsto (fun H : ℕ => (((Icc 1 H).filter (fun a : ℕ => Squarefree a ∧
    2 ≤ E.twistRank (a:ℤ))).card:ℝ)/H) atTop (𝓝 0)

/-- Multiplication of the twist parameter by a nonzero square gives an
isomorphism of groups of rational points. -/
def H2 : Prop := ∀ E : RatEllipticCurve, ∀ a b : ℕ, 0 < a → 0 < b →
  Nonempty ((E.quadraticTwist ((b^2*a:ℕ):ℤ)).Point ≃+ (E.quadraticTwist (a:ℤ)).Point)

lemma square_saturation (T : ℕ → Prop)
    (invar : ∀ a b : ℕ, 0 < a → 0 < b → T (b^2*a) → T a)
    (density : Tendsto (fun H : ℕ => (((Icc 1 H).filter (fun a => Squarefree a ∧ T a)).card:ℝ)/H)
      atTop (𝓝 0)) :
    Tendsto (fun H : ℕ => (((Icc 1 H).filter T).card:ℝ)/H) atTop (𝓝 0) := by
  classical
  let A := fun H : ℕ => (Icc 1 H).filter (fun a => Squarefree a ∧ T a)
  let f (H b : ℕ) : ℝ := ((A (H / b^2)).card:ℝ)/H
  have Ac (m : ℕ) : (A m).card ≤ m := by
    simpa [Nat.card_Icc] using card_le_card (filter_subset (fun a => Squarefree a ∧ T a) (Icc 1 m))
  have nonneg (H b : ℕ) : 0 ≤ f H b := by dsimp [f]; positivity
  have fbound (H b : ℕ) : ‖f H b‖ ≤ 1/(b:ℝ)^2 := by
    rw [Real.norm_of_nonneg (nonneg H b)]
    by_cases h0 : H = 0
    · simp [h0,f]
    by_cases b0 : b = 0
    · simp [b0,f,A]
    have Hpos : (0:ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero h0
    have bpos : (0:ℝ) < (b:ℝ)^2 := by positivity
    have le := (Nat.mul_le_mul_right (b^2) (Ac (H/b^2))).trans (Nat.div_mul_le_self H (b^2))
    apply (div_le_div_iff₀ Hpos bpos).mpr
    simpa using (show ((A (H/b^2)).card:ℝ)*(b:ℝ)^2 ≤ (H:ℝ) by exact_mod_cast le)
  have key (b : ℕ) : Tendsto (fun H : ℕ => f H b) atTop (𝓝 0) := by
    by_cases b0 : b = 0
    · simp [b0,f,A]
    have L := Nat.tendsto_div_const_atTop (pow_ne_zero 2 b0)
    have upper := density.comp L
    apply squeeze_zero' (Eventually.of_forall (fun H => nonneg H b)) _ upper
    filter_upwards [L.eventually_ge_atTop 1] with H hp
    have le : H/b^2 ≤ H := Nat.div_le_self _ _
    have p : (0:ℝ) < (H/b^2:ℕ) := by exact_mod_cast (show 0 < H/b^2 by omega)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) p (by exact_mod_cast le)
  have dom := Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  have result := tendsto_tsum_of_dominated_convergence (f:=f) (g:=fun _ : ℕ => (0:ℝ))
    dom key (Eventually.of_forall fbound)
  have total : Tendsto (fun H : ℕ => ∑' b,f H b) atTop (𝓝 0) := by simpa using result
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ total
  filter_upwards [eventually_ge_atTop 1] with H hH
  let V := (Icc 1 H).filter T
  let S (b : ℕ) := (A (H/b^2)).image (fun a => b^2*a)
  have sub : V ⊆ (Icc 1 H).biUnion S := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn,nt⟩
    obtain ⟨np,nH⟩ := mem_Icc.mp hn
    obtain ⟨a,b,ap,bp,eq,sa⟩ := Nat.sq_mul_squarefree_of_pos np
    have b2 : b ≤ b^2 := by simpa [sq] using Nat.le_mul_of_pos_right b bp
    have bH : b ≤ H := b2.trans ((Nat.le_mul_of_pos_right _ ap).trans (eq ▸ nH))
    refine mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨bp,bH⟩,mem_image.mpr ⟨a,?_,eq⟩⟩
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ap,(Nat.le_div_iff_mul_le (by positivity)).mpr ?_⟩,
      sa,invar a b ap bp (eq ▸ nt)⟩
    simpa [Nat.mul_comm] using eq.trans_le nH
  have le : V.card ≤ ∑ b ∈ Icc 1 H,(A (H/b^2)).card :=
    (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le)))
  have sum : Summable (f H) := Summable.of_norm_bounded dom (fbound H)
  calc
    (V.card:ℝ)/H ≤ ((∑ b ∈ Icc 1 H,(A (H/b^2)).card:ℕ):ℝ)/H := by gcongr
    _ = ∑ b ∈ Icc 1 H,f H b := by simp [f,Nat.cast_sum,sum_div]
    _ ≤ _ := sum.sum_le_tsum _ (fun b _ => nonneg H b)

theorem main : H1 → H2 → OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1.H1 := by
  intro sqfree equiv E
  let T (a : ℕ) := 2 ≤ E.twistRank (a:ℤ)
  have inv (a b : ℕ) (ap : 0 < a) (bp : 0 < b) : T (b^2*a) → T a := by
    obtain ⟨e⟩ := equiv E a b ap bp
    have eq := (e.toIntLinearEquiv).finrank_eq
    change 2 ≤ Module.finrank ℤ _ → 2 ≤ Module.finrank ℤ _
    rw [eq]
    exact id
  have lim := square_saturation T inv (by
    apply (sqfree E).congr
    intro H
    apply congrArg (fun S : Finset ℕ => (S.card:ℝ)/H)
    ext a
    simp only [mem_filter,T])
  apply lim.congr (fun H => ?_)
  let A := (Icc 1 H).filter T
  have sub : {d : ℤ | 0 < d ∧ d ≤ (H:ℤ) ∧ 2 ≤ E.twistRank d} =
      (↑(A.image (fun a : ℕ => (a:ℤ))) : Set ℤ) := by
    ext d
    constructor
    · rintro ⟨dp,dH,rank⟩
      have e : (d.toNat:ℤ)=d := Int.toNat_of_nonneg dp.le
      refine mem_image.mpr ⟨d.toNat,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩,e⟩
      simpa [T,e] using rank
    · intro hd
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hd
      obtain ⟨ha,ta⟩ := mem_filter.mp ha
      obtain ⟨ap,aH⟩ := mem_Icc.mp ha
      exact ⟨by omega,by omega,ta⟩
  rw [sub,Set.ncard_coe_finset,card_image_of_injective _ Nat.cast_injective]
  apply congrArg (fun S : Finset ℕ => (S.card:ℝ)/H)
  ext a
  simp only [A,mem_filter]

end OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1_H1_R1
