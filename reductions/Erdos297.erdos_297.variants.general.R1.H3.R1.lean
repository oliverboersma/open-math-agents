import OMAReductions.R_Erdos297_erdos_297_variants_general_R1
import Mathlib

/-! # Passing from a sublevel count to an exact Egyptian fraction

The sublevel entropy estimate only counts sums below a fixed threshold. The
arithmetic input reserves a small complement in which each partial sum can
be completed. Restricting a subset to the dense part loses at most one bit
per deleted denominator, since the deleted trace and any completion recover
the original set. The calibrated weight is constant on every exact fiber.
This follows the entropy and absorption split in Conlon et al., arXiv:2404.16016,
Sections 2 and 4. -/

namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1

open Finset Real Filter Topology Erdos297
open scoped Classical

-- A strictly smaller sublevel has almost all the exponential entropy
-- required at the calibrated tilt. A sublevel uses an inequality only.
def H1 : Prop := ∀ (x : ℚ) (l : ℝ), 0 < x → massIntegral l = x → ∀ ε > (0:ℝ),
    ∃ d : ℚ, 0 < d ∧ ∀ᶠ N : ℕ in atTop,
      exp (-ε*N) * (∏ n ∈ Icc 1 N, (1+exp (-l*(N:ℝ)/n))) ≤
      (((Icc 1 N).powerset.filter (fun A : Finset ℕ => (∑ n ∈ A, (1:ℚ)/n) ≤ x-d)).card:ℝ) *
        exp (-l*N*(x:ℝ))

-- A small set of reserved denominators can complete every eligible partial
-- sum. Taking the intersection with U recovers the partial choice exactly.
def H2 : Prop := ∀ (x d : ℚ), 0 < x → 0 < d → ∀ δ > (0:ℝ), ∀ᶠ N : ℕ in atTop,
    ∃ U ⊆ Icc 1 N, (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧
      ∀ A ⊆ U, (∑ n ∈ A, (1:ℚ)/n) ≤ x-d → ∃ B ⊆ Icc 1 N,
        B ∩ U = A ∧ (∑ n ∈ B, (1:ℚ)/n) = x

lemma trace_count {α : Type*} [DecidableEq α] (P U : Finset α) (F G : Finset (Finset α))
    (contained : ∀ A ∈ F, A ⊆ P) (complete : ∀ A ∈ F, ∃ B ∈ G, B ∩ U = A ∩ U) :
    F.card ≤ G.card * 2^(P \ U).card := by
  classical
  choose C good trace using complete
  let f (A : F) : G × (P \ U).powerset :=
    (⟨C A.val A.property,good A.val A.property⟩,⟨A.val \ U,mem_powerset.mpr
      (fun a h => mem_sdiff.mpr ⟨contained _ A.property (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)⟩)
  have inj : Function.Injective f := by
    intro A B eq
    have e₁ := congrArg (fun w : G × (P \ U).powerset => (w.1:Finset α)) eq
    have e₂ := congrArg (fun w : G × (P \ U).powerset => (w.2:Finset α)) eq
    change C A.val A.property = C B.val B.property at e₁
    change A.val \ U = B.val \ U at e₂
    have e₃ : A.val ∩ U = B.val ∩ U := by rw [←trace _ A.property,←trace _ B.property,e₁]
    apply Subtype.ext
    ext a
    by_cases mem : a ∈ U
    · simpa [mem] using Finset.ext_iff.mp e₃ a
    · simpa [mem] using Finset.ext_iff.mp e₂ a
  simpa using Fintype.card_le_of_injective f inj

lemma exact_weight {N : ℕ} {x : ℚ} (l : ℝ) (A : Finset ℕ) (h : ∑ n ∈ A,(1:ℚ)/n=x) :
    ∏ n ∈ A, exp (-l*(N:ℝ)/n) = exp (-l*N*(x:ℝ)) := by
  have hs : ∑ n ∈ A,(1:ℝ)/n=(x:ℝ) := by
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using congrArg (fun r : ℚ => (r:ℝ)) h
  rw [←Real.exp_sum,←hs,mul_sum]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1.H3 := by
  intro entropy absorb x l hx calibration η hη
  have ep : 0 < η/2 := by positivity
  obtain ⟨d,hd,many⟩ := entropy x l hx calibration (η/2) ep
  filter_upwards [many,absorb x d hx hd (η/2) ep] with N hmany hreservoir
  classical
  let P := Icc 1 N
  let F := P.powerset.filter (fun A : Finset ℕ => (∑ n ∈ A,(1:ℚ)/n) ≤ x-d)
  let G := P.powerset.filter (fun A : Finset ℕ => (∑ n ∈ A,(1:ℚ)/n) = x)
  let Z := ∏ n ∈ P, (1+exp (-l*(N:ℝ)/n))
  let X := exp (-l*N*(x:ℝ))
  obtain ⟨U,hU,deleted,complete⟩ := hreservoir
  have traces (A : Finset ℕ) (mem : A ∈ F) : ∃ B ∈ G, B ∩ U = A ∩ U := by
    have small := (mem_filter.mp mem).2
    have tr : (∑ n ∈ A ∩ U,(1:ℚ)/n) ≤ x-d :=
      (sum_le_sum_of_subset_of_nonneg inter_subset_left (fun n _ _ => by positivity)).trans small
    obtain ⟨B,subB,e,s⟩ := complete (A ∩ U) inter_subset_right tr
    exact ⟨B,mem_filter.mpr ⟨mem_powerset.mpr subB,s⟩,e⟩
  have cnt := trace_count P U F G (fun A h => mem_powerset.mp (mem_filter.mp h).1) traces
  have cr : (F.card:ℝ) ≤ G.card * (2:ℝ)^(P \ U).card := by exact_mod_cast cnt
  let E := exp ((η/2)*(N:ℝ))
  have bound : (2:ℝ)^(P \ U).card ≤ E := calc
    _ ≤ (exp 1)^(P \ U).card := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp (1:ℝ)]
    _ = exp ((P \ U).card:ℝ) := by rw [←Real.exp_nat_mul]; simp
    _ ≤ E := Real.exp_le_exp.mpr deleted
  have Zpos : 0<Z := prod_pos (fun n _ => by positivity)
  have Xpos : 0<X := exp_pos _
  have countLoss : (F.card:ℝ)*X ≤ ((G.card:ℝ)*X)*E := calc
    _ ≤ ((G.card:ℝ)*E)*X := by gcongr; exact cr.trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _))
    _ = _ := by ring
  have weighted : (∑ A ∈ G, ∏ n ∈ A, exp (-l*(N:ℝ)/n)) = G.card*X := calc
    _ = ∑ _A ∈ G,X := by
      apply sum_congr rfl; intro A hA
      exact exact_weight l A (mem_filter.mp hA).2
    _ = _ := by simp
  change exp (-η*(N:ℝ)) ≤ (∑ A ∈ G, ∏ n ∈ A, exp (-l*(N:ℝ)/n))/Z
  rw [weighted,le_div_iff₀ Zpos]
  apply le_of_mul_le_mul_right _ (show 0<E from exp_pos _)
  have id : exp (-η*(N:ℝ))*Z*E=exp (-(η/2)*N)*Z := by
    dsimp [E]
    rw [mul_right_comm,←exp_add]
    congr 2
    ring
  rw [id]
  exact hmany.trans countLoss

end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1
