import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1
import Mathlib

/-! The deletion masks of the defect strings split according to whether they retain
the extra one. Embeddings in a run of alternating pairs are counted by a single
binomial coefficient. The remaining analytic estimate is the weighted second moment
of the difference of the two binomial sums in Chase, Section 3. -/
namespace OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1
open Finset Real Filter

private theorem distance (b u v n:ℕ) :
    (sqrt (((b+u:ℕ):ℝ)/(2:ℝ)^n)-sqrt (((b+v:ℕ):ℝ)/(2:ℝ)^n))^2 ≤
      ((u:ℝ)-v)^2/((2:ℝ)^n*(max 1 b:ℕ)) := by
  let s := sqrt (((b+u:ℕ):ℝ)/(2:ℝ)^n)
  let t := sqrt (((b+v:ℕ):ℝ)/(2:ℝ)^n)
  have h : 0<(2:ℝ)^n := by positivity
  have es : s^2=((b+u:ℕ):ℝ)/(2:ℝ)^n := sq_sqrt (by positivity)
  have et : t^2=((b+v:ℕ):ℝ)/(2:ℝ)^n := sq_sqrt (by positivity)
  have st : 0 ≤ s*t := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  change (s-t)^2≤_
  by_cases empty : b+u=0 ∧ b+v=0
  · obtain ⟨rfl,rfl,rfl⟩ : b=0 ∧ u=0 ∧ v=0 := by omega
    simp [s,t]
  have hi : max 1 b ≤ (b+u)+(b+v) := by omega
  have z : ((max 1 b:ℕ):ℝ)/(2:ℝ)^n ≤ (s+t)^2 := by
    have hr : (((max 1 b:ℕ):ℝ))/(2:ℝ)^n ≤ (((b+u)+(b+v):ℕ):ℝ)/(2:ℝ)^n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hi) h.le
    rw [Nat.cast_add,add_div] at hr
    nlinarith only [es,et,hr,st]
  have eq : (s-t)*(s+t)=((u:ℝ)-v)/(2:ℝ)^n := by
    calc _ = s^2-t^2 := by ring
         _ = _ := by rw [es,et,←sub_div]; push_cast; ring
  have hh := mul_le_mul_of_nonneg_left z (sq_nonneg (s-t))
  rw [←mul_pow,eq,div_pow] at hh
  have pos : (0:ℝ)<(max 1 b:ℕ) := by exact_mod_cast (by omega : 0 < max 1 b)
  apply (le_div_iff₀ (mul_pos h pos)).mpr
  calc _ = ((s-t)^2 * (((max 1 b:ℕ):ℝ)/(2:ℝ)^n))*((2:ℝ)^n)^2 := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_right hh (sq_nonneg ((2:ℝ)^n))
       _ = _ := by field_simp

def H1 : Prop := ∀ n : ℕ, n%4=3 →
  let k := n/4
  let W (b:ℕ) (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
  let F (a:ℕ) (v:List Bool) := (a+(v.zip v.tail).count (false,true)).choose v.length
  let B (w:List Bool) := F (2*k+1) w
  let D (b:ℕ) (w:List Bool) := ∑ j∈range w.length,if w[j]?=some true then
    F b (w.take j)*F (2*k+1-b) (w.drop (j+1)) else 0
  ∀ b, b≤2*k+1 → ∀ w:List Bool,
    (univ.filter (fun S:Finset (Fin n) => Green92.trace (W b) S=w)).card=B w+D b w

def H2 : Prop := ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop,n%4=3 →
  let k := n/4
  let F (a:ℕ) (v:List Bool) := (a+(v.zip v.tail).count (false,true)).choose v.length
  let B (w:List Bool) := F (2*k+1) w
  let D (b:ℕ) (w:List Bool) := ∑ j∈range w.length,if w[j]?=some true then
    F b (w.take j)*F (2*k+1-b) (w.drop (j+1)) else 0
  let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m→Bool)).image List.ofFn
  let E (w:List Bool) := |(w.length:ℝ)-2*k|≤ sqrt k*log k ∧
    |(((w.zip w.tail).count (false,true):ℕ):ℝ)-2*k/3|≤ sqrt k*log k
  ∑ w∈U.filter E, ((D k w:ℝ)-D (k+1) w)^2 / ((2:ℝ)^n * (max 1 (B w):ℕ)) ≤
    C*(log n)^7/(n:ℝ)^(3/2:ℝ)

theorem main : H1 → H2 → OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1.H2 := by
  classical
  rintro emb ⟨C,cp,estimate⟩
  refine ⟨C,cp,?_⟩
  filter_upwards [estimate] with n est
  intro hm k W p T E
  specialize est hm
  let F (a:ℕ) (v:List Bool) := (a+(v.zip v.tail).count (false,true)).choose v.length
  let B (w:List Bool) := F (2*k+1) w
  let D (b:ℕ) (w:List Bool) := ∑ j∈range w.length,if w[j]?=some true then
    F b (w.take j)*F (2*k+1-b) (w.drop (j+1)) else 0
  let U := (range (n+1)).biUnion fun m => (univ : Finset (Fin m→Bool)).image List.ofFn
  change ∑ w∈U.filter E, ((D k w:ℝ)-D (k+1) w)^2 / ((2:ℝ)^n*(max 1 (B w):ℕ)) ≤ _ at est
  have count (b:ℕ) (hb:b≤2*k+1) (w:List Bool) :
      p b w=(((B w+D b w:ℕ):ℝ)/(2:ℝ)^n) := by
    dsimp only [p]
    rw [emb n hm b hb w]
    simp [B,D,F,k]
  have incl : T.filter E ⊆ U.filter E := by
    intro w hw
    obtain ⟨ht,he⟩ := mem_filter.mp hw
    apply mem_filter.mpr ⟨?_,he⟩
    have length_bound (b:ℕ) (S:Finset (Fin n)) : (Green92.trace (W b) S).length≤n := by
      simp only [Green92.trace,List.length_map]
      exact (List.length_filter_le ..).trans (by simp)
    have len : w.length≤n := by
      rcases mem_union.mp ht with x|x <;> obtain ⟨S,_,rfl⟩ := mem_image.mp x <;> apply length_bound
    exact mem_biUnion.mpr ⟨w.length,mem_range.mpr (by omega),
      mem_image.mpr ⟨fun i:Fin w.length => w[i.val],mem_univ _,by simp⟩⟩
  refine le_trans (sum_le_sum (g:=fun w => ((D k w:ℝ)-D (k+1) w)^2 /
    ((2:ℝ)^n*(max 1 (B w):ℕ))) (fun w _ => ?_)) ?_
  · rw [count k (by omega),count (k+1) (by omega)]
    exact distance _ _ _ _
  · exact (sum_le_sum_of_subset_of_nonneg incl (fun _ _ _ => by positivity)).trans est

end OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1
