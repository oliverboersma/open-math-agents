import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1
import Mathlib

/-! Conlon, Fox, He, Mubayi, Pham, Suk and Verstraëte, A question of Erdős
and Graham on Egyptian fractions, Section 4. The prime-power corrections
leave an integer multiple of a fixed reciprocal. For a fixed target x,
only finitely many such integers occur, so all their representations fit
in the reserved progression once N is large enough. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1

open Finset Filter
open scoped Topology

/-- Prime-power cleaning with the multiples of K reserved. The correction
only has to control the denominator of the positive residual. -/
def H1 : Prop := ∀ (x d : ℚ), 0 < x → 0 < d → ∀ δ > (0:ℝ),
  ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
    ∃ U ⊆ Icc 1 N, (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧ (∀ u ∈ U, ¬ K ∣ u) ∧
      ∀ A ⊆ U, (∑ n ∈ A, (1:ℚ)/n) ≤ x-d → ∃ P ⊆ Icc 1 N,
        Disjoint P U ∧ (∀ p ∈ P, ¬ K ∣ p) ∧
        ∃ j : ℕ, 0 < j ∧ (j:ℚ)/K = x-(∑ n ∈ A, (1:ℚ)/n)-(∑ n ∈ P, (1:ℚ)/n)

/-- Each positive integer has a finite representation by distinct unit fractions. -/
def H2 : Prop := ∀ j : ℕ, 0 < j → ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧
  (∑ n ∈ S, (1:ℚ)/n) = j

lemma scale_set (S : Finset ℕ) {K : ℕ} (hk : 0 < K) :
    (∑ n ∈ S.image (K*·), (1:ℚ)/n) = (∑ n ∈ S, (1:ℚ)/n)/K := by
  rw [sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hk hab),sum_div]
  apply sum_congr rfl
  intro n hn
  push_cast
  ring

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1.H2 := by
  classical
  intro clean integers x d hx hd δ hδ
  obtain ⟨K,hk,hn⟩ := clean x d hx hd δ hδ
  have allj (j : ℕ) : ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ (∑ n ∈ S, (1:ℚ)/n) = j := by
    rcases j.eq_zero_or_pos with rfl|hj
    · exact ⟨∅,by simp,by simp⟩
    · exact integers j hj
  choose S pos total using allj
  let J := ⌈x*K⌉₊
  let cutoff := (range (J+1)).sup (fun j => (S j).sup id)
  filter_upwards [hn,eventually_ge_atTop (K*cutoff)] with N hclean hN
  obtain ⟨U,hU,small,skip,correct⟩ := hclean
  refine ⟨U,hU,small,?_⟩
  intro A hA low
  obtain ⟨P,hP,apart,avoid,j,hj,eq⟩ := correct A hA low
  have hK : (0:ℚ)<K := by exact_mod_cast hk
  have jle : j ≤ J := by
    have ha : 0 ≤ ∑ n ∈ A, (1:ℚ)/n := by positivity
    have hp : 0 ≤ ∑ n ∈ P, (1:ℚ)/n := by positivity
    apply (Nat.cast_le (α := ℚ)).mp
    apply le_trans _ (Nat.le_ceil (x*K))
    exact (div_le_iff₀ hK).mp (by linarith only [eq,ha,hp])
  let V := (S j).image (K*·)
  have bound : V ⊆ Icc 1 N := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    have H : b ≤ cutoff := (Finset.le_sup (f := id) hb).trans
      (Finset.le_sup (f := fun i => (S i).sup id) (mem_range.mpr (by omega : j < J+1)))
    exact mem_Icc.mpr ⟨Nat.mul_pos hk (pos j b hb),(Nat.mul_le_mul_left K H).trans hN⟩
  have mult : ∀ v ∈ V, K ∣ v := by
    intro v hv
    obtain ⟨b,_,rfl⟩ := mem_image.mp hv
    exact dvd_mul_right K b
  have dPU : Disjoint A P := (apart.mono_right hA).symm
  have dV : Disjoint (A ∪ P) V := by
    apply Finset.disjoint_left.mpr
    intro v hv hV
    rcases mem_union.mp hv with a|p
    · exact skip v (hA a) (mult v hV)
    · exact avoid v p (mult v hV)
  refine ⟨(A ∪ P) ∪ V, union_subset (union_subset (hA.trans hU) hP) bound,?_,?_⟩
  · ext b
    simp only [mem_inter,mem_union]
    constructor
    · rintro ⟨(hb|hb)|hb,hu⟩
      · exact hb
      · exact (Finset.disjoint_left.mp apart hb hu).elim
      · exact (skip b hu (mult b hb)).elim
    · exact fun hb => ⟨Or.inl (Or.inl hb),hA hb⟩
  · rw [sum_union dV,sum_union dPU,show (∑ n ∈ V, (1:ℚ)/n) = (j:ℚ)/K by
        rw [scale_set _ hk,total]]
    linarith only [eq]

end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1
