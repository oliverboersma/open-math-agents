import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1

 /-! Conlon, Fox, He, Mubayi, Pham, Suk and Verstraëte,
A question of Erdős and Graham on Egyptian fractions, sections 3 and 4.
The dense powersmooth set avoids the correction denominators. For each
prime power one can choose a small subset of its reserved denominators
to remove that prime power from the denominator of the current rational.
The descent, its sum of costs, disjointness, and positivity are proved here. -/
namespace OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1
open Finset Filter
open scoped Classical

def H1 : Prop := ∀ (x : ℚ), 0 < x → ∀ δ > (0:ℝ),
  ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ ∀ L₀ : ℕ, ∃ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∀ᶠ N : ℕ in atTop, ∃ B ≥ L, ∃ U ⊆ Icc 1 N,
      (((Icc 1 N) \ U).card:ℝ) ≤ δ*N ∧ x.den ∣ J B ∧
      (∀ u ∈ U, u ∣ J B ∧ ¬ K ∣ u) ∧
      (∀ i ∈ Ioc L B, R i ⊆ Icc 1 N ∧ Disjoint U (R i)) ∧
      (∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B, i < j → Disjoint (R i) (R j))

def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ d : ℚ, 0 < d →
  ∃ L₀ : ℕ, ∀ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∃ cost : ℕ → ℚ, (∀ B, ∑ i ∈ Ioc L B, cost i < d) ∧
      ∀ i : ℕ, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
        (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n

lemma descend (J : ℕ → ℕ) (R : ℕ → Finset ℕ) (cost : ℕ → ℚ)
    (L : ℕ) (step : ∀ i, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n)
    (B : ℕ) (hB : L ≤ B) (apart : ∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B,
      i < j → Disjoint (R i) (R j)) (z : ℤ) :
    ∃ P ⊆ (Ioc L B).biUnion R, (∑ n ∈ P, (1:ℚ)/n) ≤ ∑ i ∈ Ioc L B, cost i ∧
    ∃ a : ℤ, (a:ℚ)/J L = (z:ℚ)/J B - ∑ n ∈ P, (1:ℚ)/n := by
  induction B,hB using Nat.le_induction generalizing z with
  | base => exact ⟨∅,empty_subset _,by simp,z,by simp⟩
  | succ b hb ih =>
    have last : b+1 ∈ Ioc L (b+1) := mem_Ioc.mpr ⟨by omega,le_rfl⟩
    have sub : Ioc L b ⊆ Ioc L (b+1) := fun i hi => mem_Ioc.mpr
      ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.le_succ _)⟩
    obtain ⟨V,hV,hv,a,ha⟩ := step (b+1) (by omega) z
    obtain ⟨P,hP,hp,j,hj⟩ := ih (fun i hi k hk => apart i (sub hi) k (sub hk)) a
    have dj : Disjoint P V := by
      apply disjoint_left.mpr
      intro n hn hnV
      obtain ⟨i,hi,hnR⟩ := mem_biUnion.mp (hP hn)
      exact disjoint_left.mp (apart i (sub hi) _ last (Nat.lt_succ_of_le (mem_Ioc.mp hi).2)) hnR (hV hnV)
    have eq : Ioc L (b+1) = insert (b+1) (Ioc L b) := by
      ext i; simp only [mem_Ioc,mem_insert]; omega
    refine ⟨P∪V,union_subset (fun n hn => ?_) (fun n hn => mem_biUnion.mpr ⟨_,last,hV hn⟩),?_,j,?_⟩
    · obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
      exact mem_biUnion.mpr ⟨_,sub hi,hh⟩
    · rw [sum_union dj,eq,sum_insert (by simp)]
      linarith
    · simp only [Nat.add_sub_cancel] at ha
      rw [sum_union dj,hj,ha]
      ring

lemma grid {T : ℕ} (hT : T ≠ 0) (x : ℚ) (hx : x.den ∣ T)
    (A : Finset ℕ) (hA : ∀ n ∈ A, n∣T) :
    ∃ z : ℤ, (z:ℚ)/T = x-∑ n ∈ A, (1:ℚ)/n := by
  have denom (n : ℕ) (hn : n∣T) : ((T/n:ℕ):ℚ)*(n:ℚ) = T := by
    exact_mod_cast Nat.div_mul_cancel hn
  have rep (n : ℕ) (hn : n∣T) : ((T/n:ℕ):ℚ)/T = 1/n := by
    have nz : n ≠ 0 := fun e => hT (by simpa [e] using hn)
    apply (div_eq_div_iff (by exact_mod_cast hT) (by exact_mod_cast nz)).mpr
    simpa using denom n hn
  refine ⟨x.num*Int.ofNat (T/x.den) - ∑ n ∈ A, (T/n:ℕ),?_⟩
  push_cast
  rw [sub_div,sum_div]
  congr 1
  · conv_rhs => rw [← Rat.num_div_den x]
    apply (div_eq_div_iff (by exact_mod_cast hT) (by exact_mod_cast x.den_nz)).mpr
    rw [mul_assoc,Int.ofNat_eq_natCast,Int.cast_natCast,denom _ hx]
  · exact sum_congr rfl (fun n hn => rep _ (hA _ hn))

theorem main : H1 → H2 → OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H1 := by
  intro dense cancel x d hx hd δ hδ
  obtain ⟨ε,hε,he,dense⟩ := dense x hx δ hδ
  obtain ⟨L₀,threshold⟩ := cancel ε hε he d hd
  obtain ⟨L,hL,supply⟩ := dense L₀
  let J (i : ℕ) := (Icc 1 i).lcm id
  let K := J L
  let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
  have pos (i : ℕ) : 0 < J i := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun n hn => Nat.ne_of_gt (mem_Icc.mp hn).1))
  obtain ⟨cost,small,step⟩ := threshold L hL
  refine ⟨K,pos L,?_⟩
  filter_upwards [supply] with N data
  obtain ⟨B,hB,U,hU,size,den,divs,space,apart⟩ := data
  refine ⟨U,hU,size,(fun n hn => (divs n hn).2),?_⟩
  intro A hA low
  obtain ⟨z,hz⟩ := grid (pos B).ne' x den A (fun n hn => (divs n (hA hn)).1)
  obtain ⟨P,hP,budget,a,ha⟩ := descend J R cost L step B hB apart z
  have location {n : ℕ} (hn : n ∈ P) : n ∈ Icc 1 N ∧ n ∉ U ∧ ¬K∣n := by
    obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
    exact ⟨(space i hi).1 hh,fun h => disjoint_left.mp (space i hi).2 h hh,(mem_filter.mp hh).2.2.2.2.2.2⟩
  have hpos : (0:ℚ) < (a:ℚ)/K := by
    rw [ha,hz]
    linarith [small B]
  have apos : 0 < a := by
    exact_mod_cast (div_pos_iff_of_pos_right (show (0:ℚ)<K by exact_mod_cast pos L)).mp hpos
  refine ⟨P,(fun n hn => (location hn).1),disjoint_left.mpr (by intro n hn h; exact (location hn).2.1 h),
    (fun n hn => (location hn).2.2),a.toNat,by omega,?_⟩
  rw [show (a.toNat:ℚ) = a by exact_mod_cast Int.toNat_of_nonneg apos.le,ha,hz]
end OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1
