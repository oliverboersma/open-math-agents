import FormalConjectures.ErdosProblems.«10»
import Mathlib

/- Gallagher's moment argument on odd integers. A finite distribution on
short sums of powers of two smooths the prime logarithm weight. The prime
number theorem gives its first moment uniformly under these shifts. The
remaining analytic input bounds its second moment. Variance and a parity
transfer then give the lower density among all integers. -/
namespace OMA.R_Erdos10_erdos_10_variants_gallagher_R1

open Finset Filter Erdos10
open scoped Classical Topology

/-- The prime number theorem, omitting the single even prime. -/
def H1 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop, (1-δ)*N ≤ ∑ j ∈ range N, v j

/-- Gallagher's second-moment estimate for a prime smoothed by powers of two.
The weights allow the multiplicities of ordered exponent tuples. -/
def H2 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum
  ∀ δ : ℝ, 0<δ → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
    ∃ Q : Finset (Multiset ℕ), ∃ a : Multiset ℕ → ℝ,
      (∀ t ∈ Q, 0 ≤ a t ∧ t.card ≤ k ∧ (s t : ℝ) ≤ δ*N) ∧
      (∑ t ∈ Q, a t)=1 ∧
      (∑ j ∈ range N, (∑ t ∈ Q, a t * (if s t ≤ j then v (j-s t) else 0))^2) ≤ (1+δ)*N

lemma shiftedSum (v : ℕ → ℝ) {N u : ℕ} (hu : u ≤ N) :
    (∑ j ∈ range N, (if u≤j then v (j-u) else 0)) = ∑ j ∈ range (N-u), v j := by
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [sum_range_add]
  have hz : (∑ j ∈ range u, if u≤j then v (j-u) else 0)=0 := by
    apply sum_eq_zero
    intro j hj
    simp [not_le.mpr (mem_range.mp hj)]
  simp [hz]

lemma momentSupport {w : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (low : (1-2*δ)*N ≤ ∑ j ∈ range N, w j)
    (high : (∑ j ∈ range N,(w j)^2) ≤ (1+δ)*N) :
    (1-5*δ)*N ≤ (((range N).filter (fun j => w j≠0)).card:ℝ) := by
  have v : (∑ j ∈ range N, (w j-1)^2) =
      (∑ j ∈ range N,(w j)^2) - 2*(∑ j ∈ range N,w j) + N := by
    simp_rw [show ∀ x : ℝ, (x-1)^2 = x^2-2*x+1 by intro x;ring]
    simp [sum_add_distrib,sum_sub_distrib,mul_sum]
  have small : (((range N).filter (fun j => w j=0)).card : ℝ) ≤ ∑ j ∈ range N,(w j-1)^2 := by
    calc
      _ = ∑ j ∈ (range N).filter (fun j => w j=0), (w j-1)^2 := by
        symm
        calc
          _ = ∑ j ∈ (range N).filter (fun j => w j=0), (1:ℝ) := by
            apply sum_congr rfl
            intro j hj
            simp [(mem_filter.mp hj).2]
          _ = _ := by simp
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun j _ _ => sq_nonneg _)
  have split := card_filter_add_card_filter_not (s:=range N) (p:=fun j => w j=0)
  simp only [card_range] at split
  have rr := congrArg (fun m : ℕ => (m:ℝ)) split
  push_cast at rr
  linarith only [low,high,v,small,rr]

lemma shortShift {k j : ℕ} (t : Multiset ℕ) (hc : t.card ≤ k) (p : ℕ)
    (hp : p.Prime) (eq : p + 2*(t.map (fun i : ℕ => 2^i)).sum = 2*j+1) :
    ∀ b : ℕ, b<2 → 2*j+1+b ∈ sumPrimeAndTwoPows (k+1) := by
  let u := t.map (·+1)
  have e : (u.map (fun i : ℕ => 2^i)).sum = 2*(t.map (fun i : ℕ => 2^i)).sum := by
    suffices h : ∀ T : Multiset ℕ, ((T.map (·+1)).map (fun i : ℕ => 2^i)).sum =
        2*(T.map (fun i : ℕ => 2^i)).sum by exact h t
    intro T
    induction T using Multiset.induction_on with
    | empty => simp
    | cons x T ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,pow_succ,ih]
      ring
  intro b hb
  have hc' : u.card ≤ k := by simpa [u] using hc
  rcases (show b=0 ∨ b=1 by omega) with rfl | rfl
  · exact ⟨p,u,hp,by omega,by simp [e,eq]⟩
  · exact ⟨p,0::ₘu,hp,by simpa using Nat.succ_le_succ hc',by simp [e] at *;omega⟩

theorem main : H1 → H2 → type_of% @Erdos10.erdos_10.variants.gallagher := by
  classical
  intro primeMean meanSquare ε hε
  let δ : ℝ := min (ε/16) (1/16)
  have d0 : 0<δ := lt_min (by positivity) (by norm_num)
  have d1 : δ≤1/16 := min_le_right .. 
  have de : δ≤ε/16 := min_le_left ..
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum
  obtain ⟨k,second⟩ := meanSquare δ d0
  obtain ⟨B,hB⟩ := eventually_atTop.mp (primeMean δ d0)
  let A := sumPrimeAndTwoPows (k+1)
  have bulk : ∀ᶠ m : ℕ in atTop,
      ∃ G ⊆ range m, (1-5*δ)*m ≤ (G.card:ℝ) ∧
      ∀ j ∈ G, ∀ b : ℕ, b<2 → 2*j+1+b ∈ A := by
    filter_upwards [second,eventually_ge_atTop (2*B)] with m hm hmB
    obtain ⟨Q,a,weights,total,h2⟩ := hm
    let w := fun j : ℕ => ∑ t ∈ Q,a t*(if s t≤j then v (j-s t) else 0)
    have part (t : Multiset ℕ) (ht : t ∈ Q) :
        (1-2*δ)*m ≤ ∑ j ∈ range m,(if s t≤j then v (j-s t) else 0) := by
      obtain ⟨_,_,hs⟩ := weights t ht
      change (s t:ℝ) ≤ δ*m at hs
      have htwice : 2 * s t ≤ m := by
        exact_mod_cast (show 2*(s t:ℝ) ≤ m by
          nlinarith only [hs,mul_le_mul_of_nonneg_right d1 (Nat.cast_nonneg m)])
      rw [shiftedSum v (by omega)]
      have le := hB (m-s t) (by omega)
      change (1-δ)*((m-s t:ℕ):ℝ) ≤ ∑ j ∈ range (m-s t),v j at le
      rw [Nat.cast_sub (by omega)] at le
      nlinarith only [le,hs,mul_nonneg d0.le (Nat.cast_nonneg (s t))]
    have low : (1-2*δ)*m ≤ ∑ j ∈ range m,w j := by
      calc
        _ = ∑ t ∈ Q,a t*((1-2*δ)*m) := by rw [←sum_mul,total,one_mul]
        _ ≤ ∑ t ∈ Q,a t*∑ j ∈ range m,(if s t≤j then v (j-s t) else 0) :=
          sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (part t ht) (weights t ht).1)
        _ = _ := by simp only [w,mul_sum]; rw [sum_comm]
    refine ⟨(range m).filter (fun j => w j≠0),filter_subset ..,momentSupport low h2,?_⟩
    intro j hj
    have nz := (mem_filter.mp hj).2
    obtain ⟨t,ht,ht'⟩ := exists_ne_zero_of_sum_ne_zero nz
    have nzt := (mul_ne_zero_iff.mp ht').2
    split_ifs at nzt with hsj
    · have pp : (2*(j-s t)+1).Prime := by
        by_contra hn
        simp [v,hn] at nzt
      apply shortShift t (weights t ht).2.1 _ pp
      change 2*(j-s t)+1+2*s t=2*j+1
      omega
    · exact (nzt rfl).elim
  refine ⟨k+1,?_⟩
  change 1-ε ≤ atTop.liminf (fun n : ℕ => A.partialDensity Set.univ n)
  apply le_liminf_of_le (IsBoundedUnder.isCoboundedUnder_ge (u:=fun n : ℕ => A.partialDensity Set.univ n)
    ⟨1,by simpa only [eventually_map] using (Eventually.of_forall (fun n : ℕ => Set.partialDensity_le_one A Set.univ n) : ∀ᶠ n : ℕ in atTop, A.partialDensity Set.univ n ≤ 1)⟩)
  obtain ⟨B',hb'⟩ := eventually_atTop.mp bulk
  obtain ⟨D,hD⟩ := exists_nat_ge (4/ε)
  filter_upwards [eventually_ge_atTop (2*B'+D+4)] with n hn
  let m := (n-1)/2
  obtain ⟨G,hG,good,hits⟩ := hb' m (by dsimp [m]; omega)
  let T := (range n).filter (·∈A)
  have inj : (G ×ˢ range 2).card ≤ T.card := by
    apply card_le_card_of_injOn (fun z : ℕ × ℕ => 2*z.1+1+z.2)
    · rintro ⟨j,b⟩ hz
      obtain ⟨hj,hb⟩ := mem_product.mp hz
      have jm := mem_range.mp (hG hj)
      have b2 := mem_range.mp hb
      exact mem_filter.mpr ⟨mem_range.mpr (by change 2*j+1+b<n; dsimp [m] at jm;omega),hits j hj b b2⟩
    · rintro ⟨i,a⟩ ha ⟨j,b⟩ hb he
      have a2 := mem_range.mp (mem_product.mp ha).2
      have b2 := mem_range.mp (mem_product.mp hb).2
      dsimp at he
      congr 1 <;> omega
  simp only [card_product,card_range] at inj
  have sub : n ≤ 2*m+2 := by dsimp [m];omega
  have sub' : (n:ℝ) ≤ 2*(m:ℝ)+2 := by exact_mod_cast sub
  have mn : (m:ℝ) ≤ n/2 := by
    rw [le_div_iff₀ (by norm_num)];exact_mod_cast (show m*2≤n by dsimp [m];omega)
  have nn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have epsN : 4 ≤ ε*(n:ℝ) := by
    have hDn : (D:ℝ) ≤ n := by exact_mod_cast (show D≤n by omega)
    have hh := (div_le_iff₀ hε).mp (hD.trans hDn)
    linarith
  have seteq : A ∩ Set.Iio n = (T:Set ℕ) := by ext j;simp [T,and_comm]
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,seteq,Set.ncard_coe_finset,Nat.ncard_Iio]
  rw [le_div_iff₀ nn]
  have inj' : (G.card:ℝ)*2 ≤ T.card := by exact_mod_cast inj
  nlinarith only [inj',good,sub',epsN,mul_le_mul_of_nonneg_left mn d0.le,
    mul_le_mul_of_nonneg_right de nn.le]

end OMA.R_Erdos10_erdos_10_variants_gallagher_R1

