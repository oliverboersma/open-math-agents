import FormalConjectures.ErdosProblems.«950»
import Mathlib

/-! The prime number theorem supplies the first moment. For the second moment,
partial fractions bound the correlation of two reciprocal kernels a distance d
apart by H_d / d. Compare O. Gorodetsky, MathOverflow 508491. Cauchy–Schwarz
gives the matching lower bound from the first moment alone, so only an upper
estimate for the off-diagonal prime pairs is needed. -/

namespace OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1

open Finset Filter Real Asymptotics Erdos950
open scoped Topology

/-- The prime number theorem at a fixed proportion of the endpoint. -/
def H1 : Prop := ∀ a : ℝ, 0 < a → a ≤ 1 → Tendsto (fun N : ℕ =>
  (((range N).filter fun p : ℕ => p.Prime ∧ (p:ℝ) ≤ a*N).card:ℝ) * log N / N) atTop (𝓝 a)

/-- One-sided harmonic pair estimate, counting both orders. -/
def H2 : Prop :=
  let P (N : ℕ) := (range N).filter Nat.Prime
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (∑ p ∈ P N, ∑ q ∈ (P N).erase p, (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q) ≤ (1+ε)*N

lemma kernel_rows (a : ℕ → ℕ → ℝ)
    (ha : ∀ p n, a p n = if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0) (N p : ℕ) (hp : p < N) :
    (∑ n ∈ range N, a p n) = (harmonic (N-(p+1)) : ℝ) := by
  let m := N-(p+1)
  have split : N = (p+1)+m := by dsimp [m]; omega
  rw [split,sum_range_add]
  have zero : ∑ n ∈ range (p+1), a p n = 0 := sum_eq_zero fun n hn => by
    rw [ha,if_neg (by have := mem_range.mp hn; omega)]
  rw [zero,zero_add,show p+1+m-(p+1)=m by omega]
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  exact sum_congr rfl fun i _ => by rw [ha,if_pos (by omega),show p+1+i-p=i+1 by omega]

lemma kernel_diag (a : ℕ → ℕ → ℝ)
    (ha : ∀ p n, a p n = if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0) (N p : ℕ) (hp : p < N) :
    ∑ n ∈ range N, a p n * a p n ≤ ∑' j : ℕ, ((j:ℝ)^2)⁻¹ := by
  let m := N-(p+1)
  rw [show N = p+1+m by dsimp [m]; omega,sum_range_add]
  have zero : ∑ n ∈ range (p+1), a p n * a p n = 0 := sum_eq_zero fun n hn => by
    simp [ha,show ¬ p<n by have := mem_range.mp hn; omega]
  rw [zero,zero_add]
  calc
    _ = ∑ i ∈ range m, ((((i+1:ℕ):ℝ)^2)⁻¹) := sum_congr rfl fun i _ => by
      rw [ha,if_pos (by omega),show p+1+i-p=i+1 by omega,sq,mul_inv_rev]
    _ = ∑ i ∈ range (m+1), ((i:ℝ)^2)⁻¹ := by rw [sum_range_succ']; simp
    _ ≤ _ := (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).sum_le_tsum _ fun _ _ => by positivity

lemma kernel_cross (a : ℕ → ℕ → ℝ)
    (ha : ∀ p n, a p n = if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0) (N p q : ℕ) (hpq : p<q) (hq : q<N) :
    ∑ n ∈ range N, a p n * a q n ≤ (harmonic (q-p):ℝ) / (q-p:ℕ) := by
  let d := q-p
  let m := N-(q+1)
  let u (j : ℕ) : ℝ := ((j+1:ℕ):ℝ)⁻¹
  have dp : 0 < d := by dsimp [d]; omega
  have dr : (0:ℝ) < d := by exact_mod_cast dp
  have decompose (j : ℕ) : a p (q+1+j)*a q (q+1+j) = (u j-u (d+j))/d := by
    have hp : p<q+1+j := by omega
    have hq' : q<q+1+j := by omega
    simp only [ha,if_pos hp,if_pos hq',u,show q+1+j-p = d+j+1 by dsimp [d]; omega,
      show q+1+j-q = j+1 by omega,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  have zero : ∑ n ∈ range (q+1), a p n * a q n = 0 := sum_eq_zero fun n hn => by
    rw [ha q n,if_neg (by have := mem_range.mp hn; omega),mul_zero]
  rw [show N = q+1+m by dsimp [m]; omega,sum_range_add,zero,zero_add]
  simp_rw [decompose]
  rw [← sum_div,sum_sub_distrib]
  change _ ≤ (harmonic d:ℝ) / d
  apply div_le_div_of_nonneg_right _ dr.le
  have rearrange := sum_range_add u m d
  rw [Nat.add_comm m d,sum_range_add] at rearrange
  have nonneg : 0 ≤ ∑ j ∈ range d, u (m+j) := sum_nonneg fun _ _ => by dsimp [u]; positivity
  have H : (harmonic d:ℝ) = ∑ j ∈ range d, u j := by simp [harmonic,u]
  rw [H]
  linarith

lemma expand_kernel (a : ℕ → ℕ → ℝ)
    (ha : ∀ p n, a p n = if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0) (N n : ℕ) (hn : n < N) :
    f n = ∑ p ∈ (range N).filter Nat.Prime, a p n := by
  have seteq : ((range N).filter Nat.Prime).filter (· < n) = (range n).filter Nat.Prime := by
    ext p
    simp only [mem_filter,mem_range]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hn,h.2⟩,h.1⟩⟩
  unfold f
  simp_rw [← Nat.prime_iff]
  rw [← seteq,sum_filter]
  apply sum_congr rfl
  intro p _
  rw [ha]
  split_ifs with h
  · rw [Nat.cast_sub h.le,one_div]
  · rfl

lemma first_moment (pnt : H1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f n) / N) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => ((((range N).filter Nat.Prime).card : ℝ) / N)) atTop (𝓝 0) := by
  let P (N : ℕ) := (range N).filter Nat.Prime
  let Q (a : ℝ) (N : ℕ) := (range N).filter fun p : ℕ => p.Prime ∧ (p:ℝ) ≤ a*N
  let a (p n : ℕ) : ℝ := if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0
  have hc (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1) :
      Tendsto (fun N : ℕ => ((Q b N).card:ℝ) / N) atTop (𝓝 0) := by
    have h := (pnt b hb hb').div_atTop (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have lp : 0 < log N := log_pos (by exact_mod_cast (show 1 < N by omega))
    change _ * log N / N / log N = _
    field_simp
    rfl
  have qone (N : ℕ) : Q 1 N = P N := by
    ext p
    simp only [P,Q,mem_filter,mem_range,one_mul]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,by exact_mod_cast h.1.le⟩⟩
  have full := pnt 1 zero_lt_one le_rfl
  change Tendsto (fun N : ℕ => (Q 1 N).card * log N / N) atTop (𝓝 1) at full
  simp_rw [qone] at full
  have zero := hc 1 zero_lt_one le_rfl
  simp_rw [qone] at zero
  have exact_sum (N : ℕ) :
      ∑ n ∈ range N, f n = ∑ p ∈ P N, (harmonic (N-(p+1)) : ℝ) := by
    rw [sum_congr rfl (fun n hn => expand_kernel a (fun _ _ => rfl) N n (mem_range.mp hn)),sum_comm]
    exact sum_congr rfl fun p hp => kernel_rows a (fun _ _ => rfl) N p (mem_range.mp (mem_filter.mp hp).1)
  refine ⟨tendsto_order.mpr ⟨?_,?_⟩,zero⟩
  · intro b hb
    let t := (max b 0 + 1)/2
    have ht : 0<t := by dsimp [t]; linarith [le_max_right b 0]
    have ht' : t<1 := by dsimp [t]; linarith [max_lt hb (by norm_num : (0:ℝ)<1)]
    have hbt : b<t := by dsimp [t]; linarith [le_max_left b 0]
    have hlim := (pnt t ht ht'.le).add ((hc t ht ht'.le).mul_const (log (1-t)))
    simp only [zero_mul,add_zero] at hlim
    filter_upwards [(tendsto_order.mp hlim).1 b hbt,eventually_gt_atTop 0] with N hnear hN
    have pos : (0:ℝ) < N := by exact_mod_cast hN
    have sub : Q t N ⊆ P N := fun p hp =>
      mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
    rw [exact_sum]
    apply lt_of_lt_of_le hnear
    change (Q t N).card * log N / N + ((Q t N).card / (N:ℝ)) * log (1-t) ≤ _
    rw [show (Q t N).card * log N / N + ((Q t N).card / (N:ℝ)) * log (1-t) =
      ((Q t N).card * (log N+log (1-t))) / N by ring]
    apply div_le_div_of_nonneg_right _ pos.le
    calc
      _ = ∑ _p ∈ Q t N, (log N + log (1-t)) := by simp [mul_add]
      _ ≤ ∑ p ∈ Q t N, (harmonic (N-(p+1)) : ℝ) := by
        apply sum_le_sum
        intro p hp
        have pp := (mem_filter.mp hp).2.2
        have pN := mem_range.mp (mem_filter.mp hp).1
        have harg : (0:ℝ) < 1-t := by linarith
        rw [← log_mul pos.ne' harg.ne']
        apply (Real.log_le_log (mul_pos pos harg) _).trans (log_add_one_le_harmonic _)
        rw [show N-(p+1)+1=N-p by omega,Nat.cast_sub pN.le]
        nlinarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]; positivity)
  · intro b hb
    have upper := full.add zero
    simp only [add_zero] at upper
    filter_upwards [(tendsto_order.mp upper).2 b hb,eventually_ge_atTop 2] with N hu hn
    apply lt_of_le_of_lt _ hu
    rw [exact_sum]
    change _ ≤ (P N).card*log N/N + (P N).card/(N:ℝ)
    rw [←add_div,show (P N).card*log N + (P N).card = (P N).card*(1+log N) by ring]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro p hp
    by_cases hz : N-(p+1)=0
    · simp [hz]
      linarith [Real.log_natCast_nonneg N]
    · apply (harmonic_le_one_add_log _).trans
      gcongr

      exact Nat.sub_le N (p+1)
lemma second_upper (N : ℕ) :
    let P := (range N).filter Nat.Prime
    ∑ n ∈ range N, (f n)^2 ≤ (P.card:ℝ) * (∑' j : ℕ, ((j:ℝ)^2)⁻¹) +
      ∑ p ∈ P, ∑ q ∈ P.erase p, (harmonic (Nat.dist p q):ℝ) / Nat.dist p q := by
  let P := (range N).filter Nat.Prime
  let a (p n : ℕ) : ℝ := if p<n then ((n-p:ℕ):ℝ)⁻¹ else 0
  let b (p q : ℕ) := ∑ n ∈ range N, a p n * a q n
  have expand : ∑ n ∈ range N, (f n)^2 = ∑ p ∈ P, ∑ q ∈ P, b p q := by
    calc
      _ = ∑ n ∈ range N, ∑ p ∈ P, ∑ q ∈ P, a p n*a q n := by
        apply sum_congr rfl
        intro n hn
        rw [expand_kernel a (fun _ _ => rfl) N n (mem_range.mp hn),sq]
        change (∑ p ∈ P,a p n)*(∑ q ∈ P,a q n) = _
        simp only [Finset.sum_mul,Finset.mul_sum]
        exact sum_comm
      _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun p _ => sum_comm
  have cross (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P.erase p) :
      b p q ≤ (harmonic (Nat.dist p q):ℝ) / Nat.dist p q := by
    have hne := (mem_erase.mp hq).1
    have qN := mem_range.mp (mem_filter.mp (mem_erase.mp hq).2).1
    have pN := mem_range.mp (mem_filter.mp hp).1
    rcases lt_or_gt_of_ne hne with h|h
    · rw [Nat.dist_eq_sub_of_le_right h.le]
      simpa only [b,mul_comm] using kernel_cross a (fun _ _ => rfl) N q p h pN
    · rw [Nat.dist_eq_sub_of_le h.le]
      exact kernel_cross a (fun _ _ => rfl) N p q h qN
  change _ ≤ (P.card:ℝ)*_+_
  rw [expand]
  calc
    _ = ∑ p ∈ P, (b p p + ∑ q ∈ P.erase p, b p q) := sum_congr rfl fun p hp => by
      rw [add_comm,sum_erase_add _ _ hp]
    _ ≤ ∑ p ∈ P, ((∑' j : ℕ, ((j:ℝ)^2)⁻¹) + ∑ q ∈ P.erase p,
        (harmonic (Nat.dist p q):ℝ)/Nat.dist p q) := by
      apply sum_le_sum
      intro p hp
      exact add_le_add (kernel_diag a (fun _ _ => rfl) N p (mem_range.mp (mem_filter.mp hp).1))
        (sum_le_sum (cross p hp))
    _ = _ := by simp [sum_add_distrib,P]

theorem main : H1 → H2 → type_of% @Erdos950.erdos_950.variants.debruijn_erdos_turan := by
  intro pnt pairs
  obtain ⟨mean,sparse⟩ := first_moment pnt
  have nz : ∀ᶠ N : ℕ in atTop, (N:ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with N hn
    exact_mod_cast hn.ne'
  refine ⟨(isEquivalent_iff_tendsto_one nz).mpr mean,(isEquivalent_iff_tendsto_one nz).mpr ?_⟩
  let P (N : ℕ) := (range N).filter Nat.Prime
  let D := ∑' j : ℕ, ((j:ℝ)^2)⁻¹
  have ds : Tendsto (fun N : ℕ => ((P N).card:ℝ)/N * D) atTop (𝓝 0) := by
    simpa [P,D] using sparse.mul_const D
  apply tendsto_order.mpr
  constructor
  · intro u hu
    have lim := mean.pow 2
    rw [one_pow] at lim
    filter_upwards [(tendsto_order.mp lim).1 u hu,eventually_gt_atTop 0] with N hn hN
    apply lt_of_lt_of_le hn
    have pos : (0:ℝ) < N := by exact_mod_cast hN
    have cs := sum_mul_sq_le_sq_mul_sq (range N) f (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,sum_const,card_range,nsmul_eq_mul] at cs
    change ((∑ n ∈ range N, f n) / N)^2 ≤ (∑ n ∈ range N,(f n)^2) / N
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos pos) pos]
    nlinarith only [mul_le_mul_of_nonneg_right cs pos.le]
  · intro u hu
    let δ := (u-1)/3
    have hd : 0 < δ := by dsimp [δ]; linarith
    filter_upwards [(tendsto_order.mp ds).2 δ hd,pairs δ hd,eventually_gt_atTop 0] with N hsmall hp hn
    have pos : (0:ℝ) < N := by exact_mod_cast hn
    have h := second_upper N
    dsimp only at h
    change _ ≤ (1+δ)*(N:ℝ) at hp
    have hh : ∑ n ∈ range N,(f n)^2 ≤ ((P N).card:ℝ)*D + (1+δ)*(N:ℝ) :=
      h.trans (add_le_add le_rfl hp)
    change (∑ n ∈ range N,(f n)^2) / N < u
    rw [div_lt_iff₀ pos]
    change ((P N).card:ℝ)/N * D < δ at hsmall
    rw [div_mul_eq_mul_div,div_lt_iff₀ pos] at hsmall
    have hdelta : 1+δ+δ < u := by dsimp [δ]; linarith
    nlinarith only [hh,hsmall,mul_lt_mul_of_pos_right hdelta pos]

end OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1
