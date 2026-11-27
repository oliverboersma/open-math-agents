import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1
import Mathlib

/-! The omitted denominators form disjoint sets of multiples, one for each
eligible prime. Their exact mass is a prime sum with harmonic cofactor
weights. Squeezing the factorial cutoff between logarithmic powers reduces
the sharp constant to the continuous profile a ↦ a²/2 at a=1. -/
namespace OMA.R_Erdos308_erdos_308_variants_croot_R1_H2_R1

open Finset Real Filter
open scoped Topology

/-- The harmonic mass for a simple cutoff p > N/(log N)^a. -/
def H1 : Prop := ∀ a : ℝ, 0 < a → a < 2 →
  Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a),
    (harmonic (N/p):ℝ)/p) * log N / (log (log N))^2) atTop (𝓝 (a^2/2))

/-- Elementary factorial thresholds on either side of the exponent one. -/
def H2 : Prop := ∀ a b : ℝ, 0 < a → a < 1 → 1 < b → b < 2 → ∀ᶠ N : ℕ in atTop,
  ∀ p ∈ Nat.primesLE N,
    ((N:ℝ)<p*(log N)^a → (N/p)*(N/p).factorial < p) ∧
    ((N/p)*(N/p).factorial < p → (N:ℝ)<p*(log N)^b)

lemma partition (N : ℕ) :
    let D := (Icc 1 N).filter fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p
    let P := (Nat.primesLE N).filter fun p => (N/p)*(N/p).factorial < p
    ∑ n ∈ D, (1:ℝ)/n = ∑ p ∈ P, (harmonic (N/p):ℝ)/p := by
  classical
  intro D P
  let B (p : ℕ) := (Icc 1 (N/p)).image (fun m => m*p)
  have prop {p : ℕ} (hp : p ∈ P) : Nat.Prime p ∧ N/p < p := by
    have hh := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hh.1).2,(Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)).trans_lt hh.2⟩
  have eqn : D = P.biUnion B := by
    ext n
    constructor
    · intro hn
      obtain ⟨hi,p,hp,hb⟩ := mem_filter.mp hn
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hn0 := (mem_Icc.mp hi).1
      have hnN := (mem_Icc.mp hi).2
      have hpn := Nat.le_of_dvd hn0 hd
      exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpn.trans hnN,hpr⟩,hb⟩,
        mem_image.mpr ⟨n/p,mem_Icc.mpr ⟨Nat.div_pos hpn hpr.pos,Nat.div_le_div_right hnN⟩,
        Nat.div_mul_cancel hd⟩⟩
    · intro hn
      obtain ⟨p,hp,hb⟩ := mem_biUnion.mp hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hb
      have hr := (prop hp).1
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      have hn0 := Nat.mul_pos hm0 hr.pos
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0,(Nat.le_div_iff_mul_le hr.pos).mp (mem_Icc.mp hm).2⟩,
        p,(Nat.mem_primeFactors.mpr ⟨hr,dvd_mul_left _ _,hn0.ne'⟩),(mem_filter.mp hp).2⟩
  have unique {p q : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hlt : p < q) : Disjoint (B p) (B q) := by
    apply disjoint_left.mpr
    intro n hn hm
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    obtain ⟨k,_,heq⟩ := mem_image.mp hm
    have dq : q ∣ j*p := ⟨k,heq.symm.trans (Nat.mul_comm _ _)⟩
    have nd : ¬ q ∣ p := fun h => (not_le_of_gt hlt) (Nat.le_of_dvd (prop hp).1.pos h)
    have dj := ((prop hq).1.dvd_mul.mp dq).resolve_right nd
    exact (not_le_of_gt hlt) ((Nat.le_of_dvd (mem_Icc.mp hj).1 dj).trans ((mem_Icc.mp hj).2.trans (prop hp).2.le))
  rw [eqn,sum_biUnion]
  · apply sum_congr rfl
    intro p hp
    have hp0 := (prop hp).1.pos
    rw [show B p = (Icc 1 (N/p)).image (fun m => m*p) by rfl,sum_image]
    · rw [harmonic_eq_sum_Icc,Rat.cast_sum,sum_div]
      apply sum_congr rfl
      intro m hm
      simp [Nat.cast_mul,one_div,div_eq_mul_inv,mul_inv_rev,mul_comm]
    · exact fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hp0 hab
  · intro p hp q hq hne
    rcases lt_or_gt_of_ne hne with h|h
    · exact unique hp hq h
    · exact (unique hq hp h).symm

theorem main : H1 → H2 → OMA.R_Erdos308_erdos_308_variants_croot_R1.H2 := by
  intro model factorial
  let T (N : ℕ) := (Icc 1 N).filter fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p
  let sumP (N : ℕ) (P : Finset ℕ) := (∑ p ∈ P, (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2
  let F (t : ℝ) (N : ℕ) := sumP N ((Nat.primesLE N).filter fun p => (N:ℝ)<p*(log N)^t)
  let G (N : ℕ) := (∑ n ∈ T N, (1:ℝ)/n)*log N/(log (log N))^2
  have bound (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 1 < b) (hb' : b < 2) :
      ∀ᶠ N : ℕ in atTop, F a N ≤ G N ∧ G N ≤ F b N := by
    filter_upwards [factorial a b ha ha' hb hb',eventually_ge_atTop (1:ℕ)] with N hh hn
    let P := (Nat.primesLE N).filter fun p => (N/p)*(N/p).factorial < p
    have eqn : G N = sumP N P := by dsimp [G,T,sumP,P]; rw [partition N]
    have mono {A B : Finset ℕ} (sub : A ⊆ B) : sumP N A ≤ sumP N B := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (log_nonneg (by exact_mod_cast hn))
      exact sum_le_sum_of_subset_of_nonneg sub fun p _ _ => by rw [harmonic_eq_sum_Icc]; push_cast; positivity
    rw [eqn]
    constructor
    · apply mono
      intro p hp
      obtain ⟨hpp,hcut⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpp,(hh p hpp).1 hcut⟩
    · apply mono
      intro p hp
      obtain ⟨hpp,hcut⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpp,(hh p hpp).2 hcut⟩
  change Tendsto G atTop (𝓝 (1/2:ℝ))
  have cont : Tendsto (fun a : ℝ => a^2/2) (𝓝 1) (𝓝 (1/2:ℝ)) := by
    have idh : Tendsto (fun t : ℝ => t) (𝓝 1) (𝓝 1) := tendsto_id
    simpa using ((idh.pow 2).div_const (2:ℝ))
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have near : ∀ᶠ a in 𝓝[<] (1:ℝ), l<a^2/2 := nhdsWithin_le_nhds (cont.eventually_const_lt hl)
    obtain ⟨a,ha,hi⟩ := (near.and (show ∀ᶠ a in 𝓝[<] (1:ℝ), a ∈ Set.Ioo 0 1 from Ioo_mem_nhdsLT zero_lt_one)).exists
    filter_upwards [(model a hi.1 (by linarith [hi.2])).eventually_const_lt ha,
      bound a (3/2) hi.1 hi.2 (by norm_num) (by norm_num)] with N hm hb
    exact hm.trans_le hb.1
  · intro u hu
    have near : ∀ᶠ b in 𝓝[>] (1:ℝ), b^2/2<u := nhdsWithin_le_nhds (cont.eventually_lt_const hu)
    obtain ⟨b,hb,hi⟩ := (near.and (show ∀ᶠ b in 𝓝[>] (1:ℝ), b ∈ Set.Ioo 1 2 from Ioo_mem_nhdsGT (by norm_num))).exists
    filter_upwards [(model b (by linarith [hi.1]) hi.2).eventually_lt_const hb,
      bound (1/2) b (by norm_num) (by norm_num) hi.1 hi.2] with N hm hbound
    exact hbound.2.trans_lt hm

end OMA.R_Erdos308_erdos_308_variants_croot_R1_H2_R1
