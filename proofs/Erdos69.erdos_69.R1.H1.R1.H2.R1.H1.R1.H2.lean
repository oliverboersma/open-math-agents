import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Product truncation, elementary symmetric sums and local phase estimates adapt
@chris01-dev's merged Erdős 69 proof (PR 3926, commit 9e8500b).
The conditional moment induction below applies to arbitrary finite samples with
unit discrepancy. The resulting estimate bounds the complex difference itself. -/
namespace FiniteSieve
open Finset

lemma pc_insert {R : Type*} [CommSemiring R] (f : ℕ → R) (s : Finset ℕ) (a : ℕ) (ha : a ∉ s)
    (j : ℕ) :
    ∑ D ∈ (insert a s).powersetCard (j + 1), ∏ i ∈ D, f i
      = ∑ D ∈ s.powersetCard (j + 1), ∏ i ∈ D, f i
        + f a * ∑ D ∈ s.powersetCard j, ∏ i ∈ D, f i := by
  classical
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union, Finset.sum_image, Finset.mul_sum]
  · congr 1
    refine Finset.sum_congr rfl fun D hD => ?_
    have haD : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
    rw [Finset.prod_insert haD]
  · intro D hD D' hD' h
    have haD : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
    have haD' : a ∉ D' := fun h => ha ((Finset.mem_powersetCard.mp hD').1 h)
    have := congrArg (fun t => t.erase a) h
    simpa [Finset.erase_insert haD, Finset.erase_insert haD'] using this
  · rw [Finset.disjoint_left]
    intro D hD hD'
    obtain ⟨D0, _, rfl⟩ := Finset.mem_image.mp hD'
    exact ha ((Finset.mem_powersetCard.mp hD).1 (Finset.mem_insert_self a D0))

lemma pc_zero {R : Type*} [CommSemiring R] (f : ℕ → R) (s : Finset ℕ) :
    ∑ D ∈ s.powersetCard 0, ∏ i ∈ D, f i = 1 := by
  simp

/-- Truncating the expansion of a product of unimodular-bounded factors `1 + g i` at subsets of
size `M`: the error is at most the sum over subsets of size `M + 1` of the products of norms. -/
lemma prod_trunc (g : ℕ → ℂ) (s : Finset ℕ) (hg : ∀ i ∈ s, ‖1 + g i‖ ≤ 1) :
    ∀ M : ℕ, ‖∏ i ∈ s, (1 + g i)
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i‖
      ≤ ∑ D ∈ s.powersetCard (M + 1), ∏ i ∈ D, ‖g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro M
    have h1 : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ (∅ : Finset ℕ).powersetCard j, ∏ i ∈ D, g i
        = 1 := by
      rw [Finset.sum_range_succ', Finset.sum_eq_zero]
      · simp
      · intro j _
        rw [Finset.powersetCard_eq_empty.mpr (by simp)]
        simp
    rw [h1, Finset.prod_empty, sub_self, norm_zero]
    exact Finset.sum_nonneg fun D _ => Finset.prod_nonneg fun i _ => norm_nonneg _
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hprod1 : ‖∏ i ∈ s, (1 + g i)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    intro M
    rw [Finset.prod_insert ha, pc_insert (fun i => ‖g i‖) s a ha M]
    -- the truncated sum for the larger set
    have hT : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ (insert a s).powersetCard j, ∏ i ∈ D, g i
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i
          + g a * ∑ j ∈ Finset.range M, ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ' _ M, pc_zero, pc_zero, Finset.mul_sum,
        Finset.sum_congr rfl (fun j _ => pc_insert g s a ha j), Finset.sum_add_distrib]
      ring
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have hT0 : ∑ j ∈ Finset.range (0 + 1), ∑ D ∈ (insert a s).powersetCard j, ∏ i ∈ D, g i
          = 1 := by simp
      have hT0' : ∑ j ∈ Finset.range (0 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i = 1 := by
        simp
      rw [hT0]
      have e : (1 + g a) * ∏ i ∈ s, (1 + g i) - 1
          = (∏ i ∈ s, (1 + g i) - 1) + g a * ∏ i ∈ s, (1 + g i) := by ring
      rw [e]
      have h0 := ih' 0
      rw [hT0'] at h0
      have h1 : ‖g a * ∏ i ∈ s, (1 + g i)‖ ≤ ‖g a‖ * 1 := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hprod1 (norm_nonneg _)
      rw [pc_zero]
      calc ‖(∏ i ∈ s, (1 + g i) - 1) + g a * ∏ i ∈ s, (1 + g i)‖
          ≤ ‖∏ i ∈ s, (1 + g i) - 1‖ + ‖g a * ∏ i ∈ s, (1 + g i)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add h0 h1
    · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [hT]
      have e : (1 + g a) * ∏ i ∈ s, (1 + g i)
          - (∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i
            + g a * ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
          = (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
            + g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i) := by ring
      rw [e]
      have h1 := ih' (M' + 1)
      have h2 := ih' M'
      calc ‖(∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
            + g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)‖
          ≤ ‖∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i‖
            + ‖g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)‖ :=
            norm_add_le _ _
        _ ≤ _ := by
            rw [norm_mul]
            exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

lemma pow_succ_add_le (p x : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (n : ℕ) :
    p ^ (n + 1) + (n + 1) * (x * p ^ n) ≤ (p + x) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (p + x) ^ (n + 1 + 1) = (p + x) ^ (n + 1) * (p + x) := pow_succ _ _
    have h2 : (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x)
        ≤ (p + x) ^ (n + 1) * (p + x) := mul_le_mul_of_nonneg_right ih (by linarith)
    have h3 : p ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * (x * p ^ (n + 1))
        ≤ (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x) := by
      have e : (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x)
          - (p ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * (x * p ^ (n + 1)))
          = (n + 1) * (x ^ 2 * p ^ n) := by
        push_cast
        ring
      have h0 : (0 : ℝ) ≤ (n + 1) * (x ^ 2 * p ^ n) := by positivity
      linarith
    rw [h1]
    exact h3.trans h2

/-- Elementary symmetric sums are at most the power of the sum divided by the factorial. -/
lemma esymm_le (x : ℕ → ℝ) (s : Finset ℕ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ j : ℕ, (j.factorial : ℝ) * ∑ D ∈ s.powersetCard j, ∏ i ∈ D, x i ≤ (∑ i ∈ s, x i) ^ j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [Finset.powersetCard_eq_empty.mpr (by simpa using hj)]
      simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hp : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [pc_insert x s a ha j', Finset.sum_insert ha]
      have h1 := ih' (j' + 1)
      have h2 := ih' j'
      have hfac : ((j' + 1).factorial : ℝ) = (j' + 1) * (j'.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have h3 : ((j' + 1).factorial : ℝ) * (x a * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)
          ≤ (j' + 1) * (x a * (∑ i ∈ s, x i) ^ j') := by
        rw [hfac]
        have : (j' + 1 : ℝ) * (j'.factorial : ℝ) * (x a * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)
            = (j' + 1) * (x a * ((j'.factorial : ℝ) * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)) := by
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hxa) (by positivity)
      have h4 := pow_succ_add_le (∑ i ∈ s, x i) (x a) hp hxa j'
      rw [mul_add, add_comm (x a) (∑ i ∈ s, x i)]
      linarith

private def counts (N D : Finset ℕ) (w : ℝ) : Prop :=
  ∀ J ⊆ D, ∀ h : ℕ → ℤ, |(((N.filter fun (n : ℕ) => ∀ p ∈ J, (p:ℤ) ∣ (n:ℤ)+h p).card : ℝ)
    - w / (∏ p ∈ J, (p:ℝ)))| ≤ 1

private lemma moments {𝕜 : Type*} [RCLike 𝕜] (S : Finset (Finset ℕ × ℕ))
    (r : Finset ℕ × ℕ → ℤ) (γ : Finset ℕ × ℕ → 𝕜) (D : Finset ℕ) :
    ∀ (N : Finset ℕ) (w : ℝ), counts N D w →
    ‖∑ n ∈ N, ∏ p ∈ D, ∑ a ∈ S, γ a * (if (p:ℤ) ∣ (n:ℤ)+r a then (1:𝕜) else 0)
      - (w:𝕜) * ∏ p ∈ D, ((∑ a ∈ S, γ a)/(p:𝕜))‖ ≤ (∑ a ∈ S, ‖γ a‖)^D.card := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro N w h
    have hh := h ∅ (by simp) 0
    simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_empty, pow_zero]
    rw [show (N.card:𝕜) - (w:𝕜) = (((N.card:ℝ)-w:ℝ):𝕜) by push_cast; rfl,
      RCLike.norm_ofReal]
    simpa using hh
  | insert a D ha ih =>
    intro N w h
    let Q (α : Finset ℕ × ℕ) := N.filter fun n : ℕ => (a:ℤ) ∣ (n:ℤ)+r α
    have cond (α : Finset ℕ × ℕ) : counts (Q α) D (w/a) := by
      intro J hJ v
      have haJ : a ∉ J := fun h => ha (hJ h)
      let u (p : ℕ) := if p=a then r α else v p
      have eq : (Q α).filter (fun (n : ℕ) => ∀ p ∈ J, (p:ℤ) ∣ (n:ℤ)+v p) =
          N.filter (fun (n : ℕ) => ∀ p ∈ insert a J, (p:ℤ) ∣ (n:ℤ)+u p) := by
        ext n
        simp only [Q,mem_filter,forall_mem_insert]
        have hv (p) (hp : p ∈ J) : u p = v p := by
          have hne : p ≠ a := fun e => haJ (e ▸ hp)
          simp [u,hne]
        simp only [u,if_pos rfl] at *
        constructor
        · rintro ⟨⟨hn,hm⟩,hs⟩
          exact ⟨hn,hm,fun p hp => (hv p hp).symm ▸ hs p hp⟩
        · rintro ⟨hn,hm,hs⟩
          exact ⟨⟨hn,hm⟩,fun p hp => (hv p hp) ▸ hs p hp⟩
      rw [eq, div_div]
      have hh := h (insert a J) (insert_subset_insert a hJ) u
      rwa [prod_insert haJ] at hh
    have hsplit : ∑ n ∈ N, ∏ ℓ ∈ insert a D, ∑ α ∈ S, γ α * (if (ℓ:ℤ) ∣ (n:ℤ)+r α then (1:𝕜) else 0)
        = ∑ α ∈ S, γ α * ∑ n ∈ Q α, ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ:ℤ) ∣ (n:ℤ)+r β then (1:𝕜) else 0) := by
      have h1 : ∀ n : ℕ,
          ∏ ℓ ∈ insert a D, ∑ α ∈ S, γ α * (if (ℓ : ℤ) ∣ (n : ℤ) + r α then (1 : 𝕜) else 0)
          = ∑ α ∈ S, γ α * ((if (a : ℤ) ∣ (n : ℤ) + r α then (1 : 𝕜) else 0)
            * ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ : ℤ) ∣ (n : ℤ) + r β then (1 : 𝕜) else 0)) := by
        intro n
        rw [Finset.prod_insert ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        ring
      rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      conv_lhs => rw [← Finset.mul_sum]
      conv_rhs => rw [show Q α = N.filter (fun n : ℕ => (a:ℤ) ∣ (n:ℤ)+r α) from rfl, Finset.sum_filter]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> simp
    have hmain : (w:𝕜) * ∏ ℓ ∈ insert a D, ((∑ β ∈ S, γ β)/(ℓ:𝕜))
        = ∑ α ∈ S, γ α * (((w/(a:ℝ):ℝ):𝕜) * ∏ ℓ ∈ D, ((∑ β ∈ S, γ β)/(ℓ:𝕜))) := by
      rw [prod_insert ha, ← sum_mul]
      push_cast
      ring
    rw [hsplit,hmain,← sum_sub_distrib]
    calc
      _ ≤ ∑ α ∈ S, ‖γ α‖ * (∑ β ∈ S, ‖γ β‖)^D.card := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro α _
        rw [← mul_sub,norm_mul]
        exact mul_le_mul_of_nonneg_left (ih (Q α) (w/a) (cond α)) (norm_nonneg _)
      _ = _ := by rw [←sum_mul,card_insert_of_notMem ha,pow_succ]; ring

lemma local_factor (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (wt : Finset ℕ × ℕ → ℝ)
    (q : ℝ) (ℓ n : ℕ)
    (hsep : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ (ℓ : ℤ) ∣ r a - r c) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) : ℝ) : ℂ))
      = 1 + ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) := by
  classical
  by_cases h : ∃ a ∈ S, (ℓ : ℤ) ∣ (n : ℤ) + r a
  · obtain ⟨a0, ha0, hact⟩ := h
    have hother : ∀ c ∈ S, c ≠ a0 → ¬ (ℓ : ℤ) ∣ (n : ℤ) + r c := by
      intro c hc hne hc'
      apply hsep a0 ha0 c hc (Ne.symm hne)
      have := dvd_sub hact hc'
      simpa using this
    have e1 : ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) = wt a0 := by
      rw [Finset.sum_eq_single a0]
      · rw [if_pos hact, mul_one]
      · intro c hc hne
        rw [if_neg (hother c hc hne), mul_zero]
      · intro h
        exact absurd ha0 h
    have e2 : ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)
        = Complex.exp (2 * Real.pi * Complex.I * ((q * wt a0 : ℝ) : ℂ)) - 1 := by
      rw [Finset.sum_eq_single a0]
      · rw [if_pos hact, mul_one]
      · intro c hc hne
        rw [if_neg (hother c hc hne), mul_zero]
      · intro h
        exact absurd ha0 h
    rw [e1, e2]
    ring
  · push Not at h
    have e1 : ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [if_neg (h a ha), mul_zero]
    have e2 : ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [if_neg (h a ha), mul_zero]
    rw [e1, e2]
    simp
lemma card_le_of_sep (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hsep : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ (ℓ : ℤ) ∣ r a - r c) : S.card ≤ ℓ := by
  classical
  have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range ℓ)
    (fun a => ((r a) % (ℓ : ℤ)).toNat) ?_ ?_
  · rwa [Finset.card_range] at h
  · intro a _
    rw [Finset.mem_coe, Finset.mem_range]
    have h1 := Int.emod_lt_of_pos (r a) hpos
    have h2 := Int.emod_nonneg (r a) hpos.ne'
    exact (Int.toNat_lt h2).mpr h1
  · intro a ha c hc heq
    by_contra hne
    apply hsep a (Finset.mem_coe.mp ha) c (Finset.mem_coe.mp hc) hne
    have h2a := Int.emod_nonneg (r a) hpos.ne'
    have h2c := Int.emod_nonneg (r c) hpos.ne'
    have heq' : (r a) % (ℓ : ℤ) = (r c) % (ℓ : ℤ) := by
      have : (((r a) % (ℓ : ℤ)).toNat : ℤ) = (((r c) % (ℓ : ℤ)).toNat : ℤ) := by
        exact_mod_cast heq
      rwa [Int.toNat_of_nonneg h2a, Int.toNat_of_nonneg h2c] at this
    exact Int.modEq_iff_dvd.mp (show (r c) ≡ (r a) [ZMOD ℓ] from heq'.symm)
lemma model_le_one (S : Finset (Finset ℕ × ℕ)) (e : Finset ℕ × ℕ → ℂ) (he : ∀ a ∈ S, ‖e a‖ ≤ 1)
    (ℓ : ℕ) (hℓ : S.card ≤ ℓ) (hℓ0 : 0 < ℓ) :
    ‖1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ)‖ ≤ 1 := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ0
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0.ne'
  have e1 : 1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ)
      = ((((ℓ : ℝ) - S.card : ℝ) : ℂ) + ∑ a ∈ S, e a) / (ℓ : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [e1, norm_div, Complex.norm_natCast, div_le_one hℓR]
  have hcard : (S.card : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  calc ‖(((ℓ : ℝ) - S.card : ℝ) : ℂ) + ∑ a ∈ S, e a‖
      ≤ ‖(((ℓ : ℝ) - S.card : ℝ) : ℂ)‖ + ‖∑ a ∈ S, e a‖ := norm_add_le _ _
    _ ≤ ((ℓ : ℝ) - S.card) + S.card := by
        refine add_le_add ?_ ?_
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        · calc ‖∑ a ∈ S, e a‖ ≤ ∑ a ∈ S, ‖e a‖ := norm_sum_le _ _
            _ ≤ ∑ _a ∈ S, (1 : ℝ) := Finset.sum_le_sum he
            _ = S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ℓ := by ring

lemma phase_eq (θ : ℝ) : Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ))
    = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring

lemma phase_norm (θ : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ))‖ = 1 := by
  rw [phase_eq, Complex.norm_exp_ofReal_mul_I]

private lemma compare (N : Finset ℕ) (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ)
    (γ : Finset ℕ × ℕ → ℂ) (P : Finset ℕ) (M : ℕ) (hc : counts N P N.card)
    (hunit : ∀ n ∈ N, ∀ ℓ ∈ P,
      ‖1 + ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)‖ ≤ 1)
    (hmodel : ∀ ℓ ∈ P, ‖1 + (∑ a ∈ S, γ a) / (ℓ : ℂ)‖ ≤ 1) :
    ‖(∑ n ∈ N, ∏ ℓ ∈ P, (1 + ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)))
      - (N.card:ℂ) * ∏ ℓ ∈ P, (1 + (∑ a ∈ S, γ a) / (ℓ : ℂ))‖
      ≤ 2 * (N.card : ℝ) * ((∑ a ∈ S, ‖γ a‖) ^ (M+1) *
        ∑ D ∈ P.powersetCard (M+1), ∏ ℓ ∈ D, (1:ℝ)/ℓ)
        + ∑ j ∈ range (M+2), (P.card.choose j : ℝ) * (∑ a ∈ S, ‖γ a‖)^j := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ a ∈ S, ‖γ a‖ := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℂ, Γ = ∑ a ∈ S, γ a := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ → ℂ, ∀ ℓ n,
      g ℓ n = ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  rw [← hG, ← hΓ]
  rw [← hΓ] at hmodel
  simp only [← hg] at hunit ⊢
  have hG0 : 0 ≤ G := by rw [hG]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΓG : ‖Γ‖ ≤ G := by rw [hΓ, hG]; exact norm_sum_le _ _
  have hNn : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  have subcount (D : Finset ℕ) (hD : D ⊆ P) : counts N D N.card :=
    fun J hJ h => hc J (hJ.trans hD) h
  have hmom : ∀ D ⊆ P, ‖∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
      ≤ 1 * G ^ D.card := by
    intro D hD
    have hh := moments (𝕜:=ℂ) S r γ D N N.card (subcount D hD)
    simpa only [RCLike.ofReal_natCast,←hG,←hΓ,←hg,one_mul] using hh
  -- the real majorant
  have hmaj : ∀ D ⊆ P, ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
      ≤ (N.card : ℝ) * (G ^ D.card * ∏ ℓ ∈ D, (1 : ℝ) / ℓ) + 1 * G ^ D.card := by
    intro D hD
    have h := moments (𝕜:=ℝ) S r (fun a => ‖γ a‖) D N N.card (subcount D hD)
    simp only [RCLike.ofReal_real_eq_id, id_eq, norm_norm] at h
    rw [← hG] at h
    have hle : ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
        ≤ ∑ n ∈ N, ∏ ℓ ∈ D, ∑ a ∈ S, ‖γ a‖ * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum fun n _ => Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
      intro ℓ _
      rw [hg]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      split_ifs <;> simp
    have hprod : ∏ ℓ ∈ D, (G / (ℓ : ℝ)) = G ^ D.card * ∏ ℓ ∈ D, (1 : ℝ) / ℓ := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      ring
    rw [hprod, Real.norm_eq_abs, abs_le] at h
    linarith [h.2]
  -- truncation for each n
  have htrunc : ∀ n ∈ N, ‖∏ ℓ ∈ P, (1 + g ℓ n)
      - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n‖
      ≤ ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖g ℓ n‖ := fun n hn =>
    prod_trunc (fun ℓ => g ℓ n) P (hunit n hn) M
  have htrunc' : ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
      - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
      ≤ ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖Γ / (ℓ : ℂ)‖ :=
    prod_trunc (fun ℓ => Γ / (ℓ : ℂ)) P hmodel M
  have hsub : ∀ j, ∀ D ∈ P.powersetCard j, D ⊆ P ∧ D.card = j :=
    fun j D hD => Finset.mem_powersetCard.mp hD
  -- bound on the model remainder
  have hmodrem : ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖Γ / (ℓ : ℂ)‖
      ≤ G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun D hD => ?_
    obtain ⟨_, hcard⟩ := hsub _ D hD
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun ℓ _ => ?_
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hΓG (by positivity)
  -- bound on the summed remainders
  have hrem : ∑ n ∈ N, ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖g ℓ n‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ)
        + 1 * ((P.card.choose (M + 1) : ℝ) * G ^ (M + 1)) := by
    rw [Finset.sum_comm]
    calc ∑ D ∈ P.powersetCard (M + 1), ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
        ≤ ∑ D ∈ P.powersetCard (M + 1),
            ((N.card : ℝ) * (G ^ (M + 1) * ∏ ℓ ∈ D, (1 : ℝ) / ℓ) + 1 * G ^ (M + 1)) := by
          refine Finset.sum_le_sum fun D hD => ?_
          obtain ⟨hDP, hcard⟩ := hsub _ D hD
          have := hmaj D hDP
          rw [hcard] at this
          exact this
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- the error in the main terms
  have hθ : ‖∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
        (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))‖
      ≤ 1 * ∑ j ∈ Finset.range (M + 1), (P.card.choose j : ℝ) * G ^ j := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ D ∈ P.powersetCard j,
          ‖∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
        ≤ ∑ _D ∈ P.powersetCard j, 1 * G ^ j := by
          refine Finset.sum_le_sum fun D hD => ?_
          obtain ⟨hDP, hcard⟩ := hsub _ D hD
          have := hmom D hDP
          rw [hcard] at this
          exact this
      _ = 1 * ((P.card.choose j : ℝ) * G ^ j) := by
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
          ring
  -- algebraic decomposition
  have hdecomp : ∑ n ∈ N, ∏ ℓ ∈ P, (1 + g ℓ n)
      = (N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - (N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        + ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
            (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        + ∑ n ∈ N, (∏ ℓ ∈ P, (1 + g ℓ n)
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n) := by
    have e1 : ∑ n ∈ N, ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
    have e2 : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
          (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n
          - (N.card : ℂ) * ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
              ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [e2, Finset.sum_sub_distrib, e1]
    ring
  have hn2 : ‖(N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ) := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (htrunc'.trans hmodrem) hNn
  have hn4 : ‖∑ n ∈ N, (∏ ℓ ∈ P, (1 + g ℓ n)
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n)‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ)
        + 1 * ((P.card.choose (M + 1) : ℝ) * G ^ (M + 1)) :=
    ((norm_sum_le _ _).trans (Finset.sum_le_sum htrunc)).trans hrem
  have hchoose : ∑ j ∈ Finset.range (M + 2), (P.card.choose j : ℝ) * G ^ j
      = ∑ j ∈ Finset.range (M + 1), (P.card.choose j : ℝ) * G ^ j
        + (P.card.choose (M + 1) : ℝ) * G ^ (M + 1) := Finset.sum_range_succ _ _
  rw [hchoose]
  rw [hdecomp]
  have alg (A B E F : ℂ) : A-B+E+F-A = -B+E+F := by ring
  rw [alg]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  rw [norm_neg]
  linarith


private lemma polynomial (v : ℝ) (hv : 0 ≤ v) (k : ℕ) :
    ∑ j ∈ range (k+1), v^j ≤ (1+v)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ (1+v), pow_succ v]
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hv (show v ≤ 1+v by linarith) k) hv
    linarith

end FiniteSieve
open FiniteSieve Finset

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1.H2 := by
  classical
  intro N P S r t C k hk hC hp hs hnorm hc
  let e (a : Finset ℕ × ℕ) := Complex.exp (((2*Real.pi*t a : ℝ):ℂ)*Complex.I)
  let γ (a : Finset ℕ × ℕ) := e a - 1
  let G := ∑ a ∈ S, ‖γ a‖
  have hG : G ≤ C := hnorm
  have hG0 : 0 ≤ G := sum_nonneg fun _ _ => norm_nonneg _
  have he (a) : ‖e a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have sep (p) (hp' : p ∈ P) := fun a ha b hb hne => hs a ha b hb hne p hp'
  have model (p) (h : p ∈ P) : ‖1+(∑ a ∈ S, γ a)/(p:ℂ)‖ ≤ 1 :=
    model_le_one S e (fun a _ => (he a).le) p (card_le_of_sep S r p (hp p h).pos (sep p h)) (hp p h).pos
  let v (p n : ℕ) := ∑ a ∈ S, t a * (if (p:ℤ) ∣ (n:ℤ)+r a then (1:ℝ) else 0)
  have localEq (p) (h : p ∈ P) (n) :
      Complex.exp (((2*Real.pi*v p n : ℝ):ℂ)*Complex.I) =
        1+∑ a ∈ S, γ a * (if (p:ℤ) ∣ (n:ℤ)+r a then (1:ℂ) else 0) := by
    simpa only [one_mul,phase_eq,v,e,γ] using local_factor S r t 1 p n (sep p h)
  have hu (n : ℕ) (_ : n ∈ N) (p) (h : p ∈ P) :
      ‖1+∑ a ∈ S, γ a * (if (p:ℤ) ∣ (n:ℤ)+r a then (1:ℂ) else 0)‖ ≤ 1 := by
    rw [←localEq p h n,Complex.norm_exp_ofReal_mul_I]
  have ex (n : ℕ) :
      Complex.exp (((2*Real.pi*(∑ a ∈ S, t a *
        ((P.filter fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+r a).card:ℝ)):ℝ):ℂ)*Complex.I)
      = ∏ p ∈ P, (1+∑ a ∈ S, γ a * (if (p:ℤ) ∣ (n:ℤ)+r a then (1:ℂ) else 0)) := by
    have hsum : (∑ a ∈ S, t a *
        ((P.filter fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+r a).card:ℝ)) = ∑ p ∈ P, v p n := by
      rw [show (∑ p ∈ P, v p n) = ∑ a ∈ S, ∑ p ∈ P, t a *
        (if (p:ℤ) ∣ (n:ℤ)+r a then (1:ℝ) else 0) from Finset.sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [← mul_sum]
      congr 1
      simp
    rw [hsum, mul_sum]
    push_cast
    rw [sum_mul,Complex.exp_sum]
    apply prod_congr rfl
    intro p h
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using localEq p h n
  obtain ⟨M,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hh := FiniteSieve.compare N S r γ P M hc hu model
  rw [sum_congr rfl (fun n (_ : n ∈ N) => ex n)]
  apply hh.trans
  let m := ∑ p ∈ P, (1:ℝ)/p
  have hm : 0 ≤ m := sum_nonneg fun _ _ => by positivity
  let k := M+1
  have hs' := esymm_le (fun p : ℕ => (1:ℝ)/p) P (fun _ _ => by positivity) k
  have htail : G^k * (∑ D ∈ P.powersetCard k, ∏ p ∈ D, (1:ℝ)/p) ≤ (C*m)^k/k.factorial := by
    rw [mul_pow, le_div_iff₀ (by positivity : 0 < (k.factorial:ℝ))]
    calc
      _ = G^k * ((k.factorial:ℝ) * ∑ D ∈ P.powersetCard k, ∏ p ∈ D, (1:ℝ)/p) := by ring
      _ ≤ G^k*m^k := mul_le_mul_of_nonneg_left hs' (pow_nonneg hG0 _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG0 hG k) (pow_nonneg hm _)
  have hpoly : ∑ j ∈ range (k+1), (P.card.choose j : ℝ)*G^j ≤ ((1+C)*(1+(P.card:ℝ)))^k := calc
    _ ≤ ∑ j ∈ range (k+1), ((P.card:ℝ)*C)^j := by
      apply sum_le_sum
      intro j _
      rw [mul_pow]
      exact mul_le_mul (by exact_mod_cast Nat.choose_le_pow P.card j)
        (pow_le_pow_left₀ hG0 hG j) (pow_nonneg hG0 _) (by positivity)
    _ ≤ _ := (polynomial _ (by positivity) k).trans (pow_le_pow_left₀ (by positivity) (by nlinarith) k)
  change 2*(N.card:ℝ)*(G^k * _) + _ ≤ (N.card:ℝ)*(2*(C*m)^k/k.factorial) + 2*((1+C)*(1+(P.card:ℝ)))^k
  have hf : 2*(C*m)^k/(k.factorial:ℝ) = 2*((C*m)^k/(k.factorial:ℝ)) := by ring
  rw [hf]
  have hh' := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2*(N.card:ℝ) by positivity)
  nlinarith [pow_nonneg (show 0 ≤ (1+C)*(1+(P.card:ℝ)) by positivity) k]

