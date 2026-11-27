import OMAReductions.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1
import Mathlib

/-! Adapted from Pawan Sasanka Ammanamanchi and collaborators,
Shashi456/erdos-formalizations, Erdos/P202/Proof.lean at
286f856aa3fc08957b80950fd18a45aab8d045ea, used under Apache-2.0.
This version prunes from an explicit cardinality threshold and retains
the subset witnesses through radical selection. -/
namespace BFVPruning1190
open Filter
open Asymptotics
open scoped BigOperators
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

def restrictAssignment {Q Q' : Finset ℕ}
    (a : ResidueAssignment Q) (hsub : Q' ⊆ Q) : ResidueAssignment Q' :=
  fun q => a ⟨q.1, hsub q.2⟩

lemma PairwiseDisjointResidues.mono
    {Q Q' : Finset ℕ} {a : ResidueAssignment Q}
    (hdisj : PairwiseDisjointResidues Q a) (hsub : Q' ⊆ Q) :
    PairwiseDisjointResidues Q' (restrictAssignment a hsub) := by
  intro i j hij
  let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
  let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
  have hijQ : iQ ≠ jQ := by
    intro h
    have hval : iQ.1 = jQ.1 :=
      congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
    exact hij (Subtype.ext hval)
  simpa [restrictAssignment, iQ, jQ] using hdisj iQ jQ hijQ

def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

noncomputable def Mscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))

lemma Zscale_nonneg (N : ℕ) : 0 ≤ Zscale N :=
  Real.sqrt_nonneg _

lemma Zscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Zscale, Real.sqrt_pos]
  exact mul_pos hlog_pos hloglog_pos

lemma Zscale_eq_sqrt_log_mul_sqrt_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  rw [Zscale, Real.sqrt_mul hlog_nonneg]

lemma Mscale_nonneg (N : ℕ) : 0 ≤ Mscale N :=
  Real.sqrt_nonneg _

lemma Mscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Mscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Mscale, Real.sqrt_pos]
  exact div_pos hlog_pos hloglog_pos

lemma Mscale_mul_loglog_eq_Zscale {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.log (Real.log (N : ℝ)) = Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hleft_nonneg : 0 ≤ Mscale N * Real.log (Real.log (N : ℝ)) :=
    mul_nonneg (Mscale_nonneg N) hloglog_nonneg
  have hsq :
      (Mscale N * Real.log (Real.log (N : ℝ))) ^ 2 = (Zscale N) ^ 2 := by
    rw [Mscale, Zscale, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · field_simp [hloglog_pos.ne']
    · exact mul_nonneg hlog_nonneg hloglog_nonneg
    · exact div_nonneg hlog_nonneg hloglog_nonneg
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hright_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
    nlinarith

lemma Zscale_div_Mscale_eq_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) := by
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMpos := Mscale_pos_of_exp_one_lt_nat hN
  rw [← hMll]
  field_simp [hMpos.ne']

lemma Mscale_mul_Zscale_eq_log {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Zscale N = Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMsq : Mscale N ^ 2 =
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
    rw [Mscale, Real.sq_sqrt]
    exact div_nonneg hlog_nonneg hloglog_nonneg
  calc
    Mscale N * Zscale N
        = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by rw [hMll]
    _ = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
    _ = Real.log (N : ℝ) := by
          rw [hMsq]
          field_simp [hloglog_pos.ne']

lemma tendsto_loglog_div_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma tendsto_sqrt_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_loglog_nat_atTop

lemma eventually_sqrt_loglog_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop A

lemma eventually_Mscale_ge (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, A ≤ Mscale N := by
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have htarget_pos : (0 : ℝ) < 1 / A ^ 2 := by positivity
  have hratio_small : ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
    tendsto_loglog_div_log_nat_atTop.eventually_lt_const htarget_pos
  filter_upwards [hratio_small, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmall hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_lt :
      Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog_pos).1 hsmall
  have hmulA :
      A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hloglog_lt hA2
    field_simp [hA2.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hquot_ge :
      A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    (le_div_iff₀ hloglog_pos).2 hmulA.le
  rw [Mscale]
  exact (Real.le_sqrt hA.le (div_nonneg hlog_pos.le hloglog_pos.le)).2 hquot_ge

lemma Lscale_pos (α : ℝ) (N : ℕ) : 0 < Lscale α N :=
  Real.exp_pos _

lemma Lscale_nonneg (α : ℝ) (N : ℕ) : 0 ≤ Lscale α N :=
  (Lscale_pos α N).le

lemma Lscale_zero (N : ℕ) : Lscale 0 N = 1 := by
  simp [Lscale]

lemma Lscale_add (α β : ℝ) (N : ℕ) :
    Lscale (α + β) N = Lscale α N * Lscale β N := by
  simp [Lscale, add_mul, Real.exp_add]

lemma Lscale_neg_mul (α : ℝ) (N : ℕ) :
    Lscale (-α) N * Lscale α N = 1 := by
  rw [← Lscale_add]
  simp [Lscale]

lemma Lscale_mono_in_alpha {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    Lscale α N ≤ Lscale β N := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (Zscale_nonneg N))

lemma Lscale_neg_le_one {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    Lscale (-α) N ≤ 1 := by
  simpa [Lscale_zero] using Lscale_mono_in_alpha (α := -α) (β := 0) (by linarith) N

lemma log_nat_mul_Lscale {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Real.log ((N : ℝ) * Lscale α N) = Real.log (N : ℝ) + α * Zscale N := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL : Lscale α N ≠ 0 := (Lscale_pos α N).ne'
  rw [Real.log_mul hNreal hL, Lscale, Real.log_exp]

end BFVPruning1190
namespace BFVPruning1190
open Finset
open scoped BigOperators
def primeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

def omega (n : ℕ) : ℕ :=
  (primeSupport n).card

def rad (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, p

def hExp (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, n.factorization p

def exactBlock (C : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ C, p ^ q.factorization p

lemma hExp_pos (n : ℕ) : 0 < hExp n := by
  unfold hExp primeSupport
  exact Finset.prod_pos (fun _p hp =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))

lemma hExp_one : hExp 1 = 1 := by
  simp [hExp, primeSupport]

lemma prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) : Nat.Prime p := by
  unfold primeSupport at hp
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

lemma mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : p ∈ primeSupport n := by
  unfold primeSupport
  rw [Finsupp.mem_support_iff]
  exact hp.factorization_pos_of_dvd hn hpn |>.ne'

lemma primeSupport_disjoint_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    Disjoint (primeSupport m) (primeSupport n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hp : Nat.Prime p := prime_of_mem_primeSupport hpm
  have hpdm : p ∣ m := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpm
    exact Finsupp.mem_support_iff.1 hpm)
  have hpdn : p ∣ n := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpn
    exact Finsupp.mem_support_iff.1 hpn)
  have hp1 : p ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hpdm hpdn
  exact hp.not_dvd_one hp1

lemma primeSupport_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    primeSupport (m * n) = primeSupport m ∪ primeSupport n := by
  unfold primeSupport
  rw [Nat.factorization_mul_of_coprime hcop]
  exact Finsupp.support_add_eq (primeSupport_disjoint_of_coprime hcop)

lemma hExp_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExp (m * n) = hExp m * hExp n := by
  unfold hExp
  rw [primeSupport_mul_of_coprime hcop]
  rw [Finset.prod_union (primeSupport_disjoint_of_coprime hcop)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport n :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
    have hnzero : n.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hnzero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport m :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
    have hmzero : m.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hmzero]

lemma exactBlock_dvd (C : Finset ℕ) (q : ℕ) : exactBlock C q ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  · nth_rw 2 [← Nat.factorization_prod_pow_eq_self hq]
    unfold exactBlock
    have hfilter :
        (∏ p ∈ C, p ^ q.factorization p) =
          ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
            p ^ q.factorization p := by
      refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
      intro p hpC hpNot
      have hpnotmem : p ∉ q.factorization.support := by
        intro hp
        exact hpNot (Finset.mem_filter.2 ⟨hpC, hp⟩)
      have hzero : q.factorization p = 0 := by
        by_contra hne
        exact hpnotmem (Finsupp.mem_support_iff.2 hne)
      simp [hzero]
    rw [hfilter]
    exact Finset.prod_dvd_prod_of_subset
      (C.filter (fun p => p ∈ q.factorization.support))
      q.factorization.support
      (fun p => p ^ q.factorization p)
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)

lemma factorization_exactBlock_of_mem {C : Finset ℕ} {q p : ℕ}
    (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
    (exactBlock C q).factorization p = q.factorization p := by
  unfold exactBlock
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single p]
  · rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
  · intro x hx hxp
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxp.symm
  · intro hpnot
    exact (hpnot hpC).elim

lemma primeSupport_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    primeSupport (exactBlock C q) = C := by
  unfold primeSupport exactBlock
  ext p
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.mem_support_iff]
  constructor
  · intro hsum
    by_contra hpC
    apply hsum
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
    intro x hx
    have hxne : x ≠ p := by
      intro hxp
      exact hpC (hxp ▸ hx)
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxne.symm
  · intro hpC
    have hp : Nat.Prime p := hC p hpC
    have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
    intro hsum
    rw [Finsupp.finset_sum_apply] at hsum
    have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
    exact hqpos hterm

lemma eq_one_of_omega_eq_zero {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
    n = 1 := by
  have hsupp : primeSupport n = ∅ := by
    have hcard : (primeSupport n).card = 0 := by simpa [omega] using hω
    exact Finset.card_eq_zero.mp hcard
  unfold primeSupport at hsupp
  have hprod_eq_one : n.factorization.prod (fun p e => p ^ e) = 1 := by
    unfold Finsupp.prod
    rw [hsupp]
    simp
  have hprod := Nat.factorization_prod_pow_eq_self hn
  rw [← hprod]
  exact hprod_eq_one

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
noncomputable def BFVz (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))

lemma finite_euler_product_one_add_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hpos : ∀ p ∈ s, 0 < (p : ℝ)) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ)) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ))) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
            (g := fun p : ℕ => Real.exp (z / (p : ℝ)))
            (fun p hp => by
              have hp_nonneg : 0 ≤ (p : ℝ) := (hpos p hp).le
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ))
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ))) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

private lemma primeSupport_eq_primeFactors (n : ℕ) :
    primeSupport n = n.primeFactors := by
  unfold primeSupport
  rw [Nat.support_factorization]

private lemma rad_eq_prod_primeFactors (n : ℕ) :
    rad n = ∏ p ∈ n.primeFactors, p := by
  unfold rad
  rw [primeSupport_eq_primeFactors]

private lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  rw [rad_eq_prod_primeFactors]
  classical
  have hprod_ne : (∏ p ∈ n.primeFactors, p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
  refine (Nat.squarefree_iff_factorization_le_one hprod_ne).2 ?_
  intro q
  by_cases hq : q ∈ n.primeFactors
  · have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q
            = q.factorization q := by
                refine Finset.sum_eq_single q ?_ ?_
                · intro x hx hxq
                  have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
                  rw [← pow_one x, hxprime.factorization_pow]
                  simp [hxq]
                · intro hnot
                  exact (hnot hq).elim
        _ = 1 := by
                rw [← pow_one q, hqprime.factorization_pow]
                simp
        _ ≤ 1 := le_rfl
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero
  · rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hx
          have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
          rw [← pow_one x, hxprime.factorization_pow]
          have hxq : x ≠ q := by
            intro h
            exact hq (h ▸ hx)
          simp [hxq]
        _ ≤ 1 := by norm_num
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero

private lemma rad_dvd_self (n : ℕ) : rad n ∣ n := by
  rw [rad_eq_prod_primeFactors]
  exact Nat.prod_primeFactors_dvd n

private lemma primeSupport_rad (n : ℕ) :
    primeSupport (rad n) = primeSupport n := by
  calc
    primeSupport (rad n) = (rad n).primeFactors := primeSupport_eq_primeFactors _
    _ = (∏ p ∈ n.primeFactors, p).primeFactors := by rw [rad_eq_prod_primeFactors]
    _ = n.primeFactors := by
      exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
    _ = primeSupport n := (primeSupport_eq_primeFactors n).symm

private lemma omega_rad (n : ℕ) : omega (rad n) = omega n := by
  unfold omega
  rw [primeSupport_rad]

lemma zpow_omega_le_squarefree_divisor_sum
    (z : ℝ) (hz : 0 ≤ z) {n : ℕ} (hn : n ≠ 0) :
    z ^ omega n ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
  classical
  have hmem : rad n ∈ n.divisors.filter Squarefree := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨rad_dvd_self n, hn⟩, rad_squarefree n⟩
  have hnonneg :
      ∀ d ∈ n.divisors.filter Squarefree, 0 ≤ z ^ omega d := by
    intro d hd
    exact pow_nonneg hz _
  have hsingle :
      z ^ omega (rad n) ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d :=
    Finset.single_le_sum hnonneg hmem
  simpa [omega_rad] using hsingle

lemma card_Icc_filter_dvd_le_div (y d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
  classical
  calc
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card
        ≤ (Finset.Icc 1 (y / d)).card := by
          refine Finset.card_le_card_of_injOn
            (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
            (t := Finset.Icc 1 (y / d))
            (fun n : ℕ => n / d) ?_ ?_
          · intro n hn
            have hn' : n ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hn
            rw [Finset.mem_filter] at hn'
            have hnIcc := Finset.mem_Icc.mp hn'.1
            have hdn : d ∣ n := hn'.2
            have htarget : n / d ∈ Finset.Icc 1 (y / d) := by
              rw [Finset.mem_Icc]
              refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
              exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hnIcc.1 hdn) hd)
            simpa using htarget
          · intro a ha b hb hab
            have ha' : a ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using ha
            have hb' : b ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hb
            rw [Finset.mem_filter] at ha'
            rw [Finset.mem_filter] at hb'
            have hda : d ∣ a := ha'.2
            have hdb : d ∣ b := hb'.2
            have hab' : a / d = b / d := by simpa using hab
            calc
              a = a / d * d := (Nat.div_mul_cancel hda).symm
              _ = b / d * d := by rw [hab']
              _ = b := Nat.div_mul_cancel hdb
    _ = y / d := by simp

lemma omega_weighted_sum_le_squarefree_multiple_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
        (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact zpow_omega_le_squarefree_divisor_sum z hz
            (by
              have hnIcc := Finset.mem_Icc.mp hn
              exact Nat.ne_of_gt hnIcc.1)
    _ ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ d ∣ n),
              z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            have hddiv : d ∈ n.divisors := hd.1
            have hdsq : Squarefree d := hd.2
            have hnIcc := Finset.mem_Icc.mp hn
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
            have hddvd : d ∣ n := (Nat.mem_divisors.mp hddiv).1
            have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
            have hdle : d ≤ y := (Nat.le_of_dvd hnpos hddvd).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩, hdsq, hddvd⟩
          · intro d hd _hnot
            exact pow_nonneg hz _
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
          (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : Squarefree d
          · calc
              (∑ x ∈ Finset.Icc 1 y, if Squarefree d ∧ d ∣ x then z ^ omega d else 0)
                  = ∑ x ∈ Finset.Icc 1 y, if d ∣ x then z ^ omega d else 0 := by
                    simp [hsq]
              _ = ∑ x ∈ (Finset.Icc 1 y).filter (fun x => d ∣ x), z ^ omega d := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                    z ^ omega d := by
                    simp [Finset.sum_const, nsmul_eq_mul]
              _ = if Squarefree d then
                    (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                      z ^ omega d
                  else 0 := by
                    simp [hsq]
          · simp [hsq]

lemma omega_weighted_sum_le_squarefree_recip_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
              z ^ omega d :=
          omega_weighted_sum_le_squarefree_multiple_sum y z hz
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            ((y : ℝ) / (d : ℝ)) * z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
          have hcard_nat :
              ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d :=
            card_Icc_filter_dvd_le_div y d hdpos
          have hcard_real :
              (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) ≤
                (y : ℝ) / (d : ℝ) := by
            exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right hcard_real (pow_nonneg hz _)
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (y : ℝ) * (z ^ omega d / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
          field_simp [hdne]
    _ = (y : ℝ) *
          ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
          rw [Finset.mul_sum]

lemma squarefree_zpow_omega_div_eq_primeSupport_prod
    (z : ℝ) {d : ℕ} (hsq : Squarefree d) :
    z ^ omega d / (d : ℝ) =
      ∏ p ∈ primeSupport d, z / (p : ℝ) := by
  classical
  have hprod_nat : ∏ p ∈ primeSupport d, p = d := by
    rw [primeSupport_eq_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hsq
  have hprod_real : (d : ℝ) = ∏ p ∈ primeSupport d, (p : ℝ) := by
    calc
      (d : ℝ) = ((∏ p ∈ primeSupport d, p : ℕ) : ℝ) := by
        exact_mod_cast hprod_nat.symm
      _ = ∏ p ∈ primeSupport d, (p : ℝ) := by
        norm_num
  have hpow : z ^ omega d = ∏ p ∈ primeSupport d, z := by
    simp [omega, Finset.prod_const]
  calc
    z ^ omega d / (d : ℝ)
        = (∏ p ∈ primeSupport d, z) / (∏ p ∈ primeSupport d, (p : ℝ)) := by
          rw [hpow, hprod_real]
    _ = ∏ p ∈ primeSupport d, z / (p : ℝ) := by
          rw [Finset.prod_div_distrib]

private lemma primeSupport_subset_primesUpTo_of_le
    {d y : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
    primeSupport d ⊆ (Finset.Icc 1 y).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter]
  have hpPrime : Nat.Prime p := prime_of_mem_primeSupport hp
  have hp_pf : p ∈ d.primeFactors := by
    simpa [primeSupport_eq_primeFactors] using hp
  have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_pf
  have hp_le_d : p ≤ d :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hd1) hpdvd
  exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hp_le_d.trans hdy⟩, hpPrime⟩

lemma squarefree_recip_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ)) ≤
      ((Finset.Icc 1 y).filter Nat.Prime).prod
        (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 y).filter Squarefree
  let P : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let term : Finset ℕ → ℝ := fun T => (∏ p ∈ T, z / (p : ℝ))
  have hinj :
      ∀ d ∈ S, ∀ e ∈ S, primeSupport d = primeSupport e → d = e := by
    intro d hd e he hsupport
    simp [S] at hd he
    have hdprod : ∏ p ∈ primeSupport d, p = d := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree hd.2
    have heprod : ∏ p ∈ primeSupport e, p = e := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree he.2
    calc
      d = ∏ p ∈ primeSupport d, p := hdprod.symm
      _ = ∏ p ∈ primeSupport e, p := by rw [hsupport]
      _ = e := heprod
  have himage_subset : S.image primeSupport ⊆ P.powerset := by
    intro T hT
    rw [Finset.mem_powerset]
    rcases Finset.mem_image.mp hT with ⟨d, hdS, rfl⟩
    simp [S] at hdS
    have hdIcc := hdS.1
    exact primeSupport_subset_primesUpTo_of_le hdIcc.1 hdIcc.2
  have hterm_nonneg :
      ∀ T ∈ P.powerset, 0 ≤ term T := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine Finset.prod_nonneg ?_
    intro p hpT
    have hpP : p ∈ P := hT hpT
    simp [P] at hpP
    have hpPrime : Nat.Prime p := hpP.2
    exact div_nonneg hz (by exact_mod_cast hpPrime.pos.le)
  calc
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ))
        = ∑ d ∈ S, term (primeSupport d) := by
          apply Finset.sum_congr
          · simp [S]
          · intro d hd
            simp [S] at hd
            exact squarefree_zpow_omega_div_eq_primeSupport_prod z hd.2
    _ = ∑ T ∈ S.image primeSupport, term T := by
          rw [Finset.sum_image]
          intro d hd e he hsupport
          exact hinj d hd e he hsupport
    _ ≤ ∑ T ∈ P.powerset, term T := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
            (by
              intro T hTP _hnot
              exact hterm_nonneg T hTP)
    _ = P.prod (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rw [Finset.prod_one_add]
    _ = ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rfl

lemma omega_weighted_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  exact (omega_weighted_sum_le_squarefree_recip_sum y z hz).trans
    (mul_le_mul_of_nonneg_left
      (squarefree_recip_sum_le_euler_product y z hz)
      (by positivity))

lemma eventually_primeCounting_nat_le_const_log :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
  refine ⟨Real.log 4 + 1, ?_, ?_⟩
  · have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · have hreal :
        ∀ᶠ x : ℝ in atTop,
          (Nat.primeCounting (Nat.floor x) : ℝ) ≤
            (Real.log 4 + 1) * x / Real.log x :=
      Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
    have hnat := tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat] with n hn
    simpa using hn

lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h :=
    Real.one_sub_inv_le_log_of_pos
      (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

lemma harmonic_Icc_one_le_one_add_log (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (m : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        have htop_not : m + 1 ∉ Finset.Icc 1 m := by
          simp
        have hIcc :
            Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k
          simp
          omega
        have hterm := one_div_nat_succ_le_log_succ_sub_log (m := m) hm
        calc
          (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
              = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
                  (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                    rw [hIcc, Finset.sum_insert htop_not]
                    ring
          _ ≤ (1 + Real.log (m : ℝ)) +
                (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
          _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
                  linarith
          _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
                  rfl

lemma primeCounting_eq_card_Icc_filter_prime (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  have hset :
      (Finset.Icc 1 n).filter Nat.Prime =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      have hpIcc := Finset.mem_Icc.mp hp.1
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpIcc.2), hp.2⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_Icc.mpr
        ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card
        = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
    _ = Nat.count Nat.Prime (n + 1) := by
          exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
    _ = Nat.primeCounting n := rfl

lemma reciprocal_prime_sum_Ico_pow_two_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
  classical
  let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
    intro p hp
    simp [S] at hp
    have hlow_nat : 2 ^ k ≤ p := hp.1.1
    have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast hlow_nat
    exact one_div_le_one_div_of_le hdenpos hlow
  have hcard_le :
      S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
    rw [← primeCounting_eq_card_Icc_filter_prime]
    refine Finset.card_le_card ?_
    intro p hp
    simp [S] at hp
    rw [Finset.mem_filter]
    have hpIco := hp.1
    have hpPrime : Nat.Prime p := hp.2
    exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpIco.2.le⟩, hpPrime⟩
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hdenpos.le

lemma reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound
    (B : ℝ) {k : ℕ}
    (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
      B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
        Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
            ((2 ^ k : ℕ) : ℝ) :=
          reciprocal_prime_sum_Ico_pow_two_le k
    _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
          Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
            ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hπ hdenpos.le
    _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
          have hpow_succ :
              (((2 ^ (k + 1) : ℕ) : ℝ)) =
                (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
            norm_num [pow_succ, mul_comm]
          have hlog_pow :
              Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
                ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
            rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
            rw [Real.log_pow]
          rw [hlog_pow, hpow_succ]
          field_simp [hdenpos.ne', hlog2pos.ne', hkpos.ne']

lemma eventually_reciprocal_prime_sum_Ico_pow_two_le_const :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  rcases eventually_primeCounting_nat_le_const_log with ⟨B, hBpos, hBbound⟩
  refine ⟨2 * B / Real.log 2, ?_, ?_⟩
  · positivity
  · have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hBpow := hpw.eventually hBbound
    filter_upwards [hBpow] with k hk
    exact reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound B hk

lemma reciprocal_prime_sum_Ico_pow_two_le_const_global :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  classical
  rcases eventually_reciprocal_prime_sum_Ico_pow_two_le_const with
    ⟨D, hDpos, hDevent⟩
  rcases eventually_atTop.1 hDevent with ⟨K, hK⟩
  let block : ℕ → ℝ := fun k =>
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)
  let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
  refine ⟨D + extra + 1, ?_, ?_⟩
  · have hextra_nonneg : 0 ≤ extra := by
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (by positivity)
        (by
          refine Finset.sum_nonneg ?_
          intro p hp
          exact div_nonneg zero_le_one (by positivity))
    linarith
  · intro k
    have hdenpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    by_cases hlarge : K ≤ k
    · have hDle : D ≤ D + extra + 1 := by
        have hextra_nonneg : 0 ≤ extra := by
          refine Finset.sum_nonneg ?_
          intro j hj
          exact mul_nonneg (by positivity)
            (by
              refine Finset.sum_nonneg ?_
              intro p hp
              exact div_nonneg zero_le_one (by positivity))
        linarith
      calc
        block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k hlarge
        _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hDle hdenpos.le
    · have hkle : k ≤ K := Nat.le_of_not_ge hlarge
      have hk_mem : k ∈ Finset.Icc 0 K := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
        intro j hj
        exact mul_nonneg (by positivity)
          (by
            refine Finset.sum_nonneg ?_
            intro p hp
            exact div_nonneg zero_le_one (by positivity))
      have hsingle :
          ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
        Finset.single_le_sum hterm_nonneg hk_mem
      have hmul :
          block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
        calc
          block k * ((k + 1 : ℕ) : ℝ)
              = ((k + 1 : ℕ) : ℝ) * block k := by ring
          _ ≤ extra := hsingle
          _ ≤ D + extra + 1 := by linarith
      exact (le_div_iff₀ hdenpos).2 hmul

lemma reciprocal_prime_sum_le_dyadic_harmonic
    (D : ℝ)
    (hD : ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ))
    (N : ℕ) :
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
      ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  let T : Finset ℕ := Finset.Icc 0 (Nat.log 2 N)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    simp [S, T] at hp ⊢
    exact Nat.log_mono_right hp.1.2
  have hdecomp :
      ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (1 : ℝ) / (p : ℝ))
  have hfiber_le :
      ∀ k ∈ T,
        (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
            (1 : ℝ) / (p : ℝ)) ≤
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      simp [S] at hp ⊢
      have hpPrime : Nat.Prime p := hp.1.2
      have hpne : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hp.2
      exact ⟨⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
        by simpa [hlog, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩, hpPrime⟩
    · intro p hp _hnot
      exact div_nonneg zero_le_one (by positivity)
  have hsum_blocks :
      ∑ k ∈ T,
        (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ))
        ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := by
    exact Finset.sum_le_sum (fun k hk => hD k)
  have hsum_shift :
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
    have himage :
        T.image (fun k : ℕ => k + 1) = Finset.Icc 1 (Nat.log 2 N + 1) := by
      ext j
      simp [T]
    have hinj : Set.InjOn (fun k : ℕ => k + 1) T := by
      intro a ha b hb hab
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    have hsum_image :
        (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
          = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    calc
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
          = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
            exact hsum_image.symm
      _ = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
            rw [himage]
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ) := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ)) :=
          Finset.sum_le_sum hfiber_le
    _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := hsum_blocks
    _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
          rw [hsum_shift]
    _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (harmonic_Icc_one_le_one_add_log (Nat.log 2 N + 1))
            (by
              have hD0 := hD 0
              have hblock0_nonneg :
                  0 ≤
                    (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
                      (1 : ℝ) / (p : ℝ)) := by
                refine Finset.sum_nonneg ?_
                intro p hp
                exact div_nonneg zero_le_one (by positivity)
              have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
              nlinarith [hD0, hblock0_nonneg])

lemma eventually_one_add_log_nat_log_le_two_loglog :
    ∀ᶠ N : ℕ in atTop,
      1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ 2 * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := 2 / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hloglog_large :
      ∀ᶠ N : ℕ in atTop,
        1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually_ge_atTop (1 + Real.log C)
  filter_upwards [hloglog_large,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hll_large hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog2_lt_one : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
  have hlog2_le_logN : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
  have hquot_ge_one : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      simpa using hlog2_le_logN
    exact (le_div_iff₀ hlog2pos).2 this
  have hlog_nat_le :
      ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  have hnatlog_add_le :
      (((Nat.log 2 N + 1 : ℕ) : ℝ)) ≤ C * Real.log (N : ℝ) := by
    calc
      (((Nat.log 2 N + 1 : ℕ) : ℝ))
          = ((Nat.log 2 N : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
      _ ≤ Real.log (N : ℝ) / Real.log 2 +
            Real.log (N : ℝ) / Real.log 2 := by linarith
      _ = C * Real.log (N : ℝ) := by
            dsimp [C]
            ring
  have hleft_pos : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
  have hright_pos : 0 < C * Real.log (N : ℝ) := mul_pos hCpos hlogpos
  have hlog_bound :
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
          ≤ Real.log (C * Real.log (N : ℝ)) :=
            Real.log_le_log hleft_pos hnatlog_add_le
      _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
            rw [Real.log_mul hCpos.ne' hlogpos.ne']
  linarith

theorem reciprocal_prime_sum_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter Nat.Prime).sum
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ A * Real.log (Real.log (N : ℝ)) + C := by
  rcases reciprocal_prime_sum_Ico_pow_two_le_const_global with ⟨D, hDpos, hD⟩
  refine ⟨2 * D, 0, by positivity, ?_⟩
  filter_upwards [eventually_one_add_log_nat_log_le_two_loglog] with N hloglog
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
          reciprocal_prime_sum_le_dyadic_harmonic D hD N
    _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hloglog hDpos.le
    _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring

theorem omega_weighted_sum_euler_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) *
              Real.exp (BFVz N *
                (A * Real.log (Real.log (N : ℝ)) + C)) := by
  rcases reciprocal_prime_sum_mertens with ⟨A, C, hA, hMertens⟩
  refine ⟨A, C, hA, ?_⟩
  filter_upwards [hMertens,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hMertensN hNlarge_nat
  intro y hy
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg (Real.sqrt_nonneg _) hloglog_pos.le
  let Py : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let PN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hPy_subset : Py ⊆ PN := by
    intro p hp
    simp [Py, PN] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hy⟩, hp.2⟩
  have hsum_y_le_N :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        PN.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hPy_subset
      (by
        intro p hpN _hpnot
        simp [PN] at hpN
        exact div_nonneg zero_le_one (by exact_mod_cast hpN.2.pos.le))
  have hsum_y_bound :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        A * Real.log (Real.log (N : ℝ)) + C := by
    exact hsum_y_le_N.trans (by simpa [PN] using hMertensN)
  have hpos_p : ∀ p ∈ Py, 0 < (p : ℝ) := by
    intro p hp
    simp [Py] at hp
    exact_mod_cast hp.2.pos
  have hprod_exp :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
    finite_euler_product_one_add_le_exp_sum Py hz_nonneg hpos_p
  have hprod_bound :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          (A * Real.log (Real.log (N : ℝ)) + C)) := by
    exact hprod_exp.trans
      (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left hsum_y_bound hz_nonneg))
  exact (omega_weighted_sum_le_euler_product y (BFVz N) hz_nonneg).trans
    (mul_le_mul_of_nonneg_left (by simpa [Py] using hprod_bound) (by positivity))

lemma BFVz_linear_loglog_exponent_le_Zscale
    (A C ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤ ε * Zscale N := by
  let R : ℝ := max (4 * (A + 1) / ε) (max 1 |C|)
  filter_upwards [eventually_sqrt_loglog_ge R,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hA1_pos : 0 < A + 1 := by linarith
  have hR_ge_main : 4 * (A + 1) / ε ≤ R := le_max_left _ _
  have hR_ge_one : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR_ge_abs : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt_ge_main :
      4 * (A + 1) / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_main.trans hsqrt
  have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_one.trans hsqrt
  have hsqrt_ge_abs : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_abs.trans hsqrt
  have hloglog_ge_abs : |C| ≤ Real.log (Real.log (N : ℝ)) := by
    calc
      |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := hsqrt_ge_abs
      _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
      _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt hloglog_nonneg
  have hmain_sqrt :
      2 * (A + 1) ≤
        ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have hfour :
        4 * (A + 1) ≤
          ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hε).1 hsqrt_ge_main
    linarith
  have hBFVz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg hsqrtlog_nonneg hloglog_nonneg
  have hlinear_le :
      A * Real.log (Real.log (N : ℝ)) + C ≤
        (A + 1) * Real.log (Real.log (N : ℝ)) := by
    calc
      A * Real.log (Real.log (N : ℝ)) + C
          ≤ A * Real.log (Real.log (N : ℝ)) + |C| := by
            nlinarith [le_abs_self C]
      _ ≤ A * Real.log (Real.log (N : ℝ)) +
            Real.log (Real.log (N : ℝ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hloglog_ge_abs
                (A * Real.log (Real.log (N : ℝ)))
      _ = (A + 1) * Real.log (Real.log (N : ℝ)) := by ring
  have hwith_bound :
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤
        BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hlinear_le hBFVz_nonneg
  have hZeq := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hbound :
      BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) ≤
        ε * Zscale N := by
    rw [BFVz, hZeq]
    calc
      Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
          ((A + 1) * Real.log (Real.log (N : ℝ)))
          = (A + 1) * Real.sqrt (Real.log (N : ℝ)) := by
            field_simp [hloglog_pos.ne']
      _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
            Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
            calc
              (A + 1) * Real.sqrt (Real.log (N : ℝ))
                  ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                      Real.sqrt (Real.log (N : ℝ)) := by
                        exact mul_le_mul_of_nonneg_right
                          (by linarith [hmain_sqrt]) hsqrtlog_nonneg
              _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
                    Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
  exact hwith_bound.trans hbound

theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N) := by
  intro ε hε
  rcases omega_weighted_sum_euler_mertens with ⟨A, C, hA, hC⟩
  filter_upwards [hC, BFVz_linear_loglog_exponent_le_Zscale A C ε hA hε]
    with N hAnalytic hExp y hy
  have hExp_le :
      Real.exp (BFVz N * (A * Real.log (Real.log (N : ℝ)) + C)) ≤
        Real.exp (ε * Zscale N) :=
    Real.exp_le_exp.2 hExp
  exact (hAnalytic y hy).trans
    (mul_le_mul_of_nonneg_left hExp_le (by positivity))

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
lemma card_le_floor_of_natCast_le {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
  (Nat.le_floor_iff hx).2 hm

lemma rankin_omega_tail_sum_le (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
  classical
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  calc
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
        = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ omega n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact pow_le_pow_right₀ hz (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro n _hnIcc hnNotFilter
          exact pow_nonneg hz0 (omega n)

lemma omega_tail_card_real_le_of_sum_le
    (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
      ≤ (y : ℝ) * B / z ^ t := by
  classical
  have hzpow_pos : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
  have htail := rankin_omega_tail_sum_le y t hz
  have hmul_le : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ (y : ℝ) * B :=
    htail.trans hSum
  exact (le_div_iff₀ hzpow_pos).2 hmul_le

lemma omega_tail_card_le_floor_of_sum_le
    (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
    (hX : 0 ≤ X)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
    (hRankinTarget : (y : ℝ) * B / z ^ t ≤ X) :
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
  refine card_le_floor_of_natCast_le hX ?_
  exact (omega_tail_card_real_le_of_sum_le y t hz hSum).trans hRankinTarget

private lemma tendsto_logloglog_div_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
        Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma eventually_logloglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (Real.log (Real.log (N : ℝ))) /
          Real.log (Real.log (N : ℝ)) < δ :=
    tendsto_logloglog_div_loglog_nat_atTop.eventually_lt_const hδ
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  exact ((div_lt_iff₀ hloglog_pos).1 hsmallN).le

private lemma BFVz_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < BFVz N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [BFVz]
  exact div_pos (Real.sqrt_pos.2 hlog_pos) hloglog_pos

private lemma eventually_BFVz_log_lower
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (BFVz N) := by
  filter_upwards [eventually_logloglog_le_mul_loglog δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlll hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlog_pos
  have hlog_BFVz :
      Real.log (BFVz N) =
        Real.log (Real.log (N : ℝ)) / 2 -
          Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [BFVz, Real.log_div hsqrt_pos.ne' hloglog_pos.ne',
      Real.log_sqrt hlog_nonneg]
  rw [hlog_BFVz]
  nlinarith

private lemma eventually_BFVz_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ BFVz N := by
  filter_upwards [eventually_BFVz_log_lower ((1 : ℝ) / 4) (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hlog_nonneg : 0 ≤ Real.log (BFVz N) := by
    nlinarith
  have hone : Real.exp 0 ≤ BFVz N :=
    (Real.le_log_iff_exp_le hzpos).1 hlog_nonneg
  simpa using hone

private lemma eventually_rankin_factor_le
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
        Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          ≤ Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  let δ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_BFVz_log_lower δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat t ht
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hLL :
      Real.log (Real.log (N : ℝ)) = Zscale N / Mscale N :=
    (Zscale_div_Mscale_eq_loglog hNlarge).symm
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  have hlog_mul :
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
        ≤ (t : ℝ) * Real.log (BFVz N) :=
    mul_le_mul_of_nonneg_left hlog_lower ht_nonneg
  have ht_div_le : (t : ℝ) / Mscale N ≤ 3 := by
    exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
  have hdelta_div : δ * ((t : ℝ) / Mscale N) ≤ ε / 2 := by
    calc
      δ * ((t : ℝ) / Mscale N) ≤ δ * 3 := by
        exact mul_le_mul_of_nonneg_left ht_div_le hδ.le
      _ = ε / 2 := by
        dsimp [δ]
        ring
  have hexp_le :
      (ε / 2) * Zscale N - (t : ℝ) * Real.log (BFVz N)
        ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
    have hmain :
        (ε / 2) * Zscale N -
            (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
          ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
      rw [hLL]
      have hdeltaZ :
          (δ * ((t : ℝ) / Mscale N)) * Zscale N ≤ (ε / 2) * Zscale N :=
        mul_le_mul_of_nonneg_right hdelta_div hZnonneg
      have hrewrite :
          (t : ℝ) * (((1 : ℝ) / 2 - δ) * (Zscale N / Mscale N)) =
            (((1 : ℝ) / 2 - δ) * ((t : ℝ) / Mscale N)) * Zscale N := by
        field_simp [hMpos.ne']
      rw [hrewrite]
      nlinarith
    nlinarith
  have hzpow :
      (BFVz N) ^ t = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
    calc
      (BFVz N) ^ t = (Real.exp (Real.log (BFVz N))) ^ t := by
        rw [Real.exp_log hzpos]
      _ = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
        rw [← Real.exp_nat_mul]
  rw [hzpow, ← Real.exp_sub]
  exact Real.exp_le_exp.2 hexp_le

theorem bfv_omega_tail_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * Mscale N →
        let α : ℝ := (t : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [omega_weighted_sum_bfvz_bound (ε / 2) hε2,
      eventually_rankin_factor_le ε hε, eventually_BFVz_ge_one]
    with N hWeighted hRankin hBFVz_ge_one
  intro y t hy ht
  dsimp only
  refine omega_tail_card_le_floor_of_sum_le (y := y) (t := t)
    (z := BFVz N) (B := Real.exp ((ε / 2) * Zscale N))
    (X := (y : ℝ) *
      Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    hBFVz_ge_one ?_ (hWeighted y hy) ?_
  · positivity
  · have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
    calc
      (y : ℝ) * Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          = (y : ℝ) *
              (Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t) := by
              ring
      _ ≤ (y : ℝ) *
              Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
              exact mul_le_mul_of_nonneg_left (hRankin t ht) hy_nonneg

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open Asymptotics
open scoped BigOperators
lemma Zscale_eq_exp_half_loglog_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set Y := Real.log (Real.log (N : ℝ))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_eq : Real.log (N : ℝ) = Real.exp Y := by
    dsimp [Y]
    rw [Real.exp_log hlog_pos]
  have hsqrt_log :
      Real.sqrt (Real.log (N : ℝ)) = Real.exp (Y / 2) := by
    rw [hlog_eq, ← Real.exp_half]
  rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge, hsqrt_log]

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
end BFVPruning1190
namespace BFVPruning1190
open Filter
end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
structure PrunedData (N : ℕ) where
  Q : Finset ℕ
  Q_nonempty : Q.Nonempty
  a : ResidueAssignment Q
  admissible : Admissible N Q
  pairwise_disjoint : PairwiseDisjointResidues Q a
  K : ℕ
  K_pos : 1 ≤ K
  modulus_lower : ∀ q ∈ Q, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ)
  modulus_upper : ∀ q ∈ Q, q ≤ N
  hExp_bound : ∀ q ∈ Q, (hExp q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
  omega_eq : ∀ q ∈ Q, omega q = K
  K_bound : (K : ℝ) ≤ 3 * Mscale N
  rad_injective : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r

lemma PrunedData.card_pos {N : ℕ} (D : PrunedData N) : 0 < D.Q.card :=
  D.Q_nonempty.card_pos

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
end BFVPruning1190
namespace BFVPruning1190
open Finset
open scoped BigOperators
lemma filter_large_of_bad_small {α : Type*} [DecidableEq α]
    (Q Bad : Finset α) {δ : ℝ}
    (hBad : Bad ⊆ Q)
    (hsmall : (Bad.card : ℝ) ≤ δ * (Q.card : ℝ)) :
    (((Q \ Bad).card : ℝ) ≥ (1 - δ) * (Q.card : ℝ)) := by
  have hreal : ((Q \ Bad).card : ℝ) = (Q.card : ℝ) - (Bad.card : ℝ) := by
    simpa using (Finset.cast_card_sdiff (R := ℝ) hBad)
  rw [hreal]
  nlinarith

lemma filter_large_of_three_bad_small {α : Type*} [DecidableEq α]
    (Q Bad₁ Bad₂ Bad₃ : Finset α) {δ₁ δ₂ δ₃ : ℝ}
    (hBad₁ : Bad₁ ⊆ Q) (hBad₂ : Bad₂ ⊆ Q) (hBad₃ : Bad₃ ⊆ Q)
    (hsmall₁ : (Bad₁.card : ℝ) ≤ δ₁ * (Q.card : ℝ))
    (hsmall₂ : (Bad₂.card : ℝ) ≤ δ₂ * (Q.card : ℝ))
    (hsmall₃ : (Bad₃.card : ℝ) ≤ δ₃ * (Q.card : ℝ)) :
    (((Q \ (Bad₁ ∪ Bad₂ ∪ Bad₃)).card : ℝ) ≥
      (1 - (δ₁ + δ₂ + δ₃)) * (Q.card : ℝ)) := by
  have hBad : Bad₁ ∪ Bad₂ ∪ Bad₃ ⊆ Q := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx12 | hx3
    · rcases Finset.mem_union.1 hx12 with hx1 | hx2
      · exact hBad₁ hx1
      · exact hBad₂ hx2
    · exact hBad₃ hx3
  refine filter_large_of_bad_small Q (Bad₁ ∪ Bad₂ ∪ Bad₃) hBad ?_
  have hcard_nat :
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card ≤ Bad₁.card + Bad₂.card + Bad₃.card := by
    calc
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card
          ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
      _ ≤ (Bad₁.card + Bad₂.card) + Bad₃.card := by
            exact Nat.add_le_add_right (Finset.card_union_le Bad₁ Bad₂) Bad₃.card
      _ = Bad₁.card + Bad₂.card + Bad₃.card := by omega
  have hcard_real :
      ((Bad₁ ∪ Bad₂ ∪ Bad₃).card : ℝ) ≤
        (Bad₁.card : ℝ) + (Bad₂.card : ℝ) + (Bad₃.card : ℝ) := by
    exact_mod_cast hcard_nat
  nlinarith

lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

noncomputable def chooseOnePerImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) : Finset α :=
  ((s.image g).attach.image fun b =>
    Classical.choose (Finset.mem_image.1 b.2))

lemma chooseOnePerImage_subset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    chooseOnePerImage s g ⊆ s := by
  classical
  intro x hx
  unfold chooseOnePerImage at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨b, -, rfl⟩
  exact (Classical.choose_spec (Finset.mem_image.1 b.2)).1

lemma chooseOnePerImage_maps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) {b : β} (hb : b ∈ s.image g) :
    g (Classical.choose (Finset.mem_image.1 hb)) = b := by
  exact (Classical.choose_spec (Finset.mem_image.1 hb)).2

lemma chooseOnePerImage_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    ∀ x ∈ chooseOnePerImage s g, ∀ y ∈ chooseOnePerImage s g, g x = g y → x = y := by
  classical
  intro x hx y hy hxy
  unfold chooseOnePerImage at hx hy
  rw [Finset.mem_image] at hx
  rw [Finset.mem_image] at hy
  rcases hx with ⟨bx, hbx, rfl⟩
  rcases hy with ⟨byy, hby, rfl⟩
  have hbxval : g (Classical.choose (Finset.mem_image.1 bx.2)) = bx.1 := by
    exact chooseOnePerImage_maps s g bx.2
  have hbyval : g (Classical.choose (Finset.mem_image.1 byy.2)) = byy.1 := by
    exact chooseOnePerImage_maps s g byy.2
  have hbxy : bx = byy := by
    ext
    simpa [hbxval, hbyval] using hxy
  subst hbxy
  rfl

lemma chooseOnePerImage_card_eq_image_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    (chooseOnePerImage s g).card = (s.image g).card := by
  classical
  unfold chooseOnePerImage
  calc
    (((s.image g).attach.image fun b =>
        Classical.choose (Finset.mem_image.1 b.2))).card =
        (s.image g).attach.card := by
          apply Finset.card_image_of_injective
          intro b₁ b₂ h
          have hb₁ : g (Classical.choose (Finset.mem_image.1 b₁.2)) = b₁.1 :=
            chooseOnePerImage_maps s g b₁.2
          have hb₂ : g (Classical.choose (Finset.mem_image.1 b₂.2)) = b₂.1 :=
            chooseOnePerImage_maps s g b₂.2
          ext
          simpa [hb₁, hb₂] using congrArg g h
    _ = (s.image g).card := by simp

lemma image_card_mul_fiber_bound_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    s.card ≤ C * (s.image g).card := by
  classical
  exact Finset.card_le_mul_card_image s C hC

lemma choose_one_per_fiber_card_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    ∃ s' : Finset α,
      s' ⊆ s ∧
      (∀ x ∈ s', ∀ y ∈ s', g x = g y → x = y) ∧
      s.card ≤ C * s'.card := by
  classical
  refine ⟨chooseOnePerImage s g, chooseOnePerImage_subset s g,
    chooseOnePerImage_injOn s g, ?_⟩
  simpa [chooseOnePerImage_card_eq_image_card s g] using
    image_card_mul_fiber_bound_ge s g C hC

end BFVPruning1190
namespace BFVPruning1190
open Finset
open scoped BigOperators
lemma sum_inv_sq_le_two_bfv (H : ℕ) :
    (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ H : ℕ, 1 ≤ H →
      (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (H : ℝ) := by
    intro H hH
    induction H with
    | zero =>
        cases hH
    | succ H ih =>
        cases H with
        | zero =>
            norm_num
        | succ H =>
            rw [Finset.sum_range_succ]
            have ih' :
                (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  ≤ 2 - 1 / ((H + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
                  1 / ((H + 1 : ℕ) : ℝ) -
                    1 / (((H + 1 + 1 : ℕ) : ℝ)) := by
              have hcast :
                  (((H + 1 + 1 : ℕ) : ℝ)) = ((H + 1 : ℕ) : ℝ) + 1 := by
                norm_num
              rw [hcast]
              have hH1 : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
              have hH2 : 0 < ((H + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hH1.ne', hH2.ne']
              ring_nf
              nlinarith [show 0 ≤ (H : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  + 1 / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2
                  ≤ (2 - 1 / ((H + 1 : ℕ) : ℝ))
                      + (1 / ((H + 1 : ℕ) : ℝ) -
                        1 / (((H + 1 + 1 : ℕ) : ℝ))) := by
                    gcongr
              _ = 2 - 1 / ((H + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hH : H = 0
  · simp [hH]
  · have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
    exact (hstrong H hH1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod_bfv {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos (fun p hp => (prime_of_mem_primeSupport hp).pos)

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 :=
  (rad_pos n).ne'

lemma primeSupport_rad_of_ne_zero {n : ℕ} (_hn : n ≠ 0) :
    primeSupport (rad n) = primeSupport n := by
  classical
  ext p
  constructor
  · intro hpRad
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpRad
    have hpdvd : p ∣ rad n := Nat.dvd_of_factorization_pos (by
      unfold primeSupport at hpRad
      exact Finsupp.mem_support_iff.1 hpRad)
    unfold rad at hpdvd
    rcases (hp.prime.dvd_finset_prod_iff
        (S := primeSupport n) (fun x : ℕ => x)).1 hpdvd with ⟨q, hq, hpq⟩
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
    have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).1 hpq
    simpa [hqp] using hq
  · intro hpN
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpN
    have hpdvd : p ∣ rad n := by
      unfold rad
      exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hpN
    exact mem_primeSupport_of_prime_dvd hp (rad_ne_zero n) hpdvd

lemma primeSupport_eq_of_rad_eq {q r : ℕ} (hq : q ≠ 0) (hqr : rad q = r) :
    primeSupport q = primeSupport r := by
  rw [← primeSupport_rad_of_ne_zero hq, hqr]

private lemma factorization_le_hExp_of_mem {q p : ℕ} (hp : p ∈ primeSupport q) :
    q.factorization p ≤ hExp q := by
  have hdvd : q.factorization p ∣ hExp q := by
    unfold hExp
    exact Finset.dvd_prod_of_mem (fun x : ℕ => q.factorization x) hp
  exact Nat.le_of_dvd (hExp_pos q) hdvd

private lemma rad_multiplicity_weight_sum_le
    (S : Finset ℕ) (C : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hSupp : ∀ q ∈ S, primeSupport q = C)
    (hHbound : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range (Nat.floor H)
  let vec : ℕ → Index → ℕ := fun q p => q.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hH_nonneg : 0 ≤ H := by
    linarith
  have hvec_mem : ∀ q ∈ S, vec q ∈ E := by
    intro q hqS
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport q = C := hSupp q hqS
    have hpSupport : p.1 ∈ primeSupport q := by
      simp [hsupport, p.2]
    have hfac_pos : 1 ≤ q.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_hExp : q.factorization p.1 ≤ hExp q :=
      factorization_le_hExp_of_mem hpSupport
    have hfac_le_H : ((q.factorization p.1 : ℕ) : ℝ) ≤ H := by
      have hfac_le_hExp_real :
          ((q.factorization p.1 : ℕ) : ℝ) ≤ (hExp q : ℝ) := by
        exact_mod_cast hfac_le_hExp
      exact hfac_le_hExp_real.trans (hHbound q hqS)
    have hfac_floor : q.factorization p.1 ≤ Nat.floor H :=
      (Nat.le_floor_iff hH_nonneg).2 hfac_le_H
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec S := by
    intro q hqS q' hq'S hqq'
    apply Nat.eq_of_factorization_eq (hSpos q hqS) (hSpos q' hq'S)
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hqq' ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hsupport : primeSupport q = C := hSupp q hqS
      have hsupport' : primeSupport q' = C := hSupp q' hq'S
      have hfac_pos : 1 ≤ q.factorization p := by
        have hpSupport : p ∈ primeSupport q := by simpa [hsupport] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hfac_pos' : 1 ≤ q'.factorization p := by
        have hpSupport : p ∈ primeSupport q' := by simpa [hsupport'] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpq : p ∉ primeSupport q := by simpa [hSupp q hqS] using hp
      have hpq' : p ∉ primeSupport q' := by simpa [hSupp q' hq'S] using hp
      rw [Finsupp.notMem_support_iff.1 hpq, Finsupp.notMem_support_iff.1 hpq']
  have hterm_eq :
      ∀ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) = term (vec q) := by
    intro q hqS
    have hsupport : primeSupport q = C := hSupp q hqS
    have hhexp :
        hExp q = ∏ p : Index, q.factorization p.1 := by
      calc
        hExp q = ∏ p ∈ C, q.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, q.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec q p + 1 = q.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport q := by simp [hsupport, p.2]
      have hpos : 1 ≤ q.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod_bfv]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2))
        = ∑ q ∈ S, term (vec q) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hterm_eq q hq
    _ = ∑ e ∈ S.image vec, term e := by
            rw [Finset.sum_image]
            intro q hq q' hq' hEq
            exact hvec_inj hq hq' hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
                exact hvec_mem q hq)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range (Nat.floor H),
            (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset
                  (fun _ : Index => Finset.range (Nat.floor H)),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range (Nat.floor H),
                  (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range (Nat.floor H))
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                exact sum_inv_sq_le_two_bfv (Nat.floor H))
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

theorem rad_multiplicity_bfv33
    (S : Finset ℕ) (r K : ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H) :
    (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K := by
  classical
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨q0, hq0S⟩
    let C : Finset ℕ := primeSupport r
    have hSupp : ∀ q ∈ S, primeSupport q = C := by
      intro q hq
      exact primeSupport_eq_of_rad_eq (hSpos q hq) (hS q hq).1
    have hCcard : C.card = K := by
      have homega := (hS q0 hq0S).2.1
      unfold omega at homega
      rw [hSupp q0 hq0S] at homega
      exact homega
    have hWeighted :
        (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ K := by
      simpa [C, hCcard] using
        rad_multiplicity_weight_sum_le S C H hH hSpos hSupp
          (fun q hq => (hS q hq).2.2)
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hHsq_pos : 0 < H ^ 2 := by positivity
    have hTermLower :
        ∀ q ∈ S, (1 : ℝ) / (H ^ 2) ≤
          (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
      intro q hq
      have hExp_nonneg : 0 ≤ (hExp q : ℝ) := by positivity
      have hExp_pos : 0 < (hExp q : ℝ) := by exact_mod_cast hExp_pos q
      have hExp_le : (hExp q : ℝ) ≤ H := (hS q hq).2.2
      have hsq_le : (hExp q : ℝ) ^ 2 ≤ H ^ 2 := by
        nlinarith [sq_nonneg (H - (hExp q : ℝ))]
      exact one_div_le_one_div_of_le (by positivity) hsq_le
    have hCardScaled :
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2)) ≤ (2 : ℝ) ^ K := by
      calc
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2))
            = ∑ _q ∈ S, ((1 : ℝ) / (H ^ 2)) := by
                simp
        _ ≤ ∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
                exact Finset.sum_le_sum hTermLower
        _ ≤ (2 : ℝ) ^ K := hWeighted
    have hmul := mul_le_mul_of_nonneg_right hCardScaled hHsq_pos.le
    field_simp [hHsq_pos.ne'] at hmul
    nlinarith
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSne
    have hnonneg : 0 ≤ H ^ 2 * (2 : ℝ) ^ K := by positivity
    simpa [hEmpty] using hnonneg

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
open scoped BigOperators
noncomputable def hExpCutoff (N : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (N : ℝ)))

lemma hExp_prime_pow {p e : ℕ} (hp : Nat.Prime p) :
    hExp (p ^ e) = if e = 0 then 1 else e := by
  by_cases he : e = 0
  · simp [he, hExp_one]
  · unfold hExp primeSupport
    rw [hp.factorization_pow]
    rw [Finsupp.support_single_ne_zero p he]
    rw [if_neg he]
    change (∏ q ∈ ({p} : Finset ℕ), Finsupp.single p e q) = e
    simp

noncomputable def hExpMomentTerm (s n : ℕ) : ℝ :=
  if n = 0 then 0 else (hExp n : ℝ) ^ s / (n : ℝ)

lemma hExpMomentTerm_nonneg (s n : ℕ) :
    0 ≤ hExpMomentTerm s n := by
  by_cases hn : n = 0
  · simp [hExpMomentTerm, hn]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp [hExpMomentTerm, hn]
    exact div_nonneg (by positivity) hnpos.le

lemma hExpMomentTerm_one (s : ℕ) : hExpMomentTerm s 1 = 1 := by
  simp [hExpMomentTerm, hExp_one]

lemma hExpMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    hExpMomentTerm s (p ^ e) =
      if e = 0 then 1 else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he : e = 0
  · rw [he, pow_zero, hExpMomentTerm_one]
    simp
  · simp [hExpMomentTerm, hExp_prime_pow hp, he, hp.ne_zero, Nat.cast_pow]

lemma hExpMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExpMomentTerm s (m * n) =
      hExpMomentTerm s m * hExpMomentTerm s n := by
  by_cases hmn : m * n = 0
  · rcases hcop.eq_of_mul_eq_zero hmn with h | h
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
  · have hm : m ≠ 0 := left_ne_zero_of_mul hmn
    have hn : n ≠ 0 := right_ne_zero_of_mul hmn
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [hExpMomentTerm, hmn, hm, hn, hExp_mul_of_coprime hcop,
      Nat.cast_mul, mul_pow]
    field_simp [hmreal, hnreal]

def squarefullSupport (n : ℕ) : Finset ℕ :=
  (primeSupport n).filter fun p => 2 ≤ n.factorization p

def squarefullKernel (n : ℕ) : ℕ :=
  exactBlock (squarefullSupport n) n

def IsSquarefull (n : ℕ) : Prop :=
  ∀ p ∈ primeSupport n, 2 ≤ n.factorization p

instance instDecidablePredIsSquarefull : DecidablePred IsSquarefull := by
  intro n
  unfold IsSquarefull
  infer_instance

lemma squarefullSupport_subset (n : ℕ) :
    squarefullSupport n ⊆ primeSupport n := by
  intro p hp
  exact (Finset.mem_filter.1 hp).1

lemma prime_of_mem_squarefullSupport {n p : ℕ}
    (hp : p ∈ squarefullSupport n) : Nat.Prime p :=
  prime_of_mem_primeSupport (squarefullSupport_subset n hp)

lemma squarefullKernel_dvd (n : ℕ) : squarefullKernel n ∣ n := by
  simp [squarefullKernel, exactBlock_dvd]

lemma primeSupport_squarefullKernel {n : ℕ} :
    primeSupport (squarefullKernel n) = squarefullSupport n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hn]
  · exact primeSupport_exactBlock
      (fun p hp => prime_of_mem_squarefullSupport hp)
      (squarefullSupport_subset n)

lemma squarefullKernel_isSquarefull (n : ℕ) :
    IsSquarefull (squarefullKernel n) := by
  intro p hp
  rw [primeSupport_squarefullKernel] at hp
  have hp' := Finset.mem_filter.1 hp
  change 2 ≤ (exactBlock (squarefullSupport n) n).factorization p
  rw [factorization_exactBlock_of_mem
    (C := squarefullSupport n)
    (q := n)
    (p := p)
    (fun r hr => prime_of_mem_squarefullSupport hr)
    hp]
  exact hp'.2

lemma isSquarefull_mul_iff_of_coprime {m n : ℕ}
    (hcop : Nat.Coprime m n) :
    IsSquarefull (m * n) ↔ IsSquarefull m ∧ IsSquarefull n := by
  constructor
  · intro hmn
    constructor
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_left _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hnzero] using htwo
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_right _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hmzero] using htwo
  · rintro ⟨hm, hn⟩ p hp
    rw [primeSupport_mul_of_coprime hcop] at hp
    rw [Nat.factorization_mul_of_coprime hcop]
    rcases Finset.mem_union.1 hp with hp | hp
    · have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hnzero] using hm p hp
    · have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hmzero, add_comm] using hn p hp

lemma hExp_squarefullKernel_eq (n : ℕ) :
    hExp (squarefullKernel n) = hExp n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hExp, hn]
  · unfold hExp
    rw [primeSupport_squarefullKernel]
    have hprod :
        (∏ p ∈ primeSupport n, n.factorization p) =
          ∏ p ∈ squarefullSupport n, n.factorization p := by
      refine (Finset.prod_subset (squarefullSupport_subset n) ?_).symm
      intro p hpPrime hpNot
      have hpos : 1 ≤ n.factorization p := by
        unfold primeSupport at hpPrime
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.1 hpPrime))
      have hnot_two : ¬ 2 ≤ n.factorization p := by
        intro htwo
        exact hpNot (Finset.mem_filter.2 ⟨hpPrime, htwo⟩)
      omega
    rw [hprod]
    apply Finset.prod_congr rfl
    intro p hp
    change (exactBlock (squarefullSupport n) n).factorization p =
      n.factorization p
    rw [factorization_exactBlock_of_mem
      (C := squarefullSupport n)
      (q := n)
      (p := p)
      (fun r hr => prime_of_mem_squarefullSupport hr)
      hp]

lemma squarefullKernel_mem_divisors {n : ℕ} (hn : n ≠ 0) :
    squarefullKernel n ∈ n.divisors := by
  exact Nat.mem_divisors.2
    ⟨squarefullKernel_dvd n, hn⟩

lemma hExp_pow_le_squarefull_divisor_sum (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (hExp n : ℝ) ^ s ≤
      ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
  classical
  have hmem :
      squarefullKernel n ∈ n.divisors.filter IsSquarefull := by
    exact Finset.mem_filter.2
      ⟨squarefullKernel_mem_divisors hn, squarefullKernel_isSquarefull n⟩
  have hterm :
      (hExp (squarefullKernel n) : ℝ) ^ s = (hExp n : ℝ) ^ s := by
    rw [hExp_squarefullKernel_eq]
  calc
    (hExp n : ℝ) ^ s = (hExp (squarefullKernel n) : ℝ) ^ s := hterm.symm
    _ ≤ ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s :=
        Finset.single_le_sum
          (fun d _hd => pow_nonneg (by positivity : 0 ≤ (hExp d : ℝ)) s)
          hmem

lemma nat_pow_le_factorial_mul_exp_quarter (s e : ℕ) :
    ((e : ℝ) ^ s) ≤
      (4 : ℝ) ^ s * (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
  have hx : 0 ≤ (e : ℝ) / 4 := by positivity
  have h := Real.pow_div_factorial_le_exp ((e : ℝ) / 4) hx s
  have hfac : ((s.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s
  have h1 :
      ((e : ℝ) / 4) ^ s ≤
        (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
    have hmul := mul_le_mul_of_nonneg_left h
      (by positivity : 0 ≤ (s.factorial : ℝ))
    field_simp [hfac] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    (e : ℝ) ^ s = (4 : ℝ) ^ s * ((e : ℝ) / 4) ^ s := by
      rw [div_pow]
      field_simp
    _ ≤ (4 : ℝ) ^ s *
          ((s.factorial : ℝ) * Real.exp ((e : ℝ) / 4)) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (4 : ℝ) ^ s * (s.factorial : ℝ) *
          Real.exp ((e : ℝ) / 4) := by
      ring

lemma exp_quarter_lt_three_halves :
    Real.exp ((1 : ℝ) / 4) < 3 / 2 := by
  have hpow_lt : Real.exp ((1 : ℝ) / 4) ^ 4 < ((3 : ℝ) / 2) ^ 4 := by
    calc
      Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < ((3 : ℝ) / 2) ^ 4 := by norm_num
  by_contra hnot
  have hge : (3 : ℝ) / 2 ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
  have hpow_ge :
      ((3 : ℝ) / 2) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2) hge 4
  exact not_lt_of_ge hpow_ge hpow_lt

lemma hExp_large_rankin_sum_le
    (N s : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
      ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
  classical
  let Bad := (Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)
  have hpoint :
      ∀ n ∈ Bad, H ^ s ≤ (hExp n : ℝ) ^ s := by
    intro n hn
    exact pow_le_pow_left₀ hH (le_of_lt (Finset.mem_filter.1 hn).2) s
  calc
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
        = ∑ n ∈ Bad, H ^ s := by
            simp [Bad, mul_comm]
    _ ≤ ∑ n ∈ Bad, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (by
                intro n _hn _hnot
                positivity)

lemma hExp_moment_sum_le_squarefull_divisor_multiple_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      ∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then
          (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
            (hExp d : ℝ) ^ s
        else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          exact hExp_pow_le_squarefull_divisor_sum s
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter
                (fun d => d ∣ n ∧ IsSquarefull d),
              (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter]
            rw [Finset.mem_filter] at hd
            have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd.1
            have hnIcc := Finset.mem_Icc.mp hn
            have hdle : d ≤ N :=
              (Nat.le_of_dvd
                (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩,
              hdn, hd.2⟩
          · intro d _hd _hnot
            positivity
    _ = ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
              (hExp d : ℝ) ^ s
          else 0 := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            calc
              (∑ x ∈ Finset.Icc 1 N,
                  if d ∣ x then (hExp d : ℝ) ^ s else 0)
                  = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
                      (hExp d : ℝ) ^ s := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                    (hExp d : ℝ) ^ s := by
                    simp [Finset.sum_const, nsmul_eq_mul]
          · simp [hsq]

lemma hExp_moment_sum_le_squarefull_recip_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then
              (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                (hExp d : ℝ) ^ s
            else 0 :=
          hExp_moment_sum_le_squarefull_divisor_multiple_sum N s
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            ((N : ℝ) / (d : ℝ)) * (hExp d : ℝ) ^ s
          else 0 := by
          refine Finset.sum_le_sum ?_
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
            have hcard_nat :
                ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
              exact card_Icc_filter_dvd_le_div N d hdpos
            have hcard_real :
                (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
                  (N : ℝ) / (d : ℝ) := by
              exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
            exact mul_le_mul_of_nonneg_right hcard_real (by positivity)
          · simp [hsq]
    _ = ∑ d ∈ Finset.Icc 1 N,
          (N : ℝ) *
            (if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdne : (d : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
            field_simp [hdne]
          · simp [hsq]
    _ = (N : ℝ) *
          ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
          rw [Finset.mul_sum]

noncomputable def squarefullMomentTerm (s n : ℕ) : ℝ :=
  if IsSquarefull n then hExpMomentTerm s n else 0

lemma squarefullMomentTerm_nonneg (s n : ℕ) :
    0 ≤ squarefullMomentTerm s n := by
  unfold squarefullMomentTerm
  by_cases hsq : IsSquarefull n <;> simp [hsq, hExpMomentTerm_nonneg]

lemma one_isSquarefull : IsSquarefull 1 := by
  intro p hp
  simp [primeSupport] at hp

lemma squarefullMomentTerm_one (s : ℕ) :
    squarefullMomentTerm s 1 = 1 := by
  simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]

lemma not_isSquarefull_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ IsSquarefull p := by
  intro hsq
  have hmem : p ∈ primeSupport p := by
    unfold primeSupport
    rw [Finsupp.mem_support_iff]
    exact Nat.Prime.factorization_self hp ▸ one_ne_zero
  have htwo := hsq p hmem
  rw [Nat.Prime.factorization_self hp] at htwo
  omega

lemma squarefullMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    squarefullMomentTerm s (p ^ e) =
      if e = 0 then 1
      else if e = 1 then 0
      else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he0 : e = 0
  · subst e
    simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]
  · by_cases he1 : e = 1
    · subst e
      simp [squarefullMomentTerm, not_isSquarefull_prime hp]
    · have hsq : IsSquarefull (p ^ e) := by
        intro q hq
        have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
        have hqeq : q = p := by
          have hfac_ne : (p ^ e).factorization q ≠ 0 := by
            unfold primeSupport at hq
            exact Finsupp.mem_support_iff.1 hq
          rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            nsmul_eq_mul] at hfac_ne
          have hpq_ne : p.factorization q ≠ 0 := by
            intro hpq
            simp [hpq] at hfac_ne
          exact (hp.eq_of_factorization_pos hpq_ne).symm
        subst q
        rw [Nat.factorization_pow_self hp]
        omega
      simp [squarefullMomentTerm, hExpMomentTerm_prime_pow hp, he0, he1, hsq]

lemma squarefullMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    squarefullMomentTerm s (m * n) =
      squarefullMomentTerm s m * squarefullMomentTerm s n := by
  by_cases hm : IsSquarefull m
  · by_cases hn : IsSquarefull n
    · have hmn : IsSquarefull (m * n) :=
        (isSquarefull_mul_iff_of_coprime hcop).2 ⟨hm, hn⟩
      simp [squarefullMomentTerm, hm, hn, hmn,
        hExpMomentTerm_mul_of_coprime s hcop]
    · have hmn : ¬ IsSquarefull (m * n) := by
        intro h
        exact hn ((isSquarefull_mul_iff_of_coprime hcop).1 h).2
      simp [squarefullMomentTerm, hn, hmn]
  · have hmn : ¬ IsSquarefull (m * n) := by
      intro h
      exact hm ((isSquarefull_mul_iff_of_coprime hcop).1 h).1
    simp [squarefullMomentTerm, hm, hmn]

lemma squarefullMomentTerm_prime_pow_summable
    (s p : ℕ) (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖squarefullMomentTerm s (p ^ e)‖) := by
  have hp_real_gt_one : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hp_real_pos : 0 < (p : ℝ) := zero_lt_one.trans hp_real_gt_one
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp_real_pos]
    exact inv_lt_one_of_one_lt₀ hp_real_gt_one
  have hgeom :
      Summable fun e : ℕ =>
        ‖(((e : ℝ) ^ s) * ((p : ℝ)⁻¹) ^ e : ℝ)‖ :=
    summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) s hr
  refine hgeom.congr_atTop ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with e he
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1, div_eq_mul_inv, inv_pow]

lemma squarefullMomentTerm_prime_pow_le_factorial_exp
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      ((4 : ℝ) ^ s * (s.factorial : ℝ) *
        Real.exp ((e : ℝ) / 4)) / (p : ℝ) ^ e := by
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1]
  exact div_le_div_of_nonneg_right
    (nat_pow_le_factorial_mul_exp_quarter s e) hp_pos.le

lemma exp_e_div_four_le_three_halves_pow (e : ℕ) :
    Real.exp ((e : ℝ) / 4) ≤ ((3 : ℝ) / 2) ^ e := by
  calc
    Real.exp ((e : ℝ) / 4) = Real.exp ((1 : ℝ) / 4) ^ e := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((3 : ℝ) / 2) ^ e :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        (le_of_lt exp_quarter_lt_three_halves) e

lemma squarefullMomentTerm_prime_pow_le_geo
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      (4 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2) *
        ((3 : ℝ) / 4) ^ e := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  have hden2_pos : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) := by positivity
  have hp_pow_ge :
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) ≤ (p : ℝ) ^ e := by
    calc
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)
          ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ (e - 2) := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp_two (e - 2))
              (by positivity)
      _ = (p : ℝ) ^ e := by
            rw [← pow_add]
            congr 1
            omega
  have hstep1 :
      squarefullMomentTerm s (p ^ e) ≤
        A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e := by
    simpa [A, mul_assoc] using
      squarefullMomentTerm_prime_pow_le_factorial_exp (s := s) hp he
  have hstep2 :
      A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e ≤
        A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg hA_nonneg (Real.exp_pos _).le)
      hden2_pos hp_pow_ge
  have hstep3 :
      A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) ≤
        A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_e_div_four_le_three_halves_pow e) hA_nonneg)
      hden2_pos.le
  have hidentity :
      A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) =
        (4 * A / (p : ℝ) ^ 2) * ((3 : ℝ) / 4) ^ e := by
    have h2pos : (0 : ℝ) < 2 ^ (e - 2) := by positivity
    have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    rw [show e = 2 + (e - 2) by omega]
    rw [pow_add, pow_add]
    norm_num
    field_simp [hp2pos.ne', h2pos.ne']
    have hmul :
        ((3 : ℝ) / 4) ^ (e - 2) * 2 ^ (e - 2) =
          ((3 : ℝ) / 2) ^ (e - 2) := by
      rw [← mul_pow]
      norm_num
    rw [← hmul]
    ring_nf
  exact hstep1.trans (hstep2.trans (hstep3.trans_eq hidentity))

lemma squarefullMomentTerm_prime_pow_tsum_le
    (s p : ℕ) (hp : Nat.Prime p) :
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
      1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let C : ℝ := 4 * A / (p : ℝ) ^ 2
  let g : ℕ → ℝ := fun e => (if e = 0 then 1 else 0) + C * ((3 : ℝ) / 4) ^ e
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hlhs : Summable fun e : ℕ => squarefullMomentTerm s (p ^ e) :=
    (squarefullMomentTerm_prime_pow_summable s p hp).of_norm
  have hsingle : Summable fun e : ℕ => if e = 0 then (1 : ℝ) else 0 :=
    (hasSum_single (0 : ℕ)
      (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)
      (by intro e he; simp [he])).summable
  have hgeo : Summable fun e : ℕ => C * ((3 : ℝ) / 4) ^ e :=
    (summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 : ℝ) / 4 < 1)).mul_left C
  have hg : Summable g := hsingle.add hgeo
  have hpoint :
      ∀ e : ℕ, squarefullMomentTerm s (p ^ e) ≤ g e := by
    intro e
    by_cases he0 : e = 0
    · subst e
      change squarefullMomentTerm s 1 ≤ g 0
      rw [squarefullMomentTerm_one]
      simp [g]
      exact hC_nonneg
    · by_cases he1 : e = 1
      · subst e
        rw [squarefullMomentTerm_prime_pow hp]
        simp [g]
        dsimp [C]
        positivity
      · have he2 : 2 ≤ e := by omega
        have h := squarefullMomentTerm_prime_pow_le_geo
          (s := s) (p := p) (e := e) hp he2
        simpa [g, C, A, he0] using h
  calc
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        ≤ ∑' e : ℕ, g e := hlhs.tsum_le_tsum hpoint hg
    _ = 1 + C * (∑' e : ℕ, ((3 : ℝ) / 4) ^ e) := by
          dsimp [g]
          rw [hsingle.tsum_add hgeo]
          rw [tsum_eq_single (0 : ℕ)
            (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)]
          · rw [tsum_mul_left]
            simp
          · intro e he
            simp [he]
    _ = 1 + 16 * A / (p : ℝ) ^ 2 := by
          rw [tsum_geometric_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 3 / 4)
            (by norm_num : (3 : ℝ) / 4 < 1)]
          dsimp [C]
          norm_num
          ring
    _ = 1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
          rfl

lemma sum_Icc_inv_sq_le_two_bfv (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  classical
  have hIcc :
      Finset.Icc 1 N = (Finset.range N).image (fun ν : ℕ => ν + 1) := by
    ext d
    constructor
    · intro hd
      have hdIcc := Finset.mem_Icc.mp hd
      exact Finset.mem_image.2
        ⟨d - 1, Finset.mem_range.2 (Nat.sub_one_lt_of_le hdIcc.1 hdIcc.2),
          by omega⟩
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨ν, hν, rfl⟩
      exact Finset.mem_Icc.2
        ⟨by omega, Nat.succ_le_iff.2 (Finset.mem_range.1 hν)⟩
  rw [hIcc]
  rw [Finset.sum_image]
  ·
    simpa using sum_inv_sq_le_two_bfv N
  · intro a _ha b _hb h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)

lemma primes_Icc_inv_sq_sum_le_two_bfv (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
    (by
      intro p _hp _hnot
      positivity)).trans (sum_Icc_inv_sq_le_two_bfv N)

lemma finite_euler_product_one_add_sq_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2)) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (g := fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2))
            (fun p hp => by
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ) ^ 2)
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ) ^ 2)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

lemma finite_squarefull_eulerProduct_le
    (N s : ℕ) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
      ≤ Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
  classical
  let P := (Finset.Icc 1 N).filter Nat.Prime
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let z : ℝ := 16 * A
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hz_nonneg : 0 ≤ z := by
    dsimp [z]
    positivity
  have hlocal :
      ∀ p ∈ P,
        (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
          (1 : ℝ) + z / (p : ℝ) ^ 2 := by
    intro p hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.1 hp).2
    simpa [z, A] using squarefullMomentTerm_prime_pow_tsum_le s p hpprime
  calc
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        = P.prod fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          change (P.filter Nat.Prime).prod
              (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) =
            P.prod (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
          rw [Finset.filter_true_of_mem]
          intro p hp
          exact (Finset.mem_filter.1 hp).2
    _ ≤ P.prod fun p => (1 : ℝ) + z / (p : ℝ) ^ 2 := by
          exact Finset.prod_le_prod
            (s := P)
            (f := fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
            (g := fun p => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (fun p hp => by
              have hsum_nonneg :
                  0 ≤ ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
                exact tsum_nonneg (fun e => squarefullMomentTerm_nonneg s (p ^ e))
              exact hsum_nonneg)
            hlocal
    _ ≤ Real.exp (z * P.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) :=
          finite_euler_product_one_add_sq_le_exp_sum P hz_nonneg
    _ ≤ Real.exp (z * 2) := by
          exact Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left
              (by
                simpa [P] using primes_Icc_inv_sq_sum_le_two_bfv N)
              hz_nonneg)
    _ = Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
          congr 1
          dsimp [z, A]
          ring

lemma eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          tendsto_loglog_nat_atTop
    simpa [Real.sqrt_eq_rpow,Function.comp_def] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2,
      eventually_sqrt_loglog_ge (2 * |Real.log A| / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hlog_small hsqrt_large hY_large
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hY_large)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hlogY_nonneg : 0 ≤ Real.log Y := Real.log_nonneg (by simpa [Y] using hY_large)
  have hleft_norm :
      ‖Real.log Y‖ = Real.log Y := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.sqrt Y‖ = Real.sqrt Y := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  have hlogY_le : Real.log Y ≤ (δ / 2) * Real.sqrt Y := by
    simpa [Y, hleft_norm, hright_norm] using hlog_small
  have hconst : Real.log A ≤ (δ / 2) * Real.sqrt Y := by
    have hmul : 2 * |Real.log A| ≤ δ * Real.sqrt Y :=
      by simpa [mul_comm] using (div_le_iff₀ hδ).1 hsqrt_large
    have hlogA_le_abs : Real.log A ≤ |Real.log A| := le_abs_self _
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Real.sqrt Y + ((δ / 2) * Real.sqrt Y) / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Real.sqrt Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY_le (by norm_num)
            nlinarith
    _ ≤ δ * Real.sqrt Y := by nlinarith

lemma eventually_squarefull_moment_factor_le_Zscale
    (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
  let B' : ℝ := B + 1
  let C : ℝ := 4 * B'
  have hB' : 0 < B' := by dsimp [B']; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < (1 / (12 * B') : ℝ) := by positivity
  filter_upwards [eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
      C (1 / (12 * B')) hC hδ,
      eventually_sqrt_loglog_ge (max 1 (1 / B)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop (max 1 (12 * Real.log 32)),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogC hsqrt_large hY_large hNlarge_nat
  set Y := Real.log (Real.log (N : ℝ))
  set R := Real.sqrt Y
  set s : ℕ := Nat.ceil (B * R)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hY_ge_one : 1 ≤ Y := (le_max_left _ _).trans (by simpa [Y] using hY_large)
  have hY_ge_log32 : 12 * Real.log 32 ≤ Y :=
    (le_max_right _ _).trans (by simpa [Y] using hY_large)
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hR_pos : 0 < R := by simpa [R] using Real.sqrt_pos.2 hY_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hR_ge_one : 1 ≤ R := by
    have hsquares :
        (1 : ℝ) ^ 2 ≤ R ^ 2 := by
      simpa [R, Real.sq_sqrt hY_pos.le] using hY_ge_one
    have habs : |(1 : ℝ)| ≤ |R| := sq_le_sq.mp hsquares
    simpa [abs_of_nonneg hR_nonneg] using habs
  have hBR_nonneg : 0 ≤ B * R := by positivity
  have hs_le : (s : ℝ) ≤ B' * R := by
    have hsceil : (s : ℝ) ≤ B * R + 1 := by
      dsimp [s]
      exact (Nat.ceil_lt_add_one hBR_nonneg).le
    have hone_le_R : (1 : ℝ) ≤ R := hR_ge_one
    dsimp [B']
    nlinarith
  have hfour_s_le : (4 : ℝ) * (s : ℝ) ≤ C * R := by
    dsimp [C]
    nlinarith [hs_le, hR_nonneg]
  have hC_R_pos : 0 < C * R := mul_pos hC hR_pos
  have hC_R_ge_one : 1 ≤ C * R := by
    have hC_ge_one_or : 0 < C := hC
    nlinarith [hC_ge_one_or, hR_ge_one]
  have hlogC_nonneg : 0 ≤ Real.log (C * R) :=
    Real.log_nonneg hC_R_ge_one
  have hs_log_le :
      (s : ℝ) * Real.log (C * R) ≤ Y / 12 := by
    have hlogC' :
        Real.log (C * R) ≤ (1 / (12 * B')) * R := by
      simpa [C, Y, R] using hlogC
    calc
      (s : ℝ) * Real.log (C * R)
          ≤ (B' * R) * Real.log (C * R) := by
            exact mul_le_mul_of_nonneg_right hs_le hlogC_nonneg
      _ ≤ (B' * R) * ((1 / (12 * B')) * R) := by
            exact mul_le_mul_of_nonneg_left hlogC' (by positivity)
      _ = Y / 12 := by
            have hRsq : R ^ 2 = Y := by
              simpa [R] using Real.sq_sqrt hY_pos.le
            have hcoef : B' * (1 / (12 * B')) = (1 / 12 : ℝ) := by
              have hden : (12 : ℝ) * B' ≠ 0 :=
                mul_ne_zero (by norm_num) hB'.ne'
              apply (mul_right_injective₀ hden)
              calc
                (12 * B') * (B' * (1 / (12 * B'))) = B' := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (B' * (1 * (12 * B')⁻¹)) =
                    B' * ((12 * B') * (12 * B')⁻¹) by ring]
                  rw [mul_inv_cancel₀ hden, mul_one]
                _ = (12 * B') * (1 / 12 : ℝ) := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (1 * 12⁻¹) =
                    B' * (12 * 12⁻¹) by ring]
                  rw [mul_inv_cancel₀ (by norm_num : (12 : ℝ) ≠ 0), mul_one]
            calc
              (B' * R) * ((1 / (12 * B')) * R)
                  = (B' * (1 / (12 * B'))) * R ^ 2 := by ring
              _ = (1 / 12 : ℝ) * Y := by rw [hcoef, hRsq]
              _ = Y / 12 := by ring
  have hfac :
      ((s.factorial : ℕ) : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast Nat.factorial_le_pow s
  have hmoment_le_pow :
      (4 : ℝ) ^ s * (s.factorial : ℝ) ≤ ((4 : ℝ) * (s : ℝ)) ^ s := by
    calc
      (4 : ℝ) ^ s * (s.factorial : ℝ)
          ≤ (4 : ℝ) ^ s * (s : ℝ) ^ s := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((4 : ℝ) * (s : ℝ)) ^ s := by rw [mul_pow]
  have hbase_le :
      ((4 : ℝ) * (s : ℝ)) ^ s ≤ (C * R) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hfour_s_le s
  have hpow_exp :
      (C * R) ^ s ≤ Real.exp (Y / 12) := by
    have hpow_eq :
        (C * R) ^ s = Real.exp ((s : ℝ) * Real.log (C * R)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC_R_pos]
      ring_nf
    rw [hpow_eq]
    exact Real.exp_le_exp.2 hs_log_le
  have hthirtytwo :
      (32 : ℝ) ≤ Real.exp (Y / 12) := by
    have hlog32 : Real.log 32 ≤ Y / 12 := by nlinarith
    calc
      (32 : ℝ) = Real.exp (Real.log 32) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      _ ≤ Real.exp (Y / 12) := Real.exp_le_exp.2 hlog32
  have hmain :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Real.exp (Y / 6) := by
    calc
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          ≤ Real.exp (Y / 12) * Real.exp (Y / 12) := by
            exact mul_le_mul hthirtytwo (hmoment_le_pow.trans (hbase_le.trans hpow_exp))
              (by positivity) (by positivity)
      _ = Real.exp (Y / 6) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
        ≤ Real.exp (Y / 6) := hmain
    _ ≤ Real.exp (Y / 2) * R := by
          have hexp : Real.exp (Y / 6) ≤ Real.exp (Y / 2) :=
            Real.exp_le_exp.2 (by nlinarith)
          exact hexp.trans (by
            calc
              Real.exp (Y / 2) ≤ Real.exp (Y / 2) * R := by
                nlinarith [Real.exp_pos (Y / 2), hR_ge_one])
    _ = Zscale N := by
          rw [hZeq]

lemma squarefullMoment_eulerProduct_hasSum (N s : ℕ) :
    HasSum
      (fun m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        squarefullMomentTerm s m)
      (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := squarefullMomentTerm s)
    (squarefullMomentTerm_one s)
    (fun {m n} hcop => squarefullMomentTerm_mul_of_coprime s hcop)
    (fun {p} hp => squarefullMomentTerm_prime_pow_summable s p hp)
    ((Finset.Icc 1 N).filter Nat.Prime)).2

lemma squarefull_mem_factored_primes_Icc {N d : ℕ}
    (hd : d ∈ Finset.Icc 1 N) :
    d ∈ Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpd
  have hdIcc := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
  have hple : p ≤ N := (Nat.le_of_dvd hdpos hpd).trans hdIcc.2
  exact Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hp.pos, hple⟩, hp⟩

lemma squarefullMomentTerm_eq_of_squarefull_Icc
    {N d s : ℕ} (hd : d ∈ Finset.Icc 1 N) (hsq : IsSquarefull d) :
    squarefullMomentTerm s d = (hExp d : ℝ) ^ s / (d : ℝ) := by
  have hdIcc := Finset.mem_Icc.mp hd
  have hdne : d ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1)
  simp [squarefullMomentTerm, hExpMomentTerm, hsq, hdne]

noncomputable def squarefullFactoredFinset (N : ℕ) :
    Finset (Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)) :=
  ((Finset.Icc 1 N).filter IsSquarefull).attach.image
    (fun d =>
      (⟨d.1, squarefull_mem_factored_primes_Icc
        (Finset.mem_filter.1 d.2).1⟩ :
        Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)))

lemma squarefull_recip_sum_eq_factoredFinset_sum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      =
    ∑ x ∈ squarefullFactoredFinset N, squarefullMomentTerm s x := by
  classical
  unfold squarefullFactoredFinset
  rw [Finset.sum_image]
  · rw [Finset.sum_attach]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    exact (squarefullMomentTerm_eq_of_squarefull_Icc
      (N := N) (d := d) (s := s)
      (Finset.mem_filter.1 hd).1
      (Finset.mem_filter.1 hd).2).symm
  · intro a _ha b _hb hab
    apply Subtype.ext
    exact congrArg
      (fun x : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        (x : ℕ)) hab

lemma squarefull_recip_sum_le_factored_tsum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∑' m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime),
      squarefullMomentTerm s m := by
  rw [squarefull_recip_sum_eq_factoredFinset_sum]
  exact (squarefullMoment_eulerProduct_hasSum N s).summable.sum_le_tsum
    (squarefullFactoredFinset N)
    (fun x _hx => squarefullMomentTerm_nonneg s x)

lemma squarefull_recip_sum_le_eulerProduct (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
      ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  rw [← (squarefullMoment_eulerProduct_hasSum N s).tsum_eq]
  exact squarefull_recip_sum_le_factored_tsum N s

lemma hExp_moment_sum_le_squarefull_eulerProduct (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ (N : ℝ) *
            ∑ d ∈ Finset.Icc 1 N,
              if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 :=
          hExp_moment_sum_le_squarefull_recip_sum N s
    _ ≤ (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          exact mul_le_mul_of_nonneg_left
            (squarefull_recip_sum_le_eulerProduct N s)
            (by positivity)

lemma hExp_rare_count_rankin_real_bound (N s : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
      ≤ (N : ℝ) *
          Real.exp
            (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
              - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
  have hH_nonneg : 0 ≤ hExpCutoff N := by
    unfold hExpCutoff
    positivity
  have hRankin :=
    hExp_large_rankin_sum_le (N := N) (s := s) (H := hExpCutoff N) hH_nonneg
  have hMoment :
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
        (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
          ≤ (N : ℝ) *
              ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
                ∑' e : ℕ, squarefullMomentTerm s (p ^ e) :=
            hExp_moment_sum_le_squarefull_eulerProduct N s
      _ ≤ (N : ℝ) *
            Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (finite_squarefull_eulerProduct_le N s)
              (by positivity)
  have hCombined :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ) *
          hExpCutoff N ^ s
        ≤ (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) :=
    hRankin.trans hMoment
  have hHpow :
      hExpCutoff N ^ s =
        Real.exp ((s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
    unfold hExpCutoff
    rw [← Real.exp_nat_mul]
  have hHpow_pos :
      0 < hExpCutoff N ^ s := by
    rw [hHpow]
    positivity
  have hdiv :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ ((N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)))) /
            hExpCutoff N ^ s := by
    exact (le_div_iff₀ hHpow_pos).2 hCombined
  refine hdiv.trans_eq ?_
  rw [hHpow]
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
  congr 1

theorem hExp_rare_count_rankin_squarefull :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  intro A hA
  let B : ℝ := A + 2
  have hB : 0 < B := by dsimp [B]; linarith
  filter_upwards [eventually_squarefull_moment_factor_le_Zscale B hB,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hfactor hNlarge_nat
  let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (zero_lt_one.trans hlog_gt_one).le
  have hZ_nonneg : 0 ≤ Zscale N := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    positivity
  have hfactor' :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
    simpa [s, B] using hfactor
  have hs_ge :
      B * Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ (s : ℝ) := by
    dsimp [s]
    exact Nat.le_ceil _
  have hs_cutoff :
      B * Zscale N ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    calc
      B * (Real.sqrt (Real.log (N : ℝ)) *
          Real.sqrt (Real.log (Real.log (N : ℝ))))
          = (B * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
              Real.sqrt (Real.log (N : ℝ)) := by ring
      _ ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg _)
  have hexponent :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
        ≤ -A * Zscale N := by
    have hstep :
        32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
            - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
          ≤ Zscale N - B * Zscale N := by
      nlinarith [hfactor', hs_cutoff]
    have htarget : Zscale N - B * Zscale N ≤ -A * Zscale N := by
      dsimp [B]
      nlinarith [hZ_nonneg]
    exact hstep.trans htarget
  have hreal :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ (N : ℝ) * Lscale (-A) N := by
    calc
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
          ≤ (N : ℝ) *
              Real.exp
                (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
                  - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) :=
            hExp_rare_count_rankin_real_bound N s
      _ ≤ (N : ℝ) * Lscale (-A) N := by
            rw [Lscale]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 hexponent) hN_nonneg
  exact Nat.le_floor hreal

theorem hExp_rare_count_superL :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) :=
  hExp_rare_count_rankin_squarefull

theorem hExp_rare_subset_count
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N →
        (S.filter fun n => hExpCutoff N < (hExp n : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  filter_upwards [hExp_rare_count_superL A hA] with N hN S hS
  exact (Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN

end BFVPruning1190
namespace BFVPruning1190
open Filter Finset
lemma eventually_Zscale_ge_const (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_Lscale_neg_le_const {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Lscale (-A) N ≤ c := by
  filter_upwards [eventually_Zscale_ge_const ((-Real.log c) / A)] with N hZ
  rw [Lscale]
  exact (Real.le_log_iff_exp_le hc).1 (by
    have hmul : -Real.log c ≤ A * Zscale N := by
      simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
    nlinarith)

lemma eventually_const_mul_Zscale_le_Lscale {C η : ℝ}
    (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * Zscale N ≤ Lscale η N := by
  have hηsq_pos : 0 < η ^ 2 := sq_pos_of_pos hη
  filter_upwards [eventually_Zscale_ge_const (4 * C / η ^ 2)] with N hZlarge
  let x : ℝ := η * Zscale N / 2
  have hZ_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfactor : 2 * C / η ≤ x := by
    dsimp [x]
    rw [div_le_iff₀ hη]
    have hmul' : 4 * C ≤ η ^ 2 * Zscale N := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hηsq_pos).1 hZlarge
    have hmul'' : 4 * C ≤ η * (η * Zscale N) := by
      simpa [pow_two, mul_assoc] using hmul'
    nlinarith
  have hCZ_eq : C * Zscale N = (2 * C / η) * x := by
    dsimp [x]
    field_simp [hη.ne']
  have hCZ_le_xsq : C * Zscale N ≤ x ^ 2 := by
    rw [hCZ_eq, pow_two]
    exact mul_le_mul_of_nonneg_right hfactor hx_nonneg
  have hx_le_exp : x ≤ Real.exp x := by
    calc
      x ≤ 1 + x := by linarith
      _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hxsq_le : x ^ 2 ≤ Real.exp (2 * x) := by
    calc
      x ^ 2 = x * x := by ring
      _ ≤ Real.exp x * Real.exp x := by
            exact mul_le_mul hx_le_exp hx_le_exp hx_nonneg (Real.exp_pos x).le
      _ = Real.exp (2 * x) := by
            rw [← Real.exp_add]
            ring_nf
  calc
    C * Zscale N ≤ x ^ 2 := hCZ_le_xsq
    _ ≤ Real.exp (2 * x) := hxsq_le
    _ = Lscale η N := by
          dsimp [x, Lscale]
          congr 1
          ring

lemma eventually_Mscale_le_Zscale :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Zscale N := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (1 : ℝ) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hsqrt 2
    simpa [Real.sq_sqrt hloglog_nonneg] using hsq
  rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
  exact le_mul_of_one_le_right (Mscale_nonneg N) hloglog_ge_one

lemma eventually_floor_threeM_succ_le_Lscale
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ) ≤ Lscale η N := by
  filter_upwards [eventually_Mscale_le_Zscale,
      eventually_Zscale_ge_const 1,
      eventually_const_mul_Zscale_le_Lscale (C := 4) (by norm_num) hη] with
    N hMleZ hZge h4Z
  have hfloor :
      ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) ≤ 3 * Mscale N := by
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  calc
    ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ)
        = ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ 3 * Mscale N + 1 := by linarith
    _ ≤ 3 * Zscale N + Zscale N := by nlinarith
    _ = 4 * Zscale N := by ring
    _ ≤ Lscale η N := h4Z

lemma q_card_lower_from_bfv_lower
    {ε η : ℝ} {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ ((N : ℝ) * Lscale (-1) N)) :
    (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-(1 + η + ε)) N
        = ((N : ℝ) * Lscale (-(1 + η)) N) * Lscale (-ε) N := by
            rw [show -(1 + η + ε) = -(1 + η) + -ε by ring, Lscale_add]
            ring
    _ ≤ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N := by
          exact mul_le_mul_of_nonneg_right hf (Lscale_nonneg (-ε) N)
    _ ≤ (Q.card : ℝ) := hQ

lemma eventually_nat_mul_Lscale_neg_gt_one (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 < (N : ℝ) * Lscale (-A) N := by
  let B : ℝ := max (A + 1) 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right (A + 1) 1)
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge B hBpos] with N hN hM
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
  have hNposNat : 0 < N := by
    exact Nat.pos_of_ne_zero (by
      intro h0
      have : ((N : ℕ) : ℝ) = 0 := by simp [h0]
      linarith [show (0 : ℝ) < Real.exp 1 from Real.exp_pos 1])
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMgeA1 : A + 1 ≤ Mscale N := (le_max_left (A + 1) 1).trans hM
  have hlog_eq : Real.log ((N : ℝ) * Lscale (-A) N) =
      Real.log (N : ℝ) + (-A) * Zscale N :=
    log_nat_mul_Lscale hNposNat (-A)
  have hMZ := Mscale_mul_Zscale_eq_log hNlarge
  have hlog_pos :
      0 < Real.log ((N : ℝ) * Lscale (-A) N) := by
    rw [hlog_eq, ← hMZ]
    have hdiff : 1 ≤ Mscale N - A := by linarith
    nlinarith
  have htarget_nonneg : 0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Real.log_pos_iff htarget_nonneg).1 hlog_pos

lemma omega_pos_of_one_lt {n : ℕ} (hn : 1 < n) : 1 ≤ omega n := by
  by_contra h
  have homega : omega n = 0 := by omega
  have hnne : n ≠ 0 := by omega
  have hnone : n = 1 := eq_one_of_omega_eq_zero hnne homega
  omega

lemma eventually_omega_pos_of_modulus_lower :
    ∀ᶠ N : ℕ in atTop,
      ∀ q : ℕ, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) → 1 ≤ omega q := by
  filter_upwards [eventually_nat_mul_Lscale_neg_gt_one 2] with N hlarge q hq
  have hq_gt_one_real : (1 : ℝ) < (q : ℝ) := hlarge.trans_le hq
  have hq_gt_one : 1 < q := by exact_mod_cast hq_gt_one_real
  exact omega_pos_of_one_lt hq_gt_one

lemma nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg
    {A B δ : ℝ} (hAB : B + δ ≤ A) (N : ℕ) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
  have hmono : Lscale (-A) N ≤ Lscale (-(B + δ)) N := by
    exact Lscale_mono_in_alpha (by linarith) N
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ (N : ℝ) * Lscale (-(B + δ)) N := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
          rw [show -(B + δ) = -B + -δ by ring, Lscale_add]
          ring

lemma nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) :=
          nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg hAB N
    _ ≤ Lscale (-δ) N * (Q.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hQ (Lscale_nonneg (-δ) N)

lemma floor_nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have htarget_nonneg :
      0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Nat.floor_le htarget_nonneg).trans
    (nat_mul_Lscale_neg_le_fraction_of_card hAB hQ)

lemma floor_nat_mul_Lscale_neg_le_near_extremal_fraction
    {A ε η δ : ℝ} (hAB : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ ((N : ℝ) * Lscale (-1) N)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hQlower :
      (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQ hf
  exact floor_nat_mul_Lscale_neg_le_fraction_of_card
    (A := A) (B := 1 + η + ε) (δ := δ) (by linarith) hQlower

lemma card_filter_natCast_lt_le_floor {S : Finset ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hpos : ∀ n ∈ S, 1 ≤ n) :
    (S.filter (fun n : ℕ => (n : ℝ) < X)).card ≤ Nat.floor X := by
  classical
  have hsub :
      (S.filter (fun n : ℕ => (n : ℝ) < X)) ⊆ Finset.Icc 1 (Nat.floor X) := by
    intro n hn
    have hnS : n ∈ S := (Finset.mem_filter.1 hn).1
    have hnlt : (n : ℝ) < X := (Finset.mem_filter.1 hn).2
    exact Finset.mem_Icc.2 ⟨hpos n hnS, (Nat.le_floor_iff hX).2 hnlt.le⟩
  have hcard := Finset.card_le_card hsub
  have hIcc_le : (Finset.Icc 1 (Nat.floor X)).card ≤ Nat.floor X := by
    rw [Nat.card_Icc]
    omega
  exact hcard.trans hIcc_le

lemma small_moduli_in_admissible_count
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) :
    (Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card
      ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) := by
  exact card_filter_natCast_lt_le_floor
    (mul_nonneg (by positivity) (Lscale_nonneg (-2) N))
    (fun q hq => (hRange q hq).1)

lemma small_moduli_count_le_near_extremal_fraction
    {ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ 2)
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ ((N : ℝ) * Lscale (-1) N)) :
    ((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount := small_moduli_in_admissible_count (N := N) (Q := Q) hRange
  have hcount_real :
      (((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-2) N) : ℝ) := by
    exact_mod_cast hcount
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := 2) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma hExp_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ ((N : ℝ) * Lscale (-1) N))
    (hRare :
      (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hRare
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_tail_subset_count
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
        ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
          let α : ℝ := (t : ℝ) / Mscale N
          (Q.filter fun q => t ≤ omega q).card
            ≤ Nat.floor
                ((N : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  filter_upwards [bfv_omega_tail_theorem ε hε] with N htail Q hQ t ht
  have hsub :
      (Q.filter fun q => t ≤ omega q) ⊆
        (Finset.Icc 1 N).filter fun q => t ≤ omega q := by
    intro q hq
    exact Finset.mem_filter.2
      ⟨hQ (Finset.mem_filter.1 hq).1, (Finset.mem_filter.1 hq).2⟩
  exact (Finset.card_le_card hsub).trans (htail N t le_rfl ht)

lemma omega_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N t : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ ((N : ℝ) * Lscale (-1) N))
    (hTail :
      (Q.filter fun q : ℕ => t ≤ omega q).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hTail
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_floor_threeM_tail_subset_count :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
          (Q.filter
              (fun q : ℕ => Nat.floor (3 * Mscale N) ≤ omega q)).card
            ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
  have hτ : (0 : ℝ) < 1 / 24 := by norm_num
  filter_upwards [omega_tail_subset_count (1 / 24) hτ,
      eventually_Mscale_ge 4 (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N htail hMge hNlarge_nat Q hQ
  let t : ℕ := Nat.floor (3 * Mscale N)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have ht_le : (t : ℝ) ≤ 3 * Mscale N := by
    dsimp [t]
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  have ht_count := htail Q hQ t ht_le
  have ht_lower : 3 * Mscale N - 1 < (t : ℝ) := by
    have hlt : 3 * Mscale N < (t : ℝ) + 1 := by
      dsimp [t]
      exact Nat.lt_floor_add_one (3 * Mscale N)
    linarith
  have halpha_lower : (11 / 4 : ℝ) ≤ (t : ℝ) / Mscale N := by
    have hdiv : (3 * Mscale N - 1) / Mscale N < (t : ℝ) / Mscale N :=
      div_lt_div_of_pos_right ht_lower hMpos
    have hM_inv : 1 / Mscale N ≤ (1 / 4 : ℝ) := by
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hMge)
    have hthree_sub : (11 / 4 : ℝ) ≤ 3 - 1 / Mscale N := by
      linarith
    have hdiv_eq : (3 * Mscale N - 1) / Mscale N = 3 - 1 / Mscale N := by
      field_simp [hMpos.ne']
    linarith
  have hexp_scale :
      (N : ℝ) *
          Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
        ≤ (N : ℝ) * Lscale (-(4 / 3)) N := by
    have hcoeff :
        -((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ) ≤ -(4 / 3 : ℝ) := by
      nlinarith
    have hexp :
        Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
          ≤ Lscale (-(4 / 3)) N := by
      rw [Lscale]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcoeff hZnonneg)
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  exact ht_count.trans (Nat.floor_mono hexp_scale)

lemma eventually_radical_multiplicity_ceiling_le_Lscale
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ 3 * Mscale N →
        (Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) : ℝ) ≤
          Lscale ε N := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_nonneg : 0 ≤ Real.log 2 := hlog2_pos.le
  let Clog : ℝ := 9 * Real.log 2 / ε
  have hClog_pos : 0 < Clog := by
    dsimp [Clog]
    positivity
  filter_upwards [eventually_Zscale_ge_const (3 * Real.log 2 / ε),
      eventually_sqrt_loglog_ge (6 / ε),
      eventually_sqrt_loglog_ge (Real.sqrt Clog),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hZconst hsqrtloglog hsqrtClog hNlarge_nat K hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrtloglog_nonneg :
      0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hloglog_ge_Clog : Clog ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (Real.sqrt Clog) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg Clog) hsqrtClog 2
    simpa [Real.sq_sqrt hClog_pos.le, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZsqrt := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hZloglog := Mscale_mul_loglog_eq_Zscale hNlarge
  let a : ℝ := (ε / 3) * Zscale N
  have htwo : (2 : ℝ) ≤ Real.exp a := by
    have hlog_le : Real.log 2 ≤ a := by
      dsimp [a]
      have hzmul : 3 * Real.log 2 ≤ ε * Zscale N := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hZconst
      nlinarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).1 hlog_le
  have hHsq : hExpCutoff N ^ 2 ≤ Real.exp a := by
    have hcoeff : 2 ≤ (ε / 3) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hmul : 6 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hsqrtloglog
      nlinarith
    have hexp_arg :
        2 * Real.sqrt (Real.log (N : ℝ)) ≤ a := by
      dsimp [a]
      rw [hZsqrt]
      calc
        2 * Real.sqrt (Real.log (N : ℝ))
            ≤ ((ε / 3) * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                Real.sqrt (Real.log (N : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hcoeff hsqrtlog_nonneg
        _ = (ε / 3) *
              (Real.sqrt (Real.log (N : ℝ)) *
                Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
              ring
    have hHsq_eq :
        hExpCutoff N ^ 2 = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
      simp [hExpCutoff, pow_two, ← Real.exp_add, two_mul]
    rw [hHsq_eq]
    exact Real.exp_le_exp.2 hexp_arg
  have hpow : (2 : ℝ) ^ K ≤ Real.exp a := by
    have hlog_le : Real.log ((2 : ℝ) ^ K) ≤ a := by
      rw [Real.log_pow]
      dsimp [a]
      rw [← hZloglog]
      calc
        (K : ℝ) * Real.log 2
            ≤ (3 * Mscale N) * Real.log 2 := by
              exact mul_le_mul_of_nonneg_right hK hlog2_nonneg
        _ = Mscale N * (3 * Real.log 2) := by ring
        _ ≤ Mscale N * ((ε / 3) *
              Real.log (Real.log (N : ℝ))) := by
              have hmain : 3 * Real.log 2 ≤ (ε / 3) *
                  Real.log (Real.log (N : ℝ)) := by
                dsimp [Clog] at hloglog_ge_Clog
                have hmul : 9 * Real.log 2 ≤
                    ε * Real.log (Real.log (N : ℝ)) := by
                  simpa [mul_comm] using (div_le_iff₀ hε).1 hloglog_ge_Clog
                nlinarith
              exact mul_le_mul_of_nonneg_left hmain (Mscale_nonneg N)
        _ = (ε / 3) *
              (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
        _ = ε / 3 * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
    exact (Real.log_le_iff_le_exp (by positivity : 0 < (2 : ℝ) ^ K)).1 hlog_le
  let X : ℝ := hExpCutoff N ^ 2 * (2 : ℝ) ^ K
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hH_ge_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  have hHsq_ge_one : 1 ≤ hExpCutoff N ^ 2 := by
    nlinarith [hH_ge_one]
  have hpow_ge_one : 1 ≤ (2 : ℝ) ^ K := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    nlinarith [mul_le_mul hHsq_ge_one hpow_ge_one
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ hExpCutoff N ^ 2)]
  have hceil_le : (Nat.ceil X : ℝ) ≤ 2 * X := by
    have hceil_lt : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hX_nonneg
    linarith
  have htwoX : 2 * X ≤ Lscale ε N := by
    dsimp [X]
    calc
      2 * (hExpCutoff N ^ 2 * (2 : ℝ) ^ K)
          ≤ Real.exp a * (Real.exp a * Real.exp a) := by
            nlinarith [htwo, hHsq, hpow,
              Real.exp_pos a, hX_nonneg]
      _ = Real.exp (3 * a) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
      _ = Lscale ε N := by
            dsimp [a, Lscale]
            congr 1
            ring
  exact hceil_le.trans htwoX

lemma card_lower_of_mul_factor_le_Lscale
    {S S' : Finset ℕ} {C N : ℕ} {η : ℝ}
    (hcard : S.card ≤ C * S'.card)
    (hC : (C : ℝ) ≤ Lscale η N) :
    (S.card : ℝ) * Lscale (-η) N ≤ (S'.card : ℝ) := by
  have hcard_real : (S.card : ℝ) ≤ (C : ℝ) * (S'.card : ℝ) := by
    exact_mod_cast hcard
  have hfactor :
      (C : ℝ) * (S'.card : ℝ) ≤
        Lscale η N * (S'.card : ℝ) := by
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hmain : (S.card : ℝ) ≤ Lscale η N * (S'.card : ℝ) :=
    hcard_real.trans hfactor
  calc
    (S.card : ℝ) * Lscale (-η) N
        ≤ (Lscale η N * (S'.card : ℝ)) * Lscale (-η) N := by
          exact mul_le_mul_of_nonneg_right hmain (Lscale_nonneg (-η) N)
    _ = (S'.card : ℝ) * (Lscale η N * Lscale (-η) N) := by ring
    _ = (S'.card : ℝ) := by
          rw [show Lscale η N * Lscale (-η) N = 1 by
            rw [mul_comm, Lscale_neg_mul]]
          ring

lemma prunedData_of_subset {N : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (K : ℕ)
    (hKpos : 1 ≤ K)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hRadInj : ∀ q ∈ S, ∀ r ∈ S, rad q = rad r → q = r) :
    ∃ D : PrunedData N, D.Q = S ∧ D.K = K ∧
      (D.Q.card : ℝ) = (S.card : ℝ) := by
  let aS : ResidueAssignment S := restrictAssignment a hsub
  have hAdmissible : Admissible N S := by
    constructor
    · intro q hq
      exact hRange q (hsub hq)
    · exact ⟨aS, PairwiseDisjointResidues.mono hDisj hsub⟩
  refine ⟨{
      Q := S
      Q_nonempty := hSnonempty
      a := aS
      admissible := hAdmissible
      pairwise_disjoint := PairwiseDisjointResidues.mono hDisj hsub
      K := K
      K_pos := hKpos
      modulus_lower := hModLower
      modulus_upper := ?_
      hExp_bound := ?_
      omega_eq := hOmega
      K_bound := hKbound
      rad_injective := hRadInj
    }, rfl, rfl, rfl⟩
  · intro q hq
    exact (hRange q (hsub hq)).2
  · intro q hq
    simpa [hExpCutoff] using hHExp q hq

lemma rad_fiber_card_le_ceiling {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∀ r ∈ S.image rad,
      (S.filter fun q => rad q = r).card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) := by
  intro r hr
  let F : Finset ℕ := S.filter fun q => rad q = r
  have hFpos : ∀ q ∈ F, q ≠ 0 := by
    intro q hq
    exact hSpos q (Finset.mem_filter.1 hq).1
  have hF :
      ∀ q ∈ F, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H := by
    intro q hq
    exact ⟨(Finset.mem_filter.1 hq).2,
      hOmega q (Finset.mem_filter.1 hq).1,
      hHExp q (Finset.mem_filter.1 hq).1⟩
  have hreal := rad_multiplicity_bfv33 F r K H hH hFpos hF
  have hceil : H ^ 2 * (2 : ℝ) ^ K ≤
      (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

lemma choose_rad_representatives {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∃ S' : Finset ℕ,
      S' ⊆ S ∧
      (∀ q ∈ S', ∀ r ∈ S', rad q = rad r → q = r) ∧
      S.card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) * S'.card := by
  exact choose_one_per_fiber_card_lower S rad
    (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K))
    (rad_fiber_card_le_ceiling hH hSpos hOmega hHExp)

lemma exists_prunedData_after_radical_selection
    {N K : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (hKpos : 1 ≤ K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hH : 1 ≤ hExpCutoff N)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K) :
    ∃ D : PrunedData N, D.Q ⊆ S ∧
      S.card ≤ Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) * D.Q.card := by
  have hSpos : ∀ q ∈ S, q ≠ 0 := by
    intro q hq
    have hqpos : 1 ≤ q := (hRange q (hsub hq)).1
    omega
  rcases choose_rad_representatives
      (S := S) (K := K) (H := hExpCutoff N)
      hH hSpos hOmega hHExp with
    ⟨S', hS'sub, hRadInj, hCard⟩
  have hS'nonempty : S'.Nonempty := by
    by_contra hnone
    have hS'empty : S' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hnone
    have hSpos_card : 0 < S.card := hSnonempty.card_pos
    have hle0 : S.card ≤ 0 := by
      simpa [hS'empty] using hCard
    exact (Nat.lt_irrefl 0) (hSpos_card.trans_le hle0)
  rcases prunedData_of_subset (N := N) (Q := Q) (S := S') a
      (fun q hq => hsub (hS'sub hq))
      hRange hDisj hS'nonempty K hKpos
      (fun q hq => hModLower q (hS'sub hq))
      (fun q hq => hHExp q (hS'sub hq))
      (fun q hq => hOmega q (hS'sub hq))
      hKbound
      (fun q hq r hr hrad => hRadInj q hq r hr hrad) with
    ⟨D, hDQ, _hDK, hDcard⟩
  refine ⟨D, hDQ ▸ hS'sub, ?_⟩
  simpa [hDQ] using hCard

lemma exists_omega_fiber_large (S : Finset ℕ) (T : ℕ)
    (_hS : S.Nonempty) (hOmegaLe : ∀ q ∈ S, omega q ≤ T) :
    ∃ K : ℕ,
      K ≤ T ∧ S.card ≤ (T + 1) * (S.filter fun q => omega q = K).card := by
  classical
  have hBne : (Finset.range (T + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  have hB : ∀ q ∈ S, omega q ∈ Finset.range (T + 1) := by
    intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hOmegaLe q hq)
  rcases exists_fiber_card_mul_range_card_ge S (Finset.range (T + 1)) omega hBne hB with
    ⟨K, hKmem, hK⟩
  refine ⟨K, ?_, ?_⟩
  · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hKmem)
  · simpa [Finset.card_range] using hK

theorem bfv_pruning_small_epsilon_theorem :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (N : ℝ) * Lscale (-1) N →
        ∃ D : PrunedData N, D.Q ⊆ Q ∧
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N := by
  intro ε hε hεle
  let μ : ℝ := ε / 24
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hε3 : 0 < ε / 3 := by positivity
  have hmargin_small : 1 + μ + ε + μ ≤ 2 := by
    dsimp [μ]
    nlinarith
  have hmargin_omega : 1 + μ + ε + μ ≤ (4 / 3 : ℝ) := by
    dsimp [μ]
    nlinarith
  filter_upwards [hExp_rare_subset_count 2 (by norm_num),
      omega_floor_threeM_tail_subset_count,
      eventually_floor_threeM_succ_le_Lscale (ε / 3) hε3,
      eventually_radical_multiplicity_ceiling_le_Lscale (ε / 3) hε3,
      eventually_Lscale_neg_le_const (A := μ) (c := 1 / 6) hμ (by norm_num),
      eventually_Lscale_neg_le_const (A := ε / 3) (c := 1 / 2) hε3 (by norm_num),
      eventually_nat_mul_Lscale_neg_gt_one (1 + μ + ε),
      eventually_omega_pos_of_modulus_lower] with
    N hHrare hOmegaRare hPigeonLoss hRadLoss hBadTiny hDelTargetTiny hQlowerOne hOmegaPos
    Q a hRange hDisj hthreshold
  classical
  have hf : (N : ℝ) * Lscale (-(1+μ)) N ≤ (N:ℝ) * Lscale (-1) N :=
    mul_le_mul_of_nonneg_left (Lscale_mono_in_alpha (by linarith) N) (by positivity)
  have hQlarge : ((N : ℝ) * Lscale (-1) N) * Lscale (-ε) N ≤ (Q.card:ℝ) :=
    (mul_le_of_le_one_right (by positivity [Lscale_pos (-1) N]) (Lscale_neg_le_one hε.le N)).trans hthreshold
  let T : ℕ := Nat.floor (3 * Mscale N)
  let BadSmall : Finset ℕ :=
    Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)
  let BadOmega : Finset ℕ :=
    Q.filter (fun q : ℕ => T ≤ omega q)
  let BadH : Finset ℕ :=
    Q.filter (fun q : ℕ => hExpCutoff N < (hExp q : ℝ))
  let Good : Finset ℕ := Q \ (BadSmall ∪ BadOmega ∪ BadH)
  have hQsubset : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hRange q hq)
  have hfQlower :
      (N : ℝ) * Lscale (-(1 + μ + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQlarge hf
  have hQcard_gt_one : (1 : ℝ) < (Q.card : ℝ) :=
    hQlowerOne.trans_le hfQlower
  have hBadSmall_sub : BadSmall ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadOmega_sub : BadOmega ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadH_sub : BadH ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hSmall_small : (BadSmall.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    simpa [BadSmall] using
      small_moduli_count_le_near_extremal_fraction
        (ε := ε) (η := μ) (δ := μ) hmargin_small hRange hQlarge hf
  have hOmega_tail :
      (BadOmega.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hTail :
        (Q.filter (fun q : ℕ => T ≤ omega q)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
      simpa [T] using hOmegaRare Q hQsubset
    simpa [BadOmega] using
      omega_bad_count_le_near_extremal_fraction
        (A := 4 / 3) (ε := ε) (η := μ) (δ := μ)
        hmargin_omega hQlarge hf hTail
  have hH_tail : (BadH.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hRareQ :
        (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) :=
      hHrare Q hQsubset
    simpa [BadH] using
      hExp_bad_count_le_near_extremal_fraction
        (A := 2) (ε := ε) (η := μ) (δ := μ)
        hmargin_small hQlarge hf hRareQ
  have hGood_large_raw :
      (Good.card : ℝ) ≥
        (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) *
          (Q.card : ℝ) := by
    simpa [Good] using
      filter_large_of_three_bad_small Q BadSmall BadOmega BadH
        hBadSmall_sub hBadOmega_sub hBadH_sub
        hSmall_small hOmega_tail hH_tail
  have hGood_large :
      (Q.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Good.card : ℝ) := by
    have hcoeff :
        Lscale (-(ε / 3)) N ≤
          1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N) := by
      linarith [hBadTiny, hDelTargetTiny]
    calc
      (Q.card : ℝ) * Lscale (-(ε / 3)) N
          ≤ (Q.card : ℝ) *
              (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) := by
            exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ ≤ (Good.card : ℝ) := by
            simpa [mul_comm] using hGood_large_raw
  have hGood_nonempty : Good.Nonempty := by
    have hpos : 0 < (Good.card : ℝ) := by
      have hLpos : 0 < Lscale (-(ε / 3)) N := Lscale_pos _ _
      exact lt_of_lt_of_le (mul_pos (lt_trans zero_lt_one hQcard_gt_one) hLpos)
        hGood_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hGood_sub_Q : Good ⊆ Q := by
    intro q hq
    exact Finset.mem_sdiff.1 hq |>.1
  have hGood_modLower :
      ∀ q ∈ Good, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadSmall := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_hExp :
      ∀ q ∈ Good, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadH := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_omega_le : ∀ q ∈ Good, omega q ≤ T := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadOmega := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    have hnotle : ¬ T ≤ omega q := by
      intro hle
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hle⟩)
    omega
  rcases exists_omega_fiber_large Good T hGood_nonempty hGood_omega_le with
    ⟨K, hKleT, hGood_le_fiber⟩
  let Fiber : Finset ℕ := Good.filter fun q : ℕ => omega q = K
  have hFiber_large :
      (Good.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Fiber.card : ℝ) := by
    simpa [Fiber, T] using
      card_lower_of_mul_factor_le_Lscale
        (S := Good) (S' := Good.filter fun q : ℕ => omega q = K)
        (C := T + 1) (N := N) (η := ε / 3)
        hGood_le_fiber hPigeonLoss
  have hFiber_nonempty : Fiber.Nonempty := by
    have hpos : 0 < (Fiber.card : ℝ) := by
      exact lt_of_lt_of_le
        (mul_pos
          (lt_of_lt_of_le
            (mul_pos (lt_trans zero_lt_one hQcard_gt_one) (Lscale_pos _ _))
            hGood_large)
          (Lscale_pos _ _))
        hFiber_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hFiber_sub_Q : Fiber ⊆ Q := by
    intro q hq
    exact hGood_sub_Q (Finset.mem_filter.1 hq).1
  have hFiber_modLower :
      ∀ q ∈ Fiber, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    exact hGood_modLower q (Finset.mem_filter.1 hq).1
  have hFiber_hExp :
      ∀ q ∈ Fiber, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    exact hGood_hExp q (Finset.mem_filter.1 hq).1
  have hFiber_omega : ∀ q ∈ Fiber, omega q = K := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hKbound : (K : ℝ) ≤ 3 * Mscale N := by
    have hT_le : (T : ℝ) ≤ 3 * Mscale N := by
      dsimp [T]
      exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
    have hKleTreal : (K : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hKleT
    exact hKleTreal.trans hT_le
  have hKpos : 1 ≤ K := by
    rcases hFiber_nonempty with ⟨q, hq⟩
    have hOmegaQ : 1 ≤ omega q :=
      hOmegaPos q (hFiber_modLower q hq)
    rw [hFiber_omega q hq] at hOmegaQ
    exact hOmegaQ
  have hCutoff_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  rcases exists_prunedData_after_radical_selection (N := N) (K := K)
      (Q := Q) (S := Fiber) a hFiber_sub_Q hRange hDisj
      hFiber_nonempty hKpos hKbound hCutoff_one
      hFiber_modLower hFiber_hExp hFiber_omega with
    ⟨D, hDF, hFiber_le_D⟩
  have hD_from_fiber :
      (Fiber.card : ℝ) * Lscale (-(ε / 3)) N ≤ (D.Q.card : ℝ) := by
    exact card_lower_of_mul_factor_le_Lscale
      (S := Fiber) (S' := D.Q)
      (C := Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K))
      (N := N) (η := ε / 3) hFiber_le_D (hRadLoss K hKbound)
  refine ⟨D, hDF.trans hFiber_sub_Q, ?_⟩
  have hLsplit :
      Lscale (-ε) N =
        Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
          Lscale (-(ε / 3)) N := by
    calc
      Lscale (-ε) N
          = Lscale (-(ε / 3) + -(ε / 3) + -(ε / 3)) N := by
              congr 1
              ring
      _ = Lscale (-(ε / 3) + -(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
      _ = Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
  calc
    (Q.card : ℝ) * Lscale (-ε) N
        = (((Q.card : ℝ) * Lscale (-(ε / 3)) N) *
            Lscale (-(ε / 3)) N) * Lscale (-(ε / 3)) N := by
          rw [hLsplit]
          ring
    _ ≤ ((Good.card : ℝ) * Lscale (-(ε / 3)) N) *
          Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGood_large (Lscale_nonneg _ _))
            (Lscale_nonneg _ _)
    _ ≤ (Fiber.card : ℝ) * Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right hFiber_large (Lscale_nonneg _ _)
    _ ≤ (D.Q.card : ℝ) := hD_from_fiber
end BFVPruning1190
open Filter BFVPruning1190

private lemma scale_ident (N : ℕ) (c : ℝ) : scaleL N ^ c = Lscale c N := by
  rw [scaleL, ← Real.exp_mul, mul_comm]
  rfl

theorem OMA.solution : OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1.H1 := by
  intro ε he hδ
  filter_upwards [bfv_pruning_small_epsilon_theorem ε he hδ] with N hN Q a hr hd ht
  have hdis : PairwiseDisjointResidues Q (fun i => a i.val) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    exact hd i.val i.property j.val j.property (fun e => hij (Subtype.ext e)) ⟨z,hzi,hzj⟩
  rw [scale_ident] at ht
  obtain ⟨D, hs, hl⟩ := hN Q (fun i => a i.val) hr hdis ht
  refine ⟨D.Q,D.K,hs,?_,D.K_pos,D.K_bound,?_,?_⟩
  · simpa only [scale_ident] using hl
  · intro q hq
    refine ⟨by simpa only [scale_ident] using D.modulus_lower q hq, ?_, ?_⟩
    · simpa only [hExp,primeSupport,Nat.support_factorization] using D.hExp_bound q hq
    · simpa only [omega,primeSupport,Nat.support_factorization] using D.omega_eq q hq
  · simpa only [rad,primeSupport,Nat.support_factorization] using D.rad_injective
