import OMAReductions.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1
import Mathlib

/-! Adapted from Pawan Sasanka Ammanamanchi and collaborators,
Shashi456/erdos-formalizations, Erdos/P202/Proof.lean at
286f856aa3fc08957b80950fd18a45aab8d045ea, used under Apache-2.0.
A spread-family core, prime-factor counts and an iterated product bound give
the upper estimate for a single regular family. -/
namespace BFVRegular1190
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

lemma eventually_Mscale_le_log :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Real.log (N : ℝ) := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrt
  rw [Mscale]
  rw [Real.sqrt_le_left hlog_nonneg]
  have hquot_le_log :
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    exact (div_le_iff₀ hloglog_pos).2 (by nlinarith [hlog_nonneg, hloglog_ge_one])
  have hlog_le_sq : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [hlog_gt_one.le]
  exact hquot_le_log.trans hlog_le_sq

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

lemma Lscale_mono_in_alpha {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    Lscale α N ≤ Lscale β N := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (Zscale_nonneg N))

lemma log_nat_mul_Lscale {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Real.log ((N : ℝ) * Lscale α N) = Real.log (N : ℝ) + α * Zscale N := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL : Lscale α N ≠ 0 := (Lscale_pos α N).ne'
  rw [Real.log_mul hNreal hL, Lscale, Real.log_exp]

lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  constructor
  · rintro ⟨n, hnq, hnr⟩
    rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd] at hnq hnr
    rw [Int.modEq_iff_dvd]
    have hdq : (Nat.gcd q r : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left q r
    have hdr : (Nat.gcd q r : ℤ) ∣ (r : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right q r
    have hqa : (Nat.gcd q r : ℤ) ∣ a - n := dvd_trans hdq hnq
    have hrb : (Nat.gcd q r : ℤ) ∣ b - n := dvd_trans hdr hnr
    have hsub : (Nat.gcd q r : ℤ) ∣ (b - n) - (a - n) := dvd_sub hrb hqa
    convert hsub using 1
    ring
  · intro hab
    rw [Int.modEq_iff_dvd] at hab
    rcases hab with ⟨k, hk⟩
    let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
    refine ⟨n, ?_, ?_⟩
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨-(Nat.gcdA q r * k), ?_⟩
      simp [n]
      ring
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨Nat.gcdB q r * k, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab q r
      calc
        b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
          simp [n]
          ring
        _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hk]
        _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
              - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hbez]
        _ = (r : ℤ) * (Nat.gcdB q r * k) := by
          ring

lemma residueClass_disjoint_iff
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
    Disjoint (residueClass q a) (residueClass r b) ↔
      ¬ a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  rw [Set.disjoint_iff_inter_eq_empty]
  constructor
  · intro h hmod
    have hne : (residueClass q a ∩ residueClass r b).Nonempty :=
      (residueClass_inter_nonempty_iff hq hr a b).2 hmod
    exact hne.ne_empty h
  · intro hmod
    ext n
    constructor
    · intro hn
      exact False.elim (hmod ((residueClass_inter_nonempty_iff hq hr a b).1 ⟨n, hn⟩))
    · intro hn
      cases hn

end BFVRegular1190
namespace BFVRegular1190
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

lemma hExp_inv_sq_pos (n : ℕ) : 0 < (1 : ℝ) / ((hExp n : ℝ) ^ 2) := by
  have hn : 0 < (hExp n : ℝ) := by exact_mod_cast hExp_pos n
  positivity

lemma prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) : Nat.Prime p := by
  unfold primeSupport at hp
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

lemma mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : p ∈ primeSupport n := by
  unfold primeSupport
  rw [Finsupp.mem_support_iff]
  exact hp.factorization_pos_of_dvd hn hpn |>.ne'

lemma coprime_of_disjoint_primeSupport {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hdisj : Disjoint (primeSupport m) (primeSupport n)) :
    Nat.Coprime m n := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpm hpn
  exact (Finset.disjoint_left.1 hdisj)
    (mem_primeSupport_of_prime_dvd hp hm hpm)
    (mem_primeSupport_of_prime_dvd hp hn hpn)

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

lemma omega_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [primeSupport_mul_of_coprime hcop]
  exact Finset.card_union_of_disjoint (primeSupport_disjoint_of_coprime hcop)

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

lemma exactBlock_congr_on {C : Finset ℕ} {m n : ℕ}
    (h : ∀ p ∈ C, m.factorization p = n.factorization p) :
    exactBlock C m = exactBlock C n := by
  unfold exactBlock
  apply Finset.prod_congr rfl
  intro p hp
  rw [h p hp]

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

lemma hExp_exactBlock_le_hExp (C : Finset ℕ) (q : ℕ) :
    hExp (exactBlock C q) ≤ hExp q := by
  by_cases hq : q = 0
  · simp [hExp, primeSupport, exactBlock, hq]
  · have hdvd : exactBlock C q ∣ q := exactBlock_dvd C q
    have hdne : exactBlock C q ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)).ne'
    have hlefac : (exactBlock C q).factorization ≤ q.factorization :=
      (Nat.factorization_le_iff_dvd hdne hq).2 hdvd
    have hsub : primeSupport (exactBlock C q) ⊆ primeSupport q := by
      intro p hp
      unfold primeSupport at hp ⊢
      rw [Finsupp.mem_support_iff] at hp ⊢
      exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
    unfold hExp
    have hprod1 :
        (∏ p ∈ primeSupport (exactBlock C q), (exactBlock C q).factorization p)
          ≤ ∏ p ∈ primeSupport (exactBlock C q), q.factorization p := by
      exact Finset.prod_le_prod' (fun p _hp => hlefac p)
    have hprod2 :
        (∏ p ∈ primeSupport (exactBlock C q), q.factorization p)
          ≤ ∏ p ∈ primeSupport q, q.factorization p := by
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
        unfold primeSupport at hp
        rw [Finsupp.mem_support_iff] at hp
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
    exact hprod1.trans hprod2

lemma hExp_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    hExp m ≤ hExp n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hlefac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  have hsub : primeSupport m ⊆ primeSupport n := by
    intro p hp
    unfold primeSupport at hp ⊢
    rw [Finsupp.mem_support_iff] at hp ⊢
    exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
  unfold hExp
  have hprod1 :
      (∏ p ∈ primeSupport m, m.factorization p)
        ≤ ∏ p ∈ primeSupport m, n.factorization p := by
    exact Finset.prod_le_prod' (fun p _hp => hlefac p)
  have hprod2 :
      (∏ p ∈ primeSupport m, n.factorization p)
        ≤ ∏ p ∈ primeSupport n, n.factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
      unfold primeSupport at hp
      rw [Finsupp.mem_support_iff] at hp
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
  exact hprod1.trans hprod2

def remainingSupport (P q : ℕ) : Finset ℕ :=
  primeSupport (q / P)

lemma primeSupport_subset_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    primeSupport m ⊆ primeSupport n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  intro p hp
  unfold primeSupport at hp ⊢
  rw [Finsupp.mem_support_iff] at hp ⊢
  intro hnzero
  exact hp (Nat.eq_zero_of_le_zero (by simpa [hnzero] using hle p))

lemma omega_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    omega m ≤ omega n := by
  unfold omega
  exact Finset.card_le_card (primeSupport_subset_of_dvd hmn hn)

lemma primeSupport_div_subset_of_dvd {P q : ℕ} (hPq : P ∣ q) (hq : q ≠ 0) :
    primeSupport (q / P) ⊆ primeSupport q :=
  primeSupport_subset_of_dvd (by
    refine ⟨P, ?_⟩
    exact (Nat.div_mul_cancel hPq).symm) hq

lemma primeSupport_eq_union_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0) :
    primeSupport q = primeSupport P ∪ primeSupport (q / P) := by
  ext p
  unfold primeSupport
  rw [Finset.mem_union]
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro hqfac
    by_cases hPfac : P.factorization p = 0
    · right
      have hdivfac :
          (q / P).factorization p = q.factorization p - P.factorization p := by
        rw [Nat.factorization_div hPq]
        rfl
      rw [hdivfac, hPfac, Nat.sub_zero]
      exact hqfac
    · exact Or.inl hPfac
  · rintro (hPfac | hdivfac)
    · have hle : P.factorization ≤ q.factorization :=
        (Nat.factorization_le_iff_dvd hP hq).2 hPq
      intro hqzero
      exact hPfac (Nat.eq_zero_of_le_zero (by simpa [hqzero] using hle p))
    · have hmem : p ∈ primeSupport (q / P) := by
        unfold primeSupport
        rw [Finsupp.mem_support_iff]
        exact hdivfac
      have hmemq := primeSupport_div_subset_of_dvd hPq hq hmem
      unfold primeSupport at hmemq
      rwa [Finsupp.mem_support_iff] at hmemq

lemma mem_remainingSupport_iff_factorization_lt {P q p : ℕ} (hPq : P ∣ q) :
    p ∈ remainingSupport P q ↔ P.factorization p < q.factorization p := by
  unfold remainingSupport primeSupport
  rw [Finsupp.mem_support_iff, Nat.factorization_div hPq]
  exact Nat.sub_ne_zero_iff_lt

lemma omega_eq_add_omega_div_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega q = omega P + omega (q / P) := by
  unfold omega
  rw [primeSupport_eq_union_of_dvd hPq hP hq, Finset.card_union_of_disjoint hdisj]

lemma omega_div_eq_sub_omega_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega (q / P) = omega q - omega P := by
  have hsum := omega_eq_add_omega_div_of_dvd hPq hP hq hdisj
  omega

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

lemma gcd_dvd_of_disjoint_remainingSupport {P q r : ℕ}
    (hPq : P ∣ q) (hPr : P ∣ r)
    (hP : P ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hdisj : Disjoint (remainingSupport P q) (remainingSupport P r)) :
    Nat.gcd q r ∣ P := by
  rw [← Nat.factorization_le_iff_dvd (by
      intro hg
      exact hq (Nat.gcd_eq_zero_iff.mp hg).1) hP]
  rw [Nat.factorization_gcd hq hr]
  intro p
  rw [Finsupp.inf_apply]
  have hPq_fac : P.factorization p ≤ q.factorization p :=
    (Nat.factorization_le_iff_dvd hP hq).2 hPq p
  have hPr_fac : P.factorization p ≤ r.factorization p :=
    (Nat.factorization_le_iff_dvd hP hr).2 hPr p
  by_cases hqextra : P.factorization p < q.factorization p
  · have hrnot : ¬ P.factorization p < r.factorization p := by
      intro hrextra
      exact (Finset.disjoint_left.1 hdisj)
        ((mem_remainingSupport_iff_factorization_lt hPq).2 hqextra)
        ((mem_remainingSupport_iff_factorization_lt hPr).2 hrextra)
    have hrle : r.factorization p ≤ P.factorization p := le_of_not_gt hrnot
    exact le_trans (min_le_right _ _) hrle
  · have hqle : q.factorization p ≤ P.factorization p := le_of_not_gt hqextra
    exact le_trans (min_le_left _ _) hqle

end BFVRegular1190
namespace BFVRegular1190
open Finset
open scoped BigOperators
def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T

end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

lemma subset_upClosureIn {X : Finset α} {A : Finset (Finset α)}
    (hAX : ∀ S ∈ A, S ⊆ X) :
    A ⊆ upClosureIn X A := by
  intro S hS
  exact mem_upClosureIn.mpr ⟨hAX S hS, S, hS, subset_refl _⟩

lemma nonempty_of_upClosureIn_nonempty {X : Finset α} {A : Finset (Finset α)}
    (h : (upClosureIn X A).Nonempty) :
    A.Nonempty := by
  rcases h with ⟨T, hT⟩
  rcases mem_upClosureIn.mp hT with ⟨_, S, hSA, _⟩
  exact ⟨S, hSA⟩

lemma empty_mem_upClosureIn_iff {X : Finset α} {A : Finset (Finset α)} :
    (∅ : Finset α) ∈ upClosureIn X A ↔ (∅ : Finset α) ∈ A := by
  constructor
  · intro h
    rcases mem_upClosureIn.mp h with ⟨_, S, hSA, hSempty⟩
    have hS_eq : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hSempty hx
    simpa [hS_eq] using hSA
  · intro h
    exact mem_upClosureIn.mpr ⟨Finset.empty_subset X, ∅, h, subset_refl _⟩

lemma empty_not_mem_upClosureIn_iff {X : Finset α} {A : Finset (Finset α)} :
    (∅ : Finset α) ∉ upClosureIn X A ↔ (∅ : Finset α) ∉ A := by
  rw [empty_mem_upClosureIn_iff]

def IncreasingIn (X : Finset α) (U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U

lemma increasingIn_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    IncreasingIn X (upClosureIn X A) := by
  intro S hS T hTX hST
  rcases mem_upClosureIn.mp hS with ⟨_, S₀, hS₀A, hS₀S⟩
  exact mem_upClosureIn.mpr ⟨hTX, S₀, hS₀A, hS₀S.trans hST⟩

lemma upClosureIn_singleton_subset_of_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hIncr : IncreasingIn X U) (hS : S ∈ U) :
    upClosureIn X {S} ⊆ U := by
  intro T hT
  rcases mem_upClosureIn.mp hT with ⟨hTX, R, hR, hRT⟩
  have hR_eq : R = S := by simpa using hR
  exact hIncr S hS T hTX (by simpa [hR_eq] using hRT)

omit [DecidableEq α] in
lemma top_mem_of_nonempty_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) :
    X ∈ U := by
  rcases hU with ⟨S, hS⟩
  exact hIncr S hS X (subset_refl X) (hUX S hS)

omit [DecidableEq α] in
lemma eq_powerset_of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    U = X.powerset := by
  ext S
  constructor
  · intro hS
    exact Finset.mem_powerset.mpr (hUX S hS)
  · intro hS
    exact hIncr ∅ hEmpty S (Finset.mem_powerset.mp hS) (Finset.empty_subset S)

def minimalMembersIn (_X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
  U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S

@[simp]
lemma mem_minimalMembersIn {X : Finset α} {U : Finset (Finset α)} {S : Finset α} :
    S ∈ minimalMembersIn X U ↔ S ∈ U ∧ ∀ T ∈ U, ¬ T ⊂ S := by
  simp [minimalMembersIn]

lemma minimalMembersIn_subset {X : Finset α} {U : Finset (Finset α)} :
    minimalMembersIn X U ⊆ U := by
  intro S hS
  exact (mem_minimalMembersIn.mp hS).1

lemma not_ssubset_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
    (hS : S ∈ minimalMembersIn X U) (hT : T ∈ minimalMembersIn X U) :
    ¬ S ⊂ T := by
  exact (mem_minimalMembersIn.mp hT).2 S ((mem_minimalMembersIn.mp hS).1)

lemma eq_of_subset_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
    (hS : S ∈ minimalMembersIn X U) (hT : T ∈ minimalMembersIn X U)
    (hST : S ⊆ T) :
    S = T := by
  by_contra hne
  exact not_ssubset_of_mem_minimalMembersIn hS hT (hST.ssubset_of_ne hne)

def InclusionAntichain (A : Finset (Finset α)) : Prop :=
  ∀ S ∈ A, ∀ T ∈ A, S ⊆ T → T ⊆ S

lemma minimalMembersIn_inclusionAntichain (X : Finset α) (U : Finset (Finset α)) :
    InclusionAntichain (minimalMembersIn X U) := by
  intro S hS T hT hST
  have hEq : S = T := eq_of_subset_of_mem_minimalMembersIn hS hT hST
  simp [hEq]

noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembersIn X U).sup Finset.card)

lemma two_le_ell (X : Finset α) (U : Finset (Finset α)) : 2 ≤ ell X U :=
  le_max_left _ _

lemma ell_pos (X : Finset α) (U : Finset (Finset α)) : 0 < ell X U :=
  lt_of_lt_of_le (by norm_num) (two_le_ell X U)

lemma card_le_ell_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ minimalMembersIn X U) :
    S.card ≤ ell X U := by
  unfold ell
  exact (Finset.le_sup (s := minimalMembersIn X U) (f := Finset.card) hS).trans
    (le_max_right _ _)

lemma exists_minimal_subset
    {X : Finset α} {U : Finset (Finset α)}
    {S : Finset α} (hS : S ∈ U) :
    ∃ T ∈ minimalMembersIn X U, T ⊆ S := by
  classical
  
  let candidates : Finset (Finset α) := U.filter fun T => T ⊆ S
  have hSc : S ∈ candidates := by
    simp [candidates, hS, subset_refl]
  rcases candidates.exists_min_image Finset.card ⟨S, hSc⟩ with ⟨T₀, hT₀, hmin⟩
  have hT₀U : T₀ ∈ U := (Finset.mem_filter.mp hT₀).1
  have hT₀S : T₀ ⊆ S := (Finset.mem_filter.mp hT₀).2
  refine ⟨T₀, mem_minimalMembersIn.mpr ⟨hT₀U, ?_⟩, hT₀S⟩
  intro T hTU hT_lt
  
  
  have hTS : T ⊆ S := hT_lt.subset.trans hT₀S
  have hTcand : T ∈ candidates := by
    simp [candidates, hTU, hTS]
  have : T₀.card ≤ T.card := hmin T hTcand
  have hlt : T.card < T₀.card := Finset.card_lt_card hT_lt
  exact absurd this (not_le.mpr hlt)

lemma minimalMembersIn_nonempty_of_nonempty
    {X : Finset α} {U : Finset (Finset α)} (hU : U.Nonempty) :
    (minimalMembersIn X U).Nonempty := by
  rcases hU with ⟨S, hS⟩
  rcases exists_minimal_subset (X := X) hS with ⟨T, hT, _⟩
  exact ⟨T, hT⟩

lemma upClosureIn_minimalMembersIn_eq_of_increasing
    {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U) :
    upClosureIn X (minimalMembersIn X U) = U := by
  ext S
  constructor
  · intro hS
    rcases mem_upClosureIn.mp hS with ⟨hSX, T, hTmin, hTS⟩
    exact hIncr T (minimalMembersIn_subset hTmin) S hSX hTS
  · intro hSU
    rcases exists_minimal_subset (X := X) hSU with ⟨T, hTmin, hTS⟩
    exact mem_upClosureIn.mpr ⟨hUX S hSU, T, hTmin, hTS⟩

lemma mem_minimalMembersIn_upClosureIn_iff_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} :
    S ∈ minimalMembersIn X (upClosureIn X A) ↔ S ∈ A := by
  constructor
  · intro hS
    rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
    rcases mem_upClosureIn.mp hSup with ⟨_, S₀, hS₀A, hS₀S⟩
    have hS₀_up : S₀ ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S₀ hS₀A, S₀, hS₀A, subset_refl _⟩
    have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
    have hS₀_eq_S : S₀ = S := by
      by_contra hne
      exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
    simpa [← hS₀_eq_S] using hS₀A
  · intro hSA
    refine mem_minimalMembersIn.mpr ⟨?_, ?_⟩
    · exact mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    · intro T hTup hTlt
      rcases mem_upClosureIn.mp hTup with ⟨_, S₀, hS₀A, hS₀T⟩
      have hS₀S : S₀ ⊆ S := hS₀T.trans hTlt.subset
      have hSS₀ : S ⊆ S₀ := hAnti S₀ hS₀A S hSA hS₀S
      have hST : S ⊆ T := hSS₀.trans hS₀T
      have hTS : T ⊆ S := hTlt.subset
      have hEq : T = S := le_antisymm hTS hST
      exact hTlt.ne hEq

lemma minimalMembersIn_upClosureIn_eq_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    minimalMembersIn X (upClosureIn X A) = A := by
  ext S
  exact mem_minimalMembersIn_upClosureIn_iff_of_inclusionAntichain hAnti hAX

theorem ell_upClosure_eq_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) = max 2 (A.sup Finset.card) := by
  unfold ell
  rw [minimalMembersIn_upClosureIn_eq_of_inclusionAntichain hAnti hAX]

lemma minimalMembersIn_upClosureIn_card_le
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : BFVRegular1190.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} (hS : S ∈ minimalMembersIn X (upClosureIn X A)) :
    S.card ≤ k := by
  classical
  rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
  rcases mem_upClosureIn.mp hSup with ⟨hSX, S₀, hS₀A, hS₀S⟩
  
  have hS₀_up : S₀ ∈ upClosureIn X A :=
    mem_upClosureIn.mpr ⟨(hAX S₀ hS₀A), S₀, hS₀A, subset_refl _⟩
  have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
  
  have hS₀_eq_S : S₀ = S := by
    by_contra hne
    exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
  
  have : S.card = k := hS₀_eq_S ▸ hUniform S₀ hS₀A
  exact this.le

theorem ell_upClosure_le {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : BFVRegular1190.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) ≤ max 2 k := by
  classical
  have hsup_le : (minimalMembersIn X (upClosureIn X A)).sup Finset.card ≤ k := by
    refine Finset.sup_le ?_
    intro S hS
    exact minimalMembersIn_upClosureIn_card_le hUniform hAX hS
  unfold ell
  exact max_le_max le_rfl hsup_le

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

omit [DecidableEq α] in
lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma muP_mono_family {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : muP X U p ≤ muP X V p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
    exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
  · intros
    exact bernoulliMass_nonneg h0 h1

omit [DecidableEq α] in
lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]

lemma muP_le_one {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : muP X U p ≤ 1 := by
  have hsum := sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsub : muP X U p ≤ ∑ S ∈ X.powerset, bernoulliMass X S p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS; exact (Finset.mem_filter.mp hS).1
    · intros; exact bernoulliMass_nonneg h0 h1
  linarith

omit [DecidableEq α] in
lemma half_lt_weighted_good_of_average_lt_half_of_bad_le
    {Ω : Type*} [DecidableEq Ω] (s : Finset Ω)
    (weight : Ω → ℝ) (Good : Ω → Prop) [DecidablePred Good]
    (F : Ω → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hB : 0 < B)
    (hF_nonneg : ∀ ω ∈ s, 0 ≤ F ω)
    (hbad : ∀ ω ∈ s, ¬ Good ω → B ≤ F ω)
    (havg : (∑ ω ∈ s, weight ω * F ω) < B * (1 / 2)) :
    (1 / 2 : ℝ) < ∑ ω ∈ s.filter Good, weight ω := by
  let bad : Finset Ω := s.filter fun ω => ¬ Good ω
  have hbad_weight_le :
      (∑ ω ∈ bad, weight ω * B) ≤
        ∑ ω ∈ bad, weight ω * F ω := by
    refine Finset.sum_le_sum ?_
    intro ω hωbad
    have hωs : ω ∈ s := (Finset.mem_filter.mp hωbad).1
    have hωGood : ¬ Good ω := (Finset.mem_filter.mp hωbad).2
    exact mul_le_mul_of_nonneg_left (hbad ω hωs hωGood)
      (hweight_nonneg ω hωs)
  have hbad_avg_le :
      (∑ ω ∈ bad, weight ω * F ω) ≤
        ∑ ω ∈ s, weight ω * F ω := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro ω hωs _hωnot
    exact mul_nonneg (hweight_nonneg ω hωs) (hF_nonneg ω hωs)
  have hbad_mass_mul_lt :
      (∑ ω ∈ bad, weight ω) * B < B * (1 / 2) := by
    calc
      (∑ ω ∈ bad, weight ω) * B
          = ∑ ω ∈ bad, weight ω * B := by
              rw [Finset.sum_mul]
      _ ≤ ∑ ω ∈ bad, weight ω * F ω := hbad_weight_le
      _ ≤ ∑ ω ∈ s, weight ω * F ω := hbad_avg_le
      _ < B * (1 / 2) := havg
  have hbad_mass_lt_half :
      (∑ ω ∈ bad, weight ω) < (1 / 2 : ℝ) := by
    have hbad_mass_mul_lt' :
        (∑ ω ∈ bad, weight ω) * B < (1 / 2 : ℝ) * B := by
      linarith
    exact lt_of_mul_lt_mul_right hbad_mass_mul_lt' hB.le
  have hsplit :
      (∑ ω ∈ s.filter Good, weight ω) + (∑ ω ∈ bad, weight ω) = 1 := by
    have hsplit_raw :=
      Finset.sum_filter_add_sum_filter_not
        (s := s) (p := Good) (f := weight)
    unfold bad
    simpa using hsplit_raw.trans hsum_weight
  linarith

noncomputable def exposureTupleSpace (X : Finset α) (n : ℕ) :
    Finset (Fin n → Finset α) :=
  Fintype.piFinset fun _ : Fin n => X.powerset

omit [DecidableEq α] in
lemma mem_exposureTupleSpace
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α} :
    Ws ∈ exposureTupleSpace X n ↔ ∀ i, Ws i ∈ X.powerset := by
  simp [exposureTupleSpace, Fintype.mem_piFinset]

noncomputable def exposureTupleWeight
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ)
    (Ws : Fin n → Finset α) : ℝ :=
  ∏ i, bernoulliMass X (Ws i) (ρ i)

omit [DecidableEq α] in
lemma exposureTupleWeight_nonneg
    (X : Finset α) {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (Ws : Fin n → Finset α) :
    0 ≤ exposureTupleWeight X ρ Ws := by
  unfold exposureTupleWeight
  exact Finset.prod_nonneg fun i _hi =>
    bernoulliMass_nonneg (hρ0 i) (hρ1 i)

omit [DecidableEq α] in
lemma sum_exposureTupleWeight_eq_one
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ) :
    (∑ Ws ∈ exposureTupleSpace X n, exposureTupleWeight X ρ Ws) = 1 := by
  unfold exposureTupleSpace exposureTupleWeight
  rw [Finset.sum_prod_piFinset
    (s := X.powerset)
    (g := fun i W => bernoulliMass X W (ρ i))]
  simp [sum_bernoulliMass_eq_one]

def exposureTupleUnion {n : ℕ} (Ws : Fin n → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin n)).biUnion fun i => Ws i

noncomputable def tupleUnionDensity {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
  1 - ∏ i, (1 - ρ i)

omit [DecidableEq α] in
lemma tupleUnionDensity_snoc {n : ℕ} (ρ : Fin (n + 1) → ℝ) :
    tupleUnionDensity ρ =
      1 - (1 - tupleUnionDensity (fun i : Fin n => ρ i.castSucc)) *
        (1 - ρ (Fin.last n)) := by
  unfold tupleUnionDensity
  rw [Fin.prod_univ_castSucc]
  ring

omit [DecidableEq α] in
lemma tupleUnionDensity_nonneg {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    0 ≤ tupleUnionDensity ρ := by
  have hprod_le_one : (∏ i, (1 - ρ i)) ≤ (1 : ℝ) := by
    refine Finset.prod_le_one ?_ ?_
    · intro i _hi
      exact sub_nonneg.mpr (hρ1 i)
    · intro i _hi
      linarith [hρ0 i]
  unfold tupleUnionDensity
  linarith

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    tupleUnionDensity ρ ≤ ∑ i, ρ i := by
  induction n with
  | zero =>
      simp [tupleUnionDensity]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      have htail0 : ∀ i : Fin n, 0 ≤ ρtail i := fun i => hρ0 i.castSucc
      have htail1 : ∀ i : Fin n, ρtail i ≤ 1 := fun i => hρ1 i.castSucc
      have htail_le : tupleUnionDensity ρtail ≤ ∑ i, ρtail i :=
        ih htail0 htail1
      have htail_nonneg : 0 ≤ tupleUnionDensity ρtail :=
        tupleUnionDensity_nonneg htail0 htail1
      have hlast_nonneg : 0 ≤ ρ (Fin.last n) := hρ0 (Fin.last n)
      have hsplit :
          tupleUnionDensity ρ ≤ tupleUnionDensity ρtail + ρ (Fin.last n) := by
        rw [tupleUnionDensity_snoc]
        have hmul_nonneg :
            0 ≤ tupleUnionDensity ρtail * ρ (Fin.last n) :=
          mul_nonneg htail_nonneg hlast_nonneg
        nlinarith
      have hsum :
          (∑ i : Fin (n + 1), ρ i) =
            (∑ i : Fin n, ρtail i) + ρ (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]
      exact hsplit.trans (by
        rw [hsum]
        have h := add_le_add_right htail_le (ρ (Fin.last n))
        simpa [add_comm, add_left_comm, add_assoc] using h)

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum_of_le {n : ℕ} {ρ B : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hρB : ∀ i, ρ i ≤ B i) :
    tupleUnionDensity ρ ≤ ∑ i, B i := by
  exact (tupleUnionDensity_le_sum hρ0 hρ1).trans
    (Finset.sum_le_sum fun i _hi => hρB i)

lemma exposureTupleUnion_subset
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X n) :
    exposureTupleUnion Ws ⊆ X := by
  intro x hx
  rcases (by simpa [exposureTupleUnion] using hx : ∃ i, x ∈ Ws i) with
    ⟨i, hxi⟩
  exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i) hxi

@[simp] lemma exposureTupleUnion_snoc {n : ℕ}
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleUnion
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleUnion Ws ∪ W := by
  ext x
  constructor
  · intro hx
    rcases (by
      simpa [exposureTupleUnion] using hx :
        ∃ i : Fin (n + 1),
          x ∈ (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) i) with
      ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Finset.mem_union.mpr (Or.inl (by
        simpa [exposureTupleUnion] using (Exists.intro j (by simpa using hi))))
    · exact Finset.mem_union.mpr (Or.inr (by simpa using hi))
  · intro hx
    rcases Finset.mem_union.mp hx with htail | hlast
    · rcases (by
        simpa [exposureTupleUnion] using htail :
          ∃ i : Fin n, x ∈ Ws i) with ⟨i, hi⟩
      simpa [exposureTupleUnion] using
        (Exists.intro (i.castSucc : Fin (n + 1)) (by simpa using hi))
    · simpa [exposureTupleUnion] using
        (Exists.intro (Fin.last n) (by simpa using hlast))

omit [DecidableEq α] in
lemma exposureTupleSpace_snoc (X : Finset α) (n : ℕ) :
    exposureTupleSpace X (n + 1) =
      (X.powerset ×ˢ exposureTupleSpace X n).map
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding := by
  ext Ws
  constructor
  · intro hWs
    refine Finset.mem_map.mpr ⟨⟨Ws (Fin.last n),
      fun i : Fin n => Ws i.castSucc⟩, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_exposureTupleSpace.mp hWs) (Fin.last n),
          mem_exposureTupleSpace.mpr fun i =>
            (mem_exposureTupleSpace.mp hWs) i.castSucc⟩
    · exact (Fin.snocEquiv
        (fun _ : Fin (n + 1) => Finset α)).right_inv Ws
  · intro hWs
    rcases Finset.mem_map.mp hWs with ⟨⟨W, Ws₀⟩, hpair, hEq⟩
    rw [← hEq]
    rcases Finset.mem_product.mp hpair with ⟨hW, hWs₀⟩
    refine mem_exposureTupleSpace.mpr ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa using (mem_exposureTupleSpace.mp hWs₀) j
    · simpa using hW

omit [DecidableEq α] in
@[simp] lemma exposureTupleWeight_snoc {n : ℕ}
    (X : Finset α) (ρ : Fin (n + 1) → ℝ)
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleWeight X ρ
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
        bernoulliMass X W (ρ (Fin.last n)) := by
  unfold exposureTupleWeight
  rw [Fin.prod_univ_castSucc]
  simp

omit [DecidableEq α] in
lemma nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (L : ℝ) * q * (1 - q) ^ L ≤ 1 - (1 - q) ^ L := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hq_eq : q = 1 - r := by dsimp [r]; ring
  have hsum_ge :
      (L : ℝ) * r ^ L ≤ ∑ i ∈ Finset.range L, r ^ i := by
    calc
      (L : ℝ) * r ^ L = ∑ _i ∈ Finset.range L, r ^ L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range L, r ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact pow_le_pow_of_le_one hr0 hr1
          (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_ge (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    (L : ℝ) * q * (1 - q) ^ L
        = ((L : ℝ) * r ^ L) * (1 - r) := by
          dsimp [r]
          ring
    _ ≤ (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := hmul
    _ = 1 - r ^ L := geom_sum_mul_neg r L
    _ = 1 - (1 - q) ^ L := by rfl

omit [DecidableEq α] in
lemma one_sub_one_sub_q_pow_pos
    {q : ℝ} {L : ℕ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    0 < 1 - (1 - q) ^ L := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q ≤ 1 := by linarith
  have hpow_le : (1 - q) ^ L ≤ (1 - q) ^ 1 :=
    pow_le_pow_of_le_one hr0 hr1 hL
  have hq_le : q ≤ 1 - (1 - q) ^ L := by
    simpa using sub_le_sub_left hpow_le 1
  exact lt_of_lt_of_le hq0 hq_le

omit [DecidableEq α] in
lemma one_sub_one_sub_q_pow_le_nat_mul
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (1 - q) ^ L ≤ (L : ℝ) * q := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hsum_le :
      (∑ i ∈ Finset.range L, r ^ i) ≤
        ∑ _i ∈ Finset.range L, (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact pow_le_one₀ hr0 hr1
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_le (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    1 - (1 - q) ^ L = (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := by
        dsimp [r]
        rw [geom_sum_mul_neg]
    _ ≤ (∑ _i ∈ Finset.range L, (1 : ℝ)) * (1 - r) := hmul
    _ = (L : ℝ) * q := by
        dsimp [r]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

omit [DecidableEq α] in
lemma tupleUnionDensity_one_sub_pow_le_q_sum
    {q : ℝ} {n : ℕ} (L : Fin n → ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i) ≤
      q * ∑ i : Fin n, (L i : ℝ) := by
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 :
      ∀ i : Fin n, 0 ≤ 1 - (1 - q) ^ L i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    linarith
  have hρ1 :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    linarith
  have hbound :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ (L i : ℝ) * q := by
    intro i
    exact one_sub_one_sub_q_pow_le_nat_mul hq0 hq1
  calc
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i)
        ≤ ∑ i : Fin n, (L i : ℝ) * q :=
          tupleUnionDensity_le_sum_of_le hρ0 hρ1 hbound
    _ = q * ∑ i : Fin n, (L i : ℝ) := by
          rw [← Finset.sum_mul]
          ring

lemma bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
    {X W S : Finset α} {q ρ : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hdisj : Disjoint S W) (hUnionX : W ∪ S ⊆ X) :
    bernoulliMass X W ρ * q ^ S.card ≤
      bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
  have hρ_pos : 0 < ρ := by
    simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hone_minus_ρ_nonneg : 0 ≤ 1 - ρ := by linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hsingle : q * (1 - ρ) ≤ ρ * (1 / (L : ℝ)) := by
    have hmain :
        (L : ℝ) * q * (1 - ρ) ≤ ρ := by
      have hraw :=
        nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
          (q := q) (L := L) hq0.le hq1
      simpa [hρ, mul_assoc, mul_comm, mul_left_comm] using hraw
    rw [← div_eq_mul_one_div]
    rw [le_div_iff₀ hLpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  have hpow_single :
      (q * (1 - ρ)) ^ S.card ≤ (ρ * (1 / (L : ℝ))) ^ S.card :=
    pow_le_pow_left₀ (mul_nonneg hq0.le hone_minus_ρ_nonneg) hsingle S.card
  have hcard_union : (W ∪ S).card = W.card + S.card := by
    rw [Finset.card_union_of_disjoint]
    exact hdisj.symm
  have hWsub : W ⊆ W ∪ S := Finset.subset_union_left
  have hWcard_le : W.card ≤ X.card :=
    Finset.card_le_card (hWsub.trans hUnionX)
  have hUcard_le : (W ∪ S).card ≤ X.card :=
    Finset.card_le_card hUnionX
  have hdiff : X.card - W.card = (X.card - (W ∪ S).card) + S.card := by
    rw [hcard_union]
    omega
  have hcommon_nonneg :
      0 ≤ ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card) := by
    positivity
  calc
    bernoulliMass X W ρ * q ^ S.card
        = (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
            (q * (1 - ρ)) ^ S.card := by
          unfold bernoulliMass
          rw [hdiff, pow_add, mul_pow]
          ring
    _ ≤ (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
          (ρ * (1 / (L : ℝ))) ^ S.card :=
        mul_le_mul_of_nonneg_left hpow_single hcommon_nonneg
    _ = bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
          unfold bernoulliMass
          rw [hcard_union, pow_add, mul_pow]
          ring

omit [DecidableEq α] in
lemma bernoulliMass_self_one (X : Finset α) :
    bernoulliMass X X (1 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
lemma bernoulliMass_one_of_ne_top {X S : Finset α}
    (hSX : S ⊆ X) (hS_ne : S ≠ X) :
    bernoulliMass X S (1 : ℝ) = 0 := by
  have hlt : S.card < X.card := Finset.card_lt_card (hSX.ssubset_of_ne hS_ne)
  have hpos : 0 < X.card - S.card := Nat.sub_pos_of_lt hlt
  simp [bernoulliMass, hpos.ne']

lemma muP_one_of_mem_top {X : Finset α} {U : Finset (Finset α)}
    (hXU : X ∈ U) :
    muP X U (1 : ℝ) = 1 := by
  classical
  unfold muP
  refine Finset.sum_eq_single_of_mem X ?_ ?_ |>.trans (bernoulliMass_self_one X)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl X), hXU⟩
  · intro S hS hS_ne
    have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    exact bernoulliMass_one_of_ne_top hSX hS_ne

lemma muP_one_of_nonempty_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) :
    muP X U (1 : ℝ) = 1 :=
  muP_one_of_mem_top (top_mem_of_nonempty_increasing hUX hIncr hU)

omit [DecidableEq α] in
lemma bernoulliMass_empty_zero (X : Finset α) :
    bernoulliMass X ∅ (0 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
lemma bernoulliMass_zero_of_nonempty {X S : Finset α}
    (hS : S.Nonempty) :
    bernoulliMass X S (0 : ℝ) = 0 := by
  simp [bernoulliMass, hS.card_pos.ne']

lemma muP_zero_of_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (0 : ℝ) = 1 := by
  classical
  unfold muP
  refine (Finset.sum_eq_single_of_mem ∅ ?_ ?_).trans (bernoulliMass_empty_zero X)
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset X), hEmpty⟩
  · intro S hS hS_ne
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_ne
    exact bernoulliMass_zero_of_nonempty hS_nonempty

lemma muP_zero_of_not_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∉ U) :
    muP X U (0 : ℝ) = 0 := by
  classical
  unfold muP
  refine Finset.sum_eq_zero ?_
  intro S hS
  have hSU : S ∈ U := (Finset.mem_filter.mp hS).2
  have hS_ne : S ≠ ∅ := by
    intro hS_empty
    exact hEmpty (by simpa [hS_empty] using hSU)
  exact bernoulliMass_zero_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS_ne)

lemma exposureTupleUnion_measure_zero
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (0 : ℝ) := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            exposureTupleSpace X 0 := by
      apply Finset.filter_eq_self.mpr
      intro Ws _hWs
      simpa [exposureTupleUnion] using hEmpty
    rw [hfilter, sum_exposureTupleWeight_eq_one X ρ,
      muP_zero_of_mem_empty hEmpty]
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro Ws _hWs
      simpa [exposureTupleUnion] using hEmpty
    rw [hfilter]
    simp [muP_zero_of_not_mem_empty hEmpty]

lemma exposureTupleUnion_measure_zero_density
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  simpa [tupleUnionDensity] using exposureTupleUnion_measure_zero X U ρ

lemma muP_eq_one_of_eq_powerset {X : Finset α} {U : Finset (Finset α)}
    (hU : U = X.powerset) (p : ℝ) :
    muP X U p = 1 := by
  classical
  unfold muP
  have hfilter : X.powerset.filter (fun S => S ∈ U) = X.powerset := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    simpa [hU] using hS
  rw [hfilter]
  exact sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)

lemma muP_eq_one_of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) (p : ℝ) :
    muP X U p = 1 :=
  muP_eq_one_of_eq_powerset
    (eq_powerset_of_empty_mem_increasing hUX hIncr hEmpty) p

theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  
  
  
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · 
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        show T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  
  
  
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    show p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    show p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]

lemma bernoulliMass_insert_of_notMem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) S p = (1 - p) * bernoulliMass X S p := by
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - S.card = (X.card - S.card) + 1 := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hdiff, pow_succ]
  ring

lemma bernoulliMass_insert_with_mem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) (insert a S) p = p * bernoulliMass X S p := by
  have haS : a ∉ S := fun h => ha (hS h)
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hcardS : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - (S.card + 1) = X.card - S.card := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hcardS, hdiff, pow_succ]
  ring

lemma insert_injective_on_powerset_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Set.InjOn (fun S : Finset α => insert a S) X.powerset := by
  intro S hS T hT hST
  have haS : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
  have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
  calc
    S = (insert a S).erase a := (Finset.erase_insert haS).symm
    _ = (insert a T).erase a := congrArg (fun U : Finset α => U.erase a) hST
    _ = T := Finset.erase_insert haT

lemma powerset_disjoint_image_insert_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Disjoint X.powerset (X.powerset.image fun S : Finset α => insert a S) := by
  rw [Finset.disjoint_left]
  intro S hS hSimage
  rcases Finset.mem_image.mp hSimage with ⟨T, _hT, rfl⟩
  have ha_insert : a ∈ insert a T := Finset.mem_insert_self a T
  have ha_not_insert : a ∉ insert a T := fun h =>
    ha ((Finset.mem_powerset.mp hS) h)
  exact ha_not_insert ha_insert

noncomputable def withoutCoordFamily (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset α) :=
  X.powerset.filter fun S => S ∈ U

noncomputable def withCoordFamily (a : α) (X : Finset α)
    (U : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun S => insert a S ∈ U

noncomputable def unionShiftFamily (X : Finset α)
    (U : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun S => S ∪ W ∈ U

lemma mem_unionShiftFamily {X : Finset α} {U : Finset (Finset α)}
    {W S : Finset α} :
    S ∈ unionShiftFamily X U W ↔ S ⊆ X ∧ S ∪ W ∈ U := by
  simp [unionShiftFamily]

lemma withoutCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withoutCoordFamily X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            hSU⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU0⟩
    rcases Finset.mem_filter.mp hSU0 with ⟨_hunionX, hSU⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X), hSU⟩⟩

lemma withCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a (S ∪ W) = insert a S ∪ W := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
            (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

lemma withoutCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X),
            by rwa [hrewrite]⟩⟩

lemma withCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
              (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

lemma muP_insert_split {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (ha : a ∉ X) :
    muP (insert a X) U p =
      (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
  classical
  let ins : Finset α → Finset α := fun S => insert a S
  let A : Finset (Finset α) := X.powerset.filter fun S => S ∈ U
  let B : Finset (Finset α) := (X.powerset.image ins).filter fun S => S ∈ U
  have hdisj_raw :
      Disjoint X.powerset (X.powerset.image ins) := by
    simpa [ins] using powerset_disjoint_image_insert_of_notMem (X := X) (a := a) ha
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro S hSA hSB
    exact (Finset.disjoint_left.mp hdisj_raw)
      (Finset.mem_filter.mp hSA).1 (Finset.mem_filter.mp hSB).1
  have hfilter_union :
      (insert a X).powerset.filter (fun S => S ∈ U) = A ∪ B := by
    calc
      (insert a X).powerset.filter (fun S => S ∈ U)
          = (X.powerset ∪ X.powerset.image ins).filter (fun S => S ∈ U) := by
            rw [Finset.powerset_insert]
      _ = A ∪ B := by
            rw [Finset.filter_union]
  have hU0_filter :
      X.powerset.filter (fun S => S ∈ withoutCoordFamily X U) = A := by
    ext S
    simp [withoutCoordFamily, A]
  have hterm0 :
      (∑ S ∈ A, bernoulliMass (insert a X) S p) =
        (1 - p) * muP X (withoutCoordFamily X U) p := by
    calc
      (∑ S ∈ A, bernoulliMass (insert a X) S p)
          = ∑ S ∈ A, (1 - p) * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hSA
            have hSX : S ⊆ X :=
              Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
            exact bernoulliMass_insert_of_notMem ha hSX
      _ = (1 - p) * ∑ S ∈ A, bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = (1 - p) * muP X (withoutCoordFamily X U) p := by
            unfold muP
            rw [hU0_filter]
  have hB_image :
      (X.powerset.filter fun S => ins S ∈ U).image ins = B := by
    ext R
    constructor
    · intro hR
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩,
          (Finset.mem_filter.mp hS).2⟩
    · intro hR
      rcases Finset.mem_filter.mp hR with ⟨hRimg, hRU⟩
      rcases Finset.mem_image.mp hRimg with ⟨S, hS, rfl⟩
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨hS, hRU⟩, rfl⟩
  have hinj :
      Set.InjOn ins (↑(X.powerset.filter fun S => ins S ∈ U)) := by
    exact (insert_injective_on_powerset_of_notMem (X := X) (a := a) ha).mono
      (by intro S hS; exact (Finset.mem_filter.mp hS).1)
  have hU1_filter :
      X.powerset.filter (fun S => S ∈ withCoordFamily a X U) =
        X.powerset.filter fun S => ins S ∈ U := by
    ext S
    simp [withCoordFamily, ins]
  have hterm1 :
      (∑ S ∈ B, bernoulliMass (insert a X) S p) =
        p * muP X (withCoordFamily a X U) p := by
    calc
      (∑ S ∈ B, bernoulliMass (insert a X) S p)
          = ∑ S ∈ (X.powerset.filter fun S => ins S ∈ U).image ins,
              bernoulliMass (insert a X) S p := by rw [hB_image]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass (insert a X) (ins S) p := by
            rw [Finset.sum_image hinj]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              p * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
            simpa [ins] using bernoulliMass_insert_with_mem (X := X) (S := S)
              (a := a) (p := p) ha hSX
      _ = p * ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = p * muP X (withCoordFamily a X U) p := by
            unfold muP
            rw [hU1_filter]
  calc
    muP (insert a X) U p
        = ∑ S ∈ A ∪ B, bernoulliMass (insert a X) S p := by
          unfold muP
          rw [hfilter_union]
    _ = (∑ S ∈ A, bernoulliMass (insert a X) S p) +
        ∑ S ∈ B, bernoulliMass (insert a X) S p := by
          rw [Finset.sum_union hdisj]
    _ = (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
          rw [hterm0, hterm1]

lemma muP_insert_unionShift_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U W) p =
      (1 - p) *
          muP X (unionShiftFamily X (withoutCoordFamily X U) W) p +
        p * muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U W) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_absent (a := a) hW,
    withCoordFamily_unionShiftFamily_absent (a := a) hW]

lemma muP_insert_unionShift_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U (insert a W)) p =
      muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U (insert a W)) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_present (a := a) hW,
    withCoordFamily_unionShiftFamily_present (a := a) hW]
  ring

lemma muP_unionShift_average_eq_muP_union_density
    (X : Finset α) (U : Finset (Finset α)) (θ r : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W r * muP X (unionShiftFamily X U W) θ) =
      muP X U (1 - (1 - θ) * (1 - r)) := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hEmpty : (∅ : Finset α) ∈ U
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          exact ⟨hSempty, by simpa [hSempty] using hEmpty⟩
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          simpa [hSempty] using hEmpty
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hbad
          exact hEmpty (by simpa [hbad.1] using hbad.2)
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hSU
          have hSempty : S = ∅ := by simpa using hS
          exact hEmpty (by simpa [hSempty] using hSU)
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
  | insert a X ha ih =>
      let η : ℝ := 1 - (1 - θ) * (1 - r)
      let ins : Finset α → Finset α := fun S => insert a S
      have hdisj :
          Disjoint X.powerset (X.powerset.image ins) := by
        simpa [ins] using powerset_disjoint_image_insert_of_notMem
          (X := X) (a := a) ha
      have hinj : Set.InjOn ins (↑X.powerset) := by
        simpa [ins] using insert_injective_on_powerset_of_notMem
          (X := X) (a := a) ha
      have hpowerset_split :
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            (∑ W ∈ X.powerset,
              bernoulliMass (insert a X) W r *
                muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
              ∑ W ∈ X.powerset,
                bernoulliMass (insert a X) (insert a W) r *
                  muP (insert a X)
                    (unionShiftFamily (insert a X) U (insert a W)) θ := by
        calc
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset ∪ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.powerset_insert]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.sum_union hdisj]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset,
                  bernoulliMass (insert a X) (insert a W) r *
                    muP (insert a X)
                      (unionShiftFamily (insert a X) U (insert a W)) θ := by
                    rw [Finset.sum_image hinj]
      have habsent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset,
                  (((1 - r) * (1 - θ)) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
                  ((1 - r) * θ) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_of_notMem ha hWX,
                      muP_insert_unionShift_absent (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hpresent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ) =
            r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ)
              = ∑ W ∈ X.powerset,
                  r *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_with_mem ha hWX,
                      muP_insert_unionShift_present (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.mul_sum]
      have hwithout :=
        ih (withoutCoordFamily X U)
      have hwith :=
        ih (withCoordFamily a X U)
      rw [hpowerset_split, habsent, hpresent, hwithout, hwith]
      have hsplit :=
        muP_insert_split (X := X) (U := U) (a := a) (p := η) ha
      change
        ((1 - r) * (1 - θ)) * muP X (withoutCoordFamily X U) η +
            ((1 - r) * θ) * muP X (withCoordFamily a X U) η +
          r * muP X (withCoordFamily a X U) η =
        muP (insert a X) U η
      rw [hsplit]
      ring

lemma exposureTupleUnion_measure_eq_muP
    (X : Finset α) (U : Finset (Finset α)) {n : ℕ}
    (ρ : Fin n → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X n).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  classical
  induction n generalizing U with
  | zero =>
      simpa using exposureTupleUnion_measure_zero_density X U ρ
  | succ n ih =>
      let e : Finset α × (Fin n → Finset α) ↪
          (Fin (n + 1) → Finset α) :=
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let ρlast : ℝ := ρ (Fin.last n)
      have hmap :
          (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
            (fun Ws => exposureTupleUnion Ws ∈ U),
            exposureTupleWeight X ρ Ws) =
          ∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P) := by
        rw [exposureTupleSpace_snoc X n, Finset.filter_map]
        rw [Finset.sum_map]
        rfl
      have hproduct :
          (∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P)) =
          ∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl ?_
        intro W hW
        rw [← Finset.sum_filter]
        have hfilter :
            (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion (e (W, Ws)) ∈ U) =
              (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W) := by
          ext Ws
          by_cases hWs : Ws ∈ exposureTupleSpace X n
          · have hWsX : exposureTupleUnion Ws ⊆ X :=
              exposureTupleUnion_subset hWs
            have hevent :
                exposureTupleUnion (e (W, Ws)) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W := by
              change
                exposureTupleUnion
                    (Fin.snoc
                      (α := fun _ : Fin (n + 1) => Finset α) Ws W) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W
              rw [exposureTupleUnion_snoc]
              simp [mem_unionShiftFamily, hWsX]
            simp [hWs, hevent]
          · simp [hWs]
        rw [hfilter]
      have hfactor :
          (∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws))) =
          ∑ W ∈ X.powerset,
            bernoulliMass X W ρlast *
              (∑ Ws ∈ (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                exposureTupleWeight X ρtail Ws) := by
        refine Finset.sum_congr rfl ?_
        intro W hW
        calc
          (∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)))
              = ∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws * bernoulliMass X W ρlast := by
                    refine Finset.sum_congr rfl ?_
                    intro Ws hWs
                    change
                      exposureTupleWeight X ρ
                          (Fin.snoc
                            (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
                        exposureTupleWeight X ρtail Ws *
                          bernoulliMass X W ρlast
                    simp [ρtail, ρlast]
          _ = (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) * bernoulliMass X W ρlast := by
                    rw [Finset.sum_mul]
          _ = bernoulliMass X W ρlast *
                (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) := by
                    ring
      calc
        (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
          (fun Ws => exposureTupleUnion Ws ∈ U),
          exposureTupleWeight X ρ Ws)
            = ∑ W ∈ X.powerset,
                bernoulliMass X W ρlast *
                  (∑ Ws ∈ (exposureTupleSpace X n).filter
                    (fun Ws =>
                      exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                    exposureTupleWeight X ρtail Ws) := by
                  rw [hmap, hproduct, hfactor]
        _ = ∑ W ∈ X.powerset,
              bernoulliMass X W ρlast *
                muP X (unionShiftFamily X U W) (tupleUnionDensity ρtail) := by
                  refine Finset.sum_congr rfl ?_
                  intro W hW
                  rw [ih (unionShiftFamily X U W) ρtail]
        _ = muP X U
              (1 - (1 - tupleUnionDensity ρtail) * (1 - ρlast)) :=
            muP_unionShift_average_eq_muP_union_density
              X U (tupleUnionDensity ρtail) ρlast
        _ = muP X U (tupleUnionDensity ρ) := by
            rw [tupleUnionDensity_snoc]

theorem muP_mono_density {X : Finset α} {U : Finset (Finset α)} {p q : ℝ}
    (hIncr : IncreasingIn X U) (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    muP X U p ≤ muP X U q := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hU : (∅ : Finset α) ∈ U
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
  | insert a X ha ih =>
      let U0 : Finset (Finset α) := withoutCoordFamily X U
      let U1 : Finset (Finset α) := withCoordFamily a X U
      have hp1 : p ≤ 1 := hpq.trans hq1
      have hq0 : 0 ≤ q := hp0.trans hpq
      have hIncr0 : IncreasingIn X U0 := by
        intro S hSU0 T hTX hST
        rcases Finset.mem_filter.mp hSU0 with ⟨_hSX, hSU⟩
        have hT_insert : T ⊆ insert a X := hTX.trans (Finset.subset_insert a X)
        have hTU : T ∈ U := hIncr S hSU T hT_insert hST
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hTU⟩
      have hIncr1 : IncreasingIn X U1 := by
        intro S hSU1 T hTX hST
        rcases Finset.mem_filter.mp hSU1 with ⟨_hSX, hInsSU⟩
        have hInsT_insert : insert a T ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxT
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hTX hxT))
        have hInsSInsT : insert a S ⊆ insert a T := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hST hxS))
        have hInsTU : insert a T ∈ U :=
          hIncr (insert a S) hInsSU (insert a T) hInsT_insert hInsSInsT
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hInsTU⟩
      have hU0U1 : U0 ⊆ U1 := by
        intro S hSU0
        rcases Finset.mem_filter.mp hSU0 with ⟨hSXpow, hSU⟩
        have hSX : S ⊆ X := Finset.mem_powerset.mp hSXpow
        have hInsSX : insert a S ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hSX hxS))
        have hSInsS : S ⊆ insert a S := Finset.subset_insert a S
        have hInsSU : insert a S ∈ U := hIncr S hSU (insert a S) hInsSX hSInsS
        exact Finset.mem_filter.mpr ⟨hSXpow, hInsSU⟩
      have hF0 : muP X U0 p ≤ muP X U0 q := ih hIncr0
      have hF1 : muP X U1 p ≤ muP X U1 q := ih hIncr1
      have hF01q : muP X U0 q ≤ muP X U1 q :=
        muP_mono_family hq0 hq1 hU0U1
      rw [muP_insert_split (X := X) (U := U) (a := a) (p := p) ha,
        muP_insert_split (X := X) (U := U) (a := a) (p := q) ha]
      have hfirst :
          (1 - p) * muP X U0 p + p * muP X U1 p ≤
            (1 - p) * muP X U0 q + p * muP X U1 q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hF0 (by linarith))
          (mul_le_mul_of_nonneg_left hF1 hp0)
      have hsecond :
          (1 - p) * muP X U0 q + p * muP X U1 q ≤
            (1 - q) * muP X U0 q + q * muP X U1 q := by
        have hqp_nonneg : 0 ≤ q - p := by linarith
        have hmul := mul_le_mul_of_nonneg_left hF01q hqp_nonneg
        nlinarith
      exact hfirst.trans hsecond

lemma pow_card_le_muP_of_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U) :
    p ^ S.card ≤ muP X U p := by
  have hSX : S ⊆ X := hUX S hS
  have hsub : upClosureIn X {S} ⊆ U :=
    upClosureIn_singleton_subset_of_mem_increasing hIncr hS
  have hmono :
      muP X (upClosureIn X {S}) p ≤ muP X U p :=
    muP_mono_family hp0 hp1 hsub
  have hsingle : muP X (upClosureIn X {S}) p = p ^ S.card :=
    muP_upClosure_single X S hSX hp0 hp1
  simpa [hsingle] using hmono

lemma pow_ell_le_muP_of_nonempty_increasing
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hU : U.Nonempty) :
    p ^ ell X U ≤ muP X U p := by
  rcases minimalMembersIn_nonempty_of_nonempty (X := X) hU with ⟨S, hSmin⟩
  have hSU : S ∈ U := minimalMembersIn_subset hSmin
  have hcard : S.card ≤ ell X U := card_le_ell_of_mem_minimalMembersIn hSmin
  have hpow : p ^ ell X U ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hcard
  exact hpow.trans (pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hSU)

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def CoversIn (_X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

def coverWeight (G : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ T ∈ G, p ^ T.card

def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)

def qSmallUpper (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  ∀ p : ℝ, q < p → p ≤ 1 → ¬ pSmall X U p

omit [DecidableEq α] in
lemma pSmall_empty (X : Finset α) (p : ℝ) :
    pSmall X (∅ : Finset (Finset α)) p := by
  refine ⟨∅, ?_, ?_⟩
  · intro S hS
    simp at hS
  · simp

omit [DecidableEq α] in
lemma nonempty_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (h : ¬ pSmall X U p) :
    U.Nonempty := by
  by_contra hU
  have hUeq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
  exact h (by simpa [hUeq] using pSmall_empty X p)

lemma CoversIn.union {X : Finset α} {G H U V : Finset (Finset α)}
    (hG : CoversIn X G U) (hH : CoversIn X H V) :
    CoversIn X (G ∪ H) (U ∪ V) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hSU | hSV
  · rcases hG S hSU with ⟨T, hTG, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inl hTG), hTS⟩
  · rcases hH S hSV with ⟨T, hTH, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inr hTH), hTS⟩

lemma CoversIn_upClosureIn_iff {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    CoversIn X G (upClosureIn X U) ↔ CoversIn X G U := by
  constructor
  · intro hCover S hS
    exact hCover S (subset_upClosureIn hUX hS)
  · intro hCover S hS
    rcases mem_upClosureIn.mp hS with ⟨_, T, hTU, hTS⟩
    rcases hCover T hTU with ⟨R, hRG, hRT⟩
    exact ⟨R, hRG, hRT.trans hTS⟩

lemma CoversIn.filter_subset_ground {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hCover : CoversIn X G U) :
    CoversIn X (G.filter fun T => T ⊆ X) U := by
  intro S hS
  rcases hCover S hS with ⟨T, hTG, hTS⟩
  have hTX : T ⊆ X := hTS.trans (hUX S hS)
  exact ⟨T, Finset.mem_filter.mpr ⟨hTG, hTX⟩, hTS⟩

lemma pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X (upClosureIn X U) p ↔ pSmall X U p := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mp hCover, hsum⟩
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mpr hCover, hsum⟩

lemma not_pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X (upClosureIn X U) p ↔ ¬ pSmall X U p := by
  rw [pSmall_upClosureIn_iff hUX]

omit [DecidableEq α] in
lemma pSmall_of_cover_sum_le {X : Finset α} {U G : Finset (Finset α)}
    {p : ℝ} (hCover : CoversIn X G U)
    (hsum : (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)) :
    pSmall X U p :=
  ⟨G, hCover, hsum⟩

lemma coverWeight_union_le {G H : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverWeight (G ∪ H) p ≤ coverWeight G p + coverWeight H p := by
  classical
  unfold coverWeight
  let H' : Finset (Finset α) := H \ G
  have hdisj : Disjoint G H' := by
    exact disjoint_sdiff
  have hunion : G ∪ H = G ∪ H' := by
    ext T
    by_cases hTG : T ∈ G <;> simp [H', hTG]
  calc
    (∑ T ∈ G ∪ H, p ^ T.card)
        = ∑ T ∈ G ∪ H', p ^ T.card := by rw [hunion]
    _ = (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H', p ^ T.card := by
      rw [Finset.sum_union hdisj]
    _ ≤ (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H, p ^ T.card := by
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset : H' ⊆ H)
        (by intro T _ _; exact pow_nonneg hp0 T.card))
        (∑ T ∈ G, p ^ T.card)

lemma pSmall.exists_ground_cover
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) (hSmall : pSmall X U p) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ) := by
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G.filter fun T => T ⊆ X, ?_, ?_, ?_⟩
  · intro T hT
    exact (Finset.mem_filter.mp hT).2
  · exact hCover.filter_subset_ground hUX
  · have hfilter_le :
        (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
          ∑ T ∈ G, p ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro T _ _; exact pow_nonneg hp0 T.card)
    exact hfilter_le.trans hsum

omit [DecidableEq α] in
lemma cover_sum_gt_half_of_not_pSmall
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) (hCover : CoversIn X G U) :
    (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
  exact lt_of_not_ge fun hsum => h (pSmall_of_cover_sum_le hCover hsum)

lemma minimalMembers_cover (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X (minimalMembersIn X U) U := by
  intro S hS
  exact exists_minimal_subset hS

lemma generators_cover_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    CoversIn X A (upClosureIn X A) := by
  intro S hS
  rcases mem_upClosureIn.mp hS with ⟨_, T, hTA, hTS⟩
  exact ⟨T, hTA, hTS⟩

lemma half_lt_generators_sum_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    (1 / 2 : ℝ) < ∑ T ∈ A, p ^ T.card := by
  exact cover_sum_gt_half_of_not_pSmall h (generators_cover_upClosureIn X A)

omit [DecidableEq α] in
lemma exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    {β : Type*} (s : Finset β) (w : β → ℝ)
    (hsum : (1 / 2 : ℝ) < ∑ x ∈ s, w x) :
    ∃ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) < w x := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra hs_empty
    have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_empty
    have hbad : (1 / 2 : ℝ) < 0 := by simpa [hs_eq] using hsum
    norm_num at hbad
  by_contra hnone
  have hbound : ∀ x ∈ s, w x ≤ (1 : ℝ) / (2 * (s.card : ℝ)) := by
    intro x hx
    exact le_of_not_gt fun hxgt => hnone ⟨x, hx, hxgt⟩
  have hsum_le :
      (∑ x ∈ s, w x) ≤
        ∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) :=
    Finset.sum_le_sum hbound
  have hcard_pos_nat : 0 < s.card := hs_nonempty.card_pos
  have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hconst :
      (∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ))) = 1 / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  linarith

lemma exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    ∃ T ∈ A, (1 : ℝ) / (2 * (A.card : ℝ)) < p ^ T.card :=
  exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    A (fun T => p ^ T.card)
    (half_lt_generators_sum_of_not_pSmall_upClosureIn h)

omit [DecidableEq α] in
lemma pSmall_mono_density {X : Finset α} {U : Finset (Finset α)}
    {p₀ p : ℝ} (h0 : 0 ≤ p₀) (hle : p₀ ≤ p)
    (hSmall : pSmall X U p) : pSmall X U p₀ := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G, hCover, le_trans ?_ hsum⟩
  refine Finset.sum_le_sum ?_
  intro T _
  exact pow_le_pow_left₀ h0 hle T.card

omit [DecidableEq α] in
lemma qSmallUpper_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p₀ : ℝ} (hp₀_nonneg : 0 ≤ p₀)
    (h : ¬ pSmall X U p₀) :
    qSmallUpper X U p₀ := by
  intro p hgt _ hSmall
  exact h (pSmall_mono_density hp₀_nonneg hgt.le hSmall)

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def fragmentFamily (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  H.image fun S => S \ W

@[simp]
lemma mem_fragmentFamily {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ fragmentFamily H W ↔ ∃ S ∈ H, S \ W = T := by
  simp [fragmentFamily]

def minimalFragments (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  minimalMembersIn (∅ : Finset α) (fragmentFamily H W)

@[simp]
lemma mem_minimalFragments {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ minimalFragments H W ↔
      T ∈ fragmentFamily H W ∧
        ∀ R ∈ fragmentFamily H W, ¬ R ⊂ T := by
  simp [minimalFragments]

lemma minimalFragments_subset_fragmentFamily
    (H : Finset (Finset α)) (W : Finset α) :
    minimalFragments H W ⊆ fragmentFamily H W :=
  minimalMembersIn_subset

lemma fragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ fragmentFamily H W) :
    Disjoint T W := by
  rcases mem_fragmentFamily.mp hT with ⟨S, _hS, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx hW
  exact (Finset.mem_sdiff.mp hx).2 hW

lemma minimalFragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ minimalFragments H W) :
    Disjoint T W :=
  fragment_disjoint_exposure (minimalFragments_subset_fragmentFamily H W hT)

def largeMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => m ≤ T.card

def smallMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => T.card < m

@[simp]
lemma mem_largeMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ largeMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ m ≤ T.card := by
  simp [largeMinimalFragments]

lemma largeMinimalFragment_disjoint_exposure
    {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ largeMinimalFragments m H W) :
    Disjoint T W :=
  minimalFragment_disjoint_exposure (mem_largeMinimalFragments.mp hT).1

lemma union_sdiff_right_eq_left_of_disjoint
    {W S : Finset α} (hdisj : Disjoint S W) :
    (W ∪ S) \ S = W := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxWS, hxSnot⟩
    rcases Finset.mem_union.mp hxWS with hxW | hxS
    · exact hxW
    · exact False.elim (hxSnot hxS)
  · intro hxW
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inl hxW),
        fun hxS => (Finset.disjoint_left.mp hdisj) hxS hxW⟩

@[simp]
lemma mem_smallMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ smallMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ T.card < m := by
  simp [smallMinimalFragments]

lemma small_union_large_minimalFragments
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
      minimalFragments H W := by
  ext T
  by_cases hT : T ∈ minimalFragments H W
  · by_cases hsmall : T.card < m
    · simp [hT, hsmall, largeMinimalFragments, smallMinimalFragments,
        not_le.mpr hsmall]
    · have hlarge : m ≤ T.card := le_of_not_gt hsmall
      simp [hT, hlarge, hsmall, largeMinimalFragments, smallMinimalFragments]
  · simp [hT, largeMinimalFragments, smallMinimalFragments]

lemma minimalFragments_cover
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) :
    CoversIn X (minimalFragments H W) (fragmentFamily H W) := by
  simpa [minimalFragments,CoversIn] using
    (minimalMembers_cover (X := (∅ : Finset α)) (U := fragmentFamily H W))

lemma CoversIn.of_minimalFragments
    {X : Finset α} {G H : Finset (Finset α)} {W : Finset α}
    (hCover : CoversIn X G (minimalFragments H W)) :
    CoversIn X G H := by
  intro S hS
  have hfrag : S \ W ∈ fragmentFamily H W :=
    mem_fragmentFamily.mpr ⟨S, hS, rfl⟩
  rcases minimalFragments_cover X H W (S \ W) hfrag with
    ⟨R, hRmin, hRsub⟩
  rcases hCover R hRmin with ⟨T, hTG, hTR⟩
  have hsdiff_sub : S \ W ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  exact ⟨T, hTG, hTR.trans (hRsub.trans hsdiff_sub)⟩

lemma subset_union_of_sdiff_subset
    {S W V : Finset α} (h : S \ W ⊆ V) :
    S ⊆ W ∪ V := by
  intro x hxS
  by_cases hxW : x ∈ W
  · exact Finset.mem_union.mpr (Or.inl hxW)
  · exact Finset.mem_union.mpr
      (Or.inr (h (Finset.mem_sdiff.mpr ⟨hxS, hxW⟩)))

lemma exists_source_subset_union_of_minimalFragment_subset
    {H : Finset (Finset α)} {W V : Finset α}
    (h : ∃ R ∈ minimalFragments H W, R ⊆ V) :
    ∃ S ∈ H, S ⊆ W ∪ V := by
  rcases h with ⟨R, hR, hRV⟩
  have hRfrag : R ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W hR
  rcases mem_fragmentFamily.mp hRfrag with ⟨S, hS, hSR⟩
  refine ⟨S, hS, subset_union_of_sdiff_subset ?_⟩
  intro x hx
  exact hRV (by simpa [hSR] using hx)

lemma minimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hSmin : S ∈ minimalFragments H (Z \ S)) :
    S ⊆ T := by
  by_contra hnot
  have hRfrag : T \ (Z \ S) ∈ fragmentFamily H (Z \ S) :=
    mem_fragmentFamily.mpr ⟨T, hT, rfl⟩
  have hRsub : T \ (Z \ S) ⊆ S := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxNot⟩
    by_contra hxS
    exact hxNot (Finset.mem_sdiff.mpr ⟨hTZ hxT, hxS⟩)
  have hproper : T \ (Z \ S) ⊂ S := by
    refine hRsub.ssubset_of_ne ?_
    intro hEq
    have hST : S ⊆ T := by
      intro x hxS
      have hxR : x ∈ T \ (Z \ S) := by
        simpa [hEq] using hxS
      exact (Finset.mem_sdiff.mp hxR).1
    exact hnot hST
  exact (mem_minimalFragments.mp hSmin).2 (T \ (Z \ S)) hRfrag hproper

lemma largeMinimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α} {m : ℕ}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hS : S ∈ largeMinimalFragments m H (Z \ S)) :
    S ⊆ T :=
  minimalFragment_subset_of_source_subset hT hTZ
    (mem_largeMinimalFragments.mp hS).1

lemma largeMinimalFragment_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {W S : Finset α} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (hS : S ∈ largeMinimalFragments m H W) :
    S ⊆ X := by
  have hSfrag : S ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W
      (mem_largeMinimalFragments.mp hS).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, rfl⟩
  exact (Finset.sdiff_subset : T \ W ⊆ T).trans (hHX T hT)

def largeFragmentWitnesses
    (H : Finset (Finset α)) (m : ℕ) (Z : Finset α) :
    Finset (Finset α) :=
  Z.powerset.filter fun S => S ∈ largeMinimalFragments m H (Z \ S)

@[simp]
lemma mem_largeFragmentWitnesses
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α} :
    S ∈ largeFragmentWitnesses H m Z ↔
      S ⊆ Z ∧ S ∈ largeMinimalFragments m H (Z \ S) := by
  simp [largeFragmentWitnesses]

lemma largeMinimalFragment_mem_witnesses_union
    {m : ℕ} {H : Finset (Finset α)} {W S : Finset α}
    (hS : S ∈ largeMinimalFragments m H W) :
    S ∈ largeFragmentWitnesses H m (W ∪ S) := by
  have hdisj : Disjoint S W := largeMinimalFragment_disjoint_exposure hS
  have hsdiff : (W ∪ S) \ S = W :=
    union_sdiff_right_eq_left_of_disjoint hdisj
  rw [mem_largeFragmentWitnesses]
  constructor
  · exact Finset.subset_union_right
  · simpa [hsdiff] using hS

lemma largeFragmentWitnesses_subset_source_powerset_filter
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    largeFragmentWitnesses H m Z ⊆
      T.powerset.filter fun S => m ≤ S.card := by
  intro S hS
  rcases mem_largeFragmentWitnesses.mp hS with ⟨_hSZ, hSlarge⟩
  have hST : S ⊆ T :=
    largeMinimalFragment_subset_of_source_subset hT hTZ hSlarge
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hST, (mem_largeMinimalFragments.mp hSlarge).2⟩

lemma exists_source_subset_of_largeFragmentWitness
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α}
    (hS : S ∈ largeFragmentWitnesses H m Z) :
    ∃ T ∈ H, T ⊆ Z := by
  rcases mem_largeFragmentWitnesses.mp hS with ⟨hSZ, hSlarge⟩
  have hSfrag : S ∈ fragmentFamily H (Z \ S) :=
    minimalFragments_subset_fragmentFamily H (Z \ S)
      (mem_largeMinimalFragments.mp hSlarge).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, hdiff⟩
  refine ⟨T, hT, ?_⟩
  intro x hxT
  by_contra hxZ
  have hxNot : x ∉ Z \ S := by
    intro hx
    exact hxZ (Finset.mem_sdiff.mp hx).1
  have hxS : x ∈ S := by
    have hx : x ∈ T \ (Z \ S) :=
      Finset.mem_sdiff.mpr ⟨hxT, hxNot⟩
    simpa [hdiff] using hx
  exact hxZ (hSZ hxS)

lemma largeFragmentWitnesses_eq_empty_of_no_source_subset
    {H : Finset (Finset α)} {m : ℕ} {Z : Finset α}
    (hno : ¬ ∃ T ∈ H, T ⊆ Z) :
    largeFragmentWitnesses H m Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact hno (exists_source_subset_of_largeFragmentWitness hS)

lemma sum_largeFragmentWitnesses_le_source_sum
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (w : Finset α → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, w S) ≤
      ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), w S :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (largeFragmentWitnesses_subset_source_powerset_filter hT hTZ)
    (by intro S _ _; exact hw S)

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_card_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
  calc
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card)
        ≤ ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ m := by
          refine Finset.sum_le_sum ?_
          intro S hS
          exact pow_le_pow_of_le_one ha0 ha1 (Finset.mem_filter.mp hS).2
    _ = (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_two_pow_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hsum :=
    sum_powerset_filter_pow_card_le_card_mul_pow T m ha0 ha1
  have hcard_nat :
      (T.powerset.filter fun S => m ≤ S.card).card ≤ T.powerset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard_real :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (2 : ℝ) ^ T.card := by
    have hcast : (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (T.powerset.card : ℝ) := by
      exact_mod_cast hcard_nat
    simpa using hcast
  have hmul :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) ≤
        (2 : ℝ) ^ T.card * a ^ m :=
    mul_le_mul_of_nonneg_right hcard_real (pow_nonneg ha0 m)
  exact hsum.trans hmul

lemma sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hle_source :
      (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
        ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card :=
    sum_largeFragmentWitnesses_le_source_sum
      (fun S => a ^ S.card) (fun S => pow_nonneg ha0 S.card) hT hTZ
  exact hle_source.trans
    (sum_powerset_filter_pow_card_le_two_pow_mul_pow T m ha0 ha1)

def largeFragmentPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun W =>
    (largeMinimalFragments m H W).image fun S => (W, S)

lemma disjoint_largeFragmentPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {W W' : Finset α}
    (hWW' : W ≠ W') :
    Disjoint
      ((largeMinimalFragments m H W).image fun S => (W, S))
      ((largeMinimalFragments m H W').image fun S => (W', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : W = W' := by
    calc
      W = (W, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (W', S').1 := (congrArg Prod.fst hEq').symm
      _ = W' := rfl
  exact hWW' hfirst

lemma pairwiseDisjoint_largeFragmentPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ W ∈ X, ∀ W' ∈ X, W ≠ W' →
        Disjoint
          ((largeMinimalFragments m H W).image fun S => (W, S))
          ((largeMinimalFragments m H W').image fun S => (W', S)) :=
  fun _ W _ W' _ hWW' =>
    disjoint_largeFragmentPair_fibers (H := H) (m := m) (W := W) (W' := W') hWW'

@[simp]
lemma mem_largeFragmentPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeFragmentPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeMinimalFragments m H P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨W, hWXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = W := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hWXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨W, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨W, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

def largeWitnessPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun Z =>
    (largeFragmentWitnesses H m Z).image fun S => (Z, S)

lemma disjoint_largeWitnessPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {Z Z' : Finset α}
    (hZZ' : Z ≠ Z') :
    Disjoint
      ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
      ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : Z = Z' := by
    calc
      Z = (Z, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (Z', S').1 := (congrArg Prod.fst hEq').symm
      _ = Z' := rfl
  exact hZZ' hfirst

lemma pairwiseDisjoint_largeWitnessPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ Z ∈ X, ∀ Z' ∈ X, Z ≠ Z' →
        Disjoint
          ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
          ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) :=
  fun _ Z _ Z' _ hZZ' =>
    disjoint_largeWitnessPair_fibers (H := H) (m := m) (Z := Z) (Z' := Z') hZZ'

@[simp]
lemma mem_largeWitnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeWitnessPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeFragmentWitnesses H m P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨Z, hZXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = Z := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hZXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨Z, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨Z, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

def largeFragmentPairToWitness
    (P : Finset α × Finset α) : Finset α × Finset α :=
  (P.1 ∪ P.2, P.2)

lemma largeFragmentPairToWitness_mem
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    {P : Finset α × Finset α}
    (hP : P ∈ largeFragmentPairs X H m) :
    largeFragmentPairToWitness P ∈ largeWitnessPairs X H m := by
  rcases P with ⟨W, S⟩
  rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hS⟩
  rw [mem_largeWitnessPairs]
  constructor
  · exact Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hS)
  · exact largeMinimalFragment_mem_witnesses_union hS

lemma largeFragmentPairToWitness_injOn
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} :
    Set.InjOn (largeFragmentPairToWitness : Finset α × Finset α → Finset α × Finset α)
      (↑(largeFragmentPairs X H m)) := by
  intro P hP Q hQ hEq
  rcases P with ⟨W, S⟩
  rcases Q with ⟨W', S'⟩
  have hS_eq : S = S' := by
    exact congrArg Prod.snd hEq
  have hUnion_eq : W ∪ S = W' ∪ S' := by
    exact congrArg Prod.fst hEq
  rcases mem_largeFragmentPairs.mp hP with ⟨_hWX, hSlarge⟩
  rcases mem_largeFragmentPairs.mp hQ with ⟨_hW'X, hS'large⟩
  have hW_eq : W = W' := by
    have hleft :
        (W ∪ S) \ S = W :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hSlarge)
    have hright :
        (W' ∪ S') \ S' = W' :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hS'large)
    calc
      W = (W ∪ S) \ S := hleft.symm
      _ = (W' ∪ S') \ S' := by rw [hUnion_eq, hS_eq]
      _ = W' := hright
  simp [hW_eq, hS_eq]

lemma image_largeFragmentPairToWitness_subset
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X) :
    (largeFragmentPairs X H m).image largeFragmentPairToWitness ⊆
      largeWitnessPairs X H m := by
  intro Q hQ
  rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
  exact largeFragmentPairToWitness_mem hHX hP

lemma sum_largeFragmentPairs_toWitness_le_sum_witnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (w : Finset α × Finset α → ℝ)
    (hw : ∀ P, 0 ≤ w P) :
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P)) ≤
      ∑ Q ∈ largeWitnessPairs X H m, w Q := by
  have himage_subset := image_largeFragmentPairToWitness_subset
    (X := X) (H := H) (m := m) hHX
  calc
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P))
        = ∑ Q ∈ (largeFragmentPairs X H m).image largeFragmentPairToWitness, w Q := by
          rw [Finset.sum_image (largeFragmentPairToWitness_injOn
            (X := X) (H := H) (m := m))]
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m, w Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          (by intro Q _ _; exact hw Q)

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
noncomputable def groundCoversIn (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset (Finset α)) :=
  by
    classical
    exact X.powerset.powerset.filter fun G => CoversIn X G U

omit [DecidableEq α] in
lemma singleton_empty_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X ({∅} : Finset (Finset α)) U := by
  intro S _hS
  exact ⟨∅, by simp, Finset.empty_subset S⟩

omit [DecidableEq α] in
lemma groundCoversIn_nonempty (X : Finset α) (U : Finset (Finset α)) :
    (groundCoversIn X U).Nonempty := by
  refine ⟨{∅}, ?_⟩
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · rw [Finset.mem_powerset]
    intro T hT
    have hT_empty : T = ∅ := by simpa using hT
    subst hT_empty
    exact Finset.mem_powerset.mpr (Finset.empty_subset X)
  · exact singleton_empty_covers X U

omit [DecidableEq α] in
lemma mem_groundCoversIn {X : Finset α} {U G : Finset (Finset α)} :
    G ∈ groundCoversIn X U ↔
      (∀ T ∈ G, T ⊆ X) ∧ CoversIn X G U := by
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · intro h
    constructor
    · intro T hTG
      exact Finset.mem_powerset.mp (Finset.mem_powerset.mp h.1 hTG)
    · exact h.2
  · rintro ⟨hGX, hCover⟩
    refine ⟨?_, hCover⟩
    exact Finset.mem_powerset.mpr (by
      intro T hTG
      exact Finset.mem_powerset.mpr (hGX T hTG))

noncomputable def groundCoverWeights (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    Finset ℝ :=
  by
    classical
    exact (groundCoversIn X U).image fun G => coverWeight G p

omit [DecidableEq α] in
lemma groundCoverWeights_nonempty
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    (groundCoverWeights X U p).Nonempty :=
  (groundCoversIn_nonempty X U).image _

noncomputable def coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  (groundCoverWeights X U p).min' (groundCoverWeights_nonempty X U p)

omit [DecidableEq α] in
lemma coverCost_le_of_ground_cover
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (hGX : ∀ T ∈ G, T ⊆ X) (hCover : CoversIn X G U) :
    coverCost X U p ≤ coverWeight G p := by
  unfold coverCost groundCoverWeights
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨G, (mem_groundCoversIn.mpr ⟨hGX, hCover⟩), rfl⟩)

omit [DecidableEq α] in
lemma coverCost_nonneg
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, _hG, rfl⟩
  unfold coverWeight
  exact Finset.sum_nonneg fun T _ => pow_nonneg hp0 T.card

omit [DecidableEq α] in
lemma exists_ground_cover_weight_eq_coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      coverCost X U p = coverWeight G p := by
  unfold coverCost groundCoverWeights
  have hmem :=
    Finset.min'_mem ((groundCoversIn X U).image fun G => coverWeight G p)
      (groundCoverWeights_nonempty X U p)
  rcases Finset.mem_image.mp hmem with ⟨G, hG, hEq⟩
  rcases mem_groundCoversIn.mp hG with ⟨hGX, hCover⟩
  exact ⟨G, hGX, hCover, hEq.symm⟩

omit [DecidableEq α] in
lemma coverWeight_singleton_empty (p : ℝ) :
    coverWeight ({∅} : Finset (Finset α)) p = 1 := by
  simp [coverWeight]

omit [DecidableEq α] in
lemma coverCost_le_one (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    coverCost X U p ≤ 1 := by
  have hle := coverCost_le_of_ground_cover
    (X := X) (U := U) (G := ({∅} : Finset (Finset α))) (p := p)
    (by
      intro T hT
      have hT_empty : T = ∅ := by simpa using hT
      subst hT_empty
      exact Finset.empty_subset X)
    (singleton_empty_covers X U)
  simpa [coverWeight_singleton_empty] using hle

omit [DecidableEq α] in
lemma self_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X U U := by
  intro S hS
  exact ⟨S, hS, subset_refl S⟩

omit [DecidableEq α] in
lemma coverCost_le_coverWeight_self
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ T ∈ U, T ⊆ X) :
    coverCost X U p ≤ coverWeight U p :=
  coverCost_le_of_ground_cover hUX (self_covers X U)

omit [DecidableEq α] in
lemma coverCost_empty_eq_zero
    (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X (∅ : Finset (Finset α)) p = 0 := by
  have hle : coverCost X (∅ : Finset (Finset α)) p ≤ 0 := by
    have hcover : CoversIn X (∅ : Finset (Finset α))
        (∅ : Finset (Finset α)) := by
      intro S hS
      simp at hS
    have hground : ∀ T ∈ (∅ : Finset (Finset α)), T ⊆ X := by
      intro T hT
      simp at hT
    simpa [coverWeight] using
      (coverCost_le_of_ground_cover (X := X)
        (U := (∅ : Finset (Finset α)))
        (G := (∅ : Finset (Finset α))) (p := p) hground hcover)
  exact le_antisymm hle (coverCost_nonneg hp0)

omit [DecidableEq α] in
lemma one_le_coverCost_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    1 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, hG, rfl⟩
  rcases mem_groundCoversIn.mp hG with ⟨_hGX, hCover⟩
  rcases hCover ∅ hEmpty with ⟨T, hTG, hTsub⟩
  have hT_empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simpa using hTsub hx
  have hsingle :
      p ^ T.card ≤ coverWeight G p := by
    unfold coverWeight
    exact Finset.single_le_sum
      (s := G) (f := fun S : Finset α => p ^ S.card)
      (fun S _ => pow_nonneg hp0 S.card) hTG
  have hterm : p ^ T.card = 1 := by
    subst hT_empty
    simp
  linarith

omit [DecidableEq α] in
lemma coverCost_eq_one_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    coverCost X U p = 1 :=
  le_antisymm (coverCost_le_one X U p)
    (one_le_coverCost_of_empty_mem hp0 hEmpty)

omit [DecidableEq α] in
lemma eq_empty_of_forall_card_zero_empty_not_mem
    {U : Finset (Finset α)}
    (hcard : ∀ S ∈ U, S.card = 0)
    (hEmpty : (∅ : Finset α) ∉ U) :
    U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hS_empty : S = ∅ := Finset.card_eq_zero.mp (hcard S hS)
  exact hEmpty (by simpa [hS_empty] using hS)

omit [DecidableEq α] in
lemma coverCost_pos_iff_empty_mem_of_forall_card_zero
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p)
    (hcard : ∀ S ∈ U, S.card = 0) :
    0 < coverCost X U p ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro hpos
    by_contra hEmpty
    have hU_empty : U = ∅ :=
      eq_empty_of_forall_card_zero_empty_not_mem hcard hEmpty
    have hcost : coverCost X U p = 0 := by
      rw [hU_empty]
      exact coverCost_empty_eq_zero X hp0
    linarith
  · intro hEmpty
    rw [coverCost_eq_one_of_empty_mem hp0 hEmpty]
    norm_num

theorem pSmall_iff_coverCost_le
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X U p ↔ coverCost X U p ≤ (1 / 2 : ℝ) := by
  constructor
  · intro hSmall
    rcases pSmall.exists_ground_cover hp0 hUX hSmall with
      ⟨G, hGX, hCover, hsum⟩
    exact (coverCost_le_of_ground_cover hGX hCover).trans hsum
  · intro hCost
    rcases exists_ground_cover_weight_eq_coverCost X U p with
      ⟨G, _hGX, hCover, hEq⟩
    exact ⟨G, hCover, by simpa [hEq,coverWeight] using hCost⟩

lemma not_pSmall_iff_half_lt_coverCost
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X U p ↔ (1 / 2 : ℝ) < coverCost X U p := by
  rw [pSmall_iff_coverCost_le hp0 hUX]
  exact not_le

lemma coverCost_union_le
    {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverCost X (U ∪ V) p ≤ coverCost X U p + coverCost X V p := by
  rcases exists_ground_cover_weight_eq_coverCost X U p with
    ⟨G, hGX, hCoverU, hEqG⟩
  rcases exists_ground_cover_weight_eq_coverCost X V p with
    ⟨H, hHX, hCoverV, hEqH⟩
  have hGroundUnion : ∀ T ∈ G ∪ H, T ⊆ X := by
    intro T hT
    rcases Finset.mem_union.mp hT with hTG | hTH
    · exact hGX T hTG
    · exact hHX T hTH
  have hCoverUnion : CoversIn X (G ∪ H) (U ∪ V) :=
    hCoverU.union hCoverV
  calc
    coverCost X (U ∪ V) p ≤ coverWeight (G ∪ H) p :=
      coverCost_le_of_ground_cover hGroundUnion hCoverUnion
    _ ≤ coverWeight G p + coverWeight H p := coverWeight_union_le hp0
    _ = coverCost X U p + coverCost X V p := by
      rw [hEqG, hEqH]

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
lemma coverCost_le_minimalFragments
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) (p : ℝ) :
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := by
  rcases exists_ground_cover_weight_eq_coverCost X (minimalFragments H W) p with
    ⟨G, hGX, hCover, hEq⟩
  exact (coverCost_le_of_ground_cover hGX hCover.of_minimalFragments).trans_eq
    hEq.symm

lemma coverCost_le_small_add_large_minimalFragments
    (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := by
  have htoMin :
      coverCost X H p ≤ coverCost X (minimalFragments H W) p :=
    coverCost_le_minimalFragments X H W p
  have hpartition :
      smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
        minimalFragments H W :=
    small_union_large_minimalFragments m H W
  have hsubadd :
      coverCost X (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p ≤
        coverCost X (smallMinimalFragments m H W) p +
          coverCost X (largeMinimalFragments m H W) p :=
    coverCost_union_le hp0
  calc
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := htoMin
    _ = coverCost X
          (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p := by
        rw [hpartition]
    _ ≤ coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := hsubadd

lemma smallMinimalFragments_one_card_zero
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ smallMinimalFragments 1 H W) :
    T.card = 0 := by
  exact Nat.lt_one_iff.mp (mem_smallMinimalFragments.mp hT).2

lemma coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 H W) p ↔
      ∃ S ∈ H, S ⊆ W := by
  rw [coverCost_pos_iff_empty_mem_of_forall_card_zero
    (X := X) (U := smallMinimalFragments 1 H W) (p := p) hp0
    (fun T hT => smallMinimalFragments_one_card_zero hT)]
  simp

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def smallStepExposureUnion : List (ℕ × Finset α) → Finset α
  | [] => ∅
  | step :: steps => step.2 ∪ smallStepExposureUnion steps

def iteratedSmallFragments (H : Finset (Finset α)) :
    List (ℕ × Finset α) → Finset (Finset α)
  | [] => H
  | step :: steps =>
      iteratedSmallFragments
        (smallMinimalFragments step.1 H step.2) steps

noncomputable def iteratedLargeCostSum
    (X : Finset α) (p : ℝ) (H : Finset (Finset α)) :
    List (ℕ × Finset α) → ℝ
  | [] => 0
  | step :: steps =>
      coverCost X (largeMinimalFragments step.1 H step.2) p +
        iteratedLargeCostSum X p
          (smallMinimalFragments step.1 H step.2) steps

def exposureTupleStepsSnoc :
    {n : ℕ} → (Fin n → ℕ) → (Fin n → Finset α) → List (ℕ × Finset α)
  | 0, _cutoff, _Ws => []
  | n + 1, cutoff, Ws =>
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => Ws i.castSucc) ++
        [(cutoff (Fin.last n), Ws (Fin.last n))]

omit [DecidableEq α] in
lemma exposureTupleStepsSnoc_snoc {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    exposureTupleStepsSnoc cutoff
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws ++
        [(cutoff (Fin.last n), W)] := by
  simp [exposureTupleStepsSnoc]

lemma sum_largeFragmentPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeFragmentPairs X H m, w P) =
      ∑ W ∈ X.powerset,
        ∑ S ∈ largeMinimalFragments m H W, w (W, S) := by
  unfold largeFragmentPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeFragmentPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCoverWeight_eq_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (ρ q : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ * coverWeight (largeMinimalFragments m H W) q) =
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  rw [sum_largeFragmentPairs_eq_nested]
  unfold coverWeight
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.mul_sum]

lemma sum_largeWitnessPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeWitnessPairs X H m, w P) =
      ∑ Z ∈ X.powerset,
        ∑ S ∈ largeFragmentWitnesses H m Z, w (Z, S) := by
  unfold largeWitnessPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeWitnessPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro Z _hZ
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCost_le_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ q : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ W ∈ X.powerset,
            bernoulliMass X W ρ *
              coverWeight (largeMinimalFragments m H W) q := by
          refine Finset.sum_le_sum ?_
          intro W _hW
          have hcost :
              coverCost X (largeMinimalFragments m H W) q ≤
                coverWeight (largeMinimalFragments m H W) q :=
            coverCost_le_coverWeight_self
              (fun T hT => largeMinimalFragment_subset_ground hHX hT)
          exact mul_le_mul_of_nonneg_left hcost
            (bernoulliMass_nonneg hρ0 hρ1)
    _ = ∑ P ∈ largeFragmentPairs X H m,
          bernoulliMass X P.1 ρ * q ^ P.2.card :=
        bernoulli_average_largeCoverWeight_eq_pair_sum X H m ρ q

lemma largeFragment_pair_sum_le_witness_sum
    (X : Finset α) (H : Finset (Finset α)) (m L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ P ∈ largeFragmentPairs X H m,
      bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
      ∑ Q ∈ largeWitnessPairs X H m,
        bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  let w : Finset α × Finset α → ℝ :=
    fun Q => bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card
  have hterm :
      (∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
        ∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P) := by
    refine Finset.sum_le_sum ?_
    intro P hP
    rcases P with ⟨W, S⟩
    rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hSlarge⟩
    have hdisj : Disjoint S W :=
      largeMinimalFragment_disjoint_exposure hSlarge
    have hUnionX : W ∪ S ⊆ X :=
      Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hSlarge)
    exact bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
      (X := X) (W := W) (S := S) (q := q) (ρ := ρ) (L := L)
      hL hq0 hq1 hρ hdisj hUnionX
  have hw_nonneg : ∀ Q, 0 ≤ w Q := by
    intro Q
    exact mul_nonneg (bernoulliMass_nonneg hρ0 hρ1)
      (pow_nonneg (by positivity : 0 ≤ (1 / (L : ℝ))) Q.2.card)
  exact hterm.trans
    (sum_largeFragmentPairs_toWitness_le_sum_witnessPairs hHX w hw_nonneg)

lemma largeWitness_sum_le_muP_mul_two_pow
    (X : Finset α) (H : Finset (Finset α)) (m ell : ℕ)
    {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hHbound : ∀ T ∈ H, T.card ≤ ell) :
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card) ≤
      muP X (upClosureIn X H) ρ * ((2 : ℝ) ^ ell * a ^ m) := by
  let B : ℝ := (2 : ℝ) ^ ell * a ^ m
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hinner_zero :
      ∀ Z ∈ X.powerset, Z ∉ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) = 0 := by
    intro Z _hZ hZnot
    have hno : ¬ ∃ T ∈ H, T ⊆ Z := by
      intro h
      exact hZnot (mem_upClosureIn.mpr
        ⟨Finset.mem_powerset.mp _hZ, h⟩)
    rw [largeFragmentWitnesses_eq_empty_of_no_source_subset hno]
    simp
  have hinner_bound :
      ∀ Z ∈ X.powerset, Z ∈ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) ≤
          bernoulliMass X Z ρ * B := by
    intro Z _hZ hZU
    rcases mem_upClosureIn.mp hZU with ⟨_hZX, T, hT, hTZ⟩
    have hsum_le :
        (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
          (2 : ℝ) ^ T.card * a ^ m :=
      sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow ha0 ha1 hT hTZ
    have hT_le : T.card ≤ ell := hHbound T hT
    have hpow2_le : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ ell :=
      pow_le_pow_right₀ (by norm_num) hT_le
    have hsource_le_B :
        (2 : ℝ) ^ T.card * a ^ m ≤ B := by
      exact mul_le_mul_of_nonneg_right hpow2_le (pow_nonneg ha0 m)
    calc
      (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card)
          = bernoulliMass X Z ρ *
              ∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card := by
            rw [Finset.mul_sum]
      _ ≤ bernoulliMass X Z ρ * ((2 : ℝ) ^ T.card * a ^ m) :=
            mul_le_mul_of_nonneg_left hsum_le
              (bernoulliMass_nonneg hρ0 hρ1)
      _ ≤ bernoulliMass X Z ρ * B :=
            mul_le_mul_of_nonneg_left hsource_le_B
              (bernoulliMass_nonneg hρ0 hρ1)
  calc
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card)
        = ∑ Z ∈ X.powerset,
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [sum_largeWitnessPairs_eq_nested]
    _ = ∑ Z ∈ X.powerset,
            if Z ∈ upClosureIn X H then
              ∑ S ∈ largeFragmentWitnesses H m Z,
                bernoulliMass X Z ρ * a ^ S.card
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro Z hZ
          by_cases hZU : Z ∈ upClosureIn X H
          · simp [hZU]
          · simp [hZU, hinner_zero Z hZ hZU]
    _ = ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [Finset.sum_filter]
    _ ≤ ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            bernoulliMass X Z ρ * B := by
          refine Finset.sum_le_sum ?_
          intro Z hZ
          exact hinner_bound Z (Finset.mem_filter.mp hZ).1
            (Finset.mem_filter.mp hZ).2
    _ = muP X (upClosureIn X H) ρ * B := by
          unfold muP
          rw [← Finset.sum_mul]

lemma bernoulli_average_largeCost_le_muP_mul_two_pow_inv
    (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hinv0 : 0 ≤ (1 / (L : ℝ)) := by positivity
  have hinv1 : (1 / (L : ℝ)) ≤ 1 := by
    rw [div_le_one hLpos]
    exact_mod_cast hL
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ P ∈ largeFragmentPairs X H m,
            bernoulliMass X P.1 ρ * q ^ P.2.card :=
          bernoulli_average_largeCost_le_pair_sum X H m hρ0 hρ1 hHX
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m,
          bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card :=
          largeFragment_pair_sum_le_witness_sum
            X H m L hL hq0 hq1 hρ hHX
    _ ≤ muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) :=
          largeWitness_sum_le_muP_mul_two_pow
            X H m ell hρ0 hρ1 hinv0 hinv1 hHbound

lemma smallStepExposureUnion_append_singleton
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) :
    smallStepExposureUnion (steps ++ [step]) =
      smallStepExposureUnion steps ∪ step.2 := by
  induction steps with
  | nil =>
      simp [smallStepExposureUnion]
  | cons head steps ih =>
      simp [smallStepExposureUnion, ih, Finset.union_assoc]

lemma smallStepExposureUnion_exposureTupleStepsSnoc
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
    smallStepExposureUnion (exposureTupleStepsSnoc cutoff Ws) =
      exposureTupleUnion Ws := by
  induction n with
  | zero =>
      ext x
      simp [exposureTupleStepsSnoc, smallStepExposureUnion, exposureTupleUnion]
  | succ n ih =>
      rw [exposureTupleStepsSnoc]
      rw [smallStepExposureUnion_append_singleton]
      rw [ih]
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxtail | hxlast
        · rcases (by
            simpa [exposureTupleUnion] using hxtail :
              ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
          simpa [exposureTupleUnion] using
            (Exists.intro (i.castSucc : Fin (n + 1)) hi)
        · simpa [exposureTupleUnion] using
            (Exists.intro (Fin.last n) hxlast)
      · intro hx
        rcases (by
          simpa [exposureTupleUnion] using hx :
            ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Finset.mem_union.mpr (Or.inl (by
            simpa [exposureTupleUnion] using (Exists.intro j hi)))
        · exact Finset.mem_union.mpr (Or.inr hi)

lemma exposureTupleStepsSnoc_last_shape
    {X : Finset α} {n : ℕ} {cutoff : Fin (n + 1) → ℕ}
    {Ws : Fin (n + 1) → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X (n + 1))
    (hlast : cutoff (Fin.last n) = 1) :
    ∃ steps V,
      exposureTupleStepsSnoc cutoff Ws = steps ++ [(1, V)] ∧
      smallStepExposureUnion steps ∪ V ⊆ X := by
  refine ⟨exposureTupleStepsSnoc
      (fun i : Fin n => cutoff i.castSucc)
      (fun i : Fin n => Ws i.castSucc),
    Ws (Fin.last n), ?_, ?_⟩
  · simp [exposureTupleStepsSnoc, hlast]
  · rw [smallStepExposureUnion_exposureTupleStepsSnoc]
    intro x hx
    rcases Finset.mem_union.mp hx with hxtail | hxlast
    · rcases (by
        simpa [exposureTupleUnion] using hxtail :
          ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
      exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i.castSucc) hi
    · exact Finset.mem_powerset.mp
        ((mem_exposureTupleSpace.mp hWs) (Fin.last n)) hxlast

lemma iteratedSmallFragments_append_singleton
    (H : Finset (Finset α)) (steps : List (ℕ × Finset α))
    (step : ℕ × Finset α) :
    iteratedSmallFragments H (steps ++ [step]) =
      smallMinimalFragments step.1 (iteratedSmallFragments H steps) step.2 := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedSmallFragments, ih]

lemma smallMinimalFragments_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} {W : Finset α}
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ smallMinimalFragments m H W, T ⊆ X := by
  intro T hT x hx
  rcases mem_smallMinimalFragments.mp hT with ⟨hTmin, _hsmall⟩
  rcases mem_fragmentFamily.mp
      (minimalFragments_subset_fragmentFamily H W hTmin) with
    ⟨S, hS, rfl⟩
  exact hHX S hS (Finset.mem_sdiff.mp hx).1

lemma iteratedSmallFragments_subset_ground
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α))
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ iteratedSmallFragments H steps, T ⊆ X := by
  induction steps generalizing H with
  | nil =>
      simpa [iteratedSmallFragments] using hHX
  | cons step steps ih =>
      simpa [iteratedSmallFragments] using
        ih (H := smallMinimalFragments step.1 H step.2)
          (smallMinimalFragments_subset_ground (X := X) hHX)

lemma iteratedLargeCostSum_nonneg
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum]
  | cons step steps ih =>
      have hcost :
          0 ≤ coverCost X (largeMinimalFragments step.1 H step.2) p :=
        coverCost_nonneg hp0
      have hrest :
          0 ≤ iteratedLargeCostSum X p
            (smallMinimalFragments step.1 H step.2) steps :=
        ih (H := smallMinimalFragments step.1 H step.2)
      simpa [iteratedLargeCostSum] using add_nonneg hcost hrest

lemma iteratedLargeCostSum_append_singleton
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) {p : ℝ} :
    iteratedLargeCostSum X p H (steps ++ [step]) =
      iteratedLargeCostSum X p H steps +
        coverCost X
          (largeMinimalFragments step.1 (iteratedSmallFragments H steps) step.2) p := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum, iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedLargeCostSum, iteratedSmallFragments, ih, add_assoc]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc cutoff
          (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
      iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc
          (fun i : Fin n => cutoff i.castSucc) Ws) +
        coverCost X
          (largeMinimalFragments (cutoff (Fin.last n))
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) W) p := by
  rw [exposureTupleStepsSnoc_snoc]
  simpa using
    iteratedLargeCostSum_append_singleton
      (X := X) (H := H)
      (steps := exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
      (step := (cutoff (Fin.last n), W)) (p := p)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) =
      ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
  classical
  let e : Finset α × (Fin n → Finset α) ↪
      (Fin (n + 1) → Finset α) :=
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
  calc
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω))
        = ∑ P ∈ (X.powerset ×ˢ exposureTupleSpace X n),
            exposureTupleWeight X ρ (e P) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff (e P)) := by
            rw [exposureTupleSpace_snoc X n, Finset.sum_map]
    _ = ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl ?_
          intro W _hW
          refine Finset.sum_congr rfl ?_
          intro Ws _hWs
          change
            exposureTupleWeight X ρ
                (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff
                  (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
            (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
                bernoulliMass X W (ρ (Fin.last n))) *
              (iteratedLargeCostSum X p H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws) +
                coverCost X
                  (largeMinimalFragments (cutoff (Fin.last n))
                    (iteratedSmallFragments H
                      (exposureTupleStepsSnoc
                        (fun i : Fin n => cutoff i.castSucc) Ws)) W) p)
          rw [exposureTupleWeight_snoc,
            iteratedLargeCostSum_exposureTupleStepsSnoc_snoc]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (B : (Fin n → Finset α) → ℝ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) ≤
          B Ws) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) ≤
      ∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            iteratedLargeCostSum X p H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws) := by
  classical
  rw [iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro Ws hWs
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let ρlast : ℝ := ρ (Fin.last n)
  let loss : ℝ :=
    iteratedLargeCostSum X p H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
  let finalCost : Finset α → ℝ := fun W =>
    coverCost X
      (largeMinimalFragments (cutoff (Fin.last n))
        (iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws)) W) p
  let wt : ℝ := exposureTupleWeight X ρtail Ws
  have hwt0 : 0 ≤ wt := by
    dsimp [wt, ρtail]
    exact exposureTupleWeight_nonneg X
      (fun i : Fin n => hρ0 i.castSucc)
      (fun i : Fin n => hρ1 i.castSucc) Ws
  have hinner_eq :
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W)) =
        wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
    calc
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W))
          = ∑ W ∈ X.powerset,
            (  bernoulliMass X W ρlast * (wt * loss) +
                wt * (bernoulliMass X W ρlast * finalCost W)) := by
              refine Finset.sum_congr rfl ?_
              intro W _hW
              ring
      _ = (∑ W ∈ X.powerset, bernoulliMass X W ρlast) * (wt * loss) +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = wt * loss +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [sum_bernoulliMass_eq_one (α := α) X (p := ρlast) (by ring)]
              ring
  calc
    (∑ W ∈ X.powerset,
      (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          bernoulliMass X W (ρ (Fin.last n))) *
        (iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
          coverCost X
            (largeMinimalFragments (cutoff (Fin.last n))
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)) W) p))
        = wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
            simpa [wt, loss, finalCost, ρtail, ρlast] using hinner_eq
    _ ≤ wt * loss + wt * B Ws := by
          have hmul_le :
              wt * (∑ W ∈ X.powerset,
                bernoulliMass X W ρlast * finalCost W) ≤ wt * B Ws :=
            mul_le_mul_of_nonneg_left (by
              simpa [finalCost, ρlast] using hfinal Ws hWs) hwt0
          linarith
    _ = exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws := by
          simp [wt, loss, ρtail]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hCurrentBound :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∀ S ∈ iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws),
          S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X q H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws)) +
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  classical
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          C := by
    intro Ws hWs
    have hlarge :
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          muP X
            (upClosureIn X
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)))
            (ρ (Fin.last n)) * C := by
      simpa [C] using
        bernoulli_average_largeCost_le_muP_mul_two_pow_inv
          X
          (iteratedSmallFragments H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws))
          (cutoff (Fin.last n)) ell L hL hq0 hq1 hρlast
          (iteratedSmallFragments_subset_ground X H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) hHX)
          (hCurrentBound Ws hWs)
    have hmu_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) ≤ 1 :=
      muP_le_one (hρ0 (Fin.last n)) (hρ1 (Fin.last n))
    have hmuC_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) * C ≤ C := by
      have := mul_le_mul_of_nonneg_right hmu_le hC0
      simpa using this
    exact hlarge.trans hmuC_le
  have hbase :=
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
      X H ρ cutoff (fun _Ws => C) hρ0 hρ1 hfinal
  have hsum_eq :
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C)) =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
    calc
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C))
          =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          ∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws * C := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws) * C := by
            rw [Finset.sum_mul]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
            rw [sum_exposureTupleWeight_eq_one X ρtail]
            ring
  exact hbase.trans_eq hsum_eq

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card < cutoff (Fin.last n) := by
  intro T hT
  rw [exposureTupleStepsSnoc, iteratedSmallFragments_append_singleton] at hT
  exact (mem_smallMinimalFragments.mp hT).2

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card ≤ cutoff (Fin.last n) := by
  intro T hT
  exact Nat.le_of_lt
    (iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last H cutoff Ws T hT)

def snocCurrentCardBound :
    {n : ℕ} → ℕ → (Fin n → ℕ) → ℕ
  | 0, ell, _cutoff => ell
  | n + 1, _ell, cutoff => cutoff (Fin.last n)

noncomputable def snocLargeCostBudget :
    {n : ℕ} → ℕ → (Fin n → ℕ) → (Fin n → ℕ) → ℝ
  | 0, _ell, _cutoff, _L => 0
  | n + 1, ell, cutoff, L =>
      snocLargeCostBudget ell
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => L i.castSucc) +
        (2 : ℝ) ^
            snocCurrentCardBound ell
              (fun i : Fin n => cutoff i.castSucc) *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
    (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ws ∈ exposureTupleSpace X n,
      exposureTupleWeight X ρ Ws *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) ≤
      snocLargeCostBudget ell cutoff L := by
  classical
  induction n with
  | zero =>
      simp [snocLargeCostBudget, exposureTupleSpace, exposureTupleWeight,
        exposureTupleStepsSnoc, iteratedLargeCostSum]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let cutoffTail : Fin n → ℕ := fun i => cutoff i.castSucc
      let Ltail : Fin n → ℕ := fun i => L i.castSucc
      have htail :
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc cutoffTail Ws)) ≤
            snocLargeCostBudget ell cutoffTail Ltail := by
        exact ih ρtail cutoffTail Ltail
          (fun i => hρ0 i.castSucc)
          (fun i => hρ1 i.castSucc)
          (fun i => hL i.castSucc)
          (fun i => hρ i.castSucc)
      have hCurrentBound :
          ∀ Ws ∈ exposureTupleSpace X n,
            ∀ S ∈ iteratedSmallFragments H
              (exposureTupleStepsSnoc cutoffTail Ws),
              S.card ≤ snocCurrentCardBound ell cutoffTail := by
        cases n with
        | zero =>
            intro Ws _hWs S hS
            simpa [snocCurrentCardBound, exposureTupleStepsSnoc,
              iteratedSmallFragments] using hHbound S hS
        | succ m =>
            intro Ws _hWs S hS
            exact
              iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
                H cutoffTail Ws S hS
      have hsnoc :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ Ws ∈ exposureTupleSpace X n,
              exposureTupleWeight X ρtail Ws *
                iteratedLargeCostSum X q H
                  (exposureTupleStepsSnoc cutoffTail Ws)) +
              ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        exact
          iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
            X H (snocCurrentCardBound ell cutoffTail) (L (Fin.last n))
            ρ cutoff hρ0 hρ1 (hL (Fin.last n)) hq0 hq1
            (hρ (Fin.last n)) hHX hCurrentBound
      have hadd := add_le_add_right htail
        ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
      exact hsnoc.trans (by
        simpa [snocLargeCostBudget, cutoffTail, Ltail, add_comm,
          add_left_comm, add_assoc] using hadd)

lemma exists_source_subset_union_of_iteratedSmallFragment_subset
    {H : Finset (Finset α)} {steps : List (ℕ × Finset α)} {V : Finset α}
    (h : ∃ T ∈ iteratedSmallFragments H steps, T ⊆ V) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  induction steps generalizing H V with
  | nil =>
      simpa [iteratedSmallFragments, smallStepExposureUnion] using h
  | cons step steps ih =>
      rcases ih (H := smallMinimalFragments step.1 H step.2) h with
        ⟨R, hRsmall, hRsub⟩
      have hRmin : R ∈ minimalFragments H step.2 :=
        (mem_smallMinimalFragments.mp hRsmall).1
      rcases exists_source_subset_union_of_minimalFragment_subset
          (H := H) (W := step.2)
          (V := smallStepExposureUnion steps ∪ V)
          ⟨R, hRmin, hRsub⟩ with
        ⟨S, hS, hSsub⟩
      exact ⟨S, hS, by
        simpa [smallStepExposureUnion, Finset.union_assoc] using hSsub⟩

lemma coverCost_le_iteratedSmallFragments_add_largeCostSum
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (iteratedSmallFragments H steps) p +
        iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments, iteratedLargeCostSum]
  | cons step steps ih =>
      let H' : Finset (Finset α) :=
        smallMinimalFragments step.1 H step.2
      let L : Finset (Finset α) :=
        largeMinimalFragments step.1 H step.2
      have hstep :
          coverCost X H p ≤ coverCost X H' p + coverCost X L p := by
        simpa [H', L] using
          coverCost_le_small_add_large_minimalFragments
            X step.1 H step.2 hp0
      have hih :
          coverCost X H' p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              iteratedLargeCostSum X p H' steps :=
        ih (H := H')
      have hcombine :
          coverCost X H' p + coverCost X L p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              (coverCost X L p + iteratedLargeCostSum X p H' steps) := by
        linarith
      exact hstep.trans (by
        simpa [iteratedSmallFragments, iteratedLargeCostSum, H', L,
          add_assoc, add_comm, add_left_comm] using hcombine)

lemma coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p)
    (hloss : iteratedLargeCostSum X p H steps < coverCost X H p) :
    0 < coverCost X (iteratedSmallFragments H steps) p := by
  have hle :=
    coverCost_le_iteratedSmallFragments_add_largeCostSum
      X H steps hp0
  linarith

lemma exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos' :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedSmallFragments H steps) V) p := by
    simpa [iteratedSmallFragments_append_singleton] using hpos
  rcases
      (coverCost_smallMinimalFragments_one_pos_iff_exists_subset
        X (iteratedSmallFragments H steps) V hp0).mp hpos' with
    ⟨T, hT, hTV⟩
  exact exists_source_subset_union_of_iteratedSmallFragment_subset
    (H := H) (steps := steps) (V := V) ⟨T, hT, hTV⟩

lemma exists_source_subset_union_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p :=
    coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
      X H (steps ++ [(1, V)]) hp0 hloss
  exact exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    X H steps V hp0 hpos

lemma exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : smallStepExposureUnion steps ∪ V ⊆ X)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    smallStepExposureUnion steps ∪ V ∈ upClosureIn X H := by
  rcases exists_source_subset_union_of_largeCostSum_lt_append_one
      X H steps V hp0 hloss with
    ⟨S, hS, hSsub⟩
  exact mem_upClosureIn.mpr ⟨hUnionX, S, hS, hSsub⟩

lemma half_lt_coverCost_of_not_pSmall_upClosureIn
    {X : Finset α} {H : Finset (Finset α)} {q : ℝ}
    (hq0 : 0 ≤ q) (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q) :
    (1 / 2 : ℝ) < coverCost X H q := by
  have hNotSmallH : ¬ pSmall X H q :=
    (not_pSmall_upClosureIn_iff hHX).mp hNotSmall
  exact (not_pSmall_iff_half_lt_coverCost hq0 hHX).mp hNotSmallH

lemma half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    {Ω : Type*} [DecidableEq Ω]
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    (s : Finset Ω) (weight : Ω → ℝ)
    (stepsOf : Ω → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hcost_pos : 0 < coverCost X H p)
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hshape :
      ∀ ω ∈ s,
        ∃ steps V,
          stepsOf ω = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ ω ∈ s,
        weight ω * iteratedLargeCostSum X p H (stepsOf ω)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ ω ∈ s.filter
        (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H),
        weight ω := by
  refine half_lt_weighted_good_of_average_lt_half_of_bad_le
    s weight
    (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H)
    (fun ω => iteratedLargeCostSum X p H (stepsOf ω))
    hweight_nonneg hsum_weight hcost_pos ?_ ?_ havg
  · intro ω _hωs
    exact iteratedLargeCostSum_nonneg X H (stepsOf ω) hp0
  · intro ω hωs hbad
    rcases hshape ω hωs with ⟨steps, V, hsteps, hUnionX⟩
    exact le_of_not_gt fun hloss =>
      hbad (by
        have hmem :=
          exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
            X H steps V hp0 hUnionX (by
              simpa [hsteps] using hloss)
        simpa [hsteps, smallStepExposureUnion_append_singleton] using hmem)

lemma half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin n → ℝ)
    (stepsOf : (Fin n → Finset α) → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hshape :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∃ steps V,
          stepsOf Ws = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (stepsOf Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X n).filter
        (fun Ws => smallStepExposureUnion (stepsOf Ws) ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  exact half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    X H (exposureTupleSpace X n) (exposureTupleWeight X ρ) stepsOf
    hp0 hcost_pos
    (fun Ws _hWs => exposureTupleWeight_nonneg X hρ0 hρ1 Ws)
    (sum_exposureTupleWeight_eq_one X ρ)
    hshape havg

lemma half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  have hhalf :=
    half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
      X H ρ (fun Ws => exposureTupleStepsSnoc cutoff Ws)
      hp0 hρ0 hρ1 hcost_pos
      (fun Ws hWs => exposureTupleStepsSnoc_last_shape hWs hlast)
      havg
  simpa [smallStepExposureUnion_exposureTupleStepsSnoc] using hhalf

lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    (X : Finset α) (H : Finset (Finset α)) {p θ : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (hmeasure :
      (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws) =
          muP X (upClosureIn X H) θ)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) θ := by
  have hhalf :=
    half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
      X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast havg
  rw [← hmeasure]
  simpa [upClosureIn] using hhalf

lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast
    (exposureTupleUnion_measure_eq_muP X (upClosureIn X H) ρ)
    havg

lemma half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
    (X : Finset α) (H : Finset (Finset α)) {q : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hq0 : 0 < q)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X H q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hHX hNotSmall
  have hcost_pos : 0 < coverCost X H q := by linarith
  have hbudget :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H q * (1 / 2) := by
    nlinarith
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    X H ρ cutoff hq0.le hρ0 hρ1 hcost_pos hlast hbudget

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
universe u
section ThresholdDefinitions
variable {α : Type*} [DecidableEq α]
def CriticalAtMost (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ muP X U p ≥ 1 / 2

lemma CriticalAtMost.of_mu_ge {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmu : muP X U p ≥ 1 / 2) :
    CriticalAtMost X U p :=
  ⟨hp0, hp1, hmu⟩

lemma CriticalAtMost.of_pow_ell_ge_half
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) (hpow : (1 / 2 : ℝ) ≤ p ^ ell X U) :
    CriticalAtMost X U p := by
  have hmu_lower : p ^ ell X U ≤ muP X U p :=
    pow_ell_le_muP_of_nonempty_increasing hp0 hp1 hUX hIncr hU
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hpow.trans hmu_lower)

end ThresholdDefinitions
lemma park_pham_threshold_not_small_lt_of_empty_mem
    {α : Type*} [DecidableEq α]
    (CKK : ℝ) (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hmu : muP X U (CKK * q * Real.log (ell X U)) = 1 :=
    muP_eq_one_of_empty_mem_increasing hUX hIncr hEmpty _
  rw [hmu]
  norm_num

lemma q_lt_one_of_large_constant_threshold_le_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_le_one : CKK * q * Real.log (ell X U) ≤ 1) :
    q < 1 := by
  by_contra hnot
  have hq_ge_one : (1 : ℝ) ≤ q := le_of_not_gt hnot
  have hq_eq_one : q = 1 := le_antisymm hq1 hq_ge_one
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK
  have hCKK_log2_le :
      CKK * Real.log 2 ≤ CKK * Real.log (ell X U) :=
    mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
  have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCKK hlog2_pos.le
    have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
      field_simp [hlog2_pos.ne']
    linarith
  have hCKK_log_le_one : CKK * Real.log (ell X U) ≤ 1 := by
    simpa [hq_eq_one] using hthreshold_le_one
  linarith

lemma q_lt_one_of_large_constant_threshold_lt_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1) :
    q < 1 :=
  q_lt_one_of_large_constant_threshold_le_one hCKK hq1 hthreshold_lt_one.le

def StrictNonSmallCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

def StrictHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (CKK * q * Real.log (ell X U)) ^ ell X U < 1 / 2 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

def StrictGeneratedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X (upClosureIn X A)) < 1 →
    (CKK * q * Real.log (ell X (upClosureIn X A))) ^
        ell X (upClosureIn X A) < 1 / 2 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ upClosureIn X A →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log (ell X (upClosureIn X A))) ≥ 1 / 2

def StrictAntichainHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainMultiHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    1 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainLargeHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainSparseHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainScaledHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainScaleOnlyHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainReducedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

def StrictAntichainReducedPVQuarterCertificateOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 0 ≤ ρ i) ∧
      (∀ i, ρ i ≤ 1) ∧
      cutoff (Fin.last n) = 1 ∧
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) <
        (1 / 4 : ℝ)

def StrictAntichainReducedPVSnocBudgetSchemeOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      snocLargeCostBudget (max 2 (A.sup Finset.card)) cutoff L <
        (1 / 4 : ℝ)

def PVSnocScalarParameterScheme (CKK : ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      (∑ i : Fin (n + 1), (L i : ℝ)) ≤ CKK * Real.log (m : ℝ) ∧
      snocLargeCostBudget m cutoff L < (1 / 4 : ℝ)

noncomputable def pvSnocPowerCutoff (a n : ℕ) (i : Fin (n + 1)) : ℕ :=
  2 ^ (a + (n - i.1))

lemma pvSnocPowerCutoff_tail (a n : ℕ) :
    (fun i : Fin (n + 1) => pvSnocPowerCutoff a (n + 1) i.castSucc) =
      pvSnocPowerCutoff (a + 1) n := by
  funext i
  have hi : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
  simp [pvSnocPowerCutoff]
  have hsub : n + 1 - i.1 = n - i.1 + 1 := by omega
  rw [hsub]
  omega

lemma pvSnocPowerCutoff_last (a n : ℕ) :
    pvSnocPowerCutoff a n (Fin.last n) = 2 ^ a := by
  simp [pvSnocPowerCutoff]

lemma nat_succ_le_two_pow_local (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [Nat.pow_succ]
      nlinarith

lemma pow_two_mul_inv_sixtyfour_pow_le (c b : ℕ) (hb : b ≤ 2 * c) :
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c ≤ (1 / 16 : ℝ) ^ c := by
  have hpow : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (2 * c) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  have hnonneg : 0 ≤ (1 / (64 : ℝ)) ^ c := by positivity
  calc
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c
        ≤ (2 : ℝ) ^ (2 * c) * (1 / (64 : ℝ)) ^ c :=
          mul_le_mul_of_nonneg_right hpow hnonneg
    _ = (1 / 16 : ℝ) ^ c := by
          rw [pow_mul]
          rw [← mul_pow]
          norm_num

lemma snocLargeCostBudget_pvSnocPowerCutoff_le_geometric
    (ell a n : ℕ) (hfirst : ell ≤ 2 * 2 ^ (a + n)) :
    snocLargeCostBudget ell (pvSnocPowerCutoff a n)
        (fun _ : Fin (n + 1) => 64) ≤
      ∑ j ∈ Finset.range (n + 1),
        (1 / 16 : ℝ) ^ (2 ^ (a + (n - j))) := by
  induction n generalizing a with
  | zero =>
      have hterm := pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) ell hfirst
      simpa [snocLargeCostBudget, snocCurrentCardBound, pvSnocPowerCutoff]
        using hterm
  | succ n ih =>
      have htail_first : ell ≤ 2 * 2 ^ ((a + 1) + n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
      have htail := ih (a + 1) htail_first
      have hcurrent :
          snocCurrentCardBound ell (pvSnocPowerCutoff (a + 1) n) =
            2 ^ (a + 1) := by
        simp [snocCurrentCardBound, pvSnocPowerCutoff]
      have hcurrent_le : 2 ^ (a + 1) ≤ 2 * 2 ^ a := by
        rw [Nat.pow_succ]
        omega
      have hterm :=
        pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) (2 ^ (a + 1)) hcurrent_le
      calc
        snocLargeCostBudget ell (pvSnocPowerCutoff a (n + 1))
            (fun _ : Fin (n + 1 + 1) => 64)
            ≤ (∑ j ∈ Finset.range (n + 1),
                  (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
                (1 / 16 : ℝ) ^ (2 ^ a) := by
              rw [snocLargeCostBudget]
              simp only [pvSnocPowerCutoff_tail]
              have hLtail :
                  (fun i : Fin (n + 1) =>
                    (fun _ : Fin (n + 1 + 1) => 64) i.castSucc) =
                    (fun _ : Fin (n + 1) => 64) := rfl
              rw [hLtail]
              have hlastCut :
                  pvSnocPowerCutoff a (n + 1) (Fin.last (n + 1)) = 2 ^ a :=
                pvSnocPowerCutoff_last a (n + 1)
              rw [hlastCut, hcurrent]
              exact add_le_add htail hterm
        _ = ∑ j ∈ Finset.range (n + 1 + 1),
              (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))) := by
              conv_rhs => rw [Finset.sum_range_succ]
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro j hj
                have hjle : j ≤ n :=
                  Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                have hsub : n + 1 - j = n - j + 1 := by omega
                rw [hsub]
                congr 2
                omega
              · simp

lemma pvSnocGeometricSum_le (a n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (a + (n - j)))) ≤
      (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
  induction n generalizing a with
  | zero =>
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hpow_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      have hden_pos : 0 < (1 - (1 / 16 : ℝ)) := by norm_num
      have hx : 0 ≤ (1 / 16 : ℝ) ^ (a + 1) := by positivity
      have hle_div :
          (1 / 16 : ℝ) ^ (a + 1) ≤
            (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
        rw [le_div_iff₀ hden_pos]
        nlinarith
      simpa using hpow_le.trans hle_div
  | succ n ih =>
      have htail := ih (a + 1)
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hterm_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      calc
        (∑ j ∈ Finset.range (n + 1 + 1),
          (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))))
            = (∑ j ∈ Finset.range (n + 1),
                (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
              (1 / 16 : ℝ) ^ (2 ^ a) := by
                conv_lhs => rw [Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hjle : j ≤ n :=
                    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                  have hsub : n + 1 - j = n - j + 1 := by omega
                  rw [hsub]
                  congr 2
                  omega
                · simp
        _ ≤ (1 / 16 : ℝ) ^ ((a + 1) + 1) /
              (1 - (1 / 16 : ℝ)) +
              (1 / 16 : ℝ) ^ (a + 1) := by
                exact add_le_add htail hterm_le
        _ = (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
              ring_nf

lemma pvSnocGeometricSum_zero_lt_quarter (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (0 + (n - j)))) < (1 / 4 : ℝ) := by
  have h := pvSnocGeometricSum_le 0 n
  have hconst :
      (1 / 16 : ℝ) ^ (0 + 1) / (1 - (1 / 16 : ℝ)) < (1 / 4 : ℝ) := by
    norm_num
  exact lt_of_le_of_lt h hconst

lemma natLog2_add_one_le_two_log_div_log2 (m : ℕ) (hm : 2 ≤ m) :
    (((Nat.log 2 m + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (m : ℝ) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2_le_logm : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) hm_real
  have hquot_ge_one : (1 : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ hlog2pos).2 (by simpa using hlog2_le_logm)
  have hlog_nat_le :
      ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb m
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  calc
    (((Nat.log 2 m + 1 : ℕ) : ℝ))
        = ((Nat.log 2 m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ Real.log (m : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log (m : ℝ) / Real.log 2 +
          Real.log (m : ℝ) / Real.log 2 := by linarith
    _ = 2 * Real.log (m : ℝ) / Real.log 2 := by ring

theorem pvSnocScalarParameterScheme_128_div_log_two :
    PVSnocScalarParameterScheme (128 / Real.log 2) := by
  intro m hm
  let n : ℕ := Nat.log 2 m
  let L : Fin (n + 1) → ℕ := fun _ => 64
  let cutoff : Fin (n + 1) → ℕ := pvSnocPowerCutoff 0 n
  refine ⟨n, L, cutoff, ?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [L]
  · simpa [cutoff] using pvSnocPowerCutoff_last 0 n
  · have hsum_eq :
        (∑ i : Fin (n + 1), (L i : ℝ)) =
          64 * (((n + 1 : ℕ) : ℝ)) := by
      simp [L]
      ring
    have hlog_bound := natLog2_add_one_le_two_log_div_log2 m hm
    have hmul :=
      mul_le_mul_of_nonneg_left hlog_bound (by norm_num : (0 : ℝ) ≤ 64)
    calc
      (∑ i : Fin (n + 1), (L i : ℝ))
          = 64 * (((n + 1 : ℕ) : ℝ)) := hsum_eq
      _ ≤ 64 * (2 * Real.log (m : ℝ) / Real.log 2) := by
        simpa [n, mul_assoc] using hmul
      _ = (128 / Real.log 2) * Real.log (m : ℝ) := by ring
  · have hfirst : m ≤ 2 * 2 ^ (0 + n) := by
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      have hle : m ≤ 2 ^ (Nat.log 2 m + 1) := Nat.le_of_lt hlt
      simpa [n, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using hle
    have hbudget_le :=
      snocLargeCostBudget_pvSnocPowerCutoff_le_geometric m 0 n hfirst
    have hgeom_lt := pvSnocGeometricSum_zero_lt_quarter n
    exact lt_of_le_of_lt (by simpa [cutoff, L, n] using hbudget_le) hgeom_lt

theorem exists_pv_snoc_scalar_parameter_scheme :
    ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
      PVSnocScalarParameterScheme CKK := by
  refine ⟨128 / Real.log 2, ?_, ?_, pvSnocScalarParameterScheme_128_div_log_two⟩
  · positivity
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 128)
      hlog2pos.le

theorem strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScalar : PVSnocScalarParameterScheme CKK) :
    StrictAntichainReducedPVSnocBudgetSchemeOn CKK α := by
  intro X A q hq0 _hq1 _hAX _hAnti _hEmptyA _hscale_lt _hthreshold_lt_one
    _hNoHeavy _hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  have hm_two : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  rcases hScalar m hm_two with
    ⟨n, L, cutoff, hL, hlast, hsum, hbudget⟩
  have hdensity :
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsum hq0.le
    simpa [m, mul_assoc, mul_comm, mul_left_comm] using hmul
  exact ⟨n, L, cutoff, hL, hlast, hdensity, by simpa [m] using hbudget⟩

theorem strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScheme : StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    StrictAntichainReducedPVQuarterCertificateOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  rcases hScheme X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, L, cutoff, hL, hlast, hdensity, hbudget⟩
  let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
  have hq_le_one : q ≤ 1 := hq1.le
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    dsimp [ρ]
    linarith
  have hρ1 : ∀ i, ρ i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    dsimp [ρ]
    linarith
  have htuple :
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have htuple_le :
        tupleUnionDensity ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
      simpa [ρ] using
        tupleUnionDensity_one_sub_pow_le_q_sum L hq0.le hq_le_one
    exact htuple_le.trans hdensity
  let m : ℕ := max 2 (A.sup Finset.card)
  have hAcard_bound : ∀ S ∈ A, S.card ≤ m := by
    intro S hS
    exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
      (le_max_right _ _)
  have havg_le :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) ≤
        snocLargeCostBudget m cutoff L := by
    exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
      X A m ρ cutoff L hρ0 hρ1 hL hq0 hq_le_one
      (fun i => rfl) hAX hAcard_bound
  refine ⟨n, ρ, cutoff, hρ0, hρ1, hlast, htuple, ?_⟩
  exact havg_le.trans_lt (by simpa [m] using hbudget)

theorem strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hCert : StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  let θ : ℝ :=
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  rcases hCert X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, ρ, cutoff, hρ0, hρ1, hlast, hρ_le_target, havg⟩
  have hhalf :
      (1 / 2 : ℝ) <
        muP X (upClosureIn X A) (tupleUnionDensity ρ) :=
    half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
      X A ρ cutoff hq0 hρ0 hρ1 hAX hNotSmall hlast havg
  have htuple_nonneg : 0 ≤ tupleUnionDensity ρ :=
    tupleUnionDensity_nonneg hρ0 hρ1
  have htheta_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact hthreshold_lt_one.le
  have hmono :
      muP X (upClosureIn X A) (tupleUnionDensity ρ) ≤
        muP X (upClosureIn X A) θ :=
    muP_mono_density (increasingIn_upClosureIn X A)
      htuple_nonneg (by simpa [θ] using hρ_le_target) htheta_le_one
  exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)

theorem park_pham_threshold_not_small_lt_of_pow_ell_ge_half
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    {X : Finset α} {U : Finset (Finset α)}
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q)
    (hpow : (1 / 2 : ℝ) ≤
      (CKK * q * Real.log (ell X U)) ^ ell X U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog_pos : 0 < Real.log (ell X U) :=
    lt_of_lt_of_le hlog2_pos (Real.log_le_log (by norm_num) hell_ge_two)
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hp1 : CKK * q * Real.log (ell X U) ≤ 1 := hthreshold_lt_one.le
  have hU : U.Nonempty := nonempty_of_not_pSmall hNotSmall
  exact (CriticalAtMost.of_pow_ell_ge_half hp0 hp1 hUX hIncr hU hpow).2.2

theorem strict_nonSmallCoreOn_of_hardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK) (hCore : StrictHardCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall
  by_cases hpow :
      (1 / 2 : ℝ) ≤ (CKK * q * Real.log (ell X U)) ^ ell X U
  · exact park_pham_threshold_not_small_lt_of_pow_ell_ge_half
      hCKK_pos hq0 hthreshold_lt_one hUX hIncr hNotSmall hpow
  · exact hCore X U q hq0 hq1 hthreshold_lt_one
      (lt_of_not_ge hpow) hUX hIncr hEmpty hNotSmall

theorem strict_hardCoreOn_of_generatedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictGeneratedHardCoreOn CKK α) :
    StrictHardCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hpow_lt hUX hIncr hEmpty hNotSmall
  let A : Finset (Finset α) := minimalMembersIn X U
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hS
    exact hUX S (minimalMembersIn_subset hS)
  have hAnti : InclusionAntichain A := by
    simpa [A] using minimalMembersIn_inclusionAntichain X U
  have hclosure_eq : upClosureIn X A = U := by
    simpa [A] using upClosureIn_minimalMembersIn_eq_of_increasing hUX hIncr
  have hthreshold_A :
      CKK * q * Real.log (ell X (upClosureIn X A)) < 1 := by
    simpa [hclosure_eq] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log (ell X (upClosureIn X A))) ^
          ell X (upClosureIn X A) < 1 / 2 := by
    simpa [hclosure_eq] using hpow_lt
  have hEmpty_A : (∅ : Finset α) ∉ upClosureIn X A := by
    simpa [hclosure_eq] using hEmpty
  have hNotSmall_A : ¬ pSmall X (upClosureIn X A) q := by
    simpa [hclosure_eq] using hNotSmall
  have hmu :=
    hCore X A q hq0 hq1 hthreshold_A hpow_A hAX hAnti hEmpty_A hNotSmall_A
  simpa [hclosure_eq] using hmu

theorem strictGeneratedHardCoreOn_of_antichainHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainHardCoreOn CKK α) :
    StrictGeneratedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hthreshold_lt_one hpow_lt hAX hAnti hEmpty hNotSmall
  have hA_nonempty : A.Nonempty :=
    nonempty_of_upClosureIn_nonempty (nonempty_of_not_pSmall hNotSmall)
  have hEmptyA : (∅ : Finset α) ∉ A :=
    empty_not_mem_upClosureIn_iff.mp hEmpty
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_A :
      CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 := by
    simpa [hEll] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          max 2 (A.sup Finset.card) < 1 / 2 := by
    simpa [hEll] using hpow_lt
  have hmu :=
    hCore X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
      hthreshold_A hpow_A hNotSmall
  simpa [hEll] using hmu

theorem strictAntichainHardCoreOn_of_multiHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainMultiHardCoreOn CKK α) :
    StrictAntichainHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
    hthreshold_lt_one _hpow_lt hNotSmall
  by_cases hcard_one : A.card = 1
  · rcases Finset.card_eq_one.mp hcard_one with ⟨S, hAeq⟩
    subst A
    have hSX : S ⊆ X := hAX S (by simp)
    have hCover : CoversIn X {S} (upClosureIn X {S}) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hR, hRT⟩
      have hR_eq : R = S := by simpa using hR
      exact ⟨S, by simp, by simpa [hR_eq] using hRT⟩
    have hqpow_gt : (1 / 2 : ℝ) < q ^ S.card := by
      by_contra hnot
      have hle : q ^ S.card ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
      have hSmall : pSmall X (upClosureIn X {S}) q :=
        pSmall_of_cover_sum_le hCover (by simpa using hle)
      exact hNotSmall hSmall
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have hm_ge_two_nat : 2 ≤ max 2 S.card := le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((max 2 S.card : ℕ) : ℝ) := by
      exact_mod_cast hm_ge_two_nat
    have hlog2_le : Real.log 2 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have hone_le_CKK_logm :
        (1 : ℝ) ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have hq_le_target :
        q ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      calc
        q = q * 1 := by ring
        _ ≤ q * (CKK * Real.log ((max 2 S.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hone_le_CKK_logm hq0.le
        _ = CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by ring
    have hp0 : 0 ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hthreshold_S :
        CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) < 1 := by
      simpa using hthreshold_lt_one
    have hp1 : CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) ≤ 1 :=
      hthreshold_S.le
    have hpow_q_le :
        q ^ S.card ≤
          (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
      pow_le_pow_left₀ hq0.le hq_le_target S.card
    have hmu :
        (1 / 2 : ℝ) ≤
          muP X (upClosureIn X {S})
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) := by
      have hstrict :
          (1 / 2 : ℝ) <
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        hqpow_gt.trans_le hpow_q_le
      have hsingle :
          muP X (upClosureIn X {S})
              (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) =
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        muP_upClosure_single X S hSX hp0 hp1
      rw [hsingle]
      exact hstrict.le
    simpa using hmu
  · have hcard_gt_one : 1 < A.card := by
      have hpos : 0 < A.card := hA_nonempty.card_pos
      omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
      hthreshold_lt_one _hpow_lt hNotSmall

theorem strictAntichainMultiHardCoreOn_of_largeHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainLargeHardCoreOn CKK α) :
    StrictAntichainMultiHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  by_cases hcard_two : A.card = 2
  · rcases A.exists_min_image Finset.card hA_nonempty with ⟨S, hSA, hS_min⟩
    have hCover : CoversIn X A (upClosureIn X A) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hRA, hRT⟩
      exact ⟨R, hRA, hRT⟩
    have hsum_gt :
        (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card :=
      cover_sum_gt_half_of_not_pSmall hNotSmall hCover
    have hterm : ∀ R ∈ A, q ^ R.card ≤ q ^ S.card := by
      intro R hRA
      exact pow_le_pow_of_le_one hq0.le hq1.le (hS_min R hRA)
    have hsum_le :
        (∑ R ∈ A, q ^ R.card) ≤ ∑ R ∈ A, q ^ S.card :=
      Finset.sum_le_sum hterm
    have hconst :
        (∑ R ∈ A, q ^ S.card) = (A.card : ℝ) * q ^ S.card := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hqpow_quarter : (1 / 4 : ℝ) < q ^ S.card := by
      have hhalf_lt_two : (1 / 2 : ℝ) < (2 : ℝ) * q ^ S.card := by
        calc
          (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card := hsum_gt
          _ ≤ ∑ R ∈ A, q ^ S.card := hsum_le
          _ = (A.card : ℝ) * q ^ S.card := hconst
          _ = (2 : ℝ) * q ^ S.card := by simp [hcard_two]
      linarith
    have hS_nonempty : S.Nonempty := by
      by_contra hS_empty
      have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
      exact hEmptyA (by simpa [hS_eq] using hSA)
    have hS_card_pos : 0 < S.card := hS_nonempty.card_pos
    let m : ℕ := max 2 (A.sup Finset.card)
    let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
    have hm_ge_two_nat : 2 ≤ m := by
      dsimp [m]
      exact le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have htwo_le_CKK_logm : (2 : ℝ) ≤ CKK * Real.log ((m : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have htwoq_le_p : 2 * q ≤ p := by
      calc
        2 * q = q * 2 := by ring
        _ ≤ q * (CKK * Real.log ((m : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left htwo_le_CKK_logm hq0.le
        _ = p := by simp [p]; ring
    have htwoq_nonneg : 0 ≤ 2 * q := by positivity
    have htwo_pow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ S.card := by
      cases hcard : S.card with
      | zero =>
          omega
      | succ n =>
          have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
            exact one_le_pow₀ (by norm_num)
          calc
            (2 : ℝ) = 2 * 1 := by ring
            _ ≤ 2 * (2 : ℝ) ^ n := by nlinarith
            _ = (2 : ℝ) ^ Nat.succ n := by rw [pow_succ]; ring
    have hhalf_lt_twoq_pow : (1 / 2 : ℝ) < (2 * q) ^ S.card := by
      rw [mul_pow]
      have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
      have hhalf_lt_two_qpow : (1 / 2 : ℝ) < 2 * q ^ S.card := by
        linarith
      have htwo_qpow_le :
          2 * q ^ S.card ≤ (2 : ℝ) ^ S.card * q ^ S.card := by
        nlinarith
      exact hhalf_lt_two_qpow.trans_le htwo_qpow_le
    have hp_pow_lower : (1 / 2 : ℝ) ≤ p ^ S.card := by
      have hpow_le : (2 * q) ^ S.card ≤ p ^ S.card :=
        pow_le_pow_left₀ htwoq_nonneg htwoq_le_p S.card
      exact (hhalf_lt_twoq_pow.trans_le hpow_le).le
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hp1 : p ≤ 1 := by
      dsimp [p, m]
      exact hthreshold_lt_one.le
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower :
        p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    have hmu : (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) p :=
      hp_pow_lower.trans hmu_lower
    simpa [p, m] using hmu
  · have hcard_large : 2 < A.card := by omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      hthreshold_lt_one hpow_lt hNotSmall

theorem strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainSparseHardCoreOn CKK α) :
    StrictAntichainLargeHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
    le_trans hlog2_pos.le hlog2_le
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  have hp1 : p ≤ 1 := by
    dsimp [p, m]
    exact hthreshold_lt_one.le
  by_cases hHeavy : ∃ S ∈ A, (1 / 2 : ℝ) ≤ p ^ S.card
  · rcases hHeavy with ⟨S, hSA, hS_heavy⟩
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower : p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    exact hS_heavy.trans hmu_lower
  · have hNoHeavy : ∀ S ∈ A, p ^ S.card < 1 / 2 := by
      intro S hSA
      exact lt_of_not_ge fun hge => hHeavy ⟨S, hSA, hge⟩
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      (by simpa [p, m] using hthreshold_lt_one)
      (by simpa [p, m] using hpow_lt)
      (by simpa [p, m] using hNoHeavy)
      hNotSmall

theorem park_pham_threshold_not_small_lt_of_strict_core_on
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictNonSmallCoreOn CKK α)
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · exact park_pham_threshold_not_small_lt_of_empty_mem CKK X U q hUX hIncr hEmpty
  · have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_lt_one hCKK_large hq1 hthreshold_lt_one
    exact hCore X U q hq0 hq_lt_one hthreshold_lt_one hUX hIncr hEmpty hNotSmall

theorem park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  exact park_pham_threshold_not_small_lt_of_strict_core_on hCKK_large
    (strict_nonSmallCoreOn_of_hardCoreOn (α := α) hCKK_pos (hCore (α := α)))
    X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall

theorem park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictGeneratedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strict_hardCoreOn_of_generatedHardCoreOn (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictGeneratedHardCoreOn_of_antichainHardCoreOn
      (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainMultiHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainHardCoreOn_of_multiHardCoreOn
      hCKK_large (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainLargeHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainMultiHardCoreOn_of_largeHardCoreOn
      hCKK_large (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainSparseHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
      hCKK_large (hCore (α := α)))

lemma exists_generator_scale_pow_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    ∃ S ∈ A,
      (CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^ S.card <
        (A.card : ℝ) := by
  rcases exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
      hNotSmall with ⟨S, hSA, hq_weight⟩
  have hA_nonempty : A.Nonempty := ⟨S, hSA⟩
  have hAcard_pos_nat : 0 < A.card := hA_nonempty.card_pos
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hAcard_pos_nat
  have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog_nonneg :
      0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hm_ge_two)).le
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hCKK_pos.le hlog_nonneg
  have htarget :
      (L * q) ^ S.card < 1 / 2 := by
    have h := hNoHeavy S hSA
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_lt : L ^ S.card * q ^ S.card < 1 / 2 := by
    simpa [mul_pow] using htarget
  have hscale_lt : L ^ S.card < (A.card : ℝ) := by
    by_contra hnot
    have hscale_ge : (A.card : ℝ) ≤ L ^ S.card := le_of_not_gt hnot
    have hmul_ge :
        (A.card : ℝ) * q ^ S.card ≤ L ^ S.card * q ^ S.card :=
      mul_le_mul_of_nonneg_right hscale_ge hqpow_pos.le
    have hquarter_lt : (1 / 2 : ℝ) < (A.card : ℝ) * q ^ S.card := by
      have hden_pos : 0 < 2 * (A.card : ℝ) := by positivity
      rw [div_lt_iff₀ hden_pos] at hq_weight
      nlinarith
    have : (1 / 2 : ℝ) < L ^ S.card * q ^ S.card :=
      hquarter_lt.trans_le hmul_ge
    exact not_lt_of_ge hmul_lt.le this
  exact ⟨S, hSA, by simpa [L] using hscale_lt⟩

lemma scale_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) (hq0 : 0 < q)
    (hEmptyA : (∅ : Finset α) ∉ A)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  rcases exists_generator_scale_pow_lt_card_of_sparse hCKK_pos hq0
      hNoHeavy hNotSmall with ⟨S, hSA, hscale_pow_lt⟩
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog2_le : Real.log 2 ≤
      Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hL_ge_two : (2 : ℝ) ≤ L := by
    have hmul := mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul2 := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    dsimp [L]
    linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hL_ge_one : (1 : ℝ) ≤ L := by linarith
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
    exact hEmptyA (by simpa [hS_eq] using hSA)
  have hL_le_pow : L ≤ L ^ S.card := by
    cases hcard : S.card with
    | zero =>
        have hbad : S.card ≠ 0 := hS_nonempty.card_pos.ne'
        exact False.elim (hbad hcard)
    | succ n =>
        have hpow_ge_one : (1 : ℝ) ≤ L ^ n := one_le_pow₀ hL_ge_one
        rw [pow_succ]
        nlinarith
  exact lt_of_le_of_lt hL_le_pow (by simpa [L] using hscale_pow_lt)

theorem strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainScaleOnlyHardCoreOn CKK α) :
    StrictAntichainScaledHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hA_nonempty _hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

theorem strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainReducedHardCoreOn CKK α) :
    StrictAntichainScaleOnlyHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    _hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hNoHeavy hNotSmall

theorem strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainScaledHardCoreOn CKK α) :
    StrictAntichainSparseHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  have hscale_lt :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) :=
    scale_lt_card_of_sparse hCKK_large hq0 hEmptyA hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

theorem park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainScaledHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
      hCKK_large (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainScaleOnlyHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
      (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
      (hCore (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCert : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
      (hCert (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScheme : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
        (hScheme (α := α)))

theorem park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScalar : PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
        (α := α) hScalar)

theorem park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    (hScalar :
      ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
        PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases hScalar with ⟨CKK, hCKK_pos, hCKK_large, hScheme⟩
  exact park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    hCKK_pos hCKK_large hScheme

theorem park_pham_threshold_not_small_lt_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    exists_pv_snoc_scalar_parameter_scheme

theorem park_pham_threshold_not_small_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_lt_exists with ⟨CKK, hCKK_pos, hThresholdLt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hNotSmall
  by_cases hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1
  · exact hThresholdLt X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  · have hthreshold_eq_one : CKK * q * Real.log (ell X U) = 1 :=
      le_antisymm hthreshold_le_one (le_of_not_gt hthreshold_lt_one)
    have hU_nonempty : U.Nonempty := nonempty_of_not_pSmall hNotSmall
    have hmu_one : muP X U (1 : ℝ) = 1 :=
      muP_one_of_nonempty_increasing hUX hIncr hU_nonempty
    rw [hthreshold_eq_one, hmu_one]
    norm_num

theorem park_pham_threshold_at_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_exists with ⟨C0, hC0_pos, hThresholdNS⟩
  let CKK : ℝ := max (2 * C0) (2 / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) hC0_pos) (le_max_left _ _)
  have hCKK_ge_2C0 : 2 * C0 ≤ CKK := le_max_left _ _
  have hCKK_ge_2_log2 : 2 / Real.log 2 ≤ CKK := le_max_right _ _
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hell_pos : 0 < (ell X U : ℝ) := by positivity
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hlog_nonneg : 0 ≤ Real.log (ell X U) :=
    le_trans hlog2_pos.le hlog2_le
  have htarget_nonneg : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  by_cases hq_half : q ≤ (1 / 2 : ℝ)
  · let q' : ℝ := 2 * q
    have hq'_pos : 0 < q' := by dsimp [q']; positivity
    have hq'_le_one : q' ≤ 1 := by dsimp [q']; linarith
    have hq_lt_q' : q < q' := by dsimp [q']; linarith
    have hnotSmall : ¬ pSmall X U q' :=
      hqSmall q' hq_lt_q' hq'_le_one
    have hsmall_threshold_le :
        C0 * q' * Real.log (ell X U) ≤ 1 := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      have hle :
          C0 * q' * Real.log (ell X U) ≤
            CKK * q * Real.log (ell X U) := by
        exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
      exact hle.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * q' * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U q' hq'_pos hq'_le_one hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * q' * Real.log (ell X U) := by positivity
    have hsmall_le_target :
        C0 * q' * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
    have hmono :
        muP X U (C0 * q' * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hsmall_le_target hthreshold_le_one
    exact hAtSmall.trans hmono
  · have hq_gt_half : (1 / 2 : ℝ) < q := lt_of_not_ge hq_half
    have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_le_one hCKK_ge_2_log2 hq1 hthreshold_le_one
    have hnotSmall : ¬ pSmall X U (1 : ℝ) :=
      hqSmall 1 hq_lt_one le_rfl
    have hC0_log_le_target :
        C0 * 1 * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0_le_CKKq : C0 * 1 ≤ CKK * q := by
        nlinarith [hCKK_ge_2C0, hq_gt_half, hC0_pos.le]
      exact mul_le_mul_of_nonneg_right hC0_le_CKKq hlog_nonneg
    have hsmall_threshold_le :
        C0 * 1 * Real.log (ell X U) ≤ 1 :=
      hC0_log_le_target.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * 1 * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U 1 (by norm_num) le_rfl hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * 1 * Real.log (ell X U) := by positivity
    have hmono :
        muP X U (C0 * 1 * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hC0_log_le_target hthreshold_le_one
    exact hAtSmall.trans hmono

theorem park_pham_threshold_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
  rcases park_pham_threshold_at_exists with ⟨CKK, hCKK_pos, hThresholdAt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hthreshold_nonneg :
      0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hthreshold_le_one :
      CKK * q * Real.log (ell X U) ≤ 1 := hDensity.trans hp1
  have hAt :
      muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 :=
    hThresholdAt X U q hq0 hq1 hthreshold_le_one hUX hIncr hSmall
  have hmono :
      muP X U (CKK * q * Real.log (ell X U)) ≤ muP X U p :=
    muP_mono_density hIncr hthreshold_nonneg hDensity hp1
  exact hAt.trans hmono

end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
theorem not_pSmall_of_spread
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (_hk : 1 ≤ k)
    (_hUniform : BFVRegular1190.UniformFamily A k)
    (hSpread : BFVRegular1190.SpreadFamily A κ)
    (hκ : 1 < κ)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ¬ pSmall X (upClosureIn X A) (κ⁻¹) := by
  classical
  intro hSmall
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hκ_pos : 0 < κ := by linarith
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  
  have hCoverA : ∀ S ∈ A, ∃ T ∈ G, T ⊆ S := by
    intro S hSA
    have hSup : S ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    exact hCover S hSup
  
  have hAcover : A ⊆ G.biUnion fun T => A.filter fun S => T ⊆ S := by
    intro S hSA
    rcases hCoverA S hSA with ⟨T, hTG, hTS⟩
    exact Finset.mem_biUnion.mpr ⟨T, hTG, Finset.mem_filter.mpr ⟨hSA, hTS⟩⟩
  have hAcardle_nat :
      A.card ≤ ∑ T ∈ G, (A.filter fun S => T ⊆ S).card :=
    (Finset.card_le_card hAcover).trans Finset.card_biUnion_le
  have hAcardle :
      (A.card : ℝ) ≤ ∑ T ∈ G, ((A.filter fun S => T ⊆ S).card : ℝ) := by
    have h := hAcardle_nat
    have : ((A.card : ℕ) : ℝ) ≤
        (((∑ T ∈ G, (A.filter fun S => T ⊆ S).card : ℕ) : ℝ)) := by
      exact_mod_cast h
    rw [Nat.cast_sum] at this
    exact this
  
  have hbound : ∀ T ∈ G,
      ((A.filter fun S => T ⊆ S).card : ℝ) ≤ (A.card : ℝ) * (κ ^ T.card)⁻¹ := by
    intro T _
    by_cases hTne : T.Nonempty
    · have := hSpread T hTne
      rw [div_eq_mul_inv] at this
      exact this
    · have heq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
      subst heq
      have hfilter_eq : (A.filter fun S => (∅ : Finset α) ⊆ S) = A := by
        apply Finset.filter_eq_self.mpr
        intro S _
        exact Finset.empty_subset S
      rw [hfilter_eq]
      simp
  
  have hAsum :
      (A.card : ℝ) ≤ ∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹ :=
    hAcardle.trans (Finset.sum_le_sum hbound)
  
  have hkey :
      (∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹) =
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [← inv_pow]
  rw [hkey] at hAsum
  
  have hsum_ge_one : (1 : ℝ) ≤ ∑ T ∈ G, (κ⁻¹) ^ T.card := by
    have hAsum' : (A.card : ℝ) * 1 ≤
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
      simpa using hAsum
    exact le_of_mul_le_mul_left hAsum' hAcard_pos
  
  linarith

noncomputable def CspOf (CKK : ℝ) : ℝ :=
  max 10 (8 * CKK)

lemma CspOf_pos (CKK : ℝ) : 0 < CspOf CKK := by
  unfold CspOf
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  norm_num

lemma CspOf_ge_ten (CKK : ℝ) : (10 : ℝ) ≤ CspOf CKK := le_max_left _ _

lemma CspOf_ge_two_CKK {CKK : ℝ} (hCKK_pos : 0 < CKK) :
    2 * CKK ≤ CspOf CKK := by
  unfold CspOf
  refine le_trans ?_ (le_max_right _ _)
  linarith

private lemma density_bound_from_kappa_aux
    (CKK Csp : ℝ) (hCKK_pos : 0 < CKK) (hCsp_ge_2CKK : 2 * CKK ≤ Csp)
    {ell_real κ : ℝ} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hell_real_pos : 0 < ell_real)
    (hell_ge_one : 1 ≤ ell_real)
    (hell_le_ek : ell_real ≤ Real.exp 1 * (k : ℝ))
    (hκ_pos : 0 < κ)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    CKK * κ⁻¹ * Real.log ell_real ≤ (1 : ℝ) / (2 * (r : ℝ)) := by
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek_pos : 0 < Real.exp 1 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real_ge_one
    positivity
  have hlog_ek_pos : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
    have he : (1 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    refine Real.log_pos ?_
    linarith
  have hlog_ell_le : Real.log ell_real ≤ Real.log (Real.exp 1 * (k : ℝ)) :=
    Real.log_le_log hell_real_pos hell_le_ek
  have hlog_ell_nonneg : 0 ≤ Real.log ell_real := Real.log_nonneg hell_ge_one
  have h2CKKr_nn : 0 ≤ 2 * CKK * (r : ℝ) := by positivity
  have hκ_lower : 2 * CKK * (r : ℝ) * Real.log ell_real ≤ κ := by
    have s1 : 2 * CKK * (r : ℝ) * Real.log ell_real ≤
        2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ell_le h2CKKr_nn
    have s2 : 2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
      have hrlog_nn : 0 ≤ (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
        positivity
      nlinarith
    linarith
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have hLHS_eq : CKK * κ⁻¹ * Real.log ell_real =
      CKK * Real.log ell_real / κ := by ring
  rw [hLHS_eq, div_le_div_iff₀ hκ_pos h2r_pos]
  have heq : CKK * Real.log ell_real * (2 * (r : ℝ)) =
      2 * CKK * (r : ℝ) * Real.log ell_real := by ring
  rw [heq, one_mul]
  exact hκ_lower

theorem mu_at_partition_density_ge_half_of_threshold
    (CKK : ℝ) (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2)
    {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hUniform : BFVRegular1190.UniformFamily A k)
    (hSpread : BFVRegular1190.SpreadFamily A κ)
    (hAX : ∀ S ∈ A, S ⊆ X)
    (hκ : CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
  set U := upClosureIn X A with hU_def
  
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by linarith
  
  have he_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hek_pos : (0 : ℝ) < Real.exp 1 * (k : ℝ) := by positivity
  have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_real_ge_one he_pos.le
    simpa using h1
  have hlog_ek_ge_one : (1 : ℝ) ≤ Real.log (Real.exp 1 * (k : ℝ)) := by
    have h := Real.log_le_log he_pos hek_ge_e
    simpa [Real.log_exp] using h
  
  have hCsp_ge_ten : (10 : ℝ) ≤ CspOf CKK := CspOf_ge_ten CKK
  have hCsp_pos : 0 < CspOf CKK := CspOf_pos CKK
  have hbase_ge_20 :
      (20 : ℝ) ≤ CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
    have h1 : (10 : ℝ) * 2 ≤ CspOf CKK * (r : ℝ) :=
      mul_le_mul hCsp_ge_ten hr_real_ge_two (by norm_num) hCsp_pos.le
    have h2 :
        CspOf CKK * (r : ℝ) * 1 ≤
          CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ek_ge_one (by positivity)
    linarith
  have hκ_ge_20 : (20 : ℝ) ≤ κ := le_trans hbase_ge_20 hκ
  have hκ_pos : 0 < κ := by linarith
  have hκ_gt_one : 1 < κ := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := hκ_gt_one.le
  have hκ_inv_pos : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ_pos
  have hκ_inv_le_one : κ⁻¹ ≤ 1 := by
    have h := inv_anti₀ (by linarith : (0 : ℝ) < 1) hκ_ge_one
    simpa using h
  
  have hIncr : IncreasingIn X U := increasingIn_upClosureIn X A
  have hUXU : ∀ S ∈ U, S ⊆ X := by
    intro S hS
    have hS' : S ∈ upClosureIn X A := by simpa [hU_def] using hS
    exact (mem_upClosureIn.mp hS').1
  have hNotSmall : ¬ pSmall X U (κ⁻¹) :=
    not_pSmall_of_spread hA hk hUniform hSpread hκ_gt_one hAX
  have hqSmall : qSmallUpper X U (κ⁻¹) :=
    qSmallUpper_of_not_pSmall hκ_inv_pos.le hNotSmall
  
  have hell_pos_nat : 0 < ell X U := ell_pos X U
  have hell_real_pos : (0 : ℝ) < (ell X U : ℝ) := by exact_mod_cast hell_pos_nat
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    have h := two_le_ell X U
    have h1 : 1 ≤ ell X U := le_trans (by norm_num) h
    exact_mod_cast h1
  have hell_le_max : ell X U ≤ max 2 k := ell_upClosure_le hUniform hAX
  have hmax_le_ek : ((max 2 k : ℕ) : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    rcases Nat.lt_or_ge k 2 with hk2 | h2k
    · interval_cases k
      · have : (max 2 1 : ℕ) = 2 := by decide
        rw [this]
        have : ((2 : ℕ) : ℝ) = 2 := by norm_num
        rw [this]
        linarith
    · have hmax : max 2 k = k := max_eq_right h2k
      rw [hmax]
      have he_ge_one : (1 : ℝ) ≤ Real.exp 1 := by linarith
      nlinarith
  have hell_real_le_ek : (ell X U : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : ((ell X U : ℕ) : ℝ) ≤ ((max 2 k : ℕ) : ℝ) := by exact_mod_cast hell_le_max
    exact h1.trans hmax_le_ek
  
  have h_density_bound :
      CKK * κ⁻¹ * Real.log (ell X U) ≤ (1 : ℝ) / (2 * (r : ℝ)) :=
    density_bound_from_kappa_aux CKK (CspOf CKK) hCKK_pos
      (CspOf_ge_two_CKK hCKK_pos)
      hr hk hell_real_pos hell_ge_one hell_real_le_ek hκ_pos hκ
  
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have h_p_nn : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have h_p_le_one : (1 : ℝ) / (2 * (r : ℝ)) ≤ 1 := by
    rw [div_le_one h2r_pos]
    linarith
  
  have hgoal :
      muP X U ((1 : ℝ) / (2 * (r : ℝ))) ≥ 1 / 2 :=
    hThreshold X U (κ⁻¹) ((1 : ℝ) / (2 * (r : ℝ)))
      hκ_inv_pos hκ_inv_le_one h_p_nn h_p_le_one h_density_bound hUXU hIncr hqSmall
  simpa [hU_def] using hgoal

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
namespace ParkPham
open Finset
open scoped BigOperators
section
variable {α : Type*} [DecidableEq α]
abbrev Coloring (X : Finset α) (m : ℕ) :=
  {x // x ∈ X} → Fin m

noncomputable def colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) : Finset α :=
  Finset.image Subtype.val (X.attach.filter (fun x => c x = i))

lemma mem_colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) {x : α} :
    x ∈ colorPart c i ↔ ∃ hx : x ∈ X, c ⟨x, hx⟩ = i := by
  simp [colorPart]

lemma colorPart_subset {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) :
    colorPart c i ⊆ X := by
  intro x hx
  rcases (mem_colorPart c i).1 hx with ⟨hxX, _⟩
  exact hxX

lemma colorPart_disjoint {X : Finset α} {m : ℕ} (c : Coloring X m)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (colorPart c i) (colorPart c j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases (mem_colorPart c i).1 hxi with ⟨hxX, hxi'⟩
  rcases (mem_colorPart c j).1 hxj with ⟨_, hxj'⟩
  exact hij (hxi'.symm.trans hxj')

lemma colorPart_eq_iff {X T : Finset α} (hTX : T ⊆ X) {m : ℕ}
    (c : Coloring X m) (i : Fin m) :
    colorPart c i = T ↔ ∀ x : {x // x ∈ X}, (x.1 ∈ T ↔ c x = i) := by
  constructor
  · intro h x
    constructor
    · intro hxT
      have hxpart : x.1 ∈ colorPart c i := by simpa [h] using hxT
      rcases (mem_colorPart c i).1 hxpart with ⟨hxX, hxci⟩
      have hx_eq : (⟨x.1, hxX⟩ : {x // x ∈ X}) = x := by ext; rfl
      simpa [hx_eq] using hxci
    · intro hci
      have hxpart : x.1 ∈ colorPart c i :=
        (mem_colorPart c i).2 ⟨x.2, hci⟩
      simpa [h] using hxpart
  · intro h
    ext a
    constructor
    · intro ha
      rcases (mem_colorPart c i).1 ha with ⟨haX, hci⟩
      exact (h ⟨a, haX⟩).2 hci
    · intro haT
      have haX : a ∈ X := hTX haT
      exact (mem_colorPart c i).2 ⟨haX, (h ⟨a, haX⟩).1 haT⟩

noncomputable def colorPartFiberEquiv {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    {c : Coloring X m // colorPart c i = T} ≃
      ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) where
  toFun c x := by
    refine ⟨c.1 ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩, ?_⟩
    intro hc
    have hxT : x.1 ∈ T :=
      ((colorPart_eq_iff hTX c.1 i).1 c.2
        ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩).2 hc
    exact (Finset.mem_sdiff.1 x.2).2 hxT
  invFun g := by
    refine ⟨(fun x =>
      if hxT : x.1 ∈ T then i
      else (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1), ?_⟩
    rw [colorPart_eq_iff hTX]
    intro x
    constructor
    · intro hxT
      simp [hxT]
    · intro hxcolor
      by_contra hxT
      have hg_ne : (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1 ≠ i :=
        (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).2
      simp [hxT] at hxcolor
      exact hg_ne hxcolor
  left_inv c := by
    ext x
    by_cases hxT : x.1 ∈ T
    · have hxcolor : c.1 x = i :=
        ((colorPart_eq_iff hTX c.1 i).1 c.2 x).1 hxT
      simp [hxT, hxcolor]
    · simp [hxT]
  right_inv g := by
    funext x
    apply Subtype.ext
    have hxT : x.1 ∉ T := (Finset.mem_sdiff.1 x.2).2
    simp [hxT]

lemma colorPart_fiber_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => colorPart c i = T)).card =
      (m - 1) ^ (X.card - T.card) := by
  classical
  have hleft :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)).card := by
    exact Fintype.card_ofFinset _ (by
      intro c
      change c ∈ ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)) ↔ colorPart c i = T
      simp)
  have hcongr :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        Fintype.card ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) :=
    Fintype.card_congr (colorPartFiberEquiv hTX i)
  have hcod : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun j : Fin m => j = i)
    simp [Fintype.card_fin] at hcompl ⊢
  have hdom : Fintype.card {x // x ∈ X \ T} = X.card - T.card := by
    calc
      Fintype.card {x // x ∈ X \ T} = (X \ T).card := by
          exact Fintype.card_ofFinset _ (by
            intro x
            change x ∈ X \ T ↔ x ∈ X \ T
            rfl)
      _ = X.card - T.card := Finset.card_sdiff_of_subset hTX
  rw [← hleft, hcongr, Fintype.card_fun, hcod, hdom]

lemma coloring_card (X : Finset α) (m : ℕ) :
    Fintype.card (Coloring X m) = m ^ X.card := by
  rw [Fintype.card_fun, Fintype.card_fin]
  congr
  exact Fintype.card_coe X

omit [DecidableEq α] in
lemma bernoulliMass_inv_nat_mul_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) ^ X.card) *
        bernoulliMass X T ((1 : ℝ) / m) =
      ((m - 1 : ℕ) : ℝ) ^ (X.card - T.card) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcard_le : T.card ≤ X.card := Finset.card_le_card hTX
  have hsplit : X.card = T.card + (X.card - T.card) :=
    (Nat.add_sub_of_le hcard_le).symm
  have hone :
      (1 : ℝ) - (1 : ℝ) / m = ((m - 1 : ℕ) : ℝ) / m := by
    have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1]
    field_simp [hmR]
    ring
  unfold bernoulliMass
  rw [hone, hsplit, Nat.add_sub_cancel_left, pow_add]
  rw [div_pow, div_pow]
  field_simp [hmR]
  ring

noncomputable def successfulColors {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∃ S ∈ A, S ⊆ colorPart c i

lemma mem_successfulColors {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ ∃ S ∈ A, S ⊆ colorPart c i := by
  simp [successfulColors]

lemma mem_successfulColors_iff_colorPart_mem_upClosureIn {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ colorPart c i ∈ upClosureIn X A := by
  rw [mem_successfulColors, mem_upClosureIn]
  exact ⟨fun h => ⟨colorPart_subset c i, h⟩, fun h => h.2⟩

lemma successful_colorings_card (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card =
      ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (m - 1) ^ (X.card - T.card) := by
  classical
  let s : Finset (Coloring X m) :=
    (Finset.univ : Finset (Coloring X m)).filter
      (fun c => i ∈ successfulColors A c)
  let t : Finset (Finset α) :=
    X.powerset.filter (fun T => T ∈ upClosureIn X A)
  have hmaps : Set.MapsTo (fun c : Coloring X m => colorPart c i) (↑s) (↑t) := by
    intro c hc
    have hsucc : i ∈ successfulColors A c := by
      simpa [s] using hc
    exact Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 (colorPart_subset c i),
        (mem_successfulColors_iff_colorPart_mem_upClosureIn).1 hsucc⟩
  calc
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card
        = s.card := rfl
    _ = ∑ T ∈ t, {c ∈ s | colorPart c i = T}.card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ T ∈ t, (m - 1) ^ (X.card - T.card) := by
        apply Finset.sum_congr rfl
        intro T hT
        have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
        have hTU : T ∈ upClosureIn X A := (Finset.mem_filter.1 hT).2
        have hfiber :
            {c ∈ s | colorPart c i = T} =
              (Finset.univ : Finset (Coloring X m)).filter
                (fun c => colorPart c i = T) := by
          ext c
          constructor
          · intro hc
            exact Finset.mem_filter.2 ⟨Finset.mem_univ c, (Finset.mem_filter.1 hc).2⟩
          · intro hc
            have hct : colorPart c i = T := (Finset.mem_filter.1 hc).2
            have hsucc : i ∈ successfulColors A c := by
              rw [mem_successfulColors_iff_colorPart_mem_upClosureIn, hct]
              exact hTU
            exact Finset.mem_filter.2
              ⟨by simpa [s] using hsucc, hct⟩
        rw [hfiber, colorPart_fiber_card hTX i]

lemma successful_colorings_card_real (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card : ℝ) =
      (Fintype.card (Coloring X m) : ℝ) *
        muP X (upClosureIn X A) ((1 : ℝ) / m) := by
  classical
  rw [successful_colorings_card X A i, coloring_card]
  unfold muP
  rw [Nat.cast_sum]
  calc
    (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (((m - 1) ^ (X.card - T.card) : ℕ) : ℝ))
        = ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            ((m : ℝ) ^ X.card) *
              bernoulliMass X T ((1 : ℝ) / m) := by
            apply Finset.sum_congr rfl
            intro T hT
            have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
            simpa [Nat.cast_pow] using (bernoulliMass_inv_nat_mul_card hTX hm).symm
    _ = (m : ℝ) ^ X.card *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            rw [Finset.mul_sum]
    _ = ↑(m ^ X.card) *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            norm_num
    _ = ↑(m ^ X.card) * muP X (upClosureIn X A) ((1 : ℝ) / m) := rfl

lemma sum_successfulColors_card (X : Finset α) (A : Finset (Finset α)) (m : ℕ) :
    (∑ c : Coloring X m, (successfulColors A c).card) =
      ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
  calc
    (∑ c : Coloring X m, (successfulColors A c).card)
        = ∑ c : Coloring X m, ∑ i : Fin m,
            if i ∈ successfulColors A c then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Finset.card_filter]
            simp [successfulColors]
    _ = ∑ i : Fin m, ∑ c : Coloring X m,
            if i ∈ successfulColors A c then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.card_filter]

theorem exists_coloring_many_successful_of_mu_ge
    (X : Finset α) (A : Finset (Finset α)) (r : ℕ) (hr : 2 ≤ r)
    (hmu : muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2) :
    ∃ c : Coloring X (2 * r), r ≤ (successfulColors A c).card := by
  classical
  let m := 2 * r
  have hm : 0 < m := by dsimp [m]; omega
  let C : ℕ := Fintype.card (Coloring X m)
  have hCpos_nat : 0 < C := by
    dsimp [C]
    rw [coloring_card]
    exact Nat.pow_pos (a := m) (n := X.card) hm
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos_nat
  have hsum_eq :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) =
        (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
    rw [sum_successfulColors_card X A m]
    rw [Nat.cast_sum]
    calc
      (∑ i : Fin m,
          (((Finset.univ : Finset (Coloring X m)).filter
            (fun c => i ∈ successfulColors A c)).card : ℝ))
          = ∑ _i : Fin m,
              (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [C]
              exact successful_colorings_card_real X A hm i
      _ = (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              simp [Fintype.card_fin, mul_assoc]
  have hsum_lower :
      (r : ℝ) * (C : ℝ) ≤
        ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) := by
    rw [hsum_eq]
    have hm_eq : (m : ℝ) = 2 * (r : ℝ) := by simp [m]
    have hmu' :
        (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) ((1 : ℝ) / m) := by
      simpa [m] using hmu
    have hmul :
        (C : ℝ) * (1 / 2 : ℝ) ≤
          (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hmu' hCpos.le
    calc
      (r : ℝ) * (C : ℝ) =
          (m : ℝ) * ((C : ℝ) * (1 / 2 : ℝ)) := by
            rw [hm_eq]
            ring
      _ ≤ (m : ℝ) *
          ((C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m)) := by
            exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (m : ℝ) * (C : ℝ) *
          muP X (upClosureIn X A) ((1 : ℝ) / m) := by
            ring
  by_contra hnone
  have hle_each : ∀ c : Coloring X m, (successfulColors A c).card ≤ r - 1 := by
    intro c
    have hnot : ¬ r ≤ (successfulColors A c).card := by
      intro hc
      exact hnone ⟨c, hc⟩
    omega
  have hsum_le_nat :
      (∑ c : Coloring X m, (successfulColors A c).card : ℕ) ≤
        ∑ _c : Coloring X m, (r - 1) := by
    exact Finset.sum_le_sum (fun c _ => hle_each c)
  have hsum_le :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) ≤
        (C : ℝ) * (r - 1 : ℕ) := by
    calc
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ)
          ≤ ((∑ _c : Coloring X m, (r - 1) : ℕ) : ℝ) := by
            exact_mod_cast hsum_le_nat
      _ = (C : ℝ) * (r - 1 : ℕ) := by
            simp [C]
  have hlt : (C : ℝ) * (r - 1 : ℕ) < (r : ℝ) * (C : ℝ) := by
    have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [hsub]
    nlinarith
  nlinarith

noncomputable def successfulMember {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) (i : Fin m) : Finset α :=
  if h : i ∈ successfulColors A c then
    Classical.choose ((mem_successfulColors).1 h)
  else
    ∅

lemma successfulMember_mem {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ∈ A := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).1

lemma successfulMember_subset_colorPart {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ⊆ colorPart c i := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).2

lemma member_nonempty_of_uniform
    {A : Finset (Finset α)} {S : Finset α} {k : ℕ}
    (hk : 1 ≤ k) (hUniform : BFVRegular1190.UniformFamily A k) (hS : S ∈ A) :
    S.Nonempty := by
  have hcard : S.card = k := hUniform S hS
  exact Finset.card_pos.1 (by omega)

theorem disjoint_members_of_many_successful_colors {X : Finset α} {m r k : ℕ}
    {A : Finset (Finset α)} (c : Coloring X m)
    (hk : 1 ≤ k) (hUniform : BFVRegular1190.UniformFamily A k)
    (hSuccess : r ≤ (successfulColors A c).card) :
    ∃ B : Finset (Finset α),
      B ⊆ A ∧ B.card = r ∧ BFVRegular1190.PairwiseDisjointMembers B := by
  classical
  rcases Finset.exists_subset_card_eq hSuccess with ⟨I, hI_success, hI_card⟩
  let pick : Fin m → Finset α := successfulMember A c
  let B : Finset (Finset α) := I.image pick
  have hpick_mem : ∀ i ∈ I, pick i ∈ A := by
    intro i hi
    exact successfulMember_mem (hI_success hi)
  have hpick_subset : ∀ i ∈ I, pick i ⊆ colorPart c i := by
    intro i hi
    exact successfulMember_subset_colorPart (hI_success hi)
  have hpick_inj : Set.InjOn pick I := by
    intro i hi j hj hpick_eq
    by_contra hij
    have hnonempty : (pick i).Nonempty :=
      member_nonempty_of_uniform hk hUniform (hpick_mem i hi)
    rcases hnonempty with ⟨x, hx⟩
    have hxi : x ∈ colorPart c i := hpick_subset i hi hx
    have hxj : x ∈ colorPart c j := by
      have hx' : x ∈ pick j := by simpa [hpick_eq] using hx
      exact hpick_subset j hj hx'
    exact (Finset.disjoint_left.1 (colorPart_disjoint c hij) hxi) hxj
  refine ⟨B, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    exact hpick_mem i hi
  · calc
      B.card = I.card := Finset.card_image_of_injOn hpick_inj
      _ = r := hI_card
  · intro S hS T hT hST
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.1 hT with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hST (by simp [hij])
    exact (Disjoint.mono (hpick_subset i hi) (hpick_subset j hj)
      (colorPart_disjoint c hij))

end
theorem partition_density_to_disjoint_members :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      BFVRegular1190.UniformFamily A k →
      (∀ S ∈ A, S ⊆ X) →
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ BFVRegular1190.PairwiseDisjointMembers B := by
  intro α _ X A r k _hA hr hk hUniform _hAX hmu
  rcases exists_coloring_many_successful_of_mu_ge X A r hr hmu with ⟨c, hc⟩
  exact disjoint_members_of_many_successful_colors c hk hUniform hc

section
variable {α : Type*} [DecidableEq α]
theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        BFVRegular1190.UniformFamily A k →
        BFVRegular1190.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ BFVRegular1190.PairwiseDisjointMembers B := by
  rcases park_pham_threshold_exists with ⟨CKK, hCKK_pos, hThreshold⟩
  refine ⟨CspOf CKK, CspOf_pos CKK, ?_⟩
  intro α _ A r k κ hA hr hk hUniform hSpread hκ
  
  let X : Finset α := A.biUnion id
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hSA x hxS
    exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
  have hThresholdα :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
    intro X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
    exact hThreshold X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  
  have hmu :
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
    mu_at_partition_density_ge_half_of_threshold
      CKK hCKK_pos hThresholdα hA hr hk hUniform hSpread hAX hκ
  
  exact partition_density_to_disjoint_members X A r k hA hr hk hUniform hAX hmu

end
end ParkPham
end BFVRegular1190
namespace BFVRegular1190
open Finset
open scoped BigOperators
universe u
theorem spread_disjointness_input :
  ∃ Csp : ℝ, 0 < Csp ∧
    ∀ {α : Type*} [DecidableEq α]
      (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      UniformFamily A k →
      SpreadFamily A κ →
      Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B :=
  BFVRegular1190.ParkPham.spread_disjointness_theorem

theorem dense_core_from_spread :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ {α : Type u} [DecidableEq α]
        (A : Finset (Finset α)) (k K : ℕ),
        A.Nonempty →
        1 ≤ k → k ≤ K →
        UniformFamily A k →
        (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
        ∃ C : Finset α,
          C.Nonempty ∧
          ((A.filter fun S => C ⊆ S).card : ℝ) >
            (A.card : ℝ) /
              (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := by
  classical
  let Csp : ℝ := Classical.choose (spread_disjointness_input.{u})
  have hspec := Classical.choose_spec (spread_disjointness_input.{u})
  have hCsp_pos : 0 < Csp := hspec.1
  refine ⟨Csp * 2, by positivity, ?_⟩
  intro α _ A k K hA hk_pos hkK hUniform hIntersect
  let κ : ℝ := (Csp * 2) * Real.log (Real.exp 1 * (K : ℝ))
  by_contra hNoCore
  have hSpread : SpreadFamily A κ := by
    intro T hT
    exact le_of_not_gt (by
      intro hgt
      exact hNoCore ⟨T, hT, hgt⟩)
  have hκ : Csp * (2 : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ := by
    have harg_pos : 0 < Real.exp 1 * (k : ℝ) := by positivity
    have harg_le : Real.exp 1 * (k : ℝ) ≤ Real.exp 1 * (K : ℝ) := by
      gcongr
    have hlog_le : Real.log (Real.exp 1 * (k : ℝ)) ≤
        Real.log (Real.exp 1 * (K : ℝ)) :=
      Real.log_le_log harg_pos harg_le
    have hcoef_nonneg : 0 ≤ Csp * 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
  rcases hspec.2 (A := A) (r := 2) (k := k) (κ := κ)
      hA (by norm_num) hk_pos hUniform hSpread hκ with
    ⟨B, hBA, hBcard, hBdisj⟩
  have hBgt : 1 < B.card := by omega
  rcases Finset.one_lt_card.mp hBgt with ⟨S, hS, T, hT, hST⟩
  exact hIntersect S (hBA hS) T (hBA hT) hST (hBdisj S hS T hT hST)

end BFVRegular1190
namespace BFVRegular1190
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

end BFVRegular1190
namespace BFVRegular1190
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

end BFVRegular1190
namespace BFVRegular1190
open Filter Finset
open scoped BigOperators
lemma omega_exact_filter_subset_tail (y t : ℕ) :
    (Finset.Icc 1 y).filter (fun n => omega n = t)
      ⊆ (Finset.Icc 1 y).filter (fun n => t ≤ omega n) := by
  intro n hn
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.ge⟩

lemma omega_exact_card_le_tail_card (y t : ℕ) :
    ((Finset.Icc 1 y).filter (fun n => omega n = t)).card
      ≤ ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card :=
  Finset.card_le_card (omega_exact_filter_subset_tail y t)

private lemma exact_target_eq_tail_target {N y K W : ℕ} (ε : ℝ)
    (hN : Real.exp 1 < (N : ℝ)) (hWK : W ≤ K) :
    (y : ℝ) *
        Real.exp ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
      =
    (y : ℝ) *
        Real.exp ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hN
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hN
  have hcast : (((K - W : ℕ) : ℝ)) = (K : ℝ) - (W : ℝ) := by
    exact_mod_cast (Nat.cast_sub hWK : ((K - W : ℕ) : ℝ) = (K : ℝ) - (W : ℝ))
  have hexp :
      ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        =
      ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) +
        (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    rw [hcast, ← hZdivM]
    field_simp [hMpos.ne']
    ring
  rw [hexp, Real.exp_add]
  ring

theorem bfv_omega_exact_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  intro ε hε
  filter_upwards [bfv_omega_tail_theorem ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hTail hNlarge_nat
  intro y K W hy hWK hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hExactTail := omega_exact_card_le_tail_card y (K - W)
  have ht_le_K_real : ((K - W : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K W
  have ht_bound : ((K - W : ℕ) : ℝ) ≤ 3 * Mscale N := ht_le_K_real.trans hK
  have hTailApplied := hTail y (K - W) hy ht_bound
  have htarget :=
    exact_target_eq_tail_target (N := N) (y := y) (K := K) (W := W) ε hNlarge hWK
  dsimp only at hTailApplied ⊢
  exact hExactTail.trans (by simpa [htarget] using hTailApplied)

end BFVRegular1190
namespace BFVRegular1190
open Filter Finset
open scoped BigOperators
theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_exact_theorem

end BFVRegular1190
namespace BFVRegular1190
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

lemma PrunedData.N_pos {N : ℕ} (D : PrunedData N) : 0 < N := by
  rcases D.Q_nonempty with ⟨q, hq⟩
  exact lt_of_lt_of_le (D.admissible.1 q hq).1 (D.modulus_upper q hq)

lemma PrunedData.Q_subset_Icc {N : ℕ} (D : PrunedData N) :
    D.Q ⊆ Finset.Icc 1 N := by
  intro q hq
  exact Finset.mem_Icc.2 (D.admissible.1 q hq)

lemma PrunedData.card_le_N {N : ℕ} (D : PrunedData N) :
    D.Q.card ≤ N := by
  have hcard := Finset.card_le_card D.Q_subset_Icc
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

theorem bfv_omega_count_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y K W : ℕ,
      y ≤ N →
      W ≤ K →
      (K : ℝ) ≤ 3 * Mscale N →
      let d : ℝ := (K : ℝ) / Mscale N
      ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
        ≤ Nat.floor
            ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
              * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_count_theorem

end BFVRegular1190
namespace BFVRegular1190
open Filter Finset
open scoped BigOperators
lemma nat_cast_le_of_le_floor {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : m ≤ Nat.floor x) : (m : ℝ) ≤ x := by
  exact (Nat.le_floor_iff hx).1 h

lemma weighted_pigeonhole {α : Type*} [DecidableEq α] (I : Finset α)
    (N w : α → ℝ) (hI : I.Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) :
    ∃ i ∈ I, (∑ j ∈ I, N j) * w i / (∑ j ∈ I, w j) ≤ N i := by
  classical
  let totalN := ∑ j ∈ I, N j
  let totalW := ∑ j ∈ I, w j
  have htotalW_pos : 0 < totalW := Finset.sum_pos hw hI
  by_contra h
  push_neg at h
  have hlt : ∀ i ∈ I, N i < totalN * w i / totalW := by
    intro i hi
    simpa [totalN, totalW] using h i hi
  have hsum_lt : ∑ i ∈ I, N i < ∑ i ∈ I, totalN * w i / totalW := by
    exact Finset.sum_lt_sum_of_nonempty hI hlt
  have hsum_rhs : (∑ i ∈ I, totalN * w i / totalW) = totalN := by
    calc
      (∑ i ∈ I, totalN * w i / totalW) =
          ∑ i ∈ I, (totalN / totalW) * w i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (totalN / totalW) * totalW := by rw [Finset.mul_sum]
      _ = totalN := div_mul_cancel₀ totalN htotalW_pos.ne'
  have : totalN < totalN := by
    change (∑ i ∈ I, N i) < totalN
    rw [← hsum_rhs]
    exact hsum_lt
  exact lt_irrefl _ this

lemma exists_fiber_weighted_share {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (B : α → β) (w : β → ℝ) (hS : S.Nonempty)
    (hw : ∀ b ∈ S.image B, 0 < w b) :
    ∃ b ∈ S.image B,
      (S.card : ℝ) * w b / (∑ c ∈ S.image B, w c) ≤
        ((S.filter fun a => B a = b).card : ℝ) := by
  classical
  have hImage : (S.image B).Nonempty := hS.image B
  rcases weighted_pigeonhole (S.image B)
      (fun b => ((S.filter fun a => B a = b).card : ℝ)) w hImage hw with
    ⟨b, hb, hbshare⟩
  refine ⟨b, hb, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ S.image B, (S.filter fun a => B a = b).card) = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      exact h.1
    · intro ha
      exact ⟨ha, a, ha, rfl⟩
  have hsum_counts_real :
      (∑ b ∈ S.image B, ((S.filter fun a => B a = b).card : ℝ)) =
        (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  simpa [hsum_counts_real] using hbshare

lemma fiber_nonempty_of_mem_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {B : α → β} {b : β} (hb : b ∈ S.image B) :
    (S.filter fun a => B a = b).Nonempty := by
  rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
  exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩

lemma exists_fiber_card_div_le {α β : Type*} [DecidableEq α] [Fintype β]
    [DecidableEq β] (S : Finset α) (r : α → β) (hS : S.Nonempty) :
    ∃ b : β,
      (S.card : ℝ) / (Fintype.card β : ℝ) ≤
        ((S.filter fun a => r a = b).card : ℝ) := by
  classical
  haveI : Nonempty β := by
    rcases hS with ⟨a, _ha⟩
    exact ⟨r a⟩
  have hUniv : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  rcases weighted_pigeonhole (Finset.univ : Finset β)
      (fun b => ((S.filter fun a => r a = b).card : ℝ)) (fun _ => (1 : ℝ))
      hUniv (by intro _b _hb; norm_num) with ⟨b, _hb, hbshare⟩
  refine ⟨b, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ (Finset.univ : Finset β), (S.filter fun a => r a = b).card) =
        S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hsum_counts_real :
      (∑ b ∈ (Finset.univ : Finset β),
          ((S.filter fun a => r a = b).card : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  have hsum_weights :
      (∑ _b ∈ (Finset.univ : Finset β), (1 : ℝ)) =
        (Fintype.card β : ℝ) := by
    simp
  simpa [hsum_counts_real, hsum_weights] using hbshare

lemma exists_zmod_fiber_card_div_le (T : Finset ℕ) (P : ℕ) [NeZero P]
    (r : ℕ → ZMod P) (hT : T.Nonempty) :
    ∃ b : ZMod P,
      (T.card : ℝ) / (P : ℝ) ≤ ((T.filter fun q => r q = b).card : ℝ) := by
  rcases exists_fiber_card_div_le T r hT with ⟨b, hb⟩
  exact ⟨b, by simpa [ZMod.card] using hb⟩

lemma List.mem_dvd_foldr_mul {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ∣ l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      cases ha with
      | inl h =>
          subst b
          simp
      | inr h =>
          exact dvd_mul_of_dvd_right (ih h) b

private lemma List.foldr_mul_pos {l : List ℕ}
    (hpos : ∀ a ∈ l, 0 < a) : 0 < l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons]
      exact Nat.mul_pos (hpos a (by simp)) (ih (by
        intro b hb
        exact hpos b (by simp [hb])))

private lemma List.coprime_foldr_mul_of_forall
    {P : ℕ} {Ps : List ℕ} (hcop_all : ∀ Q ∈ Ps, Nat.Coprime P Q) :
    Nat.Coprime P (Ps.foldr (· * ·) 1) := by
  induction Ps with
  | nil =>
      simp
  | cons Q Qs ih =>
      simp only [List.foldr_cons]
      exact Nat.Coprime.mul_right (hcop_all Q (by simp)) (ih (by
        intro R hR
        exact hcop_all R (by simp [hR])))

private lemma sum_inv_sq_range_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

structure ChainState (N : ℕ) (D : PrunedData N) where
  
  r : ℕ
  
  blocks : List ℕ
  blocks_length : blocks.length = r
  
  Qsurv : Finset ℕ
  Qsurv_subset : Qsurv ⊆ D.Q
  Qsurv_nonempty : Qsurv.Nonempty
  
  W : ℕ
  
  productP : ℕ
  product_eq : productP = (blocks.foldr (· * ·) 1)
  blocks_pos : ∀ P ∈ blocks, 0 < P
  productP_pos : 0 < productP
  

  pairwise_coprime : blocks.Pairwise Nat.Coprime
  

  exact_divides : ∀ q ∈ Qsurv, productP ∣ q
  no_selected_prime_remains :
    ∀ q ∈ Qsurv, ∀ p ∈ primeSupport productP,
      p ∉ primeSupport (q / productP)
  
  residues_agree :
    ∀ qi ∈ Qsurv, ∀ rj ∈ Qsurv,
      ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
        D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (productP : ℤ)]
  W_eq : W = omega productP
  W_le_K : W ≤ D.K

def ChainState.BlocksOmegaPos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Prop :=
  ∀ P ∈ S.blocks, 1 ≤ omega P

lemma ChainState.productP_le_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP ≤ q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  exact Nat.le_of_dvd hqpos (S.exact_divides q hq)

lemma ChainState.productP_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    (hExp S.productP : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hle_nat : hExp S.productP ≤ hExp q :=
    hExp_le_of_dvd (S.exact_divides q hq) hqne
  have hle_real : (hExp S.productP : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.block_dvd_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {B : ℕ} (hB : B ∈ S.blocks) : B ∣ S.productP := by
  rw [S.product_eq]
  exact List.mem_dvd_foldr_mul hB

lemma ChainState.selected_remaining_disjoint {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    Disjoint (primeSupport S.productP) (remainingSupport S.productP q) := by
  rw [Finset.disjoint_left]
  intro p hpP hpRem
  exact S.no_selected_prime_remains q hq p hpP hpRem

lemma ChainState.remainingSupport_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).card = D.K - S.W := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have homega :
      omega (q / S.productP) = omega q - omega S.productP :=
    omega_div_eq_sub_omega_of_dvd (S.exact_divides q hq)
      S.productP_pos.ne' hqpos (S.selected_remaining_disjoint hq)
  calc
    (remainingSupport S.productP q).card = omega (q / S.productP) := by
      simp [remainingSupport, omega]
    _ = omega q - omega S.productP := homega
    _ = D.K - S.W := by
      rw [D.omega_eq q hqD, ← S.W_eq]

lemma ChainState.gcd_dvd_productP_of_disjoint_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hdisj : Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r)) :
    Nat.gcd q r ∣ S.productP := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrpos : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  exact gcd_dvd_of_disjoint_remainingSupport
    (S.exact_divides q hq) (S.exact_divides r hr)
    S.productP_pos.ne' hqpos hrpos hdisj

lemma ChainState.remainingSupport_not_disjoint_of_ne {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hqr : q ≠ r) :
    ¬ Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r) := by
  intro hdisj
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1
  have hgcd_dvd : Nat.gcd q r ∣ S.productP :=
    S.gcd_dvd_productP_of_disjoint_remaining hq hr hdisj
  have hmodP := S.residues_agree q hq r hr hqD hrD
  have hmodG :
      D.a ⟨q, hqD⟩ ≡ D.a ⟨r, hrD⟩ [ZMOD (Nat.gcd q r : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hmodP ⊢
    have hgcd_dvd_int : (Nat.gcd q r : ℤ) ∣ (S.productP : ℤ) := by
      exact_mod_cast hgcd_dvd
    exact dvd_trans hgcd_dvd_int hmodP
  have hres_disj :
      Disjoint (residueClass q (D.a ⟨q, hqD⟩))
        (residueClass r (D.a ⟨r, hrD⟩)) :=
    D.pairwise_disjoint ⟨q, hqD⟩ ⟨r, hrD⟩ (by
      intro hsub
      exact hqr (Subtype.ext_iff.mp hsub))
  exact ((residueClass_disjoint_iff hqpos hrpos
    (D.a ⟨q, hqD⟩) (D.a ⟨r, hrD⟩)).1 hres_disj) hmodG

def ChainState.remainingSupportFamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Finset (Finset ℕ) :=
  S.Qsurv.image (fun q => remainingSupport S.productP q)

lemma ChainState.remainingSupportFamily_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : S.remainingSupportFamily.Nonempty := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  exact ⟨remainingSupport S.productP q, Finset.mem_image.2 ⟨q, hq, rfl⟩⟩

lemma ChainState.remainingSupport_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => remainingSupport S.productP q) S.Qsurv := by
  intro q hq r hr hqr
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrne : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  have hqsupp :
      primeSupport q = primeSupport S.productP ∪ remainingSupport S.productP q :=
    primeSupport_eq_union_of_dvd (S.exact_divides q hq) S.productP_pos.ne' hqne
  have hrsupp :
    primeSupport r = primeSupport S.productP ∪ remainingSupport S.productP r :=
    primeSupport_eq_union_of_dvd (S.exact_divides r hr) S.productP_pos.ne' hrne
  have hsupp : primeSupport q = primeSupport r := by
    change remainingSupport S.productP q = remainingSupport S.productP r at hqr
    rw [hqsupp, hrsupp, hqr]
  have hrad : rad q = rad r := by
    unfold rad
    rw [hsupp]
  exact D.rad_injective q hqD r hrD hrad

lemma ChainState.remainingSupportFamily_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card = S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_of_injOn (fun q hq r hr hqr =>
    S.remainingSupport_injOn_Qsurv hq hr hqr)

def ChainState.coreSurvivors {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  S.Qsurv.filter fun q => C ⊆ remainingSupport S.productP q

def ChainState.coreBlocks {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => exactBlock C q)

lemma ChainState.exists_coreBlock_weighted_share {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ)
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P ∈ S.coreBlocks C,
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  classical
  rw [ChainState.coreBlocks]
  exact exists_fiber_weighted_share (S.coreSurvivors C) (fun q => exactBlock C q)
    (fun P => (1 : ℝ) / ((hExp P : ℝ) ^ 2)) hCore (by
      intro P _hP
      exact hExp_inv_sq_pos P)

def ChainState.coreQuotients {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => q / S.productP)

lemma ChainState.remainingSupportFamily_filter_subset_coreImage {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A) ⊆
      (S.coreSurvivors C).image (fun q => remainingSupport S.productP q) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rw [Finset.mem_filter] at hA
  rcases Finset.mem_image.mp hA.1 with ⟨q, hq, rfl⟩
  exact Finset.mem_image.2 ⟨q, by
    rw [ChainState.coreSurvivors, Finset.mem_filter]
    exact ⟨hq, hA.2⟩, rfl⟩

lemma ChainState.remainingSupportFamily_filter_card_le_coreSurvivors {N : ℕ}
    {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A).card ≤
      (S.coreSurvivors C).card := by
  exact (Finset.card_le_card (S.remainingSupportFamily_filter_subset_coreImage C)).trans
    Finset.card_image_le

lemma ChainState.quotient_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => q / S.productP) S.Qsurv := by
  intro q hq r hr hqr
  have hqmul := Nat.div_mul_cancel (S.exact_divides q hq)
  have hrmul := Nat.div_mul_cancel (S.exact_divides r hr)
  calc
    q = (q / S.productP) * S.productP := hqmul.symm
    _ = (r / S.productP) * S.productP := by
      exact congrArg (fun x => x * S.productP) hqr
    _ = r := hrmul

lemma ChainState.coreQuotients_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreQuotients C).card = (S.coreSurvivors C).card := by
  rw [ChainState.coreQuotients]
  exact Finset.card_image_of_injOn fun q hq r hr hqr =>
    S.quotient_injOn_Qsurv (Finset.mem_filter.1 hq).1
      (Finset.mem_filter.1 hr).1 hqr

lemma ChainState.coreQuotients_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreQuotients C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W) := by
  intro n hn
  rw [ChainState.coreQuotients] at hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := (Finset.mem_filter.1 hq).1
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (S.productP_le_of_mem hqsurv) S.productP_pos),
      (Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD)⟩,
    S.remainingSupport_card_eq hqsurv⟩

lemma ChainState.coreSurvivors_card_le_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreSurvivors C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W)).card := by
  rw [← S.coreQuotients_card C]
  exact Finset.card_le_card (S.coreQuotients_subset_omegaCount C)

lemma ChainState.coreSurvivors_card_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreSurvivors C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  exact (S.coreSurvivors_card_le_omegaCount C).trans
    (hCount N D.K S.W le_rfl S.W_le_K D.K_bound)

lemma ChainState.coreSurvivors_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreSurvivors C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreSurvivors_card_le_bfv_omega_count C ε hCount

lemma ChainState.coreSurvivors_subset {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreSurvivors C ⊆ S.Qsurv := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1

lemma ChainState.core_subset_remainingSupport {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    C ⊆ remainingSupport S.productP q :=
  (Finset.mem_filter.1 hq).2

lemma ChainState.exactBlock_eq_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q = exactBlock C (q / S.productP) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  apply exactBlock_congr_on
  intro p hpC
  have hpRem : p ∈ remainingSupport S.productP q := hC hpC
  have hpNotP : p ∉ primeSupport S.productP := by
    intro hpP
    exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP hpRem
  have hPzero : S.productP.factorization p = 0 := by
      unfold primeSupport at hpNotP
      exact Finsupp.notMem_support_iff.1 hpNotP
  rw [Nat.factorization_div (S.exact_divides q hqsurv)]
  simp [Finsupp.coe_tsub, hPzero]

lemma ChainState.quotient_pos_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < q / S.productP := by
  exact Nat.div_pos (S.productP_le_of_mem hq) S.productP_pos

lemma ChainState.exactBlock_dvd_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q ∣ q / S.productP := by
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact exactBlock_dvd C (q / S.productP)

lemma ChainState.exactBlock_pos_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    0 < exactBlock C q := by
  exact Nat.pos_of_dvd_of_pos (S.exactBlock_dvd_quotient_of_core hq)
    (S.quotient_pos_of_mem (S.coreSurvivors_subset C hq))

lemma ChainState.primeSupport_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    primeSupport (exactBlock C q) = C := by
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact primeSupport_exactBlock
    (fun p hp => prime_of_mem_primeSupport (hC hp))
    hC

lemma ChainState.omega_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    omega (exactBlock C q) = C.card := by
  simp [omega, S.primeSupport_exactBlock_of_core hq]

lemma ChainState.product_mul_exactBlock_dvd_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    S.productP * exactBlock C q ∣ q := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  rcases S.exactBlock_dvd_quotient_of_core hq with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hqsurv)
  calc
    q = q / S.productP * S.productP := hdiv.symm
    _ = exactBlock C q * t * S.productP := by rw [ht]
    _ = S.productP * exactBlock C q * t := by ring

lemma ChainState.productP_coprime_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    Nat.Coprime S.productP (exactBlock C q) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  have hsupport : primeSupport (exactBlock C q) = C :=
    S.primeSupport_exactBlock_of_core hq
  refine coprime_of_disjoint_primeSupport S.productP_pos.ne'
    (S.exactBlock_pos_of_core hq).ne' ?_
  rw [hsupport]
  rw [Finset.disjoint_left]
  intro p hpP hpC
  exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP (hC hpC)

lemma ChainState.coreBlock_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : 0 < P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.exactBlock_pos_of_core hq

lemma ChainState.coreBlock_coprime_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : Nat.Coprime S.productP P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.productP_coprime_exactBlock_of_core hq

lemma ChainState.coreBlock_omega_eq_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : omega P = C.card := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.omega_exactBlock_of_core hq

lemma ChainState.coreBlock_primeSupport_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : primeSupport P = C := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.primeSupport_exactBlock_of_core hq

lemma ChainState.product_mul_coreBlock_dvd {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    S.productP * P ∣ q := by
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  simpa [hP] using S.product_mul_exactBlock_dvd_of_core hqcore

lemma ChainState.product_mul_coreBlock_no_selected_prime_remains
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    ∀ p ∈ primeSupport (S.productP * P), p ∉ primeSupport (q / (S.productP * P)) := by
  intro p hpNew hpRem
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hPmem : P ∈ S.coreBlocks C := by
    rw [ChainState.coreBlocks]
    exact Finset.mem_image.2 ⟨q, hqcore, hP⟩
  have hcop : Nat.Coprime S.productP P := S.coreBlock_coprime_productP hPmem
  have hnewdvd : S.productP * P ∣ q := S.product_mul_coreBlock_dvd hq
  have hltNew : (S.productP * P).factorization p < q.factorization p :=
    (mem_remainingSupport_iff_factorization_lt hnewdvd).1 hpRem
  have hsupportNew :
      primeSupport (S.productP * P) = primeSupport S.productP ∪ primeSupport P :=
    primeSupport_mul_of_coprime hcop
  have hfacNew : (S.productP * P).factorization p =
      S.productP.factorization p + P.factorization p := by
    rw [Nat.factorization_mul_of_coprime hcop]
    rfl
  rw [hsupportNew, Finset.mem_union] at hpNew
  cases hpNew with
  | inl hpOld =>
      have hpNotRemOld : p ∉ primeSupport (q / S.productP) :=
        S.no_selected_prime_remains q hqsurv p hpOld
      have hnotltOld : ¬ S.productP.factorization p < q.factorization p := by
        intro hlt
        exact hpNotRemOld
          ((mem_remainingSupport_iff_factorization_lt (S.exact_divides q hqsurv)).2 hlt)
      have hleOld : S.productP.factorization p ≤ q.factorization p :=
        (Nat.factorization_le_iff_dvd S.productP_pos.ne' hqne).2
          (S.exact_divides q hqsurv) p
      have hq_le_old : q.factorization p ≤ S.productP.factorization p :=
        le_of_not_gt hnotltOld
      have hEqOld : S.productP.factorization p = q.factorization p :=
        le_antisymm hleOld hq_le_old
      have hpNotP : p ∉ primeSupport P :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld
      have hPzero : P.factorization p = 0 := by
        unfold primeSupport at hpNotP
        exact Finsupp.notMem_support_iff.1 hpNotP
      rw [hfacNew, hPzero, add_zero, hEqOld] at hltNew
      exact lt_irrefl _ hltNew
  | inr hpP =>
      have hsupportP : primeSupport P = C := by
        rw [← hP]
        exact S.primeSupport_exactBlock_of_core hqcore
      have hpC : p ∈ C := by
        simpa [hsupportP] using hpP
      have hpNotOld : p ∉ primeSupport S.productP := by
        intro hpOld
        exact (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld hpP
      have hOldzero : S.productP.factorization p = 0 := by
        unfold primeSupport at hpNotOld
        exact Finsupp.notMem_support_iff.1 hpNotOld
      have hCprime : ∀ r ∈ C, Nat.Prime r := by
        intro r hr
        exact prime_of_mem_primeSupport (S.core_subset_remainingSupport hqcore hr)
      have hPfac : P.factorization p = q.factorization p := by
        rw [← hP]
        exact factorization_exactBlock_of_mem hCprime hpC
      rw [hfacNew, hOldzero, zero_add, hPfac] at hltNew
      exact lt_irrefl _ hltNew

lemma ChainState.coreBlock_card_le_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : C.card ≤ D.K - S.W := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact (Finset.card_le_card (S.core_subset_remainingSupport hq)).trans_eq
    (S.remainingSupport_card_eq (S.coreSurvivors_subset C hq))

lemma ChainState.omega_product_mul_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    omega (S.productP * P) = S.W + C.card := by
  rw [omega_mul_of_coprime (S.coreBlock_coprime_productP hP), ← S.W_eq,
    S.coreBlock_omega_eq_card hP]

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count_div
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N / (S.productP * P) : ℕ) : ℝ) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let dP : ℕ := S.productP * P
  let quotient : ℕ → ℕ := fun q => q / dP
  have hdP_pos : 0 < dP := by
    dsimp [dP]
    exact Nat.mul_pos S.productP_pos (S.coreBlock_pos hP)
  have hWle : S.W + C.card ≤ D.K := by
    have hcard := S.coreBlock_card_le_remaining hP
    have hWK := S.W_le_K
    omega
  have hinj : Set.InjOn quotient T := by
    intro q hq r hr hqr
    have hq_dvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hq)
    have hr_dvd : dP ∣ r := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hr)
    calc
      q = quotient q * dP := (Nat.div_mul_cancel hq_dvd).symm
      _ = quotient r * dP := by rw [hqr]
      _ = r := Nat.div_mul_cancel hr_dvd
  have hsubset :
      T.image quotient ⊆
        (Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card)) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨q, hqT, rfl⟩
    have hqT' : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P := by
      simpa [T] using hqT
    have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hqT').1
    have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
    have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
    have hqne : q ≠ 0 := hqpos.ne'
    have hdvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd hqT'
    have hdisj : Disjoint (primeSupport dP) (primeSupport (q / dP)) := by
      rw [Finset.disjoint_left]
      intro p hp hqrem
      exact S.product_mul_coreBlock_no_selected_prime_remains hqT' p (by simpa [dP] using hp)
        (by simpa [dP] using hqrem)
    have homega :
        omega (q / dP) = D.K - (S.W + C.card) := by
      calc
        omega (q / dP) = omega q - omega dP :=
          omega_div_eq_sub_omega_of_dvd hdvd hdP_pos.ne' hqne hdisj
        _ = D.K - (S.W + C.card) := by
          rw [D.omega_eq q hqD, show omega dP = S.W + C.card by
            dsimp [dP]
            exact S.omega_product_mul_coreBlock hP]
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdP_pos),
      Nat.div_le_div_right (D.modulus_upper q hqD)⟩, homega⟩
  have hcard : T.card ≤
      ((Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card))).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsubset
  have hcount := hCount (N / dP) D.K (S.W + C.card) (Nat.div_le_self N dP) hWle D.K_bound
  dsimp only at hcount
  have hfloor :
      T.card ≤ Nat.floor
        (((N / dP : ℕ) : ℝ) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))) :=
    hcard.trans hcount
  simpa [T, dP] using nat_cast_le_of_le_floor (by positivity) hfloor

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N : ℝ) / (S.productP * P : ℝ)) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hdiv := S.selectedFiber_card_real_le_bfv_omega_count_div hP ε hCount
  have hquot :
      ((N / (S.productP * P) : ℕ) : ℝ) ≤ (N : ℝ) / (S.productP * P : ℝ) :=
    by
      simpa [Nat.cast_mul] using
        (Nat.cast_div_le (m := N) (n := S.productP * P) : ((N / (S.productP * P) : ℕ) : ℝ) ≤
          (N : ℝ) / ((S.productP * P : ℕ) : ℝ))
  have hfactor_nonneg :
      0 ≤ Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    positivity
  calc
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ)
        ≤ ((N / (S.productP * P) : ℕ) : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := hdiv
    _ = ((N / (S.productP * P) : ℕ) : ℝ) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by ring
    _ ≤ ((N : ℝ) / (S.productP * P : ℝ)) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hquot hfactor_nonneg
    _ = ((N : ℝ) / (S.productP * P : ℝ)) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := by ring

lemma ChainState.W_add_coreBlock_card_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : S.W + C.card ≤ D.K := by
  have hcard := S.coreBlock_card_le_remaining hP
  have hW := S.W_le_K
  omega

lemma ChainState.productP_eq_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP = q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqdivpos : q / S.productP ≠ 0 := (S.quotient_pos_of_mem hq).ne'
  have hremcard : (remainingSupport S.productP q).card = 0 := by
    rw [S.remainingSupport_card_eq hq, hW]
    simp
  have homega : omega (q / S.productP) = 0 := by
    simpa [remainingSupport, omega] using hremcard
  have hquot : q / S.productP = 1 := eq_one_of_omega_eq_zero hqdivpos homega
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hq)
  calc
    S.productP = 1 * S.productP := by simp
    _ = q / S.productP * S.productP := by rw [hquot]
    _ = q := hdiv

lemma ChainState.productP_lower_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hpq := S.productP_eq_of_W_eq_K hW hq
  rw [hpq]
  exact D.modulus_lower q hqD

lemma ChainState.pairwise_cons_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (P :: S.blocks).Pairwise Nat.Coprime := by
  rw [List.pairwise_cons]
  constructor
  · intro B hB
    exact Nat.Coprime.of_dvd_right (S.block_dvd_productP hB)
      (S.coreBlock_coprime_productP hP).symm
  · exact S.pairwise_coprime

lemma ChainState.extend_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ} {Qnext : Finset ℕ}
    (hP : P ∈ S.coreBlocks C)
    (hQnext_nonempty : Qnext.Nonempty)
    (hQnext_subset : Qnext ⊆ (S.coreSurvivors C).filter fun q => exactBlock C q = P)
    (hResiduesP :
      ∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧ S'.r = S.r + 1 ∧ S'.productP = P * S.productP ∧
        S'.Qsurv = Qnext ∧ S'.W = S.W + C.card := by
  classical
  refine ⟨{
    r := S.r + 1
    blocks := P :: S.blocks
    blocks_length := by simp [S.blocks_length]
    Qsurv := Qnext
    Qsurv_subset := ?_
    Qsurv_nonempty := hQnext_nonempty
    W := S.W + C.card
    productP := P * S.productP
    product_eq := by simp [S.product_eq]
    blocks_pos := ?_
    productP_pos := ?_
    pairwise_coprime := S.pairwise_cons_coreBlock hP
    exact_divides := ?_
    no_selected_prime_remains := ?_
    residues_agree := ?_
    W_eq := ?_
    W_le_K := S.W_add_coreBlock_card_le_K hP
  }, rfl, rfl, rfl, rfl, rfl⟩
  · intro q hq
    exact S.Qsurv_subset (S.coreSurvivors_subset C
      (Finset.mem_filter.1 (hQnext_subset hq)).1)
  · intro B hB
    rw [List.mem_cons] at hB
    cases hB with
    | inl h =>
        subst B
        exact S.coreBlock_pos hP
    | inr h => exact S.blocks_pos B h
  · exact mul_pos (S.coreBlock_pos hP) S.productP_pos
  · intro q hq
    have hfiber := hQnext_subset hq
    have hdvd := S.product_mul_coreBlock_dvd hfiber
    simpa [Nat.mul_comm] using hdvd
  · intro q hq p hp
    have hfiber := hQnext_subset hq
    have hno := S.product_mul_coreBlock_no_selected_prime_remains hfiber p
    simpa [Nat.mul_comm] using hno (by simpa [Nat.mul_comm] using hp)
  · intro qi hqi rj hrj hqiD hrjD
    have hqicore : qi ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hqi)).1
    have hrjcore : rj ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hrj)).1
    have hqiSurv : qi ∈ S.Qsurv := S.coreSurvivors_subset C hqicore
    have hrjSurv : rj ∈ S.Qsurv := S.coreSurvivors_subset C hrjcore
    have hOld := S.residues_agree qi hqiSurv rj hrjSurv hqiD hrjD
    have hNew := hResiduesP qi hqi rj hrj hqiD hrjD
    have hcopInt : (S.productP : ℤ).natAbs.Coprime (P : ℤ).natAbs := by
      simpa using S.coreBlock_coprime_productP hP
    have hBoth :
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (S.productP : ℤ)] ∧
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (P : ℤ)] := ⟨hOld, hNew⟩
    have hMul := (Int.modEq_and_modEq_iff_modEq_mul hcopInt).1 hBoth
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
  · rw [Nat.mul_comm]
    exact (S.omega_product_mul_coreBlock hP).symm

lemma ChainState.exists_residue_subfamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ Qnext : Finset ℕ,
      Qnext.Nonempty ∧
      Qnext ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      (∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (Qnext.card : ℝ) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let residue : ℕ → ZMod P :=
    fun q => if hq : q ∈ D.Q then (D.a ⟨q, hq⟩ : ZMod P) else 0
  have hPpos : 0 < P := S.coreBlock_pos hP
  haveI : NeZero P := ⟨hPpos.ne'⟩
  have hTnonempty : T.Nonempty := by
    dsimp [T]
    rw [ChainState.coreBlocks] at hP
    exact fiber_nonempty_of_mem_image (S := S.coreSurvivors C)
      (B := fun q => exactBlock C q) hP
  rcases exists_zmod_fiber_card_div_le T P residue hTnonempty with ⟨b, hb⟩
  let Qnext : Finset ℕ := T.filter fun q => residue q = b
  refine ⟨Qnext, ?_, ?_, ?_, ?_⟩
  · have hratio_pos : 0 < (T.card : ℝ) / (P : ℝ) := by
      have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast hTnonempty.card_pos
      have hPreal : 0 < (P : ℝ) := by exact_mod_cast hPpos
      exact div_pos hTcard hPreal
    have hQreal : 0 < (Qnext.card : ℝ) := lt_of_lt_of_le hratio_pos hb
    exact Finset.card_pos.1 (by exact_mod_cast hQreal)
  · intro q hq
    exact (Finset.mem_filter.1 hq).1
  · intro qi hqi rj hrj hqiD hrjD
    have hqiResidue : residue qi = b := (Finset.mem_filter.1 hqi).2
    have hrjResidue : residue rj = b := (Finset.mem_filter.1 hrj).2
    have hqiCast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hqiD] using hqiResidue
    have hrjCast : ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hrjD] using hrjResidue
    have hcast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) =
        ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) := hqiCast.trans hrjCast.symm
    exact (ZMod.intCast_eq_intCast_iff
      (D.a ⟨qi, hqiD⟩) (D.a ⟨rj, hrjD⟩) P).1 hcast
  · simpa [T, Qnext] using hb

lemma ChainState.exists_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_residue_subfamily hP with
    ⟨Qnext, hQnext_nonempty, hQnext_subset, hResiduesP, hcard⟩
  rcases S.extend_coreBlock hP hQnext_nonempty hQnext_subset hResiduesP with
    ⟨S', hblocks, hr, hprod, hQsurv, hW⟩
  have hsubset : S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) := by
    intro q hq
    rw [hQsurv] at hq
    exact hQnext_subset hq
  exact ⟨S', hblocks, hr, hprod, hsubset, Finset.card_le_card hsubset, hW,
    by simpa [hQsurv] using hcard⟩

lemma ChainState.exists_weighted_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P : ℕ, ∃ S' : ChainState N D,
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_coreBlock_weighted_share C hCore with ⟨P, hP, hshare⟩
  rcases S.exists_extended_coreBlock hP with
    ⟨S', hblocks, hr, hprod, hQsubset, hQcard_le, hW, hcard⟩
  refine ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hshare, ?_⟩
  have hPreal_nonneg : 0 ≤ (P : ℝ) := by positivity
  have hdiv_share :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤
        ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ)) := by
    exact div_le_div_of_nonneg_right hshare hPreal_nonneg
  exact hdiv_share.trans hcard

lemma ChainState.coreBlocks_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreBlocks C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = C.card) := by
  intro B hB
  rw [ChainState.coreBlocks] at hB
  rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hblock_le_quotient :
      exactBlock C q ≤ q / S.productP :=
    Nat.le_of_dvd (S.quotient_pos_of_mem hqsurv) (S.exactBlock_dvd_quotient_of_core hq)
  have hblock_le_N : exactBlock C q ≤ N := by
    exact hblock_le_quotient.trans ((Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD))
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (S.exactBlock_pos_of_core hq), hblock_le_N⟩,
    S.omega_exactBlock_of_core hq⟩

lemma ChainState.coreBlock_le_N {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : P ≤ N := by
  have hmem := S.coreBlocks_subset_omegaCount C hP
  exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hmem).1).2

lemma ChainState.coreBlock_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hle_nat : hExp (exactBlock C q) ≤ hExp q := hExp_exactBlock_le_hExp C q
  have hle_real : (hExp (exactBlock C q) : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.coreBlock_card_le_K_of_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : C.card ≤ D.K := by
  rcases hCore with ⟨q, hq⟩
  have hle := Finset.card_le_card (S.core_subset_remainingSupport hq)
  have heq := S.remainingSupport_card_eq (S.coreSurvivors_subset C hq)
  omega

lemma ChainState.coreBlock_card_bound_real {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    (C.card : ℝ) ≤ 3 * Mscale N := by
  have hCK : (C.card : ℝ) ≤ (D.K : ℝ) := by
    exact_mod_cast S.coreBlock_card_le_K_of_nonempty hCore
  exact hCK.trans D.K_bound

lemma ChainState.coreBlocks_card_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreBlocks C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
  have hsubset := S.coreBlocks_subset_omegaCount C
  have hcard : (S.coreBlocks C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = C.card)).card :=
    Finset.card_le_card hsubset
  have hcount := hCount N C.card 0 le_rfl (Nat.zero_le _) (S.coreBlock_card_bound_real hCore)
  dsimp only at hcount
  have hsimp :
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((0 : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) =
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
    simp
  exact hcard.trans (by simpa [hsimp] using hcount)

lemma ChainState.coreBlocks_card_real_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreBlocks C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreBlocks_card_le_bfv_omega_count C ε hCore hCount

lemma ChainState.remainingSupportFamily_uniform {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    UniformFamily S.remainingSupportFamily (D.K - S.W) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  exact S.remainingSupport_card_eq hq

lemma ChainState.remainingSupportFamily_intersecting {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    ∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
      A ≠ B → ¬ Disjoint A B := by
  intro A hA B hB hAB
  rw [ChainState.remainingSupportFamily] at hA hB
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
  exact S.remainingSupport_not_disjoint_of_ne hq hr (by
    intro hqr
    subst r
    exact hAB rfl)

lemma ChainState.remainingSupportFamily_rank_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) : 1 ≤ D.K - S.W := by
  omega

lemma ChainState.remainingSupportFamily_rank_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : D.K - S.W ≤ D.K :=
  Nat.sub_le D.K S.W

lemma ChainState.remainingSupportFamily_denseCoreData {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    S.remainingSupportFamily.Nonempty ∧
      1 ≤ D.K - S.W ∧
      D.K - S.W ≤ D.K ∧
      UniformFamily S.remainingSupportFamily (D.K - S.W) ∧
      (∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
        A ≠ B → ¬ Disjoint A B) :=
  ⟨S.remainingSupportFamily_nonempty,
    S.remainingSupportFamily_rank_pos_of_room hRoom,
    S.remainingSupportFamily_rank_le_K,
    S.remainingSupportFamily_uniform,
    S.remainingSupportFamily_intersecting⟩

noncomputable def denseCoreConstant : ℝ :=
  Classical.choose (dense_core_from_spread.{0})

lemma denseCoreConstant_pos : 0 < denseCoreConstant :=
  (Classical.choose_spec (dense_core_from_spread.{0})).1

lemma dense_core_from_spread_fixed_nat
    (A : Finset (Finset ℕ)) (k K : ℕ) :
    A.Nonempty →
    1 ≤ k → k ≤ K →
    UniformFamily A k →
    (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((A.filter fun S => C ⊆ S).card : ℝ) >
        (A.card : ℝ) /
          (denseCoreConstant * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card :=
  (Classical.choose_spec (dense_core_from_spread.{0})).2 A k K

noncomputable def chainKappa {N : ℕ} (D : PrunedData N) : ℝ :=
  denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ))

noncomputable def chainLambda {N : ℕ} (D : PrunedData N) : ℝ :=
  2 * chainKappa D

lemma chainKappa_pos {N : ℕ} (D : PrunedData N) : 0 < chainKappa D := by
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  exact mul_pos denseCoreConstant_pos (zero_lt_one.trans_le hlog_ge_one)

lemma chainLambda_pos {N : ℕ} (D : PrunedData N) : 0 < chainLambda D := by
  dsimp [chainLambda]
  exact mul_pos (by norm_num) (chainKappa_pos D)

lemma ChainState.exists_dense_core_fixed_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases dense_core_from_spread_fixed_nat S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C, by simpa [chainKappa] using hC⟩

lemma ChainState.coreSurvivors_nonempty_of_filter_card_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ)) :
    (S.coreSurvivors C).Nonempty := by
  have hfilter_nat : 0 < (S.remainingSupportFamily.filter fun A => C ⊆ A).card := by
    exact_mod_cast hpos
  have hle := S.remainingSupportFamily_filter_card_le_coreSurvivors C
  have hcore_card : 0 < (S.coreSurvivors C).card := lt_of_lt_of_le hfilter_nat hle
  exact Finset.card_pos.1 hcore_card

lemma ChainState.exists_dense_core_fixed_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_of_room hRoom with ⟨C, hC, hbound⟩
  have hbase_nonneg : 0 ≤ chainKappa D := (chainKappa_pos D).le
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.coreSurvivors_card_gt_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {A : ℝ}
    (hbound : A < ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    A < ((S.coreSurvivors C).card : ℝ) := by
  have hle : ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ) ≤
      ((S.coreSurvivors C).card : ℝ) := by
    exact_mod_cast S.remainingSupportFamily_filter_card_le_coreSurvivors C
  exact hbound.trans_le hle

lemma ChainState.coreSurvivors_card_gt_qsurv_div_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {Λ : ℝ}
    (hbound :
      ((S.remainingSupportFamily.card : ℝ) / Λ ^ C.card) <
        ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    ((S.Qsurv.card : ℝ) / Λ ^ C.card) <
      ((S.coreSurvivors C).card : ℝ) := by
  have h := S.coreSurvivors_card_gt_of_dense_bound hbound
  simpa [S.remainingSupportFamily_card_eq] using h

lemma ChainState.coreBlocks_nonempty_of_coreSurvivors
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : (S.coreBlocks C).Nonempty := by
  rw [ChainState.coreBlocks]
  exact hCore.image _

lemma ChainState.coreBlocks_weight_sum_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) := by
  exact Finset.sum_pos (fun B _hB => hExp_inv_sq_pos B)
    (S.coreBlocks_nonempty_of_coreSurvivors hCore)

lemma ChainState.coreBlocks_weight_sum_le_two_pow_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hC : C.Nonempty) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range N
  let vec : ℕ → Index → ℕ := fun B p => B.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hvec_mem : ∀ B ∈ S.coreBlocks C, vec B ∈ E := by
    intro B hB
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hpSupport : p.1 ∈ primeSupport B := by
      simp [hsupport, p.2]
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hfac_pos : 1 ≤ B.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_N : B.factorization p.1 ≤ N := by
      exact (Nat.factorization_lt p.1 hBne).le.trans (S.coreBlock_le_N hB)
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec (S.coreBlocks C) := by
    intro B hB R hR hBR
    have hsupportB : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hsupportR : primeSupport R = C := S.coreBlock_primeSupport_eq hR
    have hBne : B ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hRne : R ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
      intro hzero
      subst R
      simp [primeSupport] at hpSupport
    apply Nat.eq_of_factorization_eq hBne hRne
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hBR ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hBpos : 1 ≤ B.factorization p := by
        have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hRpos : 1 ≤ R.factorization p := by
        have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpB : p ∉ primeSupport B := by simpa [hsupportB] using hp
      have hpR : p ∉ primeSupport R := by simpa [hsupportR] using hp
      rw [Finsupp.notMem_support_iff.1 hpB, Finsupp.notMem_support_iff.1 hpR]
  have hterm_eq :
      ∀ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) = term (vec B) := by
    intro B hB
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hhexp :
        hExp B = ∏ p : Index, B.factorization p.1 := by
      calc
        hExp B = ∏ p ∈ C, B.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, B.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec B p + 1 = B.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport B := by simp [hsupport, p.2]
      have hpos : 1 ≤ B.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))
        = ∑ B ∈ S.coreBlocks C, term (vec B) := by
            apply Finset.sum_congr rfl
            intro B hB
            exact hterm_eq B hB
    _ = ∑ e ∈ (S.coreBlocks C).image vec, term e := by
            rw [Finset.sum_image]
            intro B hB R hR hEq
            exact hvec_inj hB hR hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨B, hB, rfl⟩
                exact hvec_mem B hB)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset (fun _ : Index => Finset.range N),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range N)
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                simpa [Nat.cast_add, Nat.cast_one] using sum_inv_sq_range_le_two N)
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

noncomputable def chainTFromBlocks : List ℕ → ℕ
  | [] => 0
  | _P :: Ps => omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps

noncomputable def chainT {N : ℕ} {D : PrunedData N} (S : ChainState N D) : ℕ :=
  chainTFromBlocks S.blocks

private lemma chainTFromBlocks_le_length_mul_omega_foldr
    (blocks : List ℕ) (hpos : ∀ P ∈ blocks, 0 < P) :
    chainTFromBlocks blocks ≤ blocks.length * omega (blocks.foldr (· * ·) 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      have hPs_pos : ∀ B ∈ Ps, 0 < B := by
        intro B hB
        exact hpos B (by simp [hB])
      have htail_le_full :
          omega (Ps.foldr (· * ·) 1) ≤ omega (P * Ps.foldr (· * ·) 1) := by
        apply omega_le_of_dvd
        · exact dvd_mul_left (Ps.foldr (· * ·) 1) P
        · exact (Nat.mul_pos (hpos P (by simp)) (List.foldr_mul_pos hPs_pos)).ne'
      calc
        omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps
            ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add htail_le_full (ih hPs_pos)
        _ ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (P * Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_left Ps.length htail_le_full) _
        _ = (Ps.length + 1) * omega (P * Ps.foldr (· * ·) 1) := by
              rw [Nat.add_mul, Nat.one_mul]
              omega

private lemma chainTFromBlocks_add_omega_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    (((chainTFromBlocks blocks + omega (blocks.foldr (· * ·) 1) : ℕ) : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

lemma ChainState.chainT_le_r_mul_W {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * S.W := by
  have h := chainTFromBlocks_le_length_mul_omega_foldr S.blocks S.blocks_pos
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_le_r_mul_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * D.K := by
  exact (S.chainT_le_r_mul_W).trans (Nat.mul_le_mul_left S.r S.W_le_K)

lemma ChainState.chainT_add_W_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_add_omega_real_quadratic_bound
    S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_cons_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {P : ℕ} {S' : ChainState N D}
    (hblocks : S'.blocks = P :: S.blocks) :
    chainT S' = S.W + chainT S := by
  calc
    chainT S' = omega (S.blocks.foldr (· * ·) 1) + chainTFromBlocks S.blocks := by
      simp [chainT, hblocks, chainTFromBlocks]
    _ = S.W + chainT S := by
      rw [← S.product_eq, ← S.W_eq]
      rfl

noncomputable def chainLowerScale {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : ℝ :=
  (D.Q.card : ℝ) /
    ((S.productP : ℝ) * (hExp S.productP : ℝ) ^ 2 * Λ ^ S.W)

def ChainState.HasLowerBound {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : Prop :=
  chainLowerScale Λ S ≤ (S.Qsurv.card : ℝ)

private lemma div_scale_le_weighted_share
    {a q c w p h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hp : 0 < p) (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (p * h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) / p := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (p * h * (2 * κ) ^ n)
        = (a * w) / ((p * h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((p * h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg
                (mul_nonneg (mul_pos hp hh).le hΛpow.le)
                hw_pos.le)
    _ = (c * (1 / h) / w) / p := by
            field_simp [hp.ne', hh.ne', hΛpow.ne', hw_pos.ne']

private lemma div_scale_le_weighted_fiber
    {a q c w h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (h * (2 * κ) ^ n)
        = (a * w) / ((h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg (mul_pos hh hΛpow).le hw_pos.le)
    _ = c * (1 / h) / w := by
            field_simp [hh.ne', hΛpow.ne', hw_pos.ne']

lemma ChainState.chainLowerScale_extend_coreBlock_eq
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hP : P ∈ S.coreBlocks C)
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    chainLowerScale Λ S' =
      chainLowerScale Λ S / ((P : ℝ) * (hExp P : ℝ) ^ 2 * Λ ^ C.card) := by
  rw [chainLowerScale, chainLowerScale, hprod, hW,
    hExp_mul_of_coprime (S.coreBlock_coprime_productP hP).symm, pow_add]
  norm_num [Nat.cast_mul]
  ring_nf

lemma ChainState.hasLowerBound_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {κ Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hκ : 0 < κ) (hΛ : Λ = 2 * κ)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound Λ)
    (hDense :
      ((S.Qsurv.card : ℝ) / κ ^ C.card) <
        ((S.coreSurvivors C).card : ℝ))
    (hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card)
    (hCard :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    S'.HasLowerBound Λ := by
  rw [ChainState.HasLowerBound]
  rw [S.chainLowerScale_extend_coreBlock_eq hP hprod hW, hΛ]
  have hCore : (S.coreSurvivors C).Nonempty := by
    have hPmem := hP
    rw [ChainState.coreBlocks] at hPmem
    rcases Finset.mem_image.mp hPmem with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hP_pos_real : 0 < (P : ℝ) := by
    exact_mod_cast S.coreBlock_pos hP
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * κ) S /
          ((P : ℝ) * ((hExp P : ℝ) ^ 2) * (2 * κ) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) :=
    div_scale_le_weighted_share
      hq_nonneg hWeight_pos hP_pos_real hh_pos hκ
      (by simpa [ChainState.HasLowerBound, hΛ] using hLower)
      hDense hWeight
  exact hstep.trans hCard

lemma ChainState.selectedFiber_lower_from_invariant
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound (chainLambda D))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ)) :
    (D.Q.card : ℝ) /
        ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card)) ≤
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  have hCore : (S.coreSurvivors C).Nonempty := by
    rw [ChainState.coreBlocks] at hP
    rcases Finset.mem_image.mp hP with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * chainKappa D) S /
          (((hExp P : ℝ) ^ 2) * (2 * chainKappa D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) :=
    div_scale_le_weighted_fiber
      hq_nonneg hWeight_pos hh_pos (chainKappa_pos D)
      (by simpa [ChainState.HasLowerBound, chainLambda] using hLower)
      hDenseQ hWeight
  have hstepΛ :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) := by
    simpa [chainLambda] using hstep
  have hleft :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) =
        (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) := by
    rw [chainLowerScale,
      hExp_mul_of_coprime (S.coreBlock_coprime_productP hP), pow_add]
    norm_num [Nat.cast_mul]
    ring_nf
  rw [← hleft]
  exact hstepΛ.trans hWeightedFiber

lemma ChainState.blocksOmegaPos_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hBlocks : S.BlocksOmegaPos)
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hblocks : S'.blocks = P :: S.blocks) :
    S'.BlocksOmegaPos := by
  intro B hB
  rw [hblocks] at hB
  rcases List.mem_cons.1 hB with hBP | hBtail
  · subst B
    rw [S.coreBlock_omega_eq_card hP]
    exact Nat.succ_le_of_lt hCne.card_pos
  · exact hBlocks B hBtail

noncomputable def initialChainState (N : ℕ) (D : PrunedData N) : ChainState N D where
  r := 0
  blocks := []
  blocks_length := by simp
  Qsurv := D.Q
  Qsurv_subset := by intro q hq; exact hq
  Qsurv_nonempty := D.Q_nonempty
  W := 0
  productP := 1
  product_eq := by simp
  blocks_pos := by intro P hP; simp at hP
  productP_pos := by norm_num
  pairwise_coprime := by simp
  exact_divides := by intro q _hq; exact one_dvd q
  no_selected_prime_remains := by
    intro _q _hq _p hp
    simp [primeSupport] at hp
  residues_agree := by
    intro qi _hqi rj _hrj hqiD hrjD
    rw [Int.modEq_iff_dvd]
    exact one_dvd (D.a ⟨rj, hrjD⟩ - D.a ⟨qi, hqiD⟩)
  W_eq := by simp [omega, primeSupport]
  W_le_K := by omega

lemma initialChainState_room (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).W < D.K := by
  simp [initialChainState]
  exact D.K_pos

lemma initialChainState_blocksOmegaPos (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).BlocksOmegaPos := by
  intro P hP
  simp [initialChainState] at hP

lemma initialChainState_hasLowerBound {N : ℕ} (D : PrunedData N) (Λ : ℝ) :
    ChainState.HasLowerBound Λ (initialChainState N D) := by
  rw [ChainState.HasLowerBound, chainLowerScale]
  simp [initialChainState, hExp_one]

theorem chain_step_structural_with_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_with_survivor_of_room hRoom with
    ⟨C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hLower' : S'.HasLowerBound (chainLambda D) := by
    apply S.hasLowerBound_extend_coreBlock
      (κ := chainKappa D) (Λ := chainLambda D)
      (hκ := chainKappa_pos D) (hΛ := by rfl)
      (hP := hP) (hLower := hLower) (hDense := hDenseQ)
      (hWeight := hWeight) (hCard := hcard)
      (hprod := hprod) (hW := hW)
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le, hW,
    S.chainT_cons_eq hblocks, hLower', hShare, hcard, hDense⟩

lemma ChainState.coreSurvivors_nonempty_of_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (S.coreSurvivors C).Nonempty := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

theorem chain_step_structural_with_counts_and_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural_with_lowerBound S hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
      hW, hT, hLower', hShare, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
    hW, hT, hLower',
    hShare, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

noncomputable def chainStepBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (_S S' : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S'.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * (hExp S'.productP : ℝ) ^ 2
    * (chainLambda D) ^ S'.W

noncomputable def chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * Real.exp (2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)))
    * (chainLambda D) ^ (chainT S + S.W)

lemma chainStepBoundWithLosses_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S S' : ChainState N D) : 0 ≤ chainStepBoundWithLosses ε S S' := by
  rw [chainStepBoundWithLosses]
  have hΛ : 0 ≤ chainLambda D := (chainLambda_pos D).le
  positivity

lemma log_chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBoundWithLosses ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
        2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
        ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
  rw [chainProductBoundWithLosses]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := (((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  set c : ℝ := 2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ))
  set Λ : ℝ := chainLambda D
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hΛ_pos : 0 < Λ := by
    dsimp [Λ]
    exact chainLambda_pos D
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  have hexpc_ne : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hΛpow_ne : Λ ^ (chainT S + S.W) ≠ 0 := pow_ne_zero _ hΛ_pos.ne'
  rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne)
        hΛpow_ne,
      Real.log_mul (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne,
      Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
      Real.log_mul hqpow_ne hexpa_ne,
      Real.log_pow, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_pow]

lemma initialChainState_productBoundWithLosses {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBoundWithLosses ε (initialChainState N D) := by
  simp [chainProductBoundWithLosses, initialChainState, chainT, chainTFromBlocks]

lemma chainProductBoundWithLosses_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBoundWithLosses ε S S' :=
    chainStepBoundWithLosses_nonneg ε S S'
  have hExpBound : (hExp S'.productP : ℝ) ≤
      Real.exp (Real.sqrt (Real.log (N : ℝ))) :=
    S'.productP_hExp_bound
  have hExpSq :
      (hExp S'.productP : ℝ) ^ 2 ≤
        Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
    have hnonneg : 0 ≤ (hExp S'.productP : ℝ) := by positivity
    calc
      (hExp S'.productP : ℝ) ^ 2
          ≤ (Real.exp (Real.sqrt (Real.log (N : ℝ)))) ^ 2 :=
            sq_le_sq₀ hnonneg (Real.exp_pos _).le |>.2 hExpBound
      _ = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
            rw [sq, ← Real.exp_add]
            ring_nf
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := hStep
    _ ≤ chainProductBoundWithLosses ε S * chainStepBoundWithLosses ε S S' := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ ≤ chainProductBoundWithLosses ε S' := by
          rw [chainProductBoundWithLosses, chainStepBoundWithLosses,
            chainProductBoundWithLosses, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ) with hq
          set a : ℝ := -((D.K : ℝ) / Mscale N) / 2 + ε with ha
          set l : ℝ := Real.log (Real.log (N : ℝ)) with hl
          set u : ℝ := Real.sqrt (Real.log (N : ℝ)) with hu
          have hΛnonneg : 0 ≤ chainLambda D := (chainLambda_pos D).le
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  (hExp S'.productP : ℝ) ^ 2 * (chainLambda D) ^ S'.W)
                ≤
              (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  Real.exp (2 * u) * (chainLambda D) ^ S'.W) := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hExpSq (by positivity))
                          (pow_nonneg hΛnonneg _))
                      (by positivity)
            _ = q ^ (S.r + 1) *
                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                  (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                    rw [pow_succ]
                    calc
                      (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (2 * (S.r : ℝ) * u) *
                            (chainLambda D) ^ (chainT S + S.W)) *
                          (q * Real.exp (a * Zscale N) *
                            Real.exp (((S'.W : ℝ) / 2) * l) *
                            Real.exp (2 * u) * (chainLambda D) ^ S'.W)
                          =
                        q ^ S.r * q *
                          (Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp (a * Zscale N)) *
                          (Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (((S'.W : ℝ) / 2) * l)) *
                          (Real.exp (2 * (S.r : ℝ) * u) * Real.exp (2 * u)) *
                          ((chainLambda D) ^ (chainT S + S.W) *
                            (chainLambda D) ^ S'.W) := by ring
                      _ =
                        q ^ S.r * q *
                          Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                          Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                          Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                          (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
                              ← pow_add]
                            have hA :
                                Real.exp ((S.r : ℝ) * a * Zscale N + a * Zscale N) =
                                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) := by
                              congr 1
                              norm_num
                              ring
                            have hL :
                                Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l +
                                    ((S'.W : ℝ) / 2) * l) =
                                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) *
                                    l) := by
                              congr 1
                              norm_num [Nat.cast_add]
                              ring
                            have hU :
                                Real.exp (2 * (S.r : ℝ) * u + 2 * u) =
                                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) := by
                              congr 1
                              norm_num
                              ring
                            rw [hA, hL, hU]
                            ring

theorem chain_terminal_with_product_bound_from_state
    {N : ℕ} {D : PrunedData N} (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S')
    (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) ∧
      Sfinal.BlocksOmegaPos ∧
      (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      S.BlocksOmegaPos →
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D) ∧
        Sfinal.BlocksOmegaPos ∧
        (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS hBlocksS hProdS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS, hBlocksS, hProdS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases hStep S hLowerS hBlocksS hRoom with
            ⟨S', hr, hWincrease, hT, hLower', hBlocks', hStepProd⟩
          have hProd' : (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' :=
            chainProductBoundWithLosses_step hr hT hProdS hStepProd
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' hBlocks' hProd' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal, hBlocksFinal,
              hProdFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal, hBlocksFinal, hProdFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower hBlocks hProd

theorem chain_terminal_with_product_bound_from_initial
    (N : ℕ) (D : PrunedData N) (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) ∧
      S.BlocksOmegaPos ∧
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  have hBlocks0 : S0.BlocksOmegaPos := by
    simpa [S0] using initialChainState_blocksOmegaPos N D
  have hProd0 : (S0.productP : ℝ) ≤ chainProductBoundWithLosses ε S0 := by
    simpa [S0] using initialChainState_productBoundWithLosses D ε
  rcases hStep S0 hLower0 hBlocks0 hRoom0 with
    ⟨S1, hr1, hWincrease1, _hT1, hLower1, hBlocks1, hStepProd1⟩
  have hProd1 : (S1.productP : ℝ) ≤ chainProductBoundWithLosses ε S1 :=
    chainProductBoundWithLosses_step hr1 _hT1 hProd0 hStepProd1
  rcases chain_terminal_with_product_bound_from_state ε hStep S1 hLower1 hBlocks1 hProd1 with
    ⟨S, hle_start, hle_budget, hW, hLower, hBlocks, hProd⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower, hBlocks, hProd⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

theorem chain_step_selected_block_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (_hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (_hBlocks : S.BlocksOmegaPos)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hStepProduct : S'.productP = P * S.productP)
    (hStepW : S'.W = S.W + C.card)
    (_hStepLower : S'.HasLowerBound (chainLambda D))
    (_hQsurv_subset :
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P))
    (_hQsurv_card_le :
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ))
    (_hWeighted :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (_hCoreCount :
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
    (_hBlockCount :
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    (_hP_le_N : P ≤ N)
    (_hP_hExp : (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))) :
    (P : ℝ) ≤ chainStepBoundWithLosses ε S S' := by
  have hFiberLower :
      (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) :=
    S.selectedFiber_lower_from_invariant hCne hP hLower hDense hWeightedFiber
  have hFiberUpper :
      ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
        ((N : ℝ) / (S.productP * P : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) :=
    S.selectedFiber_card_real_le_bfv_omega_count hP ε hCount
  have hWithLosses :
      (P : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) *
          (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card) := by
    have hcompare := hFiberLower.trans hFiberUpper
    have hDQpos : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    have hSpos : 0 < (S.productP : ℝ) := by exact_mod_cast S.productP_pos
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast S.coreBlock_pos hP
    have hHpos : 0 < (hExp (S.productP * P) : ℝ) ^ 2 := by
      have h : 0 < (hExp (S.productP * P) : ℝ) := by exact_mod_cast hExp_pos (S.productP * P)
      exact sq_pos_of_pos h
    have hΛpos : 0 < (chainLambda D) ^ (S.W + C.card) :=
      pow_pos (chainLambda_pos D) _
    have hEpos :
        0 < Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) := by
      positivity
    field_simp [hSpos.ne', hPpos.ne', hHpos.ne', hΛpos.ne'] at hcompare
    have hmain :
        (D.Q.card : ℝ) * (P : ℝ) ≤
          (N : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) + 2 * ε) * Zscale N / 2) *
            Real.exp (((S.W + C.card : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) / 2) *
            ((hExp (S.productP * P) : ℝ) ^ 2) *
            (chainLambda D) ^ (S.W + C.card) := by
      have hmul := mul_le_mul_of_nonneg_right hcompare hHpos.le
      rw [div_mul_cancel₀ _ hHpos.ne'] at hmul
      nlinarith [hmul]
    field_simp [hDQpos.ne']
    nlinarith [hmain]
  rw [chainStepBoundWithLosses, hStepW, hStepProduct]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hWithLosses

theorem chain_step
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos) :
    ∃ S' : ChainState N D,
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      S'.BlocksOmegaPos ∧
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
  rcases chain_step_structural_with_counts_and_lowerBound S ε hCount hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, _hQsubset, _hQcard_le,
      _hW, hT, hLower', _hWeightedFiber, _hweighted, _hDense, _hCoreCount, _hBlockCount,
      _hP_le_N, _hP_hExp⟩
  have hBlocks' : S'.BlocksOmegaPos :=
    S.blocksOmegaPos_extend_coreBlock hBlocks hCne hP hblocks
  refine ⟨S', hr, hWincrease, hT, hLower', hBlocks', ?_⟩
  have hPbound : (P : ℝ) ≤ chainStepBoundWithLosses ε S S' :=
    chain_step_selected_block_bound S ε _hε hCount hRoom hLower hBlocks
      hCne hP hprod _hW hLower' _hQsubset _hQcard_le _hWeightedFiber _hweighted _hDense
      _hCoreCount _hBlockCount _hP_le_N _hP_hExp
  rw [hprod]
  calc
    ((P * S.productP : ℕ) : ℝ) = (P : ℝ) * (S.productP : ℝ) := by norm_num
    _ ≤ chainStepBoundWithLosses ε S S' * (S.productP : ℝ) := by
          exact mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ = (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by ring

theorem chain_inequality
    (N : ℕ) (D : PrunedData N) (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.BlocksOmegaPos ∧
      
      
      (S.productP : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) ^ R
        * Real.exp ((R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))
        * Real.exp (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)))
        * (chainLambda D) ^ (chainT S + S.W) := by
  have hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
    intro S hLower hBlocks hRoom
    exact chain_step S ε _hε hCount hRoom hLower hBlocks
  rcases chain_terminal_with_product_bound_from_initial N D ε hStep with
    ⟨R, S, hR, hRpos, hRle, hStop, _hLower, hBlocks, hProd⟩
  refine ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, ?_⟩
  simpa [chainProductBoundWithLosses, hR] using hProd

end BFVRegular1190
namespace BFVRegular1190
open Filter
open Asymptotics
open scoped BigOperators
lemma quad_bound (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := by
  nlinarith [sq_nonneg (c / 2 - σ)]

private lemma log_chain_quadratic_algebra
    (M R K σ ε : ℝ) (hM : M ≠ 0) :
    R * σ + R * (-(K / M) / 2 + ε) +
        (2 * R * K - R * (R - 1)) / (4 * M) =
      R * σ - (R * (R - 1)) / (4 * M) + R * ε := by
  field_simp [hM]
  ring

private lemma one_sub_two_div_eq (M : ℝ) (hM : M ≠ 0) :
    1 - 2 / M = (M - 2) / M := by
  field_simp [hM]

private lemma log_chain_shape_algebra
    (M R σ ε sqrtE lambdaE : ℝ) (hM : M ≠ 0) :
    (R * σ - (R * (R - 1)) / (4 * M) + R * ε + sqrtE + lambdaE) / M =
      (R / M) * σ - (R / M) ^ 2 / 4 + (R / M) / (4 * M) + (R / M) * ε +
        sqrtE / M + lambdaE / M := by
  field_simp [hM]
  ring

private lemma eventually_log_const_mul_le_mul_self
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (A * x) ≤ δ * x := by
  have hAtop : Tendsto (fun x : ℝ => A * x) atTop atTop :=
    tendsto_id.const_mul_atTop hA
  have hsmallA :
      (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => A * x :=
    Real.isLittleO_log_id_atTop.comp_tendsto hAtop
  have hbig : (fun x : ℝ => A * x) =O[atTop] fun x : ℝ => x :=
    isBigO_const_mul_self A (fun x : ℝ => x) atTop
  have hsmall : (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => x :=
    hsmallA.trans_isBigO hbig
  filter_upwards [isLittleO_iff.mp hsmall hδ, eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  calc
    Real.log (A * x) ≤ ‖Real.log (A * x)‖ := le_abs_self _
    _ ≤ δ * ‖x‖ := hx
    _ = δ * x := by rw [Real.norm_of_nonneg hxpos.le]

private lemma eventually_log_chainLambda_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ D : PrunedData N,
        Real.log (chainLambda D) ≤ δ * Real.log (Real.log (N : ℝ)) := by
  let B : ℝ := |Real.log (3 * Real.exp 1)| + 1
  let A : ℝ := 2 * denseCoreConstant * B
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos (by norm_num) denseCoreConstant_pos) hBpos
  have hlogA_real := eventually_log_const_mul_le_mul_self A δ hApos hδ
  have hlogA :
      ∀ᶠ N : ℕ in atTop,
        Real.log (A * Real.log (Real.log (N : ℝ))) ≤
          δ * Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually hlogA_real
  filter_upwards [hlogA, eventually_Mscale_le_log, eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogA_N hMle hsqrtloglog hNlarge_nat D
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrtloglog
  have hKle_log : (D.K : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    nlinarith [D.K_bound, hMle]
  have hKpos_real : 0 < (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_pos : 0 < Real.exp 1 * (D.K : ℝ) :=
    mul_pos (Real.exp_pos 1) hKpos_real
  have harg_le :
      Real.exp 1 * (D.K : ℝ) ≤ Real.exp 1 * (3 * Real.log (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hKle_log (Real.exp_pos 1).le
  have hlog_arg_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) :=
    Real.log_le_log harg_pos harg_le
  have hlog_three_pos : 0 < 3 * Real.exp 1 := by positivity
  have hlog_rhs :
      Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) =
        Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := by
    have hmul :
        Real.exp 1 * (3 * Real.log (N : ℝ)) =
          (3 * Real.exp 1) * Real.log (N : ℝ) := by ring
    rw [hmul, Real.log_mul hlog_three_pos.ne' hlog_pos.ne']
  have hlog_part_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        B * Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (Real.exp 1 * (D.K : ℝ))
          ≤ Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) := hlog_arg_le
      _ = Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := hlog_rhs
      _ ≤ B * Real.log (Real.log (N : ℝ)) := by
            dsimp [B]
            have hconst_le : Real.log (3 * Real.exp 1) ≤ |Real.log (3 * Real.exp 1)| :=
              le_abs_self _
            have hconst_mul :
                |Real.log (3 * Real.exp 1)| ≤
                  |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) :=
              le_mul_of_one_le_right (abs_nonneg _) hloglog_ge_one
            calc
              Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ))
                  ≤ |Real.log (3 * Real.exp 1)| + Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_le le_rfl
              _ ≤ |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) +
                    Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_mul le_rfl
              _ = (|Real.log (3 * Real.exp 1)| + 1) *
                    Real.log (Real.log (N : ℝ)) := by ring
  have hLambda_le :
      chainLambda D ≤ A * Real.log (Real.log (N : ℝ)) := by
    rw [chainLambda, chainKappa]
    calc
      2 * (denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)))
          = 2 * denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)) := by ring
      _ ≤ 2 * denseCoreConstant * (B * Real.log (Real.log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hlog_part_le
              (mul_nonneg (by norm_num) denseCoreConstant_pos.le)
      _ = A * Real.log (Real.log (N : ℝ)) := by
            dsimp [A]
            ring
  exact (Real.log_le_log (chainLambda_pos D) hLambda_le).trans hlogA_N

noncomputable def sigmaN (N : ℕ) (Qcard : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (Qcard : ℝ)) / Zscale N

lemma sigmaN_nonneg {N Qcard : ℕ}
    (hQpos : 0 < Qcard) (hQleN : Qcard ≤ N) (hZ : 0 < Zscale N) :
    0 ≤ sigmaN N Qcard := by
  have hQpos_real : 0 < (Qcard : ℝ) := Nat.cast_pos.mpr hQpos
  have hQleN_real : (Qcard : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hQleN
  have hone : 1 ≤ (N : ℝ) / (Qcard : ℝ) :=
    (one_le_div hQpos_real).2 hQleN_real
  rw [sigmaN]
  exact div_nonneg (Real.log_nonneg hone) hZ.le

private lemma product_lower_of_chain_stop {N : ℕ} {D : PrunedData N}
    {S : ChainState N D}
    (hStop : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases hStop with hProd | hW
  · exact hProd
  · exact S.productP_lower_of_W_eq_K hW

private lemma one_sub_le_of_sq_lower
    {η δ σ : ℝ} (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hδ_le : δ ≤ η) (hσ_nonneg : 0 ≤ σ)
    (hsq : 1 - δ ≤ σ ^ 2) :
    1 - η ≤ σ := by
  have hone_sub_nonneg : 0 ≤ 1 - η := by linarith
  have hsquare_left : (1 - η) ^ 2 ≤ 1 - δ := by
    have hsq_le_linear : (1 - η) ^ 2 ≤ 1 - η := by
      nlinarith [hη_nonneg, hη_le_one]
    linarith
  have hsquare : (1 - η) ^ 2 ≤ σ ^ 2 := hsquare_left.trans hsq
  exact (sq_le_sq₀ hone_sub_nonneg hσ_nonneg).1 hsquare

lemma card_le_of_sigma_lower {η : ℝ} {N Qcard : ℕ}
    (hN : 0 < N) (hQ : 0 < Qcard) (hZ : 0 < Zscale N)
    (hsigma : 1 - η ≤ sigmaN N Qcard) :
    (Qcard : ℝ) ≤ (N : ℝ) * Lscale (-(1 - η)) N := by
  have hQreal : 0 < (Qcard : ℝ) := by exact_mod_cast hQ
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratio_pos : 0 < (N : ℝ) / (Qcard : ℝ) := div_pos hNreal hQreal
  have hlog :
      (1 - η) * Zscale N ≤ Real.log ((N : ℝ) / (Qcard : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hsigma hZ.le
    rw [sigmaN, div_mul_cancel₀ _ hZ.ne'] at hmul
    exact hmul
  have hexp_le_ratio :
      Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) / (Qcard : ℝ) :=
    (Real.le_log_iff_exp_le hratio_pos).1 hlog
  have hmulQ :
      (Qcard : ℝ) * Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hexp_le_ratio hQreal.le
    rw [div_mul_cancel₀ _ hQreal.ne'] at hmul
    simpa [mul_comm] using hmul
  have hcancel :
      Real.exp ((1 - η) * Zscale N) *
          Real.exp (-((1 - η) * Zscale N)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    (Qcard : ℝ)
        = ((Qcard : ℝ) * Real.exp ((1 - η) * Zscale N)) *
            Real.exp (-((1 - η) * Zscale N)) := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ (N : ℝ) * Real.exp (-((1 - η) * Zscale N)) := by
          exact mul_le_mul_of_nonneg_right hmulQ (Real.exp_pos _).le
    _ = (N : ℝ) * Lscale (-(1 - η)) N := by
          rw [Lscale]
          congr 1
          ring_nf

set_option maxHeartbeats 2000000 in
theorem sigma_lower_bound :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ Qcard : ℕ, 1 ≤ Qcard →
        (∃ D : PrunedData N, D.Q.card = Qcard) →
        1 - η ≤ sigmaN N Qcard := by
  intro η hη
  let ε : ℝ := η / 8
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  filter_upwards [bfv_omega_count_input ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge (8 / η) (by positivity),
      eventually_sqrt_loglog_ge (96 / η),
      eventually_log_chainLambda_le_mul_loglog (η / 144) (by positivity)] with
    N hCount hNlarge_nat hMlarge hSqrtLogLogLarge hLogLambdaSmall
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hMZ : Mscale N * Zscale N = Real.log (N : ℝ) :=
    Mscale_mul_Zscale_eq_log hNlarge
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hNlarge
  intro Qcard _hQcard hD
  rcases hD with ⟨D, hDcard⟩
  have hsigma_nonneg : 0 ≤ sigmaN N Qcard := by
    have hQleN : Qcard ≤ N := by
      rw [← hDcard]
      exact D.card_le_N
    exact sigmaN_nonneg (Nat.succ_le_iff.mp _hQcard) hQleN hZpos
  rcases chain_inequality N D ε hε hCount with
    ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, hProdUpper⟩
  have hProdLower : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) :=
    product_lower_of_chain_stop hStop
  have hProdUpperBound : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
    simpa [chainProductBoundWithLosses, hR] using hProdUpper
  have hLogProduct :
      Real.log ((N : ℝ) * Lscale (-2) N) ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLowerPos : 0 < (N : ℝ) * Lscale (-2) N := by
      exact mul_pos (by exact_mod_cast D.N_pos) (Lscale_pos (-2) N)
    exact Real.log_le_log hLowerPos (hProdLower.trans hProdUpperBound)
  have hLogProductExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLogLower :
        Real.log ((N : ℝ) * Lscale (-2) N) =
          Real.log (N : ℝ) - 2 * Zscale N := by
      rw [log_nat_mul_Lscale D.N_pos (-2)]
      ring
    rwa [hLogLower] at hLogProduct
  have hLogChainExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        (R : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
          2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
          ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
    rw [log_chainProductBoundWithLosses ε S] at hLogProductExpanded
    simpa [hR] using hLogProductExpanded
  have hSigmaLog :
      Real.log ((N : ℝ) / (D.Q.card : ℝ)) =
        sigmaN N Qcard * Zscale N := by
    rw [sigmaN, ← hDcard]
    field_simp [hZpos.ne']
  have hLogChainNormalized :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
          (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N := by
    have hExpandedSigma :
        Real.log (N : ℝ) - 2 * Zscale N ≤
          (R : ℝ) * (sigmaN N Qcard * Zscale N) +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
            2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
            ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
      simpa [hSigmaLog] using hLogChainExpanded
    have h :
        (Mscale N - 2) * Zscale N ≤
          ((R : ℝ) * sigmaN N Qcard +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
            (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N) *
              Zscale N := by
      calc
        (Mscale N - 2) * Zscale N
            = Real.log (N : ℝ) - 2 * Zscale N := by
                rw [← hMZ]
                ring
        _ ≤ (R : ℝ) * (sigmaN N Qcard * Zscale N) +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ))) +
              2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
              ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) :=
            hExpandedSigma
        _ = ((R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
              (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                Zscale N) * Zscale N := by
            rw [← hZdivM]
            field_simp [hMpos.ne', hZpos.ne']
    have hdiv := div_le_div_of_nonneg_right h hZpos.le
    field_simp [hZpos.ne'] at hdiv
    field_simp [hMpos.ne']
    nlinarith [hdiv, hMpos]
  have hTbasic : chainT S ≤ S.r * D.K := S.chainT_le_r_mul_K
  have hTbasicR : chainT S ≤ R * D.K := by
    simpa [hR] using hTbasic
  have hTquad : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) :=
    S.chainT_add_W_real_quadratic_bound hBlocks
  have hTquadK : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1) := by
    have hWle : (S.W : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast S.W_le_K
    have hRnonneg : 0 ≤ (R : ℝ) := by positivity
    rw [← hR]
    nlinarith [hTquad, hWle, hRnonneg]
  have hTterm :
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
        (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
          (4 * Mscale N) := by
    calc
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N)
          = (((chainT S + S.W : ℕ) : ℝ) * 2) * (1 / (4 * Mscale N)) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) *
            (1 / (4 * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hTquadK (by positivity)
      _ = (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
            (4 * Mscale N) := by ring
  let sqrtE : ℝ := (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N
  let lambdaE : ℝ :=
    (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N
  have hLogChainQuadratic :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard -
          ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
          (R : ℝ) * ε + sqrtE + lambdaE := by
    calc
      Mscale N - 2
          ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              sqrtE + lambdaE :=
            hLogChainNormalized
      _ ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
                (4 * Mscale N) + sqrtE + lambdaE := by
            let A : ℝ :=
              (R : ℝ) * sigmaN N Qcard +
                (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε)
            let B : ℝ := sqrtE + lambdaE
            have hmid :
                A + ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
                  A + (2 * (R : ℝ) * (D.K : ℝ) -
                    (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) :=
              by
                have hmid' := add_le_add_left hTterm A
                linarith
            have hmidB := add_le_add_right hmid B
            dsimp [A, B] at hmidB
            linarith
      _ = (R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE := by
            have hbase :
                (R : ℝ) * sigmaN N Qcard +
                    (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
                    (2 * (R : ℝ) * (D.K : ℝ) -
                        (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) =
                  (R : ℝ) * sigmaN N Qcard -
                    ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
                    (R : ℝ) * ε :=
              log_chain_quadratic_algebra (Mscale N) (R : ℝ) (D.K : ℝ)
                (sigmaN N Qcard) ε hMpos.ne'
            rw [hbase]
  let c : ℝ := (R : ℝ) / Mscale N
  have hc_pos : 0 < c := by
    dsimp [c]
    have hRpos_real : 0 < (R : ℝ) := by exact_mod_cast hRpos
    exact div_pos hRpos_real hMpos
  have hc_le_three : c ≤ 3 := by
    dsimp [c]
    have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := hRleK_real.trans D.K_bound
    exact (div_le_iff₀ hMpos).2 hRle3M
  let sqrtLoss : ℝ := sqrtE / Mscale N
  let lambdaLoss : ℝ := lambdaE / Mscale N
  have hLogChainShape :
      (Mscale N - 2) / Mscale N ≤
        c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    have hdiv := div_le_div_of_nonneg_right hLogChainQuadratic hMpos.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ ((R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE) / Mscale N := hdiv
      _ = c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
            sqrtLoss + lambdaLoss := by
              dsimp [c, sqrtLoss, lambdaLoss]
              exact log_chain_shape_algebra (Mscale N) (R : ℝ) (sigmaN N Qcard)
                ε sqrtE lambdaE hMpos.ne'
  have hsigma_sq_shape :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    calc
      (Mscale N - 2) / Mscale N
          ≤ c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hLogChainShape
      _ ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss := by
            simpa [add_assoc] using
              add_le_add_right (quad_bound c (sigmaN N Qcard))
                (c / (4 * Mscale N) + c * ε + sqrtLoss + lambdaLoss)
  have hsigma_sq_shape_three :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss := by
    have hsmall1 : c / (4 * Mscale N) ≤ 3 / (4 * Mscale N) := by
      exact div_le_div_of_nonneg_right hc_le_three (by positivity)
    have hsmall2 : c * ε ≤ 3 * ε :=
      mul_le_mul_of_nonneg_right hc_le_three hε.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hsigma_sq_shape
      _ ≤ (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
              sqrtLoss + lambdaLoss := by
            have herr :
                c / (4 * Mscale N) + c * ε ≤
                  3 / (4 * Mscale N) + 3 * ε :=
              add_le_add hsmall1 hsmall2
            linarith
  have hsigma_sq_lower :
      1 - (2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss) ≤
        (sigmaN N Qcard) ^ 2 := by
    have hleft : (Mscale N - 2) / Mscale N = 1 - 2 / Mscale N :=
      (one_sub_two_div_eq (Mscale N) hMpos.ne').symm
    linarith [hsigma_sq_shape_three, hleft]
  by_cases hη_big : 1 ≤ η
  · have htarget : 1 - η ≤ 0 := by linarith
    exact htarget.trans hsigma_nonneg
  have hη_le_one : η ≤ 1 := le_of_lt (not_le.mp hη_big)
  let δN : ℝ :=
    2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε + sqrtLoss + lambdaLoss
  have hfinish_of_error (hδN : δN ≤ η) : 1 - η ≤ sigmaN N Qcard := by
    exact one_sub_le_of_sq_lower hη.le hη_le_one hδN hsigma_nonneg (by
      simpa [δN] using hsigma_sq_lower)
  have hδN_le : δN ≤ η := by
    have hApos : 0 < (8 : ℝ) / η := by positivity
    have hinvM_raw : 1 / Mscale N ≤ 1 / (8 / η) :=
      one_div_le_one_div_of_le hApos hMlarge
    have hinvM : 1 / Mscale N ≤ η / 8 := by
      convert hinvM_raw using 1
      field_simp [hη.ne']
    dsimp [δN, ε]
    have hterm1 : 2 / Mscale N ≤ η / 4 := by
      calc
        2 / Mscale N = 2*(1/Mscale N) := by ring
        _ ≤ 2*(η/8) := mul_le_mul_of_nonneg_left hinvM (by norm_num)
        _ = _ := by ring
    have hterm2 : 3 / (4 * Mscale N) ≤ 3 * η / 32 := by
      calc
        3 / (4 * Mscale N) = (3/4) * (1/Mscale N) := by rw [div_mul_eq_div_div]; ring
        _ ≤ (3/4) * (η/8) := mul_le_mul_of_nonneg_left hinvM (by norm_num)
        _ = _ := by ring
    have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
      Real.log_pos ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
    have hsqrtlog_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := by
      have hlog_pos : 0 < Real.log (N : ℝ) :=
        zero_lt_one.trans ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
      rw [Real.sqrt_pos]
      exact hlog_pos
    have hsqrtloglog_pos :
        0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hlarge_pos : 0 < (96 : ℝ) / η := by positivity
      exact hlarge_pos.trans_le hSqrtLogLogLarge
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := by
      have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
      exact hRleK_real.trans D.K_bound
    have hsqrtLoss_le : sqrtLoss ≤ η / 16 := by
      have hfactor_nonneg :
          0 ≤ 2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N) := by
        positivity
      calc
        sqrtLoss
            = (R : ℝ) *
                (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              dsimp [sqrtLoss, sqrtE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ (3 * Mscale N) *
              (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hRle3M hfactor_nonneg
        _ = 6 / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
              rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
              field_simp [hMpos.ne', hsqrtlog_pos.ne', hsqrtloglog_pos.ne']
              ring
        _ ≤ 6 / (96 / η) := by
              exact div_le_div_of_nonneg_left (by norm_num)
                (by positivity) hSqrtLogLogLarge
        _ = η / 16 := by
              field_simp [hη.ne']
              ring
    have hTplus_le_RK :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ (R : ℝ) * (D.K : ℝ) := by
      have hRge_one_real : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
      have hquad_nonneg : 0 ≤ (R : ℝ) * ((R : ℝ) - 1) := by
        nlinarith [hRge_one_real]
      have hT2_le_2RK :
          (((chainT S + S.W : ℕ) : ℝ) * 2) ≤
            2 * (R : ℝ) * (D.K : ℝ) := by
        nlinarith [hTquadK, hquad_nonneg]
      nlinarith
    have hTplus_le_9M2 :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ 9 * (Mscale N) ^ 2 := by
      have hKle3M : (D.K : ℝ) ≤ 3 * Mscale N := D.K_bound
      have hRnonneg : 0 ≤ (R : ℝ) := by positivity
      have hKnonneg : 0 ≤ (D.K : ℝ) := by positivity
      have hRK_le : (R : ℝ) * (D.K : ℝ) ≤ (3 * Mscale N) * (3 * Mscale N) :=
        mul_le_mul hRle3M hKle3M hKnonneg (by positivity)
      nlinarith [hTplus_le_RK, hRK_le]
    have hlambdaLog_le :
        Real.log (chainLambda D) ≤
          (η / 144) * Real.log (Real.log (N : ℝ)) :=
      hLogLambdaSmall D
    have hlambdaLoss_le : lambdaLoss ≤ η / 16 := by
      have hcoef_nonneg :
          0 ≤ (η / 144) * Real.log (Real.log (N : ℝ)) := by positivity
      have hTnonneg : 0 ≤ (((chainT S + S.W : ℕ) : ℝ)) := by positivity
      have hnum_le :
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
            (9 * (Mscale N) ^ 2) *
              ((η / 144) * Real.log (Real.log (N : ℝ))) := by
        have hlog_scaled :
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
              (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hlambdaLog_le hTnonneg
        have hT_scaled :
            (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) ≤
              (9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hTplus_le_9M2 hcoef_nonneg
        exact hlog_scaled.trans hT_scaled
      have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
      calc
        lambdaLoss
            = (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                (Zscale N * Mscale N) := by
              dsimp [lambdaLoss, lambdaE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ ((9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) /
                (Zscale N * Mscale N) := by
              exact div_le_div_of_nonneg_right hnum_le
                (mul_nonneg hZpos.le hMpos.le)
        _ = η / 16 := by
              rw [← hMll]
              field_simp [hMpos.ne', hloglog_pos.ne']
              ring
    have hmain_le :
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) ≤
          (23 / 32) * η := by
      calc
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8)
          ≤ η / 4 + 3 * η / 32 + 3 * (η / 8) := by
            gcongr
        _ = (23 / 32) * η := by ring
    calc
      2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) + sqrtLoss + lambdaLoss
          ≤ (23 / 32) * η + η / 16 + η / 16 := by
            linarith [hmain_le, hsqrtLoss_le, hlambdaLoss_le]
      _ = (27 / 32) * η := by ring
      _ ≤ η := by
            exact mul_le_of_le_one_left hη.le (by norm_num)
  exact hfinish_of_error hδN_le

end BFVRegular1190
open Filter BFVRegular1190

private lemma scale_ident (N : ℕ) (c : ℝ) : scaleL N ^ c = Lscale c N := by
  rw [scaleL, ← Real.exp_mul, mul_comm]
  rfl

theorem OMA.solution : OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1.H2 := by
  intro ε he
  filter_upwards [sigma_lower_bound ε he, eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hs hN T a K hr hd hg
  by_cases ht : T.Nonempty
  · obtain ⟨hk,hK,good,inj⟩ := hg
    have disj : PairwiseDisjointResidues T (fun i => a i.val) := by
      intro i j hne
      apply Set.disjoint_left.mpr
      intro z hi hj
      exact hd i.val i.property j.val j.property (fun h => hne (Subtype.ext h)) ⟨z,hi,hj⟩
    let D : PrunedData N := {
      Q := T
      Q_nonempty := ht
      a := fun i => a i.val
      admissible := ⟨hr,_,disj⟩
      pairwise_disjoint := disj
      K := K
      K_pos := hk
      modulus_lower := fun q hq => by simpa only [scale_ident] using (good q hq).1
      modulus_upper := fun q hq => (hr q hq).2
      hExp_bound := fun q hq => by simpa only [hExp,primeSupport,Nat.support_factorization] using (good q hq).2.1
      omega_eq := fun q hq => by simpa only [omega,primeSupport,Nat.support_factorization] using (good q hq).2.2
      K_bound := hK
      rad_injective := by simpa only [rad,primeSupport,Nat.support_factorization] using inj
    }
    have hN' : Real.exp 1 < (N:ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hN)
    have hh := card_le_of_sigma_lower D.N_pos ht.card_pos (Zscale_pos_of_exp_one_lt_nat hN')
      (hs T.card ht.card_pos ⟨D,rfl⟩)
    rw [scale_ident]
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Lscale_mono_in_alpha
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
    simp only [Finset.card_empty,Nat.cast_zero,scale_ident]
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
