import FormalConjectures.ErdosProblems.«1190»
import Mathlib

-- Credit: Pawan Sasanka Ammanamanchi and collaborators (Shashi456/erdos-formalizations, Erdos/P202/Proof.lean at 286f856aa3fc08957b80950fd18a45aab8d045ea, Apache-2.0), for the pruning and regularity pieces R1.H1.R1.H1 and R1.H1.R1.H2 (as adapted in those files)
-- Credit: @loremcdmx (R1.H2)
-- Credit: @LordMike (assembly)

namespace OMA.R1
open Filter Real Finset
private lemma afU {m : ℕ} (hm : 0 < m) (w : ℕ → ℝ) (a : ℕ → ℤ)
  (hcount : ∀ N ≥ m, ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N) →
   (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
    ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
   (S.card : ℝ) ≤ N * w N)
  (K : ℕ) (S : Finset ℕ) (hb : ∀ n ∈ S, m < n ∧ n ≤ 2 ^ K * m)
  (hd : ∀ n ∈ S, ∀ j ∈ S, n ≠ j →
   ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) :
  (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ k ∈ range K, 2 * w (2 ^ (k+1) * m) := by
 classical
 induction K generalizing S with
 | zero =>
  have he : S = ∅ := eq_empty_iff_forall_notMem.2 fun n hn => by
   have := hb n hn
   simp at this
   omega
  simp [he]
 | succ k ih =>
  let A := 2 ^ k * m
  have hA : 0 < A := Nat.mul_pos (pow_pos (by decide) k) hm
  have hmA : m ≤ A := Nat.le_mul_of_pos_left _ (pow_pos (by decide) k)
  have aiN : 2 ^ (k + 1) * m = 2 * A := by dsimp [A]; ring
  let L := S.filter (fun n => n ≤ A)
  let U := S.filter (fun n => ¬n ≤ A)
  have hL : L ⊆ S := filter_subset _ _
  have hU : U ⊆ S := filter_subset _ _
  have hl := ih L (fun n hn => ⟨(hb n (hL hn)).1, (mem_filter.1 hn).2⟩)
   (fun n hn j hj => hd n (hL hn) j (hL hj))
  have hc := hcount (2*A) (by omega) U
   (fun n hn => ⟨by have := (hb n (hU hn)).1; omega, aiN ▸ (hb n (hU hn)).2⟩)
   (fun n hn j hj => hd n (hU hn) j (hU hj))
  have hpos : 0 < (A : ℝ) := by exact_mod_cast hA
  have hu : (∑ n ∈ U, (n : ℝ)⁻¹) ≤ 2 * w (2 * A) := by
   calc
    _ ≤ ∑ _n ∈ U, (A : ℝ)⁻¹ := by
     apply sum_le_sum
     intro n hn
     have h : A < n := Nat.lt_of_not_ge (mem_filter.1 hn).2
     exact inv_anti₀ hpos (by exact_mod_cast h.le)
    _ = (U.card : ℝ) / A := by simp [div_eq_mul_inv]
    _ ≤ _ := by
     apply (div_le_iff₀ hpos).2
     push_cast at hc
     linarith only [hc]
  rw [← sum_filter_add_sum_filter_not S (fun n => n ≤ A), sum_range_succ, aiN]
  exact add_le_add hl hu
def H1 : Prop :=
 ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℤ),
  (∀ n ∈ S, 0 < n ∧ n ≤ N) →
  (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
   ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
  (S.card : ℝ) ≤ N * scaleL N ^ (-(sqrt 3 / 2) + δ)
def H2 : Prop :=
 ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ᶠ m : ℕ in atTop, ∃ B : ℝ,
  B < scaleL m ^ (-(sqrt 3 / 2) + δ) ∧ ∀ K : ℕ,
   (∑ k ∈ range K, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2)) ≤ B
theorem main : H1 → H2 → type_of% @Erdos1190.erdos_1190.variants.upper_bound := by
 intro hc ht ε hε
 let δ := min ε (1 / 2)
 have hδ : 0 < δ := lt_min hε (by norm_num)
 obtain ⟨N₀, hN⟩ := eventually_atTop.1 (hc (δ / 2) (by positivity))
 filter_upwards [eventually_ge_atTop (max N₀ 1), ht δ hδ (min_le_right _ _)] with m hm htail
 obtain ⟨B, hB, hsum⟩ := htail
 apply lt_of_le_of_lt _ (lt_of_lt_of_le hB ?_)
 swap
 ·apply Real.rpow_le_rpow_of_exponent_le
  ·exact Real.one_le_exp (Real.sqrt_nonneg _)
  ·exact add_le_add_right (min_le_left _ _) _
 apply csSup_le
 ·exact ⟨0, ∅, fun _ => 0, by simp, by simp, by simp⟩
 ·rintro s ⟨S, a, hlow, hd, rfl⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  let K := S.sup id
  have hb (n : ℕ) (hn : n ∈ S) : n ≤ 2 ^ K * m := calc
   n ≤ K := Finset.le_sup (f := id) hn
   _ ≤ 2 ^ K := (Nat.lt_two_pow_self).le
   _ ≤ _ := Nat.le_mul_of_pos_right _ hm1
  exact (afU hm1 (fun N => scaleL N ^ (-(sqrt 3 / 2) + δ/2)) a
   (fun N hNm S => hN N ((le_of_max_le_left hm).trans hNm) S a)
   K S (fun n hn => ⟨hlow n hn, hb n hn⟩) hd).trans (hsum K)
end OMA.R1

namespace OMA.R2
open Real Finset Filter
def H1 : Prop :=
 ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℤ),
  (∀ n ∈ S, 0 < n ∧ n ≤ N) →
  (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
   ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
  N * scaleL N ^ (-1 : ℝ) ≤ (S.card : ℝ) →
  ∃ (T : Finset ℕ) (K : ℕ), T ⊆ S ∧
   (S.card : ℝ) * scaleL N ^ (-ε) ≤ (T.card : ℝ) ∧
   1 ≤ K ∧ (K : ℝ) ≤ 3 * sqrt (log N / log (log N)) ∧
   (∀ q ∈ T, N * scaleL N ^ (-2 : ℝ) ≤ (q : ℝ) ∧
    ((∏ p ∈ q.primeFactors, q.factorization p : ℕ) : ℝ) ≤ exp (sqrt (log N)) ∧
    q.primeFactors.card = K) ∧
   (∀ q ∈ T, ∀ r ∈ T, (∏ p ∈ q.primeFactors, p) = (∏ p ∈ r.primeFactors, p) → q = r)
def H2 : Prop :=
 ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (T : Finset ℕ) (a : ℕ → ℤ) (K : ℕ),
  (∀ n ∈ T, 0 < n ∧ n ≤ N) →
  (∀ n ∈ T, ∀ j ∈ T, n ≠ j →
   ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
  (1 ≤ K ∧ (K : ℝ) ≤ 3 * sqrt (log N / log (log N)) ∧
   (∀ q ∈ T, N * scaleL N ^ (-2 : ℝ) ≤ (q : ℝ) ∧
    ((∏ p ∈ q.primeFactors, q.factorization p : ℕ) : ℝ) ≤ exp (sqrt (log N)) ∧
    q.primeFactors.card = K) ∧
   (∀ q ∈ T, ∀ r ∈ T, (∏ p ∈ q.primeFactors, p) = (∏ p ∈ r.primeFactors, p) → q = r)) →
  (T.card : ℝ) ≤ N * scaleL N ^ (-(sqrt 3 / 2) + ε)
theorem main : H1 → H2 → OMA.R1.H1 := by
 intro prune count δ hδ
 let ε := min (δ / 2) (1 / 4)
 have he : 0 < ε := lt_min (by positivity) (by norm_num)
 have heδ : ε + ε ≤ δ := by
  have := min_le_left (δ / 2) (1 / 4 : ℝ)
  dsimp [ε]
  linarith
 filter_upwards [prune ε he (min_le_right _ _), count ε he] with N hp hc S a hr hd
 have hb : 1 ≤ scaleL N := Real.one_le_exp (Real.sqrt_nonneg _)
 have hb' : 0 < scaleL N := lt_of_lt_of_le zero_lt_one hb
 have hN : (0 : ℝ) ≤ N := by positivity
 by_cases hbig : N * scaleL N ^ (-1 : ℝ) ≤ (S.card : ℝ)
 ·obtain ⟨T, K, ht, hl, hg⟩ := hp S a hr hd hbig
  have hT := hc T a K (fun n hn => hr n (ht hn))
   (fun n hn j hj => hd n (ht hn) j (ht hj)) hg
  calc
   (S.card : ℝ) = ((S.card : ℝ) * scaleL N ^ (-ε)) * scaleL N ^ ε := by
    rw [mul_assoc, ← Real.rpow_add hb', neg_add_cancel, Real.rpow_zero, mul_one]
   _ ≤ (N * scaleL N ^ (-(sqrt 3 / 2) + ε)) * scaleL N ^ ε :=
    mul_le_mul_of_nonneg_right (hl.trans hT) (Real.rpow_nonneg hb'.le _)
   _ ≤ _ := by
    rw [mul_assoc, ← Real.rpow_add hb']
    apply mul_le_mul_of_nonneg_left _ hN
    exact Real.rpow_le_rpow_of_exponent_le hb (by linarith)
 ·apply (not_le.mp hbig).le.trans
  apply mul_le_mul_of_nonneg_left _ hN
  apply Real.rpow_le_rpow_of_exponent_le hb
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
   sq_nonneg (Real.sqrt 3 - 2)]
end OMA.R2

namespace OMA.L1
namespace dO
open Filter
open Asymptotics
open scoped BigOperators
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
 {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}
abbrev gJ (Q : Finset ℕ) : Type :=
 {q : ℕ // q ∈ Q} → ℤ
def d7
  (Q : Finset ℕ) (a : gJ Q) : Prop :=
 ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
  Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))
def nY {Q Q' : Finset ℕ}
  (a : gJ Q) (hsub : Q' ⊆ Q) : gJ Q' :=
 fun q => a ⟨q.1, hsub q.2⟩
lemma d7.mono
  {Q Q' : Finset ℕ} {a : gJ Q}
  (hdisj : d7 Q a) (hsub : Q' ⊆ Q) :
  d7 Q' (nY a hsub) := by
 intro i j hij
 let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
 let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
 have afV : iQ ≠ jQ := by
  intro h
  have hval : iQ.1 = jQ.1 :=
   congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
  exact hij (Subtype.ext hval)
 simpa [nY, iQ, jQ] using hdisj iQ jQ afV
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
 (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
 ∃ a : gJ Q, d7 Q a
noncomputable def aZ (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))
noncomputable def bF (α : ℝ) (N : ℕ) : ℝ :=
 Real.exp (α * aZ N)
noncomputable def aO (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))
lemma nD (N : ℕ) : 0 ≤ aZ N :=
 Real.sqrt_nonneg _
lemma lJ {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < aZ N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [aZ, Real.sqrt_pos]
 exact mul_pos gC c8
lemma gN {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aZ N =
   Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 rw [aZ, Real.sqrt_mul d6]
lemma pD (N : ℕ) : 0 ≤ aO N :=
 Real.sqrt_nonneg _
lemma g5 {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < aO N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [aO, Real.sqrt_pos]
 exact div_pos gC c8
lemma gW {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aO N * Real.log (Real.log (N : ℝ)) = aZ N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have aaA : 0 ≤ aO N * Real.log (Real.log (N : ℝ)) :=
  mul_nonneg (pD N) f8
 have hsq :
   (aO N * Real.log (Real.log (N : ℝ))) ^ 2 = (aZ N) ^ 2 := by
  rw [aO, aZ, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
  ·field_simp [c8.ne']
  ·exact mul_nonneg d6 f8
  ·exact div_nonneg d6 f8
 rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
 ·exact h
 ·have aac : 0 ≤ aZ N := nD N
  nlinarith
lemma j4 {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aZ N / aO N = Real.log (Real.log (N : ℝ)) := by
 have SH := gW hN
 have hMpos := g5 hN
 rw [← SH]
 field_simp [hMpos.ne']
lemma tB {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aO N * aZ N = Real.log (N : ℝ) := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have SH := gW hN
 have afW : aO N ^ 2 =
   Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  rw [aO, Real.sq_sqrt]
  exact div_nonneg d6 f8
 calc
  aO N * aZ N
    = aO N * (aO N * Real.log (Real.log (N : ℝ))) := by rw [SH]
  _ = aO N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
  _ = Real.log (N : ℝ) := by
     rw [afW]
     field_simp [c8.ne']
lemma nS :
  Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
   atTop (nhds 0) := by
 have hreal :
   Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
  have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
    fun x : ℝ => Real.log x :=
   Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact hsmall.tendsto_div_nhds_zero
 exact hreal.comp tendsto_natCast_atTop_atTop
lemma iw :
  Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
 exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
  tendsto_natCast_atTop_atTop
lemma pO :
  Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
 exact Real.tendsto_sqrt_atTop.comp iw
lemma f9 (A : ℝ) :
  ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
 pO.eventually_ge_atTop A
lemma oM (A : ℝ) (hA : 0 < A) :
  ∀ᶠ N : ℕ in atTop, A ≤ aO N := by
 have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
 have Rd : (0 : ℝ) < 1 / A ^ 2 := by positivity
 have OV : ∀ᶠ N : ℕ in atTop,
   Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
  nS.eventually_lt_const Rd
 filter_upwards [OV, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
  with N hsmall dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have SI :
   Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
  (div_lt_iff₀ gC).1 hsmall
 have adg :
   A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
  have hmul := mul_lt_mul_of_pos_left SI hA2
  field_simp [hA2.ne'] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
 have W8 :
   A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
  (le_div_iff₀ c8).2 adg.le
 rw [aO]
 exact (Real.le_sqrt hA.le (div_nonneg gC.le c8.le)).2 W8
lemma rW (α : ℝ) (N : ℕ) : 0 < bF α N :=
 Real.exp_pos _
lemma nF (α : ℝ) (N : ℕ) : 0 ≤ bF α N :=
 (rW α N).le
lemma ab6 (N : ℕ) : bF 0 N = 1 := by
 simp [bF]
lemma JT (α β : ℝ) (N : ℕ) :
  bF (α + β) N = bF α N * bF β N := by
 simp [bF, add_mul, Real.exp_add]
lemma YO (α : ℝ) (N : ℕ) :
  bF (-α) N * bF α N = 1 := by
 rw [← JT]
 simp [bF]
lemma oN {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
  bF α N ≤ bF β N := by
 exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (nD N))
lemma WJ {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
  bF (-α) N ≤ 1 := by
 simpa [ab6] using oN (α := -α) (β := 0) (by linarith) N
lemma Dm {N : ℕ} (hN : 0 < N) (α : ℝ) :
  Real.log ((N : ℝ) * bF α N) = Real.log (N : ℝ) + α * aZ N := by
 have U9 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
 have hL : bF α N ≠ 0 := (rW α N).ne'
 rw [Real.log_mul U9 hL, bF, Real.log_exp]
end dO
namespace dO
open Finset
open scoped BigOperators
def aD (n : ℕ) : Finset ℕ :=
 n.factorization.support
def omega (n : ℕ) : ℕ :=
 (aD n).card
def rad (n : ℕ) : ℕ :=
 ∏ p ∈ aD n, p
def cQ (n : ℕ) : ℕ :=
 ∏ p ∈ aD n, n.factorization p
def cD (C : Finset ℕ) (q : ℕ) : ℕ :=
 ∏ p ∈ C, p ^ q.factorization p
lemma Dp (n : ℕ) : 0 < cQ n := by
 unfold cQ aD
 exact Finset.prod_pos (fun _p hp =>
  Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))
lemma SK : cQ 1 = 1 := by
 simp [cQ, aD]
lemma f7 {n p : ℕ} (hp : p ∈ aD n) : Nat.Prime p := by
 unfold aD at hp
 rw [Nat.support_factorization] at hp
 exact Nat.prime_of_mem_primeFactors hp
lemma k6 {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
  (hpn : p ∣ n) : p ∈ aD n := by
 unfold aD
 rw [Finsupp.mem_support_iff]
 exact hp.factorization_pos_of_dvd hn hpn |>.ne'
lemma dL {m n : ℕ} (hcop : Nat.Coprime m n) :
  Disjoint (aD m) (aD n) := by
 rw [Finset.disjoint_left]
 intro p hpm hpn
 have hp : Nat.Prime p := f7 hpm
 have afX : p ∣ m := Nat.dvd_of_factorization_pos (by
  unfold aD at hpm
  exact Finsupp.mem_support_iff.1 hpm)
 have afY : p ∣ n := Nat.dvd_of_factorization_pos (by
  unfold aD at hpn
  exact Finsupp.mem_support_iff.1 hpn)
 have hp1 : p ∣ 1 := by
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd afX afY
 exact hp.not_dvd_one hp1
lemma g9 {m n : ℕ} (hcop : Nat.Coprime m n) :
  aD (m * n) = aD m ∪ aD n := by
 unfold aD
 rw [Nat.factorization_mul_of_coprime hcop]
 exact Finsupp.support_add_eq (dL hcop)
lemma u6 {m n : ℕ} (hcop : Nat.Coprime m n) :
  cQ (m * n) = cQ m * cQ n := by
 unfold cQ
 rw [g9 hcop]
 rw [Finset.prod_union (dL hcop)]
 congr 1
 ·apply Finset.prod_congr rfl
  intro p hp
  have lK : p ∉ aD n :=
   (Finset.disjoint_left.1 (dL hcop)) hp
  have hnzero : n.factorization p = 0 := by
   unfold aD at lK
   exact Finsupp.notMem_support_iff.1 lK
  rw [Nat.factorization_mul_of_coprime hcop]
  simp [hnzero]
 ·apply Finset.prod_congr rfl
  intro p hp
  have lK : p ∉ aD m :=
   (Finset.disjoint_left.1 (dL hcop).symm) hp
  have hmzero : m.factorization p = 0 := by
   unfold aD at lK
   exact Finsupp.notMem_support_iff.1 lK
  rw [Nat.factorization_mul_of_coprime hcop]
  simp [hmzero]
lemma Eb (C : Finset ℕ) (q : ℕ) : cD C q ∣ q := by
 by_cases hq : q = 0
 ·simp [hq]
 ·nth_rw 2 [← Nat.factorization_prod_pow_eq_self hq]
  unfold cD
  have hfilter :
    (∏ p ∈ C, p ^ q.factorization p) =
     ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
      p ^ q.factorization p := by
   refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
   intro p hpC XO
   have W9 : p ∉ q.factorization.support := by
    intro hp
    exact XO (Finset.mem_filter.2 ⟨hpC, hp⟩)
   have hzero : q.factorization p = 0 := by
    by_contra hne
    exact W9 (Finsupp.mem_support_iff.2 hne)
   simp [hzero]
  rw [hfilter]
  exact Finset.prod_dvd_prod_of_subset
   (C.filter (fun p => p ∈ q.factorization.support))
   q.factorization.support
   (fun p => p ^ q.factorization p)
   (by
    intro p hp
    exact (Finset.mem_filter.1 hp).2)
lemma kC {C : Finset ℕ} {q p : ℕ}
  (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
  (cD C q).factorization p = q.factorization p := by
 unfold cD
 have tD : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
  intro x hx
  exact pow_ne_zero _ (hC x hx).ne_zero
 rw [Nat.factorization_prod tD, Finsupp.finset_sum_apply]
 rw [Finset.sum_eq_single p]
 ·rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
 ·intro x hx hxp
  rw [(hC x hx).factorization_pow]
  exact Finsupp.single_eq_of_ne hxp.symm
 ·intro lK
  exact (lK hpC).elim
lemma vG {C : Finset ℕ} {q : ℕ}
  (hC : ∀ p ∈ C, Nat.Prime p)
  (hCq : C ⊆ aD q) :
  aD (cD C q) = C := by
 unfold aD cD
 ext p
 have tD : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
  intro x hx
  exact pow_ne_zero _ (hC x hx).ne_zero
 rw [Nat.factorization_prod tD, Finsupp.mem_support_iff]
 constructor
 ·intro hsum
  by_contra hpC
  apply hsum
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
  intro x hx
  have afZ : x ≠ p := by
   intro hxp
   exact hpC (hxp ▸ hx)
  rw [(hC x hx).factorization_pow]
  exact Finsupp.single_eq_of_ne afZ.symm
 ·intro hpC
  have hp : Nat.Prime p := hC p hpC
  have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
  intro hsum
  rw [Finsupp.finset_sum_apply] at hsum
  have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
  rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
  exact hqpos hterm
lemma vH {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
  n = 1 := by
 have hsupp : aD n = ∅ := by
  have hcard : (aD n).card = 0 := by simpa [omega] using hω
  exact Finset.card_eq_zero.mp hcard
 unfold aD at hsupp
 have O1 : n.factorization.prod (fun p e => p ^ e) = 1 := by
  unfold Finsupp.prod
  rw [hsupp]
  simp
 have hprod := Nat.factorization_prod_pow_eq_self hn
 rw [← hprod]
 exact O1
end dO
namespace dO
open Filter Finset
open scoped BigOperators
noncomputable def gd (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))
lemma j9
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
private lemma eD (n : ℕ) :
  aD n = n.primeFactors := by
 unfold aD
 rw [Nat.support_factorization]
private lemma jF (n : ℕ) :
  rad n = ∏ p ∈ n.primeFactors, p := by
 unfold rad
 rw [eD]
private lemma LQ (n : ℕ) : Squarefree (rad n) := by
 rw [jF]
 classical
 have tD : (∏ p ∈ n.primeFactors, p) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
   (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
 refine (Nat.squarefree_iff_factorization_le_one tD).2 ?_
 intro q
 by_cases hq : q ∈ n.primeFactors
 ·have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  rw [Nat.factorization_prod]
  ·rw [Finsupp.finset_sum_apply]
   calc
    ∑ x ∈ n.primeFactors, x.factorization q
      = q.factorization q := by
        refine Finset.sum_eq_single q ?_ ?_
        ·intro x hx hxq
         have LV : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
         rw [← pow_one x, LV.factorization_pow]
         simp [hxq]
        ·intro hnot
         exact (hnot hq).elim
    _ = 1 := by
        rw [← pow_one q, hqprime.factorization_pow]
        simp
    _ ≤ 1 := le_rfl
  ·intro x hx
   exact (Nat.prime_of_mem_primeFactors hx).ne_zero
 ·rw [Nat.factorization_prod]
  ·rw [Finsupp.finset_sum_apply]
   calc
    ∑ x ∈ n.primeFactors, x.factorization q = 0 := by
     refine Finset.sum_eq_zero ?_
     intro x hx
     have LV : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
     rw [← pow_one x, LV.factorization_pow]
     have hxq : x ≠ q := by
      intro h
      exact hq (h ▸ hx)
     simp [hxq]
    _ ≤ 1 := by norm_num
  ·intro x hx
   exact (Nat.prime_of_mem_primeFactors hx).ne_zero
private lemma O2 (n : ℕ) : rad n ∣ n := by
 rw [jF]
 exact Nat.prod_primeFactors_dvd n
private lemma Ih (n : ℕ) :
  aD (rad n) = aD n := by
 calc
  aD (rad n) = (rad n).primeFactors := eD _
  _ = (∏ p ∈ n.primeFactors, p).primeFactors := by rw [jF]
  _ = n.primeFactors := by
   exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
  _ = aD n := (eD n).symm
private lemma Vc (n : ℕ) : omega (rad n) = omega n := by
 unfold omega
 rw [Ih]
lemma k7
  (z : ℝ) (hz : 0 ≤ z) {n : ℕ} (hn : n ≠ 0) :
  z ^ omega n ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
 classical
 have hmem : rad n ∈ n.divisors.filter Squarefree := by
  rw [Finset.mem_filter]
  exact ⟨Nat.mem_divisors.mpr ⟨O2 n, hn⟩, LQ n⟩
 have hnonneg :
   ∀ d ∈ n.divisors.filter Squarefree, 0 ≤ z ^ omega d := by
  intro d hd
  exact pow_nonneg hz _
 have nZ :
   z ^ omega (rad n) ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d :=
  Finset.single_le_sum hnonneg hmem
 simpa [Vc] using nZ
lemma nI (y d : ℕ) (hd : 0 < d) :
  ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
 classical
 calc
  ((Finset.Icc 1 y).filter fun n => d ∣ n).card
    ≤ (Finset.Icc 1 (y / d)).card := by
     refine Finset.card_le_card_of_injOn
      (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
      (t := Finset.Icc 1 (y / d))
      (fun n : ℕ => n / d) ?_ ?_
     ·intro n hn
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
     ·intro a ha b hb hab
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
lemma jP
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
     exact k7 z hz
      (by
       have hnIcc := Finset.mem_Icc.mp hn
       exact Nat.ne_of_gt hnIcc.1)
  _ ≤ ∑ n ∈ Finset.Icc 1 y,
      ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ d ∣ n),
       z ^ omega d := by
     refine Finset.sum_le_sum ?_
     intro n hn
     refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
     ·intro d hd
      rw [Finset.mem_filter] at hd ⊢
      have XP : d ∈ n.divisors := hd.1
      have af0 : Squarefree d := hd.2
      have hnIcc := Finset.mem_Icc.mp hn
      have Ec : 0 < d := Nat.pos_of_mem_divisors XP
      have XQ : d ∣ n := (Nat.mem_divisors.mp XP).1
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
      have aaB : d ≤ y := (Nat.le_of_dvd hnpos XQ).trans hnIcc.2
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt Ec, aaB⟩, af0, XQ⟩
     ·intro d hd QX
      exact pow_nonneg hz _
  _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
     (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
     simp_rw [Finset.sum_filter]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro d hd
     by_cases hsq : Squarefree d
     ·calc
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
     ·simp [hsq]
lemma jW
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
     jP y z hz
  _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
      ((y : ℝ) / (d : ℝ)) * z ^ omega d := by
     refine Finset.sum_le_sum ?_
     intro d hd
     rw [Finset.mem_filter] at hd
     have nJ := Finset.mem_Icc.mp hd.1
     have Ec : 0 < d := lt_of_lt_of_le Nat.zero_lt_one nJ.1
     have vY :
       ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d :=
      nI y d Ec
     have qC :
       (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) ≤
        (y : ℝ) / (d : ℝ) := by
      exact (Nat.cast_le.mpr vY).trans Nat.cast_div_le
     exact mul_le_mul_of_nonneg_right qC (pow_nonneg hz _)
  _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
      (y : ℝ) * (z ^ omega d / (d : ℝ)) := by
     apply Finset.sum_congr rfl
     intro d hd
     rw [Finset.mem_filter] at hd
     have nJ := Finset.mem_Icc.mp hd.1
     have SM : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one nJ.1))
     field_simp [SM]
  _ = (y : ℝ) *
     ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
     rw [Finset.mul_sum]
lemma jL
  (z : ℝ) {d : ℕ} (hsq : Squarefree d) :
  z ^ omega d / (d : ℝ) =
   ∏ p ∈ aD d, z / (p : ℝ) := by
 classical
 have Vd : ∏ p ∈ aD d, p = d := by
  rw [eD]
  exact Nat.prod_primeFactors_of_squarefree hsq
 have SN : (d : ℝ) = ∏ p ∈ aD d, (p : ℝ) := by
  calc
   (d : ℝ) = ((∏ p ∈ aD d, p : ℕ) : ℝ) := by
    exact_mod_cast Vd.symm
   _ = ∏ p ∈ aD d, (p : ℝ) := by
    norm_num
 have hpow : z ^ omega d = ∏ p ∈ aD d, z := by
  simp [omega, Finset.prod_const]
 calc
  z ^ omega d / (d : ℝ)
    = (∏ p ∈ aD d, z) / (∏ p ∈ aD d, (p : ℝ)) := by
     rw [hpow, SN]
  _ = ∏ p ∈ aD d, z / (p : ℝ) := by
     rw [Finset.prod_div_distrib]
private lemma k8
  {d y : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
  aD d ⊆ (Finset.Icc 1 y).filter Nat.Prime := by
 intro p hp
 rw [Finset.mem_filter]
 have jM : Nat.Prime p := f7 hp
 have adh : p ∈ d.primeFactors := by
  simpa [eD] using hp
 have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors adh
 have YP : p ≤ d :=
  Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hd1) hpdvd
 exact ⟨Finset.mem_Icc.mpr ⟨jM.one_le, YP.trans hdy⟩, jM⟩
lemma kV
  (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
  (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ)) ≤
   ((Finset.Icc 1 y).filter Nat.Prime).prod
    (fun p => (1 : ℝ) + z / (p : ℝ)) := by
 classical
 let S : Finset ℕ := (Finset.Icc 1 y).filter Squarefree
 let P : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
 let term : Finset ℕ → ℝ := fun T => (∏ p ∈ T, z / (p : ℝ))
 have hinj :
   ∀ d ∈ S, ∀ e ∈ S, aD d = aD e → d = e := by
  intro d hd e he hsupport
  simp [S] at hd he
  have hdprod : ∏ p ∈ aD d, p = d := by
   rw [eD]
   exact Nat.prod_primeFactors_of_squarefree hd.2
  have aaC : ∏ p ∈ aD e, p = e := by
   rw [eD]
   exact Nat.prod_primeFactors_of_squarefree he.2
  calc
   d = ∏ p ∈ aD d, p := hdprod.symm
   _ = ∏ p ∈ aD e, p := by rw [hsupport]
   _ = e := aaC
 have Bj : S.image aD ⊆ P.powerset := by
  intro T hT
  rw [Finset.mem_powerset]
  rcases Finset.mem_image.mp hT with ⟨d, hdS, rfl⟩
  simp [S] at hdS
  have nJ := hdS.1
  exact k8 nJ.1 nJ.2
 have tJ :
   ∀ T ∈ P.powerset, 0 ≤ term T := by
  intro T hT
  rw [Finset.mem_powerset] at hT
  refine Finset.prod_nonneg ?_
  intro p hpT
  have hpP : p ∈ P := hT hpT
  simp [P] at hpP
  have jM : Nat.Prime p := hpP.2
  exact div_nonneg hz (by exact_mod_cast jM.pos.le)
 calc
  (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ))
    = ∑ d ∈ S, term (aD d) := by
     apply Finset.sum_congr
     ·simp [S]
     ·intro d hd
      simp [S] at hd
      exact jL z hd.2
  _ = ∑ T ∈ S.image aD, term T := by
     rw [Finset.sum_image]
     intro d hd e he hsupport
     exact hinj d hd e he hsupport
  _ ≤ ∑ T ∈ P.powerset, term T := by
     exact Finset.sum_le_sum_of_subset_of_nonneg Bj
      (by
       intro T hTP QX
       exact tJ T hTP)
  _ = P.prod (fun p => (1 : ℝ) + z / (p : ℝ)) := by
     rw [Finset.prod_one_add]
  _ = ((Finset.Icc 1 y).filter Nat.Prime).prod
     (fun p => (1 : ℝ) + z / (p : ℝ)) := by
     rfl
lemma lN
  (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
  (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
   (y : ℝ) *
    ((Finset.Icc 1 y).filter Nat.Prime).prod
     (fun p => (1 : ℝ) + z / (p : ℝ)) := by
 exact (jW y z hz).trans
  (mul_le_mul_of_nonneg_left
   (kV y z hz)
   (by positivity))
lemma j3 :
  ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
   (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
 refine ⟨Real.log 4 + 1, ?_, ?_⟩
 ·have aeD : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith
 ·have hreal :
    ∀ᶠ x : ℝ in atTop,
     (Nat.primeCounting (Nat.floor x) : ℝ) ≤
      (Real.log 4 + 1) * x / Real.log x :=
   Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with n hn
  simpa using hn
lemma k9 {m : ℕ} (hm : 1 ≤ m) :
  (1 : ℝ) / (m + 1 : ℕ) ≤
   Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
 have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
 have Ij : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
 have h :=
  Real.one_sub_inv_le_log_of_pos
   (div_pos Ij hmpos)
 rw [Real.log_div Ij.ne' hmpos.ne'] at h
 have hleft :
   1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  field_simp [hmpos.ne', Ij.ne']
  norm_num
 calc
  (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
    = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
  _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h
lemma oA (m : ℕ) :
  (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
   1 + Real.log (m : ℝ) := by
 induction m with
 | zero =>
   simp
 | succ m ih =>
   by_cases hm0 : m = 0
   ·subst m
    simp
   ·have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
    have Xb : m + 1 ∉ Finset.Icc 1 m := by
     simp
    have hIcc :
      Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
     ext k
     simp
     omega
    have hterm := k9 (m := m) hm
    calc
     (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
       = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
         (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          rw [hIcc, Finset.sum_insert Xb]
          ring
     _ ≤ (1 + Real.log (m : ℝ)) +
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
         simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
     _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
         linarith
     _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
         rfl
lemma kL (n : ℕ) :
  ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
 have hset :
   (Finset.Icc 1 n).filter Nat.Prime =
    (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  constructor
  ·intro hp
   rw [Finset.mem_filter] at hp ⊢
   have adi := Finset.mem_Icc.mp hp.1
   exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le adi.2), hp.2⟩
  ·intro hp
   rw [Finset.mem_filter] at hp ⊢
   exact ⟨Finset.mem_Icc.mpr
    ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
 calc
  ((Finset.Icc 1 n).filter Nat.Prime).card
    = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
  _ = Nat.count Nat.Prime (n + 1) := by
     exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
  _ = Nat.primeCounting n := rfl
lemma lO (k : ℕ) :
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ)) ≤
   (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
 classical
 let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
 have n7 : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
 have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
  intro p hp
  simp [S] at hp
  have Xc : 2 ^ k ≤ p := hp.1.1
  have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast Xc
  exact one_div_le_one_div_of_le n7 hlow
 have O4 :
   S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
  rw [← kL]
  refine Finset.card_le_card ?_
  intro p hp
  simp [S] at hp
  rw [Finset.mem_filter]
  have adk := hp.1
  have jM : Nat.Prime p := hp.2
  exact ⟨Finset.mem_Icc.mpr ⟨jM.one_le, adk.2.le⟩, jM⟩
 calc
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ))
    = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
  _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     exact Finset.sum_le_sum hpoint
  _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     exact div_le_div_of_nonneg_right (by exact_mod_cast O4) n7.le
lemma iF
  (B : ℝ) {k : ℕ}
  (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
   B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
    Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ)) ≤
   (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
 have n7 : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
 have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
 calc
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ))
    ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
      ((2 ^ k : ℕ) : ℝ) :=
     lO k
  _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
     Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
      ((2 ^ k : ℕ) : ℝ) := by
     exact div_le_div_of_nonneg_right hπ n7.le
  _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
     have Ve :
       (((2 ^ (k + 1) : ℕ) : ℝ)) =
        (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
      norm_num [pow_succ, mul_comm]
     have Xd :
       Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
      rw [Real.log_pow]
     rw [Xd, Ve]
     field_simp [n7.ne', tK.ne', hkpos.ne']
lemma je :
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
   (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
     (1 : ℝ) / (p : ℝ)) ≤
    D / ((k + 1 : ℕ) : ℝ) := by
 rcases j3 with ⟨B, Om, YQ⟩
 refine ⟨2 * B / Real.log 2, ?_, ?_⟩
 ·positivity
 ·have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
   exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have adl := hpw.eventually YQ
  filter_upwards [adl] with k hk
  exact iF B hk
lemma jG :
  ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
   (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
     (1 : ℝ) / (p : ℝ)) ≤
    D / ((k + 1 : ℕ) : ℝ) := by
 classical
 rcases je with
  ⟨D, XR, YS⟩
 rcases eventually_atTop.1 YS with ⟨K, hK⟩
 let block : ℕ → ℝ := fun k =>
  ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
   (1 : ℝ) / (p : ℝ)
 let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
 refine ⟨D + extra + 1, ?_, ?_⟩
 ·have NU : 0 ≤ extra := by
   refine Finset.sum_nonneg ?_
   intro k hk
   exact mul_nonneg (by positivity)
    (by
     refine Finset.sum_nonneg ?_
     intro p hp
     exact div_nonneg zero_le_one (by positivity))
  linarith
 ·intro k
  have n7 : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  by_cases Dq : K ≤ k
  ·have af2 : D ≤ D + extra + 1 := by
    have NU : 0 ≤ extra := by
     refine Finset.sum_nonneg ?_
     intro j hj
     exact mul_nonneg (by positivity)
      (by
       refine Finset.sum_nonneg ?_
       intro p hp
       exact div_nonneg zero_le_one (by positivity))
    linarith
   calc
    block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k Dq
    _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right af2 n7.le
  ·have hkle : k ≤ K := Nat.le_of_not_ge Dq
   have hk_mem : k ∈ Finset.Icc 0 K := by
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
   have tJ :
     ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
    intro j hj
    exact mul_nonneg (by positivity)
     (by
      refine Finset.sum_nonneg ?_
      intro p hp
      exact div_nonneg zero_le_one (by positivity))
   have nZ :
     ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
    Finset.single_le_sum tJ hk_mem
   have hmul :
     block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
    calc
     block k * ((k + 1 : ℕ) : ℝ)
       = ((k + 1 : ℕ) : ℝ) * block k := by ring
     _ ≤ extra := nZ
     _ ≤ D + extra + 1 := by linarith
   exact (le_div_iff₀ n7).2 hmul
lemma ko
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
 have Vf :
   ∀ k ∈ T,
    (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
      (1 : ℝ) / (p : ℝ)) ≤
     ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) := by
  intro k hk
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  ·intro p hp
   simp [S] at hp ⊢
   have jM : Nat.Prime p := hp.1.2
   have hpne : p ≠ 0 := jM.ne_zero
   have hlog : Nat.log 2 p = k := hp.2
   exact ⟨⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
    by simpa [hlog, Nat.succ_eq_add_one] using
     Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩, jM⟩
  ·intro p hp QX
   exact div_nonneg zero_le_one (by positivity)
 have Rg :
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
  have SO :
    (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
     = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
   rw [Finset.sum_image]
   intro a ha b hb hab
   exact hinj ha hb hab
  calc
   (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
     = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
      exact SO.symm
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
     Finset.sum_le_sum Vf
  _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := Rg
  _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro k hk
     ring
  _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
     rw [hsum_shift]
  _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
     exact mul_le_mul_of_nonneg_left
      (oA (Nat.log 2 N + 1))
      (by
       have hD0 := hD 0
       have LW :
         0 ≤
          (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
           (1 : ℝ) / (p : ℝ)) := by
        refine Finset.sum_nonneg ?_
        intro p hp
        exact div_nonneg zero_le_one (by positivity)
       have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
       nlinarith [hD0, LW])
lemma jS :
  ∀ᶠ N : ℕ in atTop,
   1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
    ≤ 2 * Real.log (Real.log (N : ℝ)) := by
 let C : ℝ := 2 / Real.log 2
 have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hCpos : 0 < C := by positivity
 have NV :
   ∀ᶠ N : ℕ in atTop,
    1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
  iw.eventually_ge_atTop (1 + Real.log C)
 filter_upwards [NV,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N aeE dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have LX : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have aaD : Real.log 2 < 1 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
 have NW : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
 have Vg : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
  have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
   simpa using NW
  exact (le_div_iff₀ tK).2 this
 have W0 :
   ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have h := Real.log2_le_logb N
  simpa [Nat.log2_eq_log_two, Real.logb] using h
 have LY :
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
 have Vh : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
 have adn : 0 < C * Real.log (N : ℝ) := mul_pos hCpos LX
 have SX :
   Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
    ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
  calc
   Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
     ≤ Real.log (C * Real.log (N : ℝ)) :=
      Real.log_le_log Vh LY
   _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
      rw [Real.log_mul hCpos.ne' LX.ne']
 linarith
theorem qv :
  ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
   (((Finset.Icc 1 N).filter Nat.Prime).sum
     (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
    ≤ A * Real.log (Real.log (N : ℝ)) + C := by
 rcases jG with ⟨D, XR, hD⟩
 refine ⟨2 * D, 0, by positivity, ?_⟩
 filter_upwards [jS] with N YV
 calc
  (((Finset.Icc 1 N).filter Nat.Prime).sum
    (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
    ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
     ko D hD N
  _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
     mul_le_mul_of_nonneg_left YV XR.le
  _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring
theorem nT :
  ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
   ∀ y : ℕ, y ≤ N →
    (∑ n ∈ Finset.Icc 1 y, (gd N) ^ omega n)
     ≤ (y : ℝ) *
       Real.exp (gd N *
        (A * Real.log (Real.log (N : ℝ)) + C)) := by
 rcases qv with ⟨A, C, hA, Xf⟩
 refine ⟨A, C, hA, ?_⟩
 filter_upwards [Xf,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N Vi dG
 intro y hy
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have sW : 0 ≤ gd N := by
  rw [gd]
  exact div_nonneg (Real.sqrt_nonneg _) c8.le
 let Py : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
 let PN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
 have SY : Py ⊆ PN := by
  intro p hp
  simp [Py, PN] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hy⟩, hp.2⟩
 have Rh :
   Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
    PN.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg SY
   (by
    intro p hpN aaE
    simp [PN] at hpN
    exact div_nonneg zero_le_one (by exact_mod_cast hpN.2.pos.le))
 have O5 :
   Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
    A * Real.log (Real.log (N : ℝ)) + C := by
  exact Rh.trans (by simpa [PN] using Vi)
 have aaF : ∀ p ∈ Py, 0 < (p : ℝ) := by
  intro p hp
  simp [Py] at hp
  exact_mod_cast hp.2.pos
 have Vk :
   Py.prod (fun p : ℕ => (1 : ℝ) + gd N / (p : ℝ)) ≤
    Real.exp (gd N *
     Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
  j9 Py sW aaF
 have hprod_bound :
   Py.prod (fun p : ℕ => (1 : ℝ) + gd N / (p : ℝ)) ≤
    Real.exp (gd N *
     (A * Real.log (Real.log (N : ℝ)) + C)) := by
  exact Vk.trans
   (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left O5 sW))
 exact (lN y (gd N) sW).trans
  (mul_le_mul_of_nonneg_left (by simpa [Py] using hprod_bound) (by positivity))
lemma kW
  (A C ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   gd N * (A * Real.log (Real.log (N : ℝ)) + C) ≤ ε * aZ N := by
 let R : ℝ := max (4 * (A + 1) / ε) (max 1 |C|)
 filter_upwards [f9 R,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have d6 : 0 ≤ Real.log (N : ℝ) := gC.le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have oO : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
 have ahx : 0 < A + 1 := by linarith
 have SZ : 4 * (A + 1) / ε ≤ R := le_max_left _ _
 have Dr : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
 have Vm : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
 have NY :
   4 * (A + 1) / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  SZ.trans hsqrt
 have aaG : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  Dr.trans hsqrt
 have O6 : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  Vm.trans hsqrt
 have LZ : |C| ≤ Real.log (Real.log (N : ℝ)) := by
  calc
   |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := O6
   _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
   _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt f8
 have S5 :
   2 * (A + 1) ≤
    ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hfour :
    4 * (A + 1) ≤
     ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
   simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (div_le_iff₀ hε).1 NY
  linarith
 have O7 : 0 ≤ gd N := by
  rw [gd]
  exact div_nonneg oO f8
 have S6 :
   A * Real.log (Real.log (N : ℝ)) + C ≤
    (A + 1) * Real.log (Real.log (N : ℝ)) := by
  calc
   A * Real.log (Real.log (N : ℝ)) + C
     ≤ A * Real.log (Real.log (N : ℝ)) + |C| := by
      nlinarith [le_abs_self C]
   _ ≤ A * Real.log (Real.log (N : ℝ)) +
      Real.log (Real.log (N : ℝ)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
       add_le_add_left LZ
        (A * Real.log (Real.log (N : ℝ)))
   _ = (A + 1) * Real.log (Real.log (N : ℝ)) := by ring
 have Ri :
   gd N * (A * Real.log (Real.log (N : ℝ)) + C) ≤
    gd N * ((A + 1) * Real.log (Real.log (N : ℝ))) :=
  mul_le_mul_of_nonneg_left S6 O7
 have aaH := gN c7
 have hbound :
   gd N * ((A + 1) * Real.log (Real.log (N : ℝ))) ≤
    ε * aZ N := by
  rw [gd, aaH]
  calc
   Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
     ((A + 1) * Real.log (Real.log (N : ℝ)))
     = (A + 1) * Real.sqrt (Real.log (N : ℝ)) := by
      field_simp [c8.ne']
   _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
      Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
      calc
       (A + 1) * Real.sqrt (Real.log (N : ℝ))
         ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
           Real.sqrt (Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
             (by linarith [S5]) oO
       _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
          Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
 exact Ri.trans hbound
theorem pQ :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y : ℕ, y ≤ N →
    (∑ n ∈ Finset.Icc 1 y, (gd N) ^ omega n)
     ≤ (y : ℝ) * Real.exp (ε * aZ N) := by
 intro ε hε
 rcases nT with ⟨A, C, hA, hC⟩
 filter_upwards [hC, kW A C ε hA hε]
  with N Vq cQ y hy
 have Wz :
   Real.exp (gd N * (A * Real.log (Real.log (N : ℝ)) + C)) ≤
    Real.exp (ε * aZ N) :=
  Real.exp_le_exp.2 cQ
 exact (Vq y hy).trans
  (mul_le_mul_of_nonneg_left Wz (by positivity))
end dO
namespace dO
open Filter Finset
open scoped BigOperators
lemma qK {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
  (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
 (Nat.le_floor_iff hx).2 hm
lemma tL (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
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
     intro n aiP ab7
     exact pow_nonneg hz0 (omega n)
lemma m6
  (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
  (Xg : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
  (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
   ≤ (y : ℝ) * B / z ^ t := by
 classical
 have Vr : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
 have htail := tL y t hz
 have WA : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
   ≤ (y : ℝ) * B :=
  htail.trans Xg
 exact (le_div_iff₀ Vr).2 WA
lemma lZ
  (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
  (hX : 0 ≤ X)
  (Xg : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
  (N5 : (y : ℝ) * B / z ^ t ≤ X) :
  ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
 refine qK hX ?_
 exact (m6 y t hz Xg).trans N5
private lemma kM :
  Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
    Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
 have hreal :
   Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
  have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
    fun x : ℝ => Real.log x :=
   Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact hsmall.tendsto_div_nhds_zero
 exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
private lemma l6
  (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ N : ℕ in atTop,
   Real.log (Real.log (Real.log (N : ℝ))) ≤
    δ * Real.log (Real.log (N : ℝ)) := by
 have hsmall :
   ∀ᶠ N : ℕ in atTop,
    Real.log (Real.log (Real.log (N : ℝ))) /
     Real.log (Real.log (N : ℝ)) < δ :=
  kM.eventually_lt_const hδ
 filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
  with N YZ dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 exact ((div_lt_iff₀ c8).1 YZ).le
private lemma kB {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < gd N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [gd]
 exact div_pos (Real.sqrt_pos.2 gC) c8
private lemma kP
  (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ N : ℕ in atTop,
   ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (gd N) := by
 filter_upwards [l6 δ hδ,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N alB dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have d6 : 0 ≤ Real.log (N : ℝ) := gC.le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have MY : 0 < Real.sqrt (Real.log (N : ℝ)) :=
  Real.sqrt_pos.2 gC
 have Vt :
   Real.log (gd N) =
    Real.log (Real.log (N : ℝ)) / 2 -
     Real.log (Real.log (Real.log (N : ℝ))) := by
  rw [gd, Real.log_div MY.ne' c8.ne',
   Real.log_sqrt d6]
 rw [Vt]
 nlinarith
private lemma wO :
  ∀ᶠ N : ℕ in atTop, 1 ≤ gd N := by
 filter_upwards [kP ((1 : ℝ) / 4) (by norm_num),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N JX dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have hzpos : 0 < gd N := kB c7
 have d6 : 0 ≤ Real.log (gd N) := by
  nlinarith
 have hone : Real.exp 0 ≤ gd N :=
  (Real.le_log_iff_exp_le hzpos).1 d6
 simpa using hone
private lemma qL
  (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   ∀ t : ℕ, (t : ℝ) ≤ 3 * aO N →
    Real.exp ((ε / 2) * aZ N) / (gd N) ^ t
     ≤ Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N) := by
 let δ : ℝ := ε / 6
 have hδ : 0 < δ := by dsimp [δ]; positivity
 filter_upwards [kP δ hδ,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N JX dG t ht
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hMpos : 0 < aO N := g5 c7
 have O8 : 0 ≤ aZ N := nD N
 have hzpos : 0 < gd N := kB c7
 have hLL :
   Real.log (Real.log (N : ℝ)) = aZ N / aO N :=
  (j4 c7).symm
 have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
 have af3 :
   (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
    ≤ (t : ℝ) * Real.log (gd N) :=
  mul_le_mul_of_nonneg_left JX ht_nonneg
 have Vv : (t : ℝ) / aO N ≤ 3 := by
  exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
 have S7 : δ * ((t : ℝ) / aO N) ≤ ε / 2 := by
  calc
   δ * ((t : ℝ) / aO N) ≤ δ * 3 := by
    exact mul_le_mul_of_nonneg_left Vv hδ.le
   _ = ε / 2 := by
    dsimp [δ]
    ring
 have Y0 :
   (ε / 2) * aZ N - (t : ℝ) * Real.log (gd N)
    ≤ (-((t : ℝ) / aO N) / 2 + ε) * aZ N := by
  have hmain :
    (ε / 2) * aZ N -
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
     ≤ (-((t : ℝ) / aO N) / 2 + ε) * aZ N := by
   rw [hLL]
   have ahy :
     (δ * ((t : ℝ) / aO N)) * aZ N ≤ (ε / 2) * aZ N :=
    mul_le_mul_of_nonneg_right S7 O8
   have nU :
     (t : ℝ) * (((1 : ℝ) / 2 - δ) * (aZ N / aO N)) =
      (((1 : ℝ) / 2 - δ) * ((t : ℝ) / aO N)) * aZ N := by
    field_simp [hMpos.ne']
   rw [nU]
   nlinarith
  nlinarith
 have ado :
   (gd N) ^ t = Real.exp ((t : ℝ) * Real.log (gd N)) := by
  calc
   (gd N) ^ t = (Real.exp (Real.log (gd N))) ^ t := by
    rw [Real.exp_log hzpos]
   _ = Real.exp ((t : ℝ) * Real.log (gd N)) := by
    rw [← Real.exp_nat_mul]
 rw [ado, ← Real.exp_sub]
 exact Real.exp_le_exp.2 Y0
theorem wP :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * aO N →
    let α : ℝ := (t : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-α / 2 + ε) * aZ N)) := by
 intro ε hε
 have hε2 : 0 < ε / 2 := by positivity
 filter_upwards [pQ (ε / 2) hε2,
   qL ε hε, wO]
  with N MZ RU O9
 intro y t hy ht
 dsimp only
 refine lZ (y := y) (t := t)
  (z := gd N) (B := Real.exp ((ε / 2) * aZ N))
  (X := (y : ℝ) *
   Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N))
  O9 ?_ (MZ y hy) ?_
 ·positivity
 ·have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
  calc
   (y : ℝ) * Real.exp ((ε / 2) * aZ N) / (gd N) ^ t
     = (y : ℝ) *
       (Real.exp ((ε / 2) * aZ N) / (gd N) ^ t) := by
       ring
   _ ≤ (y : ℝ) *
       Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N) := by
       exact mul_le_mul_of_nonneg_left (RU t ht) hy_nonneg
end dO
namespace dO
open Filter Finset
open scoped BigOperators
end dO
namespace dO
open Filter Finset
open scoped BigOperators
end dO
namespace dO
open Filter Finset
end dO
namespace dO
open Filter Finset
end dO
namespace dO
open Filter Finset
open Asymptotics
open scoped BigOperators
lemma zP {N : ℕ}
  (c7 : Real.exp 1 < (N : ℝ)) :
  aZ N =
   Real.exp (Real.log (Real.log (N : ℝ)) / 2) *
    Real.sqrt (Real.log (Real.log (N : ℝ))) := by
 set Y := Real.log (Real.log (N : ℝ))
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have hlog_eq : Real.log (N : ℝ) = Real.exp Y := by
  dsimp [Y]
  rw [Real.exp_log gC]
 have aeF :
   Real.sqrt (Real.log (N : ℝ)) = Real.exp (Y / 2) := by
  rw [hlog_eq, ← Real.exp_half]
 rw [gN c7, aeF]
end dO
namespace dO
open Filter Finset
open scoped BigOperators
end dO
namespace dO
open Filter
end dO
namespace dO
open Filter Finset
open scoped BigOperators
structure bC (N : ℕ) where
 Q : Finset ℕ
 z6 : Q.Nonempty
 a : gJ Q
 admissible : Admissible N Q
 pairwise_disjoint : d7 Q a
 K : ℕ
 K_pos : 1 ≤ K
 Bk : ∀ q ∈ Q, (N : ℝ) * bF (-2) N ≤ (q : ℝ)
 q6 : ∀ q ∈ Q, q ≤ N
 Ee : ∀ q ∈ Q, (cQ q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
 L9 : ∀ q ∈ Q, omega q = K
 yD : (K : ℝ) ≤ 3 * aO N
 Bm : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r
lemma bC.card_pos {N : ℕ} (D : bC N) : 0 < D.Q.card :=
 D.z6.card_pos
end dO
namespace dO
open Filter Finset
open scoped BigOperators
end dO
namespace dO
open Finset
open scoped BigOperators
lemma Oo {α : Type*} [DecidableEq α]
  (Q Bad : Finset α) {δ : ℝ}
  (af4 : Bad ⊆ Q)
  (hsmall : (Bad.card : ℝ) ≤ δ * (Q.card : ℝ)) :
  (((Q \ Bad).card : ℝ) ≥ (1 - δ) * (Q.card : ℝ)) := by
 have hreal : ((Q \ Bad).card : ℝ) = (Q.card : ℝ) - (Bad.card : ℝ) := by
  simpa using (Finset.cast_card_sdiff (R := ℝ) af4)
 rw [hreal]
 nlinarith
lemma Jv {α : Type*} [DecidableEq α]
  (Q J4 J6 Ka : Finset α) {δ₁ δ₂ δ₃ : ℝ}
  (akt : J4 ⊆ Q) (aku : J6 ⊆ Q) (akv : Ka ⊆ Q)
  (amv : (J4.card : ℝ) ≤ δ₁ * (Q.card : ℝ))
  (amw : (J6.card : ℝ) ≤ δ₂ * (Q.card : ℝ))
  (amx : (Ka.card : ℝ) ≤ δ₃ * (Q.card : ℝ)) :
  (((Q \ (J4 ∪ J6 ∪ Ka)).card : ℝ) ≥
   (1 - (δ₁ + δ₂ + δ₃)) * (Q.card : ℝ)) := by
 have af4 : J4 ∪ J6 ∪ Ka ⊆ Q := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx12 | hx3
  ·rcases Finset.mem_union.1 hx12 with hx1 | hx2
   ·exact akt hx1
   ·exact aku hx2
  ·exact akv hx3
 refine Oo Q (J4 ∪ J6 ∪ Ka) af4 ?_
 have vY :
   (J4 ∪ J6 ∪ Ka).card ≤ J4.card + J6.card + Ka.card := by
  calc
   (J4 ∪ J6 ∪ Ka).card
     ≤ (J4 ∪ J6).card + Ka.card := Finset.card_union_le _ _
   _ ≤ (J4.card + J6.card) + Ka.card := by
      exact Nat.add_le_add_right (Finset.card_union_le J4 J6) Ka.card
   _ = J4.card + J6.card + Ka.card := by omega
 have qC :
   ((J4 ∪ J6 ∪ Ka).card : ℝ) ≤
    (J4.card : ℝ) + (J6.card : ℝ) + (Ka.card : ℝ) := by
  exact_mod_cast vY
 nlinarith
lemma Eh {α β : Type*} [DecidableEq β]
  (s : Finset α) (B : Finset β) (g : α → β)
  (Xh : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
  ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
 classical
 rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) Xh with
  ⟨b, hb, hbmax⟩
 refine ⟨b, hb, ?_⟩
 have hsum :
   s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
  exact Finset.card_eq_sum_card_fiberwise hB
 have Ej :
   (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
    ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
  exact Finset.sum_le_sum hbmax
 rw [hsum]
 exact Ej.trans (by simp)
noncomputable def kH {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) : Finset α :=
 ((s.image g).attach.image fun b =>
  Classical.choose (Finset.mem_image.1 b.2))
lemma Pd {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) :
  kH s g ⊆ s := by
 classical
 intro x hx
 unfold kH at hx
 rw [Finset.mem_image] at hx
 rcases hx with ⟨b, -, rfl⟩
 exact (Classical.choose_spec (Finset.mem_image.1 b.2)).1
lemma qE {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) {b : β} (hb : b ∈ s.image g) :
  g (Classical.choose (Finset.mem_image.1 hb)) = b := by
 exact (Classical.choose_spec (Finset.mem_image.1 hb)).2
lemma Qy {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) :
  ∀ x ∈ kH s g, ∀ y ∈ kH s g, g x = g y → x = y := by
 classical
 intro x hx y hy hxy
 unfold kH at hx hy
 rw [Finset.mem_image] at hx
 rw [Finset.mem_image] at hy
 rcases hx with ⟨bx, hbx, rfl⟩
 rcases hy with ⟨byy, hby, rfl⟩
 have aiR : g (Classical.choose (Finset.mem_image.1 bx.2)) = bx.1 := by
  exact qE s g bx.2
 have aiS : g (Classical.choose (Finset.mem_image.1 byy.2)) = byy.1 := by
  exact qE s g byy.2
 have alC : bx = byy := by
  ext
  simpa [aiR, aiS] using hxy
 subst alC
 rfl
lemma Ds {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) :
  (kH s g).card = (s.image g).card := by
 classical
 unfold kH
 calc
  (((s.image g).attach.image fun b =>
    Classical.choose (Finset.mem_image.1 b.2))).card =
    (s.image g).attach.card := by
     apply Finset.card_image_of_injective
     intro b₁ b₂ h
     have hb₁ : g (Classical.choose (Finset.mem_image.1 b₁.2)) = b₁.1 :=
      qE s g b₁.2
     have hb₂ : g (Classical.choose (Finset.mem_image.1 b₂.2)) = b₂.1 :=
      qE s g b₂.2
     ext
     simpa [hb₁, hb₂] using congrArg g h
  _ = (s.image g).card := by simp
lemma K8 {α β : Type*} [DecidableEq β]
  (s : Finset α) (g : α → β) (C : ℕ)
  (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
  s.card ≤ C * (s.image g).card := by
 classical
 exact Finset.card_le_mul_card_image s C hC
lemma Jw {α β : Type*} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (g : α → β) (C : ℕ)
  (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
  ∃ s' : Finset α,
   s' ⊆ s ∧
   (∀ x ∈ s', ∀ y ∈ s', g x = g y → x = y) ∧
   s.card ≤ C * s'.card := by
 classical
 refine ⟨kH s g, Pd s g,
  Qy s g, ?_⟩
 simpa [Ds s g] using
  K8 s g C hC
end dO
namespace dO
open Finset
open scoped BigOperators
lemma Jm (H : ℕ) :
  (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
 have Y1 : ∀ H : ℕ, 1 ≤ H →
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
 ·simp [hH]
 ·have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
  exact (Y1 H hH1).trans (by
   have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
   linarith)
private lemma Qz {ι : Type*} [Fintype ι] (f : ι → ℕ) :
  (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
   ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
 simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]
lemma ahz (n : ℕ) : 0 < rad n := by
 unfold rad
 exact Finset.prod_pos (fun p hp => (f7 hp).pos)
lemma ab8 (n : ℕ) : rad n ≠ 0 :=
 (ahz n).ne'
lemma M4 {n : ℕ} (_hn : n ≠ 0) :
  aD (rad n) = aD n := by
 classical
 ext p
 constructor
 ·intro adp
  have hp : Nat.Prime p := f7 adp
  have hpdvd : p ∣ rad n := Nat.dvd_of_factorization_pos (by
   unfold aD at adp
   exact Finsupp.mem_support_iff.1 adp)
  unfold rad at hpdvd
  rcases (hp.prime.dvd_finset_prod_iff
    (S := aD n) (fun x : ℕ => x)).1 hpdvd with ⟨q, hq, hpq⟩
  have hqprime : Nat.Prime q := f7 hq
  have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).1 hpq
  simpa [hqp] using hq
 ·intro hpN
  have hp : Nat.Prime p := f7 hpN
  have hpdvd : p ∣ rad n := by
   unfold rad
   exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hpN
  exact k6 hp (ab8 n) hpdvd
lemma Oq {q r : ℕ} (hq : q ≠ 0) (hqr : rad q = r) :
  aD q = aD r := by
 rw [← M4 hq, hqr]
private lemma Mb {q p : ℕ} (hp : p ∈ aD q) :
  q.factorization p ≤ cQ q := by
 have hdvd : q.factorization p ∣ cQ q := by
  unfold cQ
  exact Finset.dvd_prod_of_mem (fun x : ℕ => q.factorization x) hp
 exact Nat.le_of_dvd (Dp q) hdvd
private lemma Kd
  (S : Finset ℕ) (C : Finset ℕ) (H : ℝ)
  (hH : 1 ≤ H)
  (Ek : ∀ q ∈ S, q ≠ 0)
  (Ot : ∀ q ∈ S, aD q = C)
  (Mc : ∀ q ∈ S, (cQ q : ℝ) ≤ H) :
  (∑ q ∈ S, (1 : ℝ) / ((cQ q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ C.card := by
 classical
 let Index := {p : ℕ // p ∈ C}
 let E : Finset (Index → ℕ) :=
  Fintype.piFinset fun _ : Index => Finset.range (Nat.floor H)
 let vec : ℕ → Index → ℕ := fun q p => q.factorization p.1 - 1
 let term : (Index → ℕ) → ℝ :=
  fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
 have Vw : 0 ≤ H := by
  linarith
 have Xj : ∀ q ∈ S, vec q ∈ E := by
  intro q ZK
  rw [Fintype.mem_piFinset]
  intro p
  rw [Finset.mem_range]
  have hsupport : aD q = C := Ot q ZK
  have gX : p.1 ∈ aD q := by
   simp [hsupport, p.2]
  have aaI : 1 ≤ q.factorization p.1 := by
   unfold aD at gX
   exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
  have aaJ : q.factorization p.1 ≤ cQ q :=
   Mb gX
  have aeG : ((q.factorization p.1 : ℕ) : ℝ) ≤ H := by
   have WK :
     ((q.factorization p.1 : ℕ) : ℝ) ≤ (cQ q : ℝ) := by
    exact_mod_cast aaJ
   exact WK.trans (Mc q ZK)
  have akw : q.factorization p.1 ≤ Nat.floor H :=
   (Nat.le_floor_iff Vw).2 aeG
  dsimp [vec]
  omega
 have Xk : Set.InjOn vec S := by
  intro q ZK q' af5 hqq'
  apply Nat.eq_of_factorization_eq (Ek q ZK) (Ek q' af5)
  intro p
  by_cases hp : p ∈ C
  ·have aaK := congrFun hqq' ⟨p, hp⟩
   dsimp [vec] at aaK
   have hsupport : aD q = C := Ot q ZK
   have hsupport' : aD q' = C := Ot q' af5
   have aaI : 1 ≤ q.factorization p := by
    have gX : p ∈ aD q := by simpa [hsupport] using hp
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   have alf : 1 ≤ q'.factorization p := by
    have gX : p ∈ aD q' := by simpa [hsupport'] using hp
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   omega
  ·have hpq : p ∉ aD q := by simpa [Ot q ZK] using hp
   have hpq' : p ∉ aD q' := by simpa [Ot q' af5] using hp
   rw [Finsupp.notMem_support_iff.1 hpq, Finsupp.notMem_support_iff.1 hpq']
 have Xl :
   ∀ q ∈ S, (1 : ℝ) / ((cQ q : ℝ) ^ 2) = term (vec q) := by
  intro q ZK
  have hsupport : aD q = C := Ot q ZK
  have adq :
    cQ q = ∏ p : Index, q.factorization p.1 := by
   calc
    cQ q = ∏ p ∈ C, q.factorization p := by
     simp [cQ, hsupport]
    _ = ∏ p : Index, q.factorization p.1 := by
     rw [Finset.prod_coe_sort]
  have hsucc : ∀ p : Index, vec q p + 1 = q.factorization p.1 := by
   intro p
   have gX : p.1 ∈ aD q := by simp [hsupport, p.2]
   have hpos : 1 ≤ q.factorization p.1 := by
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   dsimp [vec]
   omega
  rw [adq, Qz]
  dsimp [term]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [hsucc p]
 calc
  (∑ q ∈ S, (1 : ℝ) / ((cQ q : ℝ) ^ 2))
    = ∑ q ∈ S, term (vec q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Xl q hq
  _ = ∑ e ∈ S.image vec, term e := by
      rw [Finset.sum_image]
      intro q hq q' hq' hEq
      exact Xk hq hq' hEq
  _ ≤ ∑ e ∈ E, term e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
       (by
        intro e he
        rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
        exact Xj q hq)
       (by
        intro e alD aiU
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
        exact Jm (Nat.floor H))
  _ = (2 : ℝ) ^ C.card := by
      simp [Index]
theorem Rj
  (S : Finset ℕ) (r K : ℕ) (H : ℝ)
  (hH : 1 ≤ H)
  (Ek : ∀ q ∈ S, q ≠ 0)
  (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (cQ q : ℝ) ≤ H) :
  (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K := by
 classical
 by_cases hSne : S.Nonempty
 ·rcases hSne with ⟨q0, aiV⟩
  let C : Finset ℕ := aD r
  have Ot : ∀ q ∈ S, aD q = C := by
   intro q hq
   exact Oq (Ek q hq) (hS q hq).1
  have aiW : C.card = K := by
   have yF := (hS q0 aiV).2.1
   unfold omega at yF
   rw [Ot q0 aiV] at yF
   exact yF
  have MZ :
    (∑ q ∈ S, (1 : ℝ) / ((cQ q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ K := by
   simpa [C, aiW] using
    Kd S C H hH Ek Ot
     (fun q hq => (hS q hq).2.2)
  have aaw : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have aaL : 0 < H ^ 2 := by positivity
  have adr :
    ∀ q ∈ S, (1 : ℝ) / (H ^ 2) ≤
     (1 : ℝ) / ((cQ q : ℝ) ^ 2) := by
   intro q hq
   have akj : 0 ≤ (cQ q : ℝ) := by positivity
   have Dp : 0 < (cQ q : ℝ) := by exact_mod_cast Dp q
   have Wz : (cQ q : ℝ) ≤ H := (hS q hq).2.2
   have aiX : (cQ q : ℝ) ^ 2 ≤ H ^ 2 := by
    nlinarith [sq_nonneg (H - (cQ q : ℝ))]
   exact one_div_le_one_div_of_le (by positivity) aiX
  have ab9 :
    (S.card : ℝ) * ((1 : ℝ) / (H ^ 2)) ≤ (2 : ℝ) ^ K := by
   calc
    (S.card : ℝ) * ((1 : ℝ) / (H ^ 2))
      = ∑ _q ∈ S, ((1 : ℝ) / (H ^ 2)) := by
        simp
    _ ≤ ∑ q ∈ S, (1 : ℝ) / ((cQ q : ℝ) ^ 2) := by
        exact Finset.sum_le_sum adr
    _ ≤ (2 : ℝ) ^ K := MZ
  have hmul := mul_le_mul_of_nonneg_right ab9 aaL.le
  field_simp [aaL.ne'] at hmul
  nlinarith
 ·have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSne
  have hnonneg : 0 ≤ H ^ 2 * (2 : ℝ) ^ K := by positivity
  simpa [hEmpty] using hnonneg
end dO
namespace dO
open Filter Finset
open scoped BigOperators
noncomputable def eW (N : ℕ) : ℝ :=
 Real.exp (Real.sqrt (Real.log (N : ℝ)))
lemma Y3 {p e : ℕ} (hp : Nat.Prime p) :
  cQ (p ^ e) = if e = 0 then 1 else e := by
 by_cases he : e = 0
 ·simp [he, SK]
 ·unfold cQ aD
  rw [hp.factorization_pow]
  rw [Finsupp.support_single_ne_zero p he]
  rw [if_neg he]
  change (∏ q ∈ ({p} : Finset ℕ), Finsupp.single p e q) = e
  simp
noncomputable def iJ (s n : ℕ) : ℝ :=
 if n = 0 then 0 else (cQ n : ℝ) ^ s / (n : ℝ)
lemma RV (s n : ℕ) :
  0 ≤ iJ s n := by
 by_cases hn : n = 0
 ·simp [iJ, hn]
 ·have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp [iJ, hn]
  exact div_nonneg (by positivity) hnpos.le
lemma Dt (s : ℕ) : iJ s 1 = 1 := by
 simp [iJ, SK]
lemma Pe {s p e : ℕ} (hp : Nat.Prime p) :
  iJ s (p ^ e) =
   if e = 0 then 1 else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
 by_cases he : e = 0
 ·rw [he, pow_zero, Dt]
  simp
 ·simp [iJ, Y3 hp, he, hp.ne_zero, Nat.cast_pow]
lemma Lb
  (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
  iJ s (m * n) =
   iJ s m * iJ s n := by
 by_cases hmn : m * n = 0
 ·rcases hcop.eq_of_mul_eq_zero hmn with h | h
  ·rcases h with ⟨hm, hn⟩
   simp [iJ, hm, hn]
  ·rcases h with ⟨hm, hn⟩
   simp [iJ, hm, hn]
 ·have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  have aiY : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have aiZ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [iJ, hmn, hm, hn, u6 hcop,
   Nat.cast_mul, mul_pow]
  field_simp [aiY, aiZ]
def jo (n : ℕ) : Finset ℕ :=
 (aD n).filter fun p => 2 ≤ n.factorization p
def jI (n : ℕ) : ℕ :=
 cD (jo n) n
def d9 (n : ℕ) : Prop :=
 ∀ p ∈ aD n, 2 ≤ n.factorization p
instance YN : DecidablePred d9 := by
 intro n
 unfold d9
 infer_instance
lemma tM (n : ℕ) :
  jo n ⊆ aD n := by
 intro p hp
 exact (Finset.mem_filter.1 hp).1
lemma oP {n p : ℕ}
  (hp : p ∈ jo n) : Nat.Prime p :=
 f7 (tM n hp)
lemma S8 (n : ℕ) : jI n ∣ n := by
 simp [jI, Eb]
lemma xB {n : ℕ} :
  aD (jI n) = jo n := by
 by_cases hn : n = 0
 ·simp [jI, jo, aD, cD, hn]
 ·exact vG
   (fun p hp => oP hp)
   (tM n)
lemma Lc (n : ℕ) :
  d9 (jI n) := by
 intro p hp
 rw [xB] at hp
 have hp' := Finset.mem_filter.1 hp
 change 2 ≤ (cD (jo n) n).factorization p
 rw [kC
  (C := jo n)
  (q := n)
  (p := p)
  (fun r hr => oP hr)
  hp]
 exact hp'.2
lemma oB {m n : ℕ}
  (hcop : Nat.Coprime m n) :
  d9 (m * n) ↔ d9 m ∧ d9 n := by
 constructor
 ·intro hmn
  constructor
  ·intro p hp
   have hp_prod : p ∈ aD (m * n) := by
    rw [g9 hcop]
    exact Finset.mem_union_left _ hp
   have htwo := hmn p hp_prod
   have lK : p ∉ aD n :=
    (Finset.disjoint_left.1 (dL hcop)) hp
   have hnzero : n.factorization p = 0 := by
    unfold aD at lK
    exact Finsupp.notMem_support_iff.1 lK
   rw [Nat.factorization_mul_of_coprime hcop] at htwo
   simpa [Finsupp.add_apply, hnzero] using htwo
  ·intro p hp
   have hp_prod : p ∈ aD (m * n) := by
    rw [g9 hcop]
    exact Finset.mem_union_right _ hp
   have htwo := hmn p hp_prod
   have lK : p ∉ aD m :=
    (Finset.disjoint_left.1 (dL hcop).symm) hp
   have hmzero : m.factorization p = 0 := by
    unfold aD at lK
    exact Finsupp.notMem_support_iff.1 lK
   rw [Nat.factorization_mul_of_coprime hcop] at htwo
   simpa [Finsupp.add_apply, hmzero] using htwo
 ·rintro ⟨hm, hn⟩ p hp
  rw [g9 hcop] at hp
  rw [Nat.factorization_mul_of_coprime hcop]
  rcases Finset.mem_union.1 hp with hp | hp
  ·have lK : p ∉ aD n :=
    (Finset.disjoint_left.1 (dL hcop)) hp
   have hnzero : n.factorization p = 0 := by
    unfold aD at lK
    exact Finsupp.notMem_support_iff.1 lK
   simpa [Finsupp.add_apply, hnzero] using hm p hp
  ·have lK : p ∉ aD m :=
    (Finset.disjoint_left.1 (dL hcop).symm) hp
   have hmzero : m.factorization p = 0 := by
    unfold aD at lK
    exact Finsupp.notMem_support_iff.1 lK
   simpa [Finsupp.add_apply, hmzero, add_comm] using hn p hp
lemma Pq (n : ℕ) :
  cQ (jI n) = cQ n := by
 by_cases hn : n = 0
 ·simp [jI, jo, aD, cD, cQ, hn]
 ·unfold cQ
  rw [xB]
  have hprod :
    (∏ p ∈ aD n, n.factorization p) =
     ∏ p ∈ jo n, n.factorization p := by
   refine (Finset.prod_subset (tM n) ?_).symm
   intro p jM XO
   have hpos : 1 ≤ n.factorization p := by
    unfold aD at jM
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero
     (Finsupp.mem_support_iff.1 jM))
   have alE : ¬ 2 ≤ n.factorization p := by
    intro htwo
    exact XO (Finset.mem_filter.2 ⟨jM, htwo⟩)
   omega
  rw [hprod]
  apply Finset.prod_congr rfl
  intro p hp
  change (cD (jo n) n).factorization p =
   n.factorization p
  rw [kC
   (C := jo n)
   (q := n)
   (p := p)
   (fun r hr => oP hr)
   hp]
lemma Ld {n : ℕ} (hn : n ≠ 0) :
  jI n ∈ n.divisors := by
 exact Nat.mem_divisors.2
  ⟨S8 n, hn⟩
lemma Fk (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
  (cQ n : ℝ) ^ s ≤
   ∑ d ∈ n.divisors.filter d9, (cQ d : ℝ) ^ s := by
 classical
 have hmem :
   jI n ∈ n.divisors.filter d9 := by
  exact Finset.mem_filter.2
   ⟨Ld hn, Lc n⟩
 have hterm :
   (cQ (jI n) : ℝ) ^ s = (cQ n : ℝ) ^ s := by
  rw [Pq]
 calc
  (cQ n : ℝ) ^ s = (cQ (jI n) : ℝ) ^ s := hterm.symm
  _ ≤ ∑ d ∈ n.divisors.filter d9, (cQ d : ℝ) ^ s :=
    Finset.single_le_sum
     (fun d _hd => pow_nonneg (by positivity : 0 ≤ (cQ d : ℝ)) s)
     hmem
lemma Dv (s e : ℕ) :
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
lemma M5 :
  Real.exp ((1 : ℝ) / 4) < 3 / 2 := by
 have s8 : Real.exp ((1 : ℝ) / 4) ^ 4 < ((3 : ℝ) / 2) ^ 4 := by
  calc
   Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
   _ < 3 := Real.exp_one_lt_three
   _ < ((3 : ℝ) / 2) ^ 4 := by norm_num
 by_contra hnot
 have hge : (3 : ℝ) / 2 ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
 have ahA :
   ((3 : ℝ) / 2) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
  pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2) hge 4
 exact not_lt_of_ge ahA s8
lemma Pv
  (N s : ℕ) {H : ℝ} (hH : 0 ≤ H) :
  (((Finset.Icc 1 N).filter fun n => H < (cQ n : ℝ)).card : ℝ) * H ^ s
   ≤ ∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s := by
 classical
 let Bad := (Finset.Icc 1 N).filter fun n => H < (cQ n : ℝ)
 have hpoint :
   ∀ n ∈ Bad, H ^ s ≤ (cQ n : ℝ) ^ s := by
  intro n hn
  exact pow_le_pow_left₀ hH (le_of_lt (Finset.mem_filter.1 hn).2) s
 calc
  (((Finset.Icc 1 N).filter fun n => H < (cQ n : ℝ)).card : ℝ) * H ^ s
    = ∑ n ∈ Bad, H ^ s := by
      simp [Bad, mul_comm]
  _ ≤ ∑ n ∈ Bad, (cQ n : ℝ) ^ s := by
      exact Finset.sum_le_sum (fun n hn => hpoint n hn)
  _ ≤ ∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
       (Finset.filter_subset _ _)
       (by
        intro n _hn QX
        positivity)
lemma r5 (N s : ℕ) :
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s) ≤
   ∑ d ∈ Finset.Icc 1 N,
    if d9 d then
     (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
      (cQ d : ℝ) ^ s
    else 0 := by
 classical
 calc
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s)
    ≤ ∑ n ∈ Finset.Icc 1 N,
      ∑ d ∈ n.divisors.filter d9, (cQ d : ℝ) ^ s := by
     refine Finset.sum_le_sum ?_
     intro n hn
     have hnIcc := Finset.mem_Icc.mp hn
     exact Fk s
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
  _ ≤ ∑ n ∈ Finset.Icc 1 N,
      ∑ d ∈ (Finset.Icc 1 N).filter
        (fun d => d ∣ n ∧ d9 d),
       (cQ d : ℝ) ^ s := by
     refine Finset.sum_le_sum ?_
     intro n hn
     refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
     ·intro d hd
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
      have Ec : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hnIcc := Finset.mem_Icc.mp hn
      have aaB : d ≤ N :=
       (Nat.le_of_dvd
        (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt Ec, aaB⟩,
       hdn, hd.2⟩
     ·intro d _hd QX
      positivity
  _ = ∑ d ∈ Finset.Icc 1 N,
     if d9 d then
      (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
       (cQ d : ℝ) ^ s
     else 0 := by
     simp_rw [Finset.sum_filter]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro d hd
     by_cases hsq : d9 d
     ·simp [hsq]
      calc
       (∑ x ∈ Finset.Icc 1 N,
         if d ∣ x then (cQ d : ℝ) ^ s else 0)
         = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
           (cQ d : ℝ) ^ s := by
          rw [Finset.sum_filter]
       _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
          (cQ d : ℝ) ^ s := by
          simp [Finset.sum_const, nsmul_eq_mul]
     ·simp [hsq]
lemma Bp (N s : ℕ) :
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s) ≤
   (N : ℝ) *
    ∑ d ∈ Finset.Icc 1 N,
     if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0 := by
 classical
 calc
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s)
    ≤ ∑ d ∈ Finset.Icc 1 N,
      if d9 d then
       (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
        (cQ d : ℝ) ^ s
      else 0 :=
     r5 N s
  _ ≤ ∑ d ∈ Finset.Icc 1 N,
     if d9 d then
      ((N : ℝ) / (d : ℝ)) * (cQ d : ℝ) ^ s
     else 0 := by
     refine Finset.sum_le_sum ?_
     intro d hd
     by_cases hsq : d9 d
     ·simp [hsq]
      have nJ := Finset.mem_Icc.mp hd
      have Ec : 0 < d := lt_of_lt_of_le Nat.zero_lt_one nJ.1
      have vY :
        ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
       exact nI N d Ec
      have qC :
        (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
         (N : ℝ) / (d : ℝ) := by
       exact (Nat.cast_le.mpr vY).trans Nat.cast_div_le
      exact mul_le_mul_of_nonneg_right qC (by positivity)
     ·simp [hsq]
  _ = ∑ d ∈ Finset.Icc 1 N,
     (N : ℝ) *
      (if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0) := by
     apply Finset.sum_congr rfl
     intro d hd
     by_cases hsq : d9 d
     ·simp [hsq]
      have nJ := Finset.mem_Icc.mp hd
      have SM : (d : ℝ) ≠ 0 := by
       exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one nJ.1))
      field_simp [SM]
     ·simp [hsq]
  _ = (N : ℝ) *
     ∑ d ∈ Finset.Icc 1 N,
      if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0 := by
     rw [Finset.mul_sum]
noncomputable def cw (s n : ℕ) : ℝ :=
 if d9 n then iJ s n else 0
lemma zW (s n : ℕ) :
  0 ≤ cw s n := by
 unfold cw
 by_cases hsq : d9 n <;> simp [hsq, RV]
lemma Pw : d9 1 := by
 intro p hp
 simp [aD] at hp
lemma Dw (s : ℕ) :
  cw s 1 = 1 := by
 simp [cw, Pw, Dt]
lemma Rk {p : ℕ} (hp : Nat.Prime p) :
  ¬ d9 p := by
 intro hsq
 have hmem : p ∈ aD p := by
  unfold aD
  rw [Finsupp.mem_support_iff]
  exact Nat.Prime.factorization_self hp ▸ one_ne_zero
 have htwo := hsq p hmem
 rw [Nat.Prime.factorization_self hp] at htwo
 omega
lemma oQ {s p e : ℕ} (hp : Nat.Prime p) :
  cw s (p ^ e) =
   if e = 0 then 1
   else if e = 1 then 0
   else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
 by_cases he0 : e = 0
 ·subst e
  simp [cw, Pw, Dt]
 ·by_cases he1 : e = 1
  ·subst e
   simp [cw, Rk hp]
  ·have hsq : d9 (p ^ e) := by
    intro q hq
    have hqprime : Nat.Prime q := f7 hq
    have hqeq : q = p := by
     have ac3 : (p ^ e).factorization q ≠ 0 := by
      unfold aD at hq
      exact Finsupp.mem_support_iff.1 hq
     rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
      nsmul_eq_mul] at ac3
     have ai0 : p.factorization q ≠ 0 := by
      intro hpq
      simp [hpq] at ac3
     exact (hp.eq_of_factorization_pos ai0).symm
    subst q
    rw [Nat.factorization_pow_self hp]
    omega
   simp [cw, Pe hp, he0, he1, hsq]
lemma En
  (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
  cw s (m * n) =
   cw s m * cw s n := by
 by_cases hm : d9 m
 ·by_cases hn : d9 n
  ·have hmn : d9 (m * n) :=
    (oB hcop).2 ⟨hm, hn⟩
   simp [cw, hm, hn, hmn,
    Lb s hcop]
  ·have hmn : ¬ d9 (m * n) := by
    intro h
    exact hn ((oB hcop).1 h).2
   simp [cw, hn, hmn]
 ·have hmn : ¬ d9 (m * n) := by
   intro h
   exact hm ((oB hcop).1 h).1
  simp [cw, hm, hmn]
lemma pH
  (s p : ℕ) (hp : Nat.Prime p) :
  Summable (fun e : ℕ => ‖cw s (p ^ e)‖) := by
 have RW : (1 : ℝ) < (p : ℝ) := by
  exact_mod_cast hp.one_lt
 have BW : 0 < (p : ℝ) := zero_lt_one.trans RW
 have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos BW]
  exact inv_lt_one_of_one_lt₀ RW
 have hgeom :
   Summable fun e : ℕ =>
    ‖(((e : ℝ) ^ s) * ((p : ℝ)⁻¹) ^ e : ℝ)‖ :=
  summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) s hr
 refine hgeom.congr_atTop ?_
 filter_upwards [Filter.eventually_ge_atTop 2] with e he
 have he0 : e ≠ 0 := by omega
 have he1 : e ≠ 1 := by omega
 rw [oQ hp]
 simp [he0, he1, div_eq_mul_inv, inv_pow]
lemma u7
  {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
  cw s (p ^ e) ≤
   ((4 : ℝ) ^ s * (s.factorial : ℝ) *
    Real.exp ((e : ℝ) / 4)) / (p : ℝ) ^ e := by
 have he0 : e ≠ 0 := by omega
 have he1 : e ≠ 1 := by omega
 have BW : 0 < (p : ℝ) := by exact_mod_cast hp.pos
 have hp_pos : 0 < (p : ℝ) ^ e := pow_pos BW e
 rw [oQ hp]
 simp [he0, he1]
 exact div_le_div_of_nonneg_right
  (Dv s e) hp_pos.le
lemma Fo (e : ℕ) :
  Real.exp ((e : ℝ) / 4) ≤ ((3 : ℝ) / 2) ^ e := by
 calc
  Real.exp ((e : ℝ) / 4) = Real.exp ((1 : ℝ) / 4) ^ e := by
   rw [← Real.exp_nat_mul]
   congr 1
   ring
  _ ≤ ((3 : ℝ) / 2) ^ e :=
   pow_le_pow_left₀ (Real.exp_pos _).le
    (le_of_lt M5) e
lemma CZ
  {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
  cw s (p ^ e) ≤
   (4 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2) *
    ((3 : ℝ) / 4) ^ e := by
 let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
 have hA_nonneg : 0 ≤ A := by
  dsimp [A]
  positivity
 have BW : 0 < (p : ℝ) := by exact_mod_cast hp.pos
 have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
 have hden_pos : 0 < (p : ℝ) ^ e := pow_pos BW e
 have ZL : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) := by positivity
 have aeH :
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
   cw s (p ^ e) ≤
    A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e := by
  simpa [A, mul_assoc] using
   u7 (s := s) hp he
 have hstep2 :
   A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e ≤
    A * Real.exp ((e : ℝ) / 4) /
     ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
  exact div_le_div_of_nonneg_left
   (mul_nonneg hA_nonneg (Real.exp_pos _).le)
   ZL aeH
 have ai1 :
   A * Real.exp ((e : ℝ) / 4) /
     ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) ≤
    A * ((3 : ℝ) / 2) ^ e /
     ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
  exact div_le_div_of_nonneg_right
   (mul_le_mul_of_nonneg_left (Fo e) hA_nonneg)
   ZL.le
 have aeI :
   A * ((3 : ℝ) / 2) ^ e /
     ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) =
    (4 * A / (p : ℝ) ^ 2) * ((3 : ℝ) / 4) ^ e := by
  have h2pos : (0 : ℝ) < 2 ^ (e - 2) := by positivity
  have ai2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  rw [show e = 2 + (e - 2) by omega]
  rw [pow_add, pow_add]
  norm_num
  field_simp [ai2.ne', h2pos.ne']
  have hmul :
    ((3 : ℝ) / 4) ^ (e - 2) * 2 ^ (e - 2) =
     ((3 : ℝ) / 2) ^ (e - 2) := by
   rw [← mul_pow]
   norm_num
  rw [← hmul]
  ring_nf
 exact hstep1.trans (hstep2.trans (ai1.trans_eq aeI))
lemma B8
  (s p : ℕ) (hp : Nat.Prime p) :
  (∑' e : ℕ, cw s (p ^ e)) ≤
   1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
 let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
 let C : ℝ := 4 * A / (p : ℝ) ^ 2
 let g : ℕ → ℝ := fun e => (if e = 0 then 1 else 0) + C * ((3 : ℝ) / 4) ^ e
 have BW : 0 < (p : ℝ) := by exact_mod_cast hp.pos
 have hA_nonneg : 0 ≤ A := by
  dsimp [A]
  positivity
 have aeJ : 0 ≤ C := by
  dsimp [C]
  positivity
 have hlhs : Summable fun e : ℕ => cw s (p ^ e) :=
  (pH s p hp).of_norm
 have nZ : Summable fun e : ℕ => if e = 0 then (1 : ℝ) else 0 :=
  (hasSum_single (0 : ℕ)
   (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)
   (by intro e he; simp [he])).summable
 have ai3 : Summable fun e : ℕ => C * ((3 : ℝ) / 4) ^ e :=
  (summable_geometric_of_lt_one
   (by norm_num : (0 : ℝ) ≤ 3 / 4)
   (by norm_num : (3 : ℝ) / 4 < 1)).mul_left C
 have hg : Summable g := nZ.add ai3
 have hpoint :
   ∀ e : ℕ, cw s (p ^ e) ≤ g e := by
  intro e
  by_cases he0 : e = 0
  ·subst e
   change cw s 1 ≤ g 0
   rw [Dw]
   simp [g]
   exact aeJ
  ·by_cases he1 : e = 1
   ·subst e
    rw [oQ hp]
    simp [g]
    dsimp [C]
    positivity
   ·have he2 : 2 ≤ e := by omega
    have h := CZ
     (s := s) (p := p) (e := e) hp he2
    simpa [g, C, A, he0] using h
 calc
  (∑' e : ℕ, cw s (p ^ e))
    ≤ ∑' e : ℕ, g e := hlhs.tsum_le_tsum hpoint hg
  _ = 1 + C * (∑' e : ℕ, ((3 : ℝ) / 4) ^ e) := by
     dsimp [g]
     rw [nZ.tsum_add ai3]
     rw [tsum_eq_single (0 : ℕ)
      (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)]
     ·rw [tsum_mul_left]
      simp
     ·intro e he
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
lemma Ou (N : ℕ) :
  (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
 classical
 have hIcc :
   Finset.Icc 1 N = (Finset.range N).image (fun ν : ℕ => ν + 1) := by
  ext d
  constructor
  ·intro hd
   have nJ := Finset.mem_Icc.mp hd
   exact Finset.mem_image.2
    ⟨d - 1, Finset.mem_range.2 (Nat.sub_one_lt_of_le nJ.1 nJ.2),
     by omega⟩
  ·intro hd
   rcases Finset.mem_image.1 hd with ⟨ν, hν, rfl⟩
   exact Finset.mem_Icc.2
    ⟨by omega, Nat.succ_le_iff.2 (Finset.mem_range.1 hν)⟩
 rw [hIcc]
 rw [Finset.sum_image]
 ·
  simpa using Jm N
 ·intro a _ha b _hb h
  exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
lemma Io (N : ℕ) :
  (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
 exact (Finset.sum_le_sum_of_subset_of_nonneg
  (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
  (by
   intro p _hp QX
   positivity)).trans (Ou N)
lemma yI
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
lemma F5
  (N s : ℕ) :
  (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
    ∑' e : ℕ, cw s (p ^ e))
   ≤ Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
 classical
 let P := (Finset.Icc 1 N).filter Nat.Prime
 let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
 let z : ℝ := 16 * A
 have hA_nonneg : 0 ≤ A := by
  dsimp [A]
  positivity
 have sW : 0 ≤ z := by
  dsimp [z]
  positivity
 have hlocal :
   ∀ p ∈ P,
    (∑' e : ℕ, cw s (p ^ e)) ≤
     (1 : ℝ) + z / (p : ℝ) ^ 2 := by
  intro p hp
  have hpprime : Nat.Prime p := (Finset.mem_filter.1 hp).2
  simpa [z, A] using B8 s p hpprime
 calc
  (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
    ∑' e : ℕ, cw s (p ^ e))
    = P.prod fun p => ∑' e : ℕ, cw s (p ^ e) := by
     change (P.filter Nat.Prime).prod
       (fun p => ∑' e : ℕ, cw s (p ^ e)) =
      P.prod (fun p => ∑' e : ℕ, cw s (p ^ e))
     rw [Finset.filter_true_of_mem]
     intro p hp
     exact (Finset.mem_filter.1 hp).2
  _ ≤ P.prod fun p => (1 : ℝ) + z / (p : ℝ) ^ 2 := by
     exact Finset.prod_le_prod
      (s := P)
      (f := fun p => ∑' e : ℕ, cw s (p ^ e))
      (g := fun p => (1 : ℝ) + z / (p : ℝ) ^ 2)
      (fun p hp => by
       have ace :
         0 ≤ ∑' e : ℕ, cw s (p ^ e) := by
        exact tsum_nonneg (fun e => zW s (p ^ e))
       exact ace)
      hlocal
  _ ≤ Real.exp (z * P.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) :=
     yI P sW
  _ ≤ Real.exp (z * 2) := by
     exact Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left
       (by
        simpa [P] using Io N)
       sW)
  _ = Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
     congr 1
     dsimp [z, A]
     ring
lemma qG
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
     iw
  simpa [Real.sqrt_eq_rpow,Function.comp_def] using h
 filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2,
   f9 (2 * |Real.log A| / δ),
   iw.eventually_ge_atTop 1] with
  N ads W2 Pz
 set Y := Real.log (Real.log (N : ℝ))
 have RY : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using Pz)
 have MY : 0 < Real.sqrt Y := Real.sqrt_pos.2 RY
 have aaM : 0 ≤ Real.log Y := Real.log_nonneg (by simpa [Y] using Pz)
 have adt :
   ‖Real.log Y‖ = Real.log Y := by
  rw [Real.norm_of_nonneg aaM]
 have acf :
   ‖Real.sqrt Y‖ = Real.sqrt Y := by
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
 have af6 : Real.log Y ≤ (δ / 2) * Real.sqrt Y := by
  simpa [Y, adt, acf] using ads
 have hconst : Real.log A ≤ (δ / 2) * Real.sqrt Y := by
  have hmul : 2 * |Real.log A| ≤ δ * Real.sqrt Y :=
   by simpa [mul_comm] using (div_le_iff₀ hδ).1 W2
  have ai4 : Real.log A ≤ |Real.log A| := le_abs_self _
  linarith
 have af7 : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
  Real.log_sqrt RY.le
 calc
  Real.log (A * Real.sqrt Y)
    = Real.log A + Real.log (Real.sqrt Y) := by
      rw [Real.log_mul hA.ne' MY.ne']
  _ = Real.log A + Real.log Y / 2 := by rw [af7]
  _ ≤ (δ / 2) * Real.sqrt Y + ((δ / 2) * Real.sqrt Y) / 2 := by
      have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Real.sqrt Y) / 2 := by
       exact div_le_div_of_nonneg_right af6 (by norm_num)
      nlinarith
  _ ≤ δ * Real.sqrt Y := by nlinarith
lemma vZ
  (B : ℝ) (hB : 0 < B) :
  ∀ᶠ N : ℕ in atTop,
   let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
   32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ aZ N := by
 let B' : ℝ := B + 1
 let C : ℝ := 4 * B'
 have hB' : 0 < B' := by dsimp [B']; linarith
 have hC : 0 < C := by dsimp [C]; positivity
 have hδ : 0 < (1 / (12 * B') : ℝ) := by positivity
 filter_upwards [qG
   C (1 / (12 * B')) hC hδ,
   f9 (max 1 (1 / B)),
   iw.eventually_ge_atTop (max 1 (12 * Real.log 32)),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
  N akx W2 Pz dG
 set Y := Real.log (Real.log (N : ℝ))
 set R := Real.sqrt Y
 set s : ℕ := Nat.ceil (B * R)
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have ZM : 1 ≤ Y := (le_max_left _ _).trans (by simpa [Y] using Pz)
 have akk : 12 * Real.log 32 ≤ Y :=
  (le_max_right _ _).trans (by simpa [Y] using Pz)
 have RY : 0 < Y := zero_lt_one.trans_le ZM
 have hR_pos : 0 < R := by simpa [R] using Real.sqrt_pos.2 RY
 have ZO : 0 ≤ R := hR_pos.le
 have Dr : 1 ≤ R := by
  have af8 :
    (1 : ℝ) ^ 2 ≤ R ^ 2 := by
   simpa [R, Real.sq_sqrt RY.le] using ZM
  have habs : |(1 : ℝ)| ≤ |R| := sq_le_sq.mp af8
  simpa [abs_of_nonneg ZO] using habs
 have adu : 0 ≤ B * R := by positivity
 have hs_le : (s : ℝ) ≤ B' * R := by
  have amF : (s : ℝ) ≤ B * R + 1 := by
   dsimp [s]
   exact (Nat.ceil_lt_add_one adu).le
  have alh : (1 : ℝ) ≤ R := Dr
  dsimp [B']
  nlinarith
 have adv : (4 : ℝ) * (s : ℝ) ≤ C * R := by
  dsimp [C]
  nlinarith [hs_le, ZO]
 have af9 : 0 < C * R := mul_pos hC hR_pos
 have acg : 1 ≤ C * R := by
  have aaN : 0 < C := hC
  nlinarith [aaN, Dr]
 have aaO : 0 ≤ Real.log (C * R) :=
  Real.log_nonneg acg
 have aeK :
   (s : ℝ) * Real.log (C * R) ≤ Y / 12 := by
  have ai5 :
    Real.log (C * R) ≤ (1 / (12 * B')) * R := by
   simpa [C, Y, R] using akx
  calc
   (s : ℝ) * Real.log (C * R)
     ≤ (B' * R) * Real.log (C * R) := by
      exact mul_le_mul_of_nonneg_right hs_le aaO
   _ ≤ (B' * R) * ((1 / (12 * B')) * R) := by
      exact mul_le_mul_of_nonneg_left ai5 (by positivity)
   _ = Y / 12 := by
      have alF : R ^ 2 = Y := by
       simpa [R] using Real.sq_sqrt RY.le
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
       _ = (1 / 12 : ℝ) * Y := by rw [hcoef, alF]
       _ = Y / 12 := by ring
 have hfac :
   ((s.factorial : ℕ) : ℝ) ≤ (s : ℝ) ^ s := by
  exact_mod_cast Nat.factorial_le_pow s
 have Y4 :
   (4 : ℝ) ^ s * (s.factorial : ℝ) ≤ ((4 : ℝ) * (s : ℝ)) ^ s := by
  calc
   (4 : ℝ) ^ s * (s.factorial : ℝ)
     ≤ (4 : ℝ) ^ s * (s : ℝ) ^ s := by
      exact mul_le_mul_of_nonneg_left hfac (by positivity)
   _ = ((4 : ℝ) * (s : ℝ)) ^ s := by rw [mul_pow]
 have aga :
   ((4 : ℝ) * (s : ℝ)) ^ s ≤ (C * R) ^ s := by
  exact pow_le_pow_left₀ (by positivity) adv s
 have agb :
   (C * R) ^ s ≤ Real.exp (Y / 12) := by
  have ahB :
    (C * R) ^ s = Real.exp ((s : ℝ) * Real.log (C * R)) := by
   rw [← Real.rpow_natCast, Real.rpow_def_of_pos af9]
   ring_nf
  rw [ahB]
  exact Real.exp_le_exp.2 aeK
 have adw :
   (32 : ℝ) ≤ Real.exp (Y / 12) := by
  have ai6 : Real.log 32 ≤ Y / 12 := by nlinarith
  calc
   (32 : ℝ) = Real.exp (Real.log 32) := by
     rw [Real.exp_log (by norm_num : (0 : ℝ) < 32)]
   _ ≤ Real.exp (Y / 12) := Real.exp_le_exp.2 ai6
 have hmain :
   32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Real.exp (Y / 6) := by
  calc
   32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
     ≤ Real.exp (Y / 12) * Real.exp (Y / 12) := by
      exact mul_le_mul adw (Y4.trans (aga.trans agb))
       (by positivity) (by positivity)
   _ = Real.exp (Y / 6) := by
      rw [← Real.exp_add]
      congr 1
      ring
 have aaH := zP c7
 calc
  32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
    ≤ Real.exp (Y / 6) := hmain
  _ ≤ Real.exp (Y / 2) * R := by
     have hexp : Real.exp (Y / 6) ≤ Real.exp (Y / 2) :=
      Real.exp_le_exp.2 (by nlinarith)
     exact hexp.trans (by
      calc
       Real.exp (Y / 2) ≤ Real.exp (Y / 2) * R := by
        nlinarith [Real.exp_pos (Y / 2), Dr])
  _ = aZ N := by
     rw [aaH]
lemma qM (N s : ℕ) :
  HasSum
   (fun m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
    cw s m)
   (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
    ∑' e : ℕ, cw s (p ^ e)) := by
 exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
  (f := cw s)
  (Dw s)
  (fun {m n} hcop => En s hcop)
  (fun {p} hp => pH s p hp)
  ((Finset.Icc 1 N).filter Nat.Prime)).2
lemma Fp {N d : ℕ}
  (hd : d ∈ Finset.Icc 1 N) :
  d ∈ Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) := by
 rw [Nat.mem_factoredNumbers']
 intro p hp hpd
 have nJ := Finset.mem_Icc.mp hd
 have Ec : 0 < d := lt_of_lt_of_le Nat.zero_lt_one nJ.1
 have hple : p ≤ N := (Nat.le_of_dvd Ec hpd).trans nJ.2
 exact Finset.mem_filter.2
  ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hp.pos, hple⟩, hp⟩
lemma zQ
  {N d s : ℕ} (hd : d ∈ Finset.Icc 1 N) (hsq : d9 d) :
  cw s d = (cQ d : ℝ) ^ s / (d : ℝ) := by
 have nJ := Finset.mem_Icc.mp hd
 have SM : d ≠ 0 :=
  Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one nJ.1)
 simp [cw, iJ, hsq, SM]
noncomputable def tO (N : ℕ) :
  Finset (Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)) :=
 ((Finset.Icc 1 N).filter d9).attach.image
  (fun d =>
   (⟨d.1, Fp
    (Finset.mem_filter.1 d.2).1⟩ :
    Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)))
lemma yJ (N s : ℕ) :
  (∑ d ∈ Finset.Icc 1 N,
    if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0)
   =
  ∑ x ∈ tO N, cw s x := by
 classical
 unfold tO
 rw [Finset.sum_image]
 ·rw [Finset.sum_attach]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  exact (zQ
   (N := N) (d := d) (s := s)
   (Finset.mem_filter.1 hd).1
   (Finset.mem_filter.1 hd).2).symm
 ·intro a _ha b _hb hab
  apply Subtype.ext
  exact congrArg
   (fun x : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
    (x : ℕ)) hab
lemma C4 (N s : ℕ) :
  (∑ d ∈ Finset.Icc 1 N,
    if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0)
   ≤
  ∑' m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime),
   cw s m := by
 rw [yJ]
 exact (qM N s).summable.sum_le_tsum
  (tO N)
  (fun x _hx => zW s x)
lemma Dx (N s : ℕ) :
  (∑ d ∈ Finset.Icc 1 N,
    if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0)
   ≤
  ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
   ∑' e : ℕ, cw s (p ^ e) := by
 rw [← (qM N s).tsum_eq]
 exact C4 N s
lemma yP (N s : ℕ) :
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s) ≤
   (N : ℝ) *
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
     ∑' e : ℕ, cw s (p ^ e) := by
 calc
  (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s)
    ≤ (N : ℝ) *
      ∑ d ∈ Finset.Icc 1 N,
       if d9 d then (cQ d : ℝ) ^ s / (d : ℝ) else 0 :=
     Bp N s
  _ ≤ (N : ℝ) *
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
     ∑' e : ℕ, cw s (p ^ e) := by
     exact mul_le_mul_of_nonneg_left
      (Dx N s)
      (by positivity)
lemma F6 (N s : ℕ) :
  (((Finset.Icc 1 N).filter
    (fun n => eW N < (cQ n : ℝ))).card : ℝ)
   ≤ (N : ℝ) *
     Real.exp
      (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
       - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
 have Vw : 0 ≤ eW N := by
  unfold eW
  positivity
 have RU :=
  Pv (N := N) (s := s) (H := eW N) Vw
 have ahC :
   (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s) ≤
    (N : ℝ) *
     Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
  calc
   (∑ n ∈ Finset.Icc 1 N, (cQ n : ℝ) ^ s)
     ≤ (N : ℝ) *
       ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, cw s (p ^ e) :=
      yP N s
   _ ≤ (N : ℝ) *
      Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
       (F5 N s)
       (by positivity)
 have aeL :
   (((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card : ℝ) *
     eW N ^ s
    ≤ (N : ℝ) *
     Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) :=
  RU.trans ahC
 have ahi :
   eW N ^ s =
    Real.exp ((s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
  unfold eW
  rw [← Real.exp_nat_mul]
 have aeM :
   0 < eW N ^ s := by
  rw [ahi]
  positivity
 have hdiv :
   (((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card : ℝ)
    ≤ ((N : ℝ) *
     Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)))) /
      eW N ^ s := by
  exact (le_div_iff₀ aeM).2 aeL
 refine hdiv.trans_eq ?_
 rw [ahi]
 rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
 congr 1
theorem F7 :
  ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
   ((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card
    ≤ Nat.floor ((N : ℝ) * bF (-A) N) := by
 intro A hA
 let B : ℝ := A + 2
 have hB : 0 < B := by dsimp [B]; linarith
 filter_upwards [vZ B hB,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
  N Me dG
 let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
 have d6 : 0 ≤ Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
  have bY : 1 < Real.log (N : ℝ) :=
   (Real.lt_log_iff_exp_lt hNpos).2 c7
  exact (zero_lt_one.trans bY).le
 have ZP : 0 ≤ aZ N := by
  rw [gN c7]
  positivity
 have agc :
   32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ aZ N := by
  simpa [s, B] using Me
 have hs_ge :
   B * Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ (s : ℝ) := by
  dsimp [s]
  exact Nat.le_ceil _
 have aeN :
   B * aZ N ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
  rw [gN c7]
  calc
   B * (Real.sqrt (Real.log (N : ℝ)) *
     Real.sqrt (Real.log (Real.log (N : ℝ))))
     = (B * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
       Real.sqrt (Real.log (N : ℝ)) := by ring
   _ ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg _)
 have aeO :
   32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
     - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
    ≤ -A * aZ N := by
  have hstep :
    32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
      - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
     ≤ aZ N - B * aZ N := by
   nlinarith [agc, aeN]
  have htarget : aZ N - B * aZ N ≤ -A * aZ N := by
   dsimp [B]
   nlinarith [ZP]
  exact hstep.trans htarget
 have hreal :
   (((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card : ℝ)
    ≤ (N : ℝ) * bF (-A) N := by
  calc
   (((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card : ℝ)
     ≤ (N : ℝ) *
       Real.exp
        (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
         - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) :=
      F6 N s
   _ ≤ (N : ℝ) * bF (-A) N := by
      rw [bF]
      exact mul_le_mul_of_nonneg_left
       (Real.exp_le_exp.2 aeO) hN_nonneg
 exact Nat.le_floor hreal
theorem Rm :
  ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
   ((Finset.Icc 1 N).filter
     (fun n => eW N < (cQ n : ℝ))).card
    ≤ Nat.floor ((N : ℝ) * bF (-A) N) :=
 F7
theorem Ro
  (A : ℝ) (hA : 0 < A) :
  ∀ᶠ N : ℕ in atTop,
   ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 N →
    (S.filter fun n => eW N < (cQ n : ℝ)).card
     ≤ Nat.floor ((N : ℝ) * bF (-A) N) := by
 filter_upwards [Rm A hA] with N hN S hS
 exact (Finset.card_le_card (by
  intro n hn
  exact Finset.mem_filter.2
   ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN
end dO
namespace dO
open Filter Finset
lemma nL (A : ℝ) :
  ∀ᶠ N : ℕ in atTop, A ≤ aZ N := by
 let B : ℝ := max A 1
 have Om : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
 have agd : 0 ≤ B := Om.le
 filter_upwards [oM 1 zero_lt_one,
   f9 (Real.sqrt B),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have hsq :
   (Real.sqrt B) ^ 2 ≤
    (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
  pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
 have aaP : B ≤ Real.log (Real.log (N : ℝ)) := by
  simpa [Real.sq_sqrt agd, Real.sq_sqrt f8] using hsq
 have hZ := gW c7
 have ahD : B ≤ aZ N := by
  rw [← hZ]
  nlinarith [hM, aaP, Om.le]
 exact (le_max_left A 1).trans ahD
lemma v7 {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
  ∀ᶠ N : ℕ in atTop, bF (-A) N ≤ c := by
 filter_upwards [nL ((-Real.log c) / A)] with N hZ
 rw [bF]
 exact (Real.le_log_iff_exp_le hc).1 (by
  have hmul : -Real.log c ≤ A * aZ N := by
   simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
  nlinarith)
lemma C7 {C η : ℝ}
  (hC : 0 < C) (hη : 0 < η) :
  ∀ᶠ N : ℕ in atTop, C * aZ N ≤ bF η N := by
 have agf : 0 < η ^ 2 := sq_pos_of_pos hη
 filter_upwards [nL (4 * C / η ^ 2)] with N ahE
 let x : ℝ := η * aZ N / 2
 have ZP : 0 ≤ aZ N := nD N
 have hx_nonneg : 0 ≤ x := by
  dsimp [x]
  positivity
 have Me : 2 * C / η ≤ x := by
  dsimp [x]
  rw [div_le_iff₀ hη]
  have hmul' : 4 * C ≤ η ^ 2 * aZ N := by
   simpa [mul_comm, mul_left_comm, mul_assoc] using
    (div_le_iff₀ agf).1 ahE
  have amG : 4 * C ≤ η * (η * aZ N) := by
   simpa [pow_two, mul_assoc] using hmul'
  nlinarith
 have ai7 : C * aZ N = (2 * C / η) * x := by
  dsimp [x]
  field_simp [hη.ne']
 have adx : C * aZ N ≤ x ^ 2 := by
  rw [ai7, pow_two]
  exact mul_le_mul_of_nonneg_right Me hx_nonneg
 have ZQ : x ≤ Real.exp x := by
  calc
   x ≤ 1 + x := by linarith
   _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
 have ahF : x ^ 2 ≤ Real.exp (2 * x) := by
  calc
   x ^ 2 = x * x := by ring
   _ ≤ Real.exp x * Real.exp x := by
      exact mul_le_mul ZQ ZQ hx_nonneg (Real.exp_pos x).le
   _ = Real.exp (2 * x) := by
      rw [← Real.exp_add]
      ring_nf
 calc
  C * aZ N ≤ x ^ 2 := adx
  _ ≤ Real.exp (2 * x) := ahF
  _ = bF η N := by
     dsimp [x, bF]
     congr 1
     ring
lemma M6 :
  ∀ᶠ N : ℕ in atTop, aO N ≤ aZ N := by
 filter_upwards [f9 1,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have yQ : 1 ≤ Real.log (Real.log (N : ℝ)) := by
  have hsq :
    (1 : ℝ) ^ 2 ≤
     (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
   pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hsqrt 2
  simpa [Real.sq_sqrt f8] using hsq
 rw [← gW c7]
 exact le_mul_of_one_le_right (pD N) yQ
lemma B9
  (η : ℝ) (hη : 0 < η) :
  ∀ᶠ N : ℕ in atTop,
   ((Nat.floor (3 * aO N) + 1 : ℕ) : ℝ) ≤ bF η N := by
 filter_upwards [M6,
   nL 1,
   C7 (C := 4) (by norm_num) hη] with
  N am0 am6 h4Z
 have hfloor :
   ((Nat.floor (3 * aO N) : ℕ) : ℝ) ≤ 3 * aO N := by
  exact Nat.floor_le (mul_nonneg (by norm_num) (pD N))
 calc
  ((Nat.floor (3 * aO N) + 1 : ℕ) : ℝ)
    = ((Nat.floor (3 * aO N) : ℕ) : ℝ) + 1 := by norm_num
  _ ≤ 3 * aO N + 1 := by linarith
  _ ≤ 3 * aZ N + aZ N := by nlinarith
  _ = 4 * aZ N := by ring
  _ ≤ bF η N := h4Z
lemma zX
  {ε η : ℝ} {N : ℕ} {Q : Finset ℕ}
  (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * bF (-1) N) * bF (-ε) N)
  (hf : (N : ℝ) * bF (-(1 + η)) N ≤ ((N : ℝ) * bF (-1) N)) :
  (N : ℝ) * bF (-(1 + η + ε)) N ≤ (Q.card : ℝ) := by
 calc
  (N : ℝ) * bF (-(1 + η + ε)) N
    = ((N : ℝ) * bF (-(1 + η)) N) * bF (-ε) N := by
      rw [show -(1 + η + ε) = -(1 + η) + -ε by ring, JT]
      ring
  _ ≤ ((N : ℝ) * bF (-1) N) * bF (-ε) N := by
     exact mul_le_mul_of_nonneg_right hf (nF (-ε) N)
  _ ≤ (Q.card : ℝ) := hQ
lemma qO (A : ℝ) :
  ∀ᶠ N : ℕ in atTop, 1 < (N : ℝ) * bF (-A) N := by
 let B : ℝ := max (A + 1) 1
 have Om : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right (A + 1) 1)
 filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
   oM B Om] with N hN hM
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
 have agg : 0 < N := by
  exact Nat.pos_of_ne_zero (by
   intro h0
   have : ((N : ℕ) : ℝ) = 0 := by simp [h0]
   linarith [show (0 : ℝ) < Real.exp 1 from Real.exp_pos 1])
 have Ov : 0 < aZ N := lJ c7
 have amI : A + 1 ≤ aO N := (le_max_left (A + 1) 1).trans hM
 have hlog_eq : Real.log ((N : ℝ) * bF (-A) N) =
   Real.log (N : ℝ) + (-A) * aZ N :=
  Dm agg (-A)
 have hMZ := tB c7
 have gC :
   0 < Real.log ((N : ℝ) * bF (-A) N) := by
  rw [hlog_eq, ← hMZ]
  have hdiff : 1 ≤ aO N - A := by linarith
  nlinarith
 have Eo : 0 ≤ (N : ℝ) * bF (-A) N :=
  mul_nonneg (by positivity) (nF (-A) N)
 exact (Real.log_pos_iff Eo).1 gC
lemma UG {n : ℕ} (hn : 1 < n) : 1 ≤ omega n := by
 by_contra h
 have yF : omega n = 0 := by omega
 have alG : n ≠ 0 := by omega
 have hnone : n = 1 := vH alG yF
 omega
lemma C8 :
  ∀ᶠ N : ℕ in atTop,
   ∀ q : ℕ, (N : ℝ) * bF (-2) N ≤ (q : ℝ) → 1 ≤ omega q := by
 filter_upwards [qO 2] with N Dq q hq
 have Y5 : (1 : ℝ) < (q : ℝ) := Dq.trans_le hq
 have aeP : 1 < q := by exact_mod_cast Y5
 exact UG aeP
lemma q7
  {A B δ : ℝ} (hAB : B + δ ≤ A) (N : ℕ) :
  (N : ℝ) * bF (-A) N ≤
   bF (-δ) N * ((N : ℝ) * bF (-B) N) := by
 have hmono : bF (-A) N ≤ bF (-(B + δ)) N := by
  exact oN (by linarith) N
 calc
  (N : ℝ) * bF (-A) N
    ≤ (N : ℝ) * bF (-(B + δ)) N := by
     exact mul_le_mul_of_nonneg_left hmono (by positivity)
  _ = bF (-δ) N * ((N : ℝ) * bF (-B) N) := by
     rw [show -(B + δ) = -B + -δ by ring, JT]
     ring
lemma Cc
  {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
  (hQ : (N : ℝ) * bF (-B) N ≤ (Q.card : ℝ)) :
  (N : ℝ) * bF (-A) N ≤
   bF (-δ) N * (Q.card : ℝ) := by
 calc
  (N : ℝ) * bF (-A) N
    ≤ bF (-δ) N * ((N : ℝ) * bF (-B) N) :=
     q7 hAB N
  _ ≤ bF (-δ) N * (Q.card : ℝ) := by
     exact mul_le_mul_of_nonneg_left hQ (nF (-δ) N)
lemma wQ
  {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
  (hQ : (N : ℝ) * bF (-B) N ≤ (Q.card : ℝ)) :
  (Nat.floor ((N : ℝ) * bF (-A) N) : ℝ) ≤
   bF (-δ) N * (Q.card : ℝ) := by
 have Eo :
   0 ≤ (N : ℝ) * bF (-A) N :=
  mul_nonneg (by positivity) (nF (-A) N)
 exact (Nat.floor_le Eo).trans
  (Cc hAB hQ)
lemma jv
  {A ε η δ : ℝ} (hAB : 1 + η + ε + δ ≤ A)
  {N : ℕ} {Q : Finset ℕ}
  (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * bF (-1) N) * bF (-ε) N)
  (hf : (N : ℝ) * bF (-(1 + η)) N ≤ ((N : ℝ) * bF (-1) N)) :
  (Nat.floor ((N : ℝ) * bF (-A) N) : ℝ) ≤
   bF (-δ) N * (Q.card : ℝ) := by
 have ahG :
   (N : ℝ) * bF (-(1 + η + ε)) N ≤ (Q.card : ℝ) :=
  zX hQ hf
 exact wQ
  (A := A) (B := 1 + η + ε) (δ := δ) (by linarith) ahG
lemma Jx {S : Finset ℕ} {X : ℝ}
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
 have ahH : (Finset.Icc 1 (Nat.floor X)).card ≤ Nat.floor X := by
  rw [Nat.card_Icc]
  omega
 exact hcard.trans ahH
lemma Ip
  {N : ℕ} {Q : Finset ℕ}
  (yT : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) :
  (Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * bF (-2) N)).card
   ≤ Nat.floor ((N : ℝ) * bF (-2) N) := by
 exact Jx
  (mul_nonneg (by positivity) (nF (-2) N))
  (fun q hq => (yT q hq).1)
lemma wR
  {ε η δ : ℝ} (RZ : 1 + η + ε + δ ≤ 2)
  {N : ℕ} {Q : Finset ℕ}
  (yT : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
  (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * bF (-1) N) * bF (-ε) N)
  (hf : (N : ℝ) * bF (-(1 + η)) N ≤ ((N : ℝ) * bF (-1) N)) :
  ((Q.filter
    (fun q : ℕ => (q : ℝ) < (N : ℝ) * bF (-2) N)).card : ℝ) ≤
   bF (-δ) N * (Q.card : ℝ) := by
 have hcount := Ip (N := N) (Q := Q) yT
 have F9 :
   (((Q.filter
    (fun q : ℕ => (q : ℝ) < (N : ℝ) * bF (-2) N)).card : ℕ) : ℝ) ≤
    (Nat.floor ((N : ℝ) * bF (-2) N) : ℝ) := by
  exact_mod_cast hcount
 exact F9.trans
  (jv
   (A := 2) (ε := ε) (η := η) (δ := δ) RZ hQ hf)
lemma z7
  {A ε η δ : ℝ} (RZ : 1 + η + ε + δ ≤ A)
  {N : ℕ} {Q : Finset ℕ}
  (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * bF (-1) N) * bF (-ε) N)
  (hf : (N : ℝ) * bF (-(1 + η)) N ≤ ((N : ℝ) * bF (-1) N))
  (aky :
   (Q.filter fun q : ℕ => eW N < (cQ q : ℝ)).card
    ≤ Nat.floor ((N : ℝ) * bF (-A) N)) :
  (((Q.filter
    fun q : ℕ => eW N < (cQ q : ℝ)).card : ℕ) : ℝ) ≤
   bF (-δ) N * (Q.card : ℝ) := by
 have F9 :
   (((Q.filter
    fun q : ℕ => eW N < (cQ q : ℝ)).card : ℕ) : ℝ) ≤
    (Nat.floor ((N : ℝ) * bF (-A) N) : ℝ) := by
  exact_mod_cast aky
 exact F9.trans
  (jv
   (A := A) (ε := ε) (η := η) (δ := δ) RZ hQ hf)
lemma QC
  (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   ∀ Q : Finset ℕ,
    Q ⊆ Finset.Icc 1 N →
    ∀ t : ℕ, (t : ℝ) ≤ 3 * aO N →
     let α : ℝ := (t : ℝ) / aO N
     (Q.filter fun q => t ≤ omega q).card
      ≤ Nat.floor
        ((N : ℝ) * Real.exp ((-α / 2 + ε) * aZ N)) := by
 filter_upwards [wP ε hε] with N htail Q hQ t ht
 have hsub :
   (Q.filter fun q => t ≤ omega q) ⊆
    (Finset.Icc 1 N).filter fun q => t ≤ omega q := by
  intro q hq
  exact Finset.mem_filter.2
   ⟨hQ (Finset.mem_filter.1 hq).1, (Finset.mem_filter.1 hq).2⟩
 exact (Finset.card_le_card hsub).trans (htail N t le_rfl ht)
lemma zR
  {A ε η δ : ℝ} (RZ : 1 + η + ε + δ ≤ A)
  {N t : ℕ} {Q : Finset ℕ}
  (hQ : (Q.card : ℝ) ≥ ((N : ℝ) * bF (-1) N) * bF (-ε) N)
  (hf : (N : ℝ) * bF (-(1 + η)) N ≤ ((N : ℝ) * bF (-1) N))
  (hTail :
   (Q.filter fun q : ℕ => t ≤ omega q).card
    ≤ Nat.floor ((N : ℝ) * bF (-A) N)) :
  (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
   bF (-δ) N * (Q.card : ℝ) := by
 have F9 :
   (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
    (Nat.floor ((N : ℝ) * bF (-A) N) : ℝ) := by
  exact_mod_cast hTail
 exact F9.trans
  (jv
   (A := A) (ε := ε) (η := η) (δ := δ) RZ hQ hf)
lemma Dz :
  ∀ᶠ N : ℕ in atTop,
   ∀ Q : Finset ℕ,
    Q ⊆ Finset.Icc 1 N →
     (Q.filter
       (fun q : ℕ => Nat.floor (3 * aO N) ≤ omega q)).card
      ≤ Nat.floor ((N : ℝ) * bF (-(4 / 3)) N) := by
 have hτ : (0 : ℝ) < 1 / 24 := by norm_num
 filter_upwards [QC (1 / 24) hτ,
   oM 4 (by norm_num),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
  N htail alH dG Q hQ
 let t : ℕ := Nat.floor (3 * aO N)
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hMpos : 0 < aO N := g5 c7
 have O8 : 0 ≤ aZ N := nD N
 have ht_le : (t : ℝ) ≤ 3 * aO N := by
  dsimp [t]
  exact Nat.floor_le (mul_nonneg (by norm_num) (pD N))
 have agh := htail Q hQ t ht_le
 have agi : 3 * aO N - 1 < (t : ℝ) := by
  have hlt : 3 * aO N < (t : ℝ) + 1 := by
   dsimp [t]
   exact Nat.lt_floor_add_one (3 * aO N)
  linarith
 have ai9 : (11 / 4 : ℝ) ≤ (t : ℝ) / aO N := by
  have hdiv : (3 * aO N - 1) / aO N < (t : ℝ) / aO N :=
   div_lt_div_of_pos_right agi hMpos
  have amJ : 1 / aO N ≤ (1 / 4 : ℝ) := by
   exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) alH)
  have akz : (11 / 4 : ℝ) ≤ 3 - 1 / aO N := by
   linarith
  have amy : (3 * aO N - 1) / aO N = 3 - 1 / aO N := by
   field_simp [hMpos.ne']
  linarith
 have ady :
   (N : ℝ) *
     Real.exp ((-((t : ℝ) / aO N) / 2 + (1 / 24 : ℝ)) *
      aZ N)
    ≤ (N : ℝ) * bF (-(4 / 3)) N := by
  have hcoeff :
    -((t : ℝ) / aO N) / 2 + (1 / 24 : ℝ) ≤ -(4 / 3 : ℝ) := by
   nlinarith
  have hexp :
    Real.exp ((-((t : ℝ) / aO N) / 2 + (1 / 24 : ℝ)) *
      aZ N)
     ≤ bF (-(4 / 3)) N := by
   rw [bF]
   exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcoeff O8)
  exact mul_le_mul_of_nonneg_left hexp (by positivity)
 exact agh.trans (Nat.floor_mono ady)
lemma s9
  (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   ∀ K : ℕ, (K : ℝ) ≤ 3 * aO N →
    (Nat.ceil (eW N ^ 2 * (2 : ℝ) ^ K) : ℝ) ≤
     bF ε N := by
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have aaQ : 0 ≤ Real.log 2 := jA.le
 let Xm : ℝ := 9 * Real.log 2 / ε
 have aeQ : 0 < Xm := by
  dsimp [Xm]
  positivity
 filter_upwards [nL (3 * Real.log 2 / ε),
   f9 (6 / ε),
   f9 (Real.sqrt Xm),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
  N ahI Rq aeR dG K hK
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have d6 : 0 ≤ Real.log (N : ℝ) := gC.le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have oO : 0 ≤ Real.sqrt (Real.log (N : ℝ)) :=
  Real.sqrt_nonneg _
 have aeS :
   0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  Real.sqrt_nonneg _
 have QY : Xm ≤ Real.log (Real.log (N : ℝ)) := by
  have hsq :
    (Real.sqrt Xm) ^ 2 ≤
     (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
   pow_le_pow_left₀ (Real.sqrt_nonneg Xm) aeR 2
  simpa [Real.sq_sqrt aeQ.le, Real.sq_sqrt f8] using hsq
 have aja := gN c7
 have agj := gW c7
 let a : ℝ := (ε / 3) * aZ N
 have htwo : (2 : ℝ) ≤ Real.exp a := by
  have R5 : Real.log 2 ≤ a := by
   dsimp [a]
   have am1 : 3 * Real.log 2 ≤ ε * aZ N := by
    simpa [mul_comm] using (div_le_iff₀ hε).1 ahI
   nlinarith
  exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).1 R5
 have alI : eW N ^ 2 ≤ Real.exp a := by
  have hcoeff : 2 ≤ (ε / 3) *
    Real.sqrt (Real.log (Real.log (N : ℝ))) := by
   have hmul : 6 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    simpa [mul_comm] using (div_le_iff₀ hε).1 Rq
   nlinarith
  have agk :
    2 * Real.sqrt (Real.log (N : ℝ)) ≤ a := by
   dsimp [a]
   rw [aja]
   calc
    2 * Real.sqrt (Real.log (N : ℝ))
      ≤ ((ε / 3) * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
        Real.sqrt (Real.log (N : ℝ)) := by
       exact mul_le_mul_of_nonneg_right hcoeff oO
    _ = (ε / 3) *
       (Real.sqrt (Real.log (N : ℝ)) *
        Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
       ring
  have ahJ :
    eW N ^ 2 = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
   simp [eW, pow_two, ← Real.exp_add, two_mul]
  rw [ahJ]
  exact Real.exp_le_exp.2 agk
 have hpow : (2 : ℝ) ^ K ≤ Real.exp a := by
  have R5 : Real.log ((2 : ℝ) ^ K) ≤ a := by
   rw [Real.log_pow]
   dsimp [a]
   rw [← agj]
   calc
    (K : ℝ) * Real.log 2
      ≤ (3 * aO N) * Real.log 2 := by
       exact mul_le_mul_of_nonneg_right hK aaQ
    _ = aO N * (3 * Real.log 2) := by ring
    _ ≤ aO N * ((ε / 3) *
       Real.log (Real.log (N : ℝ))) := by
       have hmain : 3 * Real.log 2 ≤ (ε / 3) *
         Real.log (Real.log (N : ℝ)) := by
        dsimp [Xm] at QY
        have hmul : 9 * Real.log 2 ≤
          ε * Real.log (Real.log (N : ℝ)) := by
         simpa [mul_comm] using (div_le_iff₀ hε).1 QY
        nlinarith
       exact mul_le_mul_of_nonneg_left hmain (pD N)
    _ = (ε / 3) *
       (aO N * Real.log (Real.log (N : ℝ))) := by ring
    _ = ε / 3 * (aO N * Real.log (Real.log (N : ℝ))) := by ring
  exact (Real.log_le_iff_le_exp (by positivity : 0 < (2 : ℝ) ^ K)).1 R5
 let X : ℝ := eW N ^ 2 * (2 : ℝ) ^ K
 have ZR : 0 ≤ X := by
  dsimp [X]
  positivity
 have aeT : 1 ≤ eW N := by
  rw [show (1 : ℝ) = Real.exp 0 by simp, eW]
  exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
 have ach : 1 ≤ eW N ^ 2 := by
  nlinarith [aeT]
 have Rr : 1 ≤ (2 : ℝ) ^ K := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
 have ali : 1 ≤ X := by
  dsimp [X]
  nlinarith [mul_le_mul ach Rr
   (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ eW N ^ 2)]
 have agl : (Nat.ceil X : ℝ) ≤ 2 * X := by
  have alJ : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one ZR
  linarith
 have akA : 2 * X ≤ bF ε N := by
  dsimp [X]
  calc
   2 * (eW N ^ 2 * (2 : ℝ) ^ K)
     ≤ Real.exp a * (Real.exp a * Real.exp a) := by
      nlinarith [htwo, alI, hpow,
       Real.exp_pos a, ZR]
   _ = Real.exp (3 * a) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
   _ = bF ε N := by
      dsimp [a, bF]
      congr 1
      ring
 exact agl.trans akA
lemma rP
  {S S' : Finset ℕ} {C N : ℕ} {η : ℝ}
  (hcard : S.card ≤ C * S'.card)
  (hC : (C : ℝ) ≤ bF η N) :
  (S.card : ℝ) * bF (-η) N ≤ (S'.card : ℝ) := by
 have qC : (S.card : ℝ) ≤ (C : ℝ) * (S'.card : ℝ) := by
  exact_mod_cast hcard
 have Me :
   (C : ℝ) * (S'.card : ℝ) ≤
    bF η N * (S'.card : ℝ) := by
  exact mul_le_mul_of_nonneg_right hC (by positivity)
 have hmain : (S.card : ℝ) ≤ bF η N * (S'.card : ℝ) :=
  qC.trans Me
 calc
  (S.card : ℝ) * bF (-η) N
    ≤ (bF η N * (S'.card : ℝ)) * bF (-η) N := by
     exact mul_le_mul_of_nonneg_right hmain (nF (-η) N)
  _ = (S'.card : ℝ) * (bF η N * bF (-η) N) := by ring
  _ = (S'.card : ℝ) := by
     rw [show bF η N * bF (-η) N = 1 by
      rw [mul_comm, YO]]
     ring
lemma S9 {N : ℕ} {Q S : Finset ℕ} (a : gJ Q)
  (hsub : S ⊆ Q)
  (yT : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
  (hDisj : d7 Q a)
  (Tf : S.Nonempty)
  (K : ℕ)
  (hKpos : 1 ≤ K)
  (Vz : ∀ q ∈ S, (N : ℝ) * bF (-2) N ≤ (q : ℝ))
  (QZ : ∀ q ∈ S, (cQ q : ℝ) ≤ eW N)
  (M7 : ∀ q ∈ S, omega q = K)
  (OQ : (K : ℝ) ≤ 3 * aO N)
  (Y6 : ∀ q ∈ S, ∀ r ∈ S, rad q = rad r → q = r) :
  ∃ D : bC N, D.Q = S ∧ D.K = K ∧
   (D.Q.card : ℝ) = (S.card : ℝ) := by
 let aS : gJ S := nY a hsub
 have aci : Admissible N S := by
  constructor
  ·intro q hq
   exact yT q (hsub hq)
  ·exact ⟨aS, d7.mono hDisj hsub⟩
 refine ⟨{
   Q := S
   z6 := Tf
   a := aS
   admissible := aci
   pairwise_disjoint := d7.mono hDisj hsub
   K := K
   K_pos := hKpos
   Bk := Vz
   q6 := ?_
   Ee := ?_
   L9 := M7
   yD := OQ
   Bm := Y6
  }, rfl, rfl, rfl⟩
 ·intro q hq
  exact (yT q (hsub hq)).2
 ·intro q hq
  simpa [eW] using QZ q hq
lemma Ow {S : Finset ℕ} {K : ℕ} {H : ℝ}
  (hH : 1 ≤ H)
  (Ek : ∀ q ∈ S, q ≠ 0)
  (M7 : ∀ q ∈ S, omega q = K)
  (QZ : ∀ q ∈ S, (cQ q : ℝ) ≤ H) :
  ∀ r ∈ S.image rad,
   (S.filter fun q => rad q = r).card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) := by
 intro r hr
 let F : Finset ℕ := S.filter fun q => rad q = r
 have akB : ∀ q ∈ F, q ≠ 0 := by
  intro q hq
  exact Ek q (Finset.mem_filter.1 hq).1
 have hF :
   ∀ q ∈ F, rad q = r ∧ omega q = K ∧ (cQ q : ℝ) ≤ H := by
  intro q hq
  exact ⟨(Finset.mem_filter.1 hq).2,
   M7 q (Finset.mem_filter.1 hq).1,
   QZ q (Finset.mem_filter.1 hq).1⟩
 have hreal := Rj F r K H hH akB hF
 have akC : H ^ 2 * (2 : ℝ) ^ K ≤
   (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) : ℝ) :=
  Nat.le_ceil _
 exact_mod_cast hreal.trans akC
lemma N7 {S : Finset ℕ} {K : ℕ} {H : ℝ}
  (hH : 1 ≤ H)
  (Ek : ∀ q ∈ S, q ≠ 0)
  (M7 : ∀ q ∈ S, omega q = K)
  (QZ : ∀ q ∈ S, (cQ q : ℝ) ≤ H) :
  ∃ S' : Finset ℕ,
   S' ⊆ S ∧
   (∀ q ∈ S', ∀ r ∈ S', rad q = rad r → q = r) ∧
   S.card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) * S'.card := by
 exact Jw S rad
  (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K))
  (Ow hH Ek M7 QZ)
lemma zS
  {N K : ℕ} {Q S : Finset ℕ} (a : gJ Q)
  (hsub : S ⊆ Q)
  (yT : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
  (hDisj : d7 Q a)
  (Tf : S.Nonempty)
  (hKpos : 1 ≤ K)
  (OQ : (K : ℝ) ≤ 3 * aO N)
  (hH : 1 ≤ eW N)
  (Vz : ∀ q ∈ S, (N : ℝ) * bF (-2) N ≤ (q : ℝ))
  (QZ : ∀ q ∈ S, (cQ q : ℝ) ≤ eW N)
  (M7 : ∀ q ∈ S, omega q = K) :
  ∃ D : bC N, D.Q ⊆ S ∧
   S.card ≤ Nat.ceil (eW N ^ 2 * (2 : ℝ) ^ K) * D.Q.card := by
 have Ek : ∀ q ∈ S, q ≠ 0 := by
  intro q hq
  have hqpos : 1 ≤ q := (yT q (hsub hq)).1
  omega
 rcases N7
   (S := S) (K := K) (H := eW N)
   hH Ek M7 QZ with
  ⟨S', VA, Y6, XS⟩
 have acj : S'.Nonempty := by
  by_contra hnone
  have agn : S' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hnone
  have adz : 0 < S.card := Tf.card_pos
  have alK : S.card ≤ 0 := by
   simpa [agn] using XS
  exact (Nat.lt_irrefl 0) (adz.trans_le alK)
 rcases S9 (N := N) (Q := Q) (S := S') a
   (fun q hq => hsub (VA hq))
   yT hDisj acj K hKpos
   (fun q hq => Vz q (VA hq))
   (fun q hq => QZ q (VA hq))
   (fun q hq => M7 q (VA hq))
   OQ
   (fun q hq r hr hrad => Y6 q hq r hr hrad) with
  ⟨D, hDQ, am7, hDcard⟩
 refine ⟨D, hDQ ▸ VA, ?_⟩
 simpa [hDQ] using XS
lemma PW (S : Finset ℕ) (T : ℕ)
  (_hS : S.Nonempty) (agp : ∀ q ∈ S, omega q ≤ T) :
  ∃ K : ℕ,
   K ≤ T ∧ S.card ≤ (T + 1) * (S.filter fun q => omega q = K).card := by
 classical
 have Xh : (Finset.range (T + 1)).Nonempty := by
  exact ⟨0, by simp⟩
 have hB : ∀ q ∈ S, omega q ∈ Finset.range (T + 1) := by
  intro q hq
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (agp q hq)
 rcases Eh S (Finset.range (T + 1)) omega Xh hB with
  ⟨K, hKmem, hK⟩
 refine ⟨K, ?_, ?_⟩
 ·exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hKmem)
 ·simpa [Finset.card_range] using hK
theorem Ga :
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop,
   ∀ Q : Finset ℕ, ∀ a : gJ Q,
    (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
    d7 Q a →
    (Q.card : ℝ) ≥ (N : ℝ) * bF (-1) N →
    ∃ D : bC N, D.Q ⊆ Q ∧
     (D.Q.card : ℝ) ≥ (Q.card : ℝ) * bF (-ε) N := by
 intro ε hε hεle
 let μ : ℝ := ε / 24
 have hμ : 0 < μ := by
  dsimp [μ]
  positivity
 have hε3 : 0 < ε / 3 := by positivity
 have Ut : 1 + μ + ε + μ ≤ 2 := by
  dsimp [μ]
  nlinarith
 have aad : 1 + μ + ε + μ ≤ (4 / 3 : ℝ) := by
  dsimp [μ]
  nlinarith
 filter_upwards [Ro 2 (by norm_num),
   Dz,
   B9 (ε / 3) hε3,
   s9 (ε / 3) hε3,
   v7 (A := μ) (c := 1 / 6) hμ (by norm_num),
   v7 (A := ε / 3) (c := 1 / 2) hε3 (by norm_num),
   qO (1 + μ + ε),
   C8] with
  N ajb adA acn agq agr Y7 adB aeU
  Q a yT hDisj adC
 classical
 have hf : (N : ℝ) * bF (-(1+μ)) N ≤ (N:ℝ) * bF (-1) N :=
  mul_le_mul_of_nonneg_left (oN (by linarith) N) (by positivity)
 have WB : ((N : ℝ) * bF (-1) N) * bF (-ε) N ≤ (Q.card:ℝ) :=
  (mul_le_of_le_one_right (by positivity [rW (-1) N]) (WJ hε.le N)).trans adC
 let T : ℕ := Nat.floor (3 * aO N)
 let z8 : Finset ℕ :=
  Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * bF (-2) N)
 let z9 : Finset ℕ :=
  Q.filter (fun q : ℕ => T ≤ omega q)
 let Tj : Finset ℕ :=
  Q.filter (fun q : ℕ => eW N < (cQ q : ℝ))
 let Good : Finset ℕ := Q \ (z8 ∪ z9 ∪ Tj)
 have DA : Q ⊆ Finset.Icc 1 N := by
  intro q hq
  exact Finset.mem_Icc.2 (yT q hq)
 have ags :
   (N : ℝ) * bF (-(1 + μ + ε)) N ≤ (Q.card : ℝ) :=
  zX WB hf
 have Uv : (1 : ℝ) < (Q.card : ℝ) :=
  adB.trans_le ags
 have aae : z8 ⊆ Q := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1
 have aaf : z9 ⊆ Q := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1
 have aeV : Tj ⊆ Q := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1
 have aaR : (z8.card : ℝ) ≤ bF (-μ) N * (Q.card : ℝ) := by
  simpa [z8] using
   wR
    (ε := ε) (η := μ) (δ := μ) Ut yT WB hf
 have aco :
   (z9.card : ℝ) ≤ bF (-μ) N * (Q.card : ℝ) := by
  have hTail :
    (Q.filter (fun q : ℕ => T ≤ omega q)).card
     ≤ Nat.floor ((N : ℝ) * bF (-(4 / 3)) N) := by
   simpa [T] using adA Q DA
  simpa [z9] using
   zR
    (A := 4 / 3) (ε := ε) (η := μ) (δ := μ)
    aad WB hf hTail
 have ahK : (Tj.card : ℝ) ≤ bF (-μ) N * (Q.card : ℝ) := by
  have ajc :
    (Q.filter fun q : ℕ => eW N < (cQ q : ℝ)).card
     ≤ Nat.floor ((N : ℝ) * bF (-2) N) :=
   ajb Q DA
  simpa [Tj] using
   z7
    (A := 2) (ε := ε) (η := μ) (δ := μ)
    Ut WB hf ajc
 have XT :
   (Good.card : ℝ) ≥
    (1 - (bF (-μ) N + bF (-μ) N + bF (-μ) N)) *
     (Q.card : ℝ) := by
  simpa [Good] using
   Jv Q z8 z9 Tj
    aae aaf aeV
    aaR aco ahK
 have Rw :
   (Q.card : ℝ) * bF (-(ε / 3)) N ≤ (Good.card : ℝ) := by
  have hcoeff :
    bF (-(ε / 3)) N ≤
     1 - (bF (-μ) N + bF (-μ) N + bF (-μ) N) := by
   linarith [agr, Y7]
  calc
   (Q.card : ℝ) * bF (-(ε / 3)) N
     ≤ (Q.card : ℝ) *
       (1 - (bF (-μ) N + bF (-μ) N + bF (-μ) N)) := by
      exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
   _ ≤ (Good.card : ℝ) := by
      simpa [mul_comm] using XT
 have Y8 : Good.Nonempty := by
  have hpos : 0 < (Good.card : ℝ) := by
   have hLpos : 0 < bF (-(ε / 3)) N := rW _ _
   exact lt_of_lt_of_le (mul_pos (lt_trans zero_lt_one Uv) hLpos)
    Rw
  exact Finset.card_pos.1 (by exact_mod_cast hpos)
 have MQ : Good ⊆ Q := by
  intro q hq
  exact Finset.mem_sdiff.1 hq |>.1
 have Y9 :
   ∀ q ∈ Good, (N : ℝ) * bF (-2) N ≤ (q : ℝ) := by
  intro q hq
  have hqQ : q ∈ Q := MQ hq
  have hnot : q ∉ z8 := by
   have M8 : q ∉ z8 ∪ z9 ∪ Tj :=
    (Finset.mem_sdiff.1 hq).2
   intro hbad
   exact M8 (by simp [hbad])
  exact le_of_not_gt (by
   intro hlt
   exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
 have adD :
   ∀ q ∈ Good, (cQ q : ℝ) ≤ eW N := by
  intro q hq
  have hqQ : q ∈ Q := MQ hq
  have hnot : q ∉ Tj := by
   have M8 : q ∉ z8 ∪ z9 ∪ Tj :=
    (Finset.mem_sdiff.1 hq).2
   intro hbad
   exact M8 (by simp [hbad])
  exact le_of_not_gt (by
   intro hlt
   exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
 have Zb : ∀ q ∈ Good, omega q ≤ T := by
  intro q hq
  have hqQ : q ∈ Q := MQ hq
  have hnot : q ∉ z9 := by
   have M8 : q ∉ z8 ∪ z9 ∪ Tj :=
    (Finset.mem_sdiff.1 hq).2
   intro hbad
   exact M8 (by simp [hbad])
  have amK : ¬ T ≤ omega q := by
   intro hle
   exact hnot (Finset.mem_filter.2 ⟨hqQ, hle⟩)
  omega
 rcases PW Good T Y8 Zb with
  ⟨K, akD, Zd⟩
 let Fiber : Finset ℕ := Good.filter fun q : ℕ => omega q = K
 have VE :
   (Good.card : ℝ) * bF (-(ε / 3)) N ≤ (Fiber.card : ℝ) := by
  simpa [Fiber, T] using
   rP
    (S := Good) (S' := Good.filter fun q : ℕ => omega q = K)
    (C := T + 1) (N := N) (η := ε / 3)
    Zd acn
 have Q7 : Fiber.Nonempty := by
  have hpos : 0 < (Fiber.card : ℝ) := by
   exact lt_of_lt_of_le
    (mul_pos
     (lt_of_lt_of_le
      (mul_pos (lt_trans zero_lt_one Uv) (rW _ _))
      Rw)
     (rW _ _))
    VE
  exact Finset.card_pos.1 (by exact_mod_cast hpos)
 have VF : Fiber ⊆ Q := by
  intro q hq
  exact MQ (Finset.mem_filter.1 hq).1
 have Q8 :
   ∀ q ∈ Fiber, (N : ℝ) * bF (-2) N ≤ (q : ℝ) := by
  intro q hq
  exact Y9 q (Finset.mem_filter.1 hq).1
 have acp :
   ∀ q ∈ Fiber, (cQ q : ℝ) ≤ eW N := by
  intro q hq
  exact adD q (Finset.mem_filter.1 hq).1
 have VJ : ∀ q ∈ Fiber, omega q = K := by
  intro q hq
  exact (Finset.mem_filter.1 hq).2
 have OQ : (K : ℝ) ≤ 3 * aO N := by
  have adG : (T : ℝ) ≤ 3 * aO N := by
   dsimp [T]
   exact Nat.floor_le (mul_nonneg (by norm_num) (pD N))
  have aeW : (K : ℝ) ≤ (T : ℝ) := by
   exact_mod_cast akD
  exact aeW.trans adG
 have hKpos : 1 ≤ K := by
  rcases Q7 with ⟨q, hq⟩
  have ac4 : 1 ≤ omega q :=
   aeU q (Q8 q hq)
  rw [VJ q hq] at ac4
  exact ac4
 have acq : 1 ≤ eW N := by
  rw [show (1 : ℝ) = Real.exp 0 by simp, eW]
  exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
 rcases zS (N := N) (K := K)
   (Q := Q) (S := Fiber) a VF yT hDisj
   Q7 hKpos OQ acq
   Q8 acp VJ with
  ⟨D, hDF, acr⟩
 have aag :
   (Fiber.card : ℝ) * bF (-(ε / 3)) N ≤ (D.Q.card : ℝ) := by
  exact rP
   (S := Fiber) (S' := D.Q)
   (C := Nat.ceil (eW N ^ 2 * (2 : ℝ) ^ K))
   (N := N) (η := ε / 3) acr (agq K OQ)
 refine ⟨D, hDF.trans VF, ?_⟩
 have ahL :
   bF (-ε) N =
    bF (-(ε / 3)) N * bF (-(ε / 3)) N *
     bF (-(ε / 3)) N := by
  calc
   bF (-ε) N
     = bF (-(ε / 3) + -(ε / 3) + -(ε / 3)) N := by
       congr 1
       ring
   _ = bF (-(ε / 3) + -(ε / 3)) N *
      bF (-(ε / 3)) N := by
       rw [JT]
   _ = bF (-(ε / 3)) N * bF (-(ε / 3)) N *
      bF (-(ε / 3)) N := by
       rw [JT]
 calc
  (Q.card : ℝ) * bF (-ε) N
    = (((Q.card : ℝ) * bF (-(ε / 3)) N) *
      bF (-(ε / 3)) N) * bF (-(ε / 3)) N := by
     rw [ahL]
     ring
  _ ≤ ((Good.card : ℝ) * bF (-(ε / 3)) N) *
     bF (-(ε / 3)) N := by
     exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Rw (nF _ _))
      (nF _ _)
  _ ≤ (Fiber.card : ℝ) * bF (-(ε / 3)) N := by
     exact mul_le_mul_of_nonneg_right VE (nF _ _)
  _ ≤ (D.Q.card : ℝ) := aag
end dO
open Filter dO
private lemma wS (N : ℕ) (c : ℝ) : scaleL N ^ c = bF c N := by
 rw [scaleL, ← Real.exp_mul, mul_comm]
 rfl
theorem solve : OMA.R2.H1 := by
 intro ε he hδ
 filter_upwards [Ga ε he hδ] with N hN Q a hr hd ht
 have hdis : d7 Q (fun i => a i.val) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  exact hd i.val i.property j.val j.property (fun e => hij (Subtype.ext e)) ⟨z,hzi,hzj⟩
 rw [wS] at ht
 obtain ⟨D, hs, hl⟩ := hN Q (fun i => a i.val) hr hdis ht
 refine ⟨D.Q,D.K,hs,?_,D.K_pos,D.yD,?_,?_⟩
 ·simpa only [wS] using hl
 ·intro q hq
  refine ⟨by simpa only [wS] using D.Bk q hq, ?_, ?_⟩
  ·simpa only [cQ,aD,Nat.support_factorization] using D.Ee q hq
  ·simpa only [omega,aD,Nat.support_factorization] using D.L9 q hq
 ·simpa only [rad,aD,Nat.support_factorization] using D.Bm
end OMA.L1

namespace OMA.L2
namespace cP
open Filter
open Asymptotics
open scoped BigOperators
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
 {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}
abbrev gJ (Q : Finset ℕ) : Type :=
 {q : ℕ // q ∈ Q} → ℤ
def d7
  (Q : Finset ℕ) (a : gJ Q) : Prop :=
 ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
  Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))
def nY {Q Q' : Finset ℕ}
  (a : gJ Q) (hsub : Q' ⊆ Q) : gJ Q' :=
 fun q => a ⟨q.1, hsub q.2⟩
lemma d7.mono
  {Q Q' : Finset ℕ} {a : gJ Q}
  (hdisj : d7 Q a) (hsub : Q' ⊆ Q) :
  d7 Q' (nY a hsub) := by
 intro i j hij
 let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
 let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
 have afV : iQ ≠ jQ := by
  intro h
  have hval : iQ.1 = jQ.1 :=
   congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
  exact hij (Subtype.ext hval)
 simpa [nY, iQ, jQ] using hdisj iQ jQ afV
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
 (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
 ∃ a : gJ Q, d7 Q a
noncomputable def aZ (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))
noncomputable def bF (α : ℝ) (N : ℕ) : ℝ :=
 Real.exp (α * aZ N)
noncomputable def aO (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))
lemma nD (N : ℕ) : 0 ≤ aZ N :=
 Real.sqrt_nonneg _
lemma lJ {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < aZ N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [aZ, Real.sqrt_pos]
 exact mul_pos gC c8
lemma gN {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aZ N =
   Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 rw [aZ, Real.sqrt_mul d6]
lemma pD (N : ℕ) : 0 ≤ aO N :=
 Real.sqrt_nonneg _
lemma g5 {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < aO N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [aO, Real.sqrt_pos]
 exact div_pos gC c8
lemma gW {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aO N * Real.log (Real.log (N : ℝ)) = aZ N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have aaA : 0 ≤ aO N * Real.log (Real.log (N : ℝ)) :=
  mul_nonneg (pD N) f8
 have hsq :
   (aO N * Real.log (Real.log (N : ℝ))) ^ 2 = (aZ N) ^ 2 := by
  rw [aO, aZ, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
  ·field_simp [c8.ne']
  ·exact mul_nonneg d6 f8
  ·exact div_nonneg d6 f8
 rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
 ·exact h
 ·have aac : 0 ≤ aZ N := nD N
  nlinarith
lemma j4 {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aZ N / aO N = Real.log (Real.log (N : ℝ)) := by
 have SH := gW hN
 have hMpos := g5 hN
 rw [← SH]
 field_simp [hMpos.ne']
lemma tB {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  aO N * aZ N = Real.log (N : ℝ) := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have SH := gW hN
 have afW : aO N ^ 2 =
   Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  rw [aO, Real.sq_sqrt]
  exact div_nonneg d6 f8
 calc
  aO N * aZ N
    = aO N * (aO N * Real.log (Real.log (N : ℝ))) := by rw [SH]
  _ = aO N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
  _ = Real.log (N : ℝ) := by
     rw [afW]
     field_simp [c8.ne']
lemma nS :
  Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
   atTop (nhds 0) := by
 have hreal :
   Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
  have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
    fun x : ℝ => Real.log x :=
   Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact hsmall.tendsto_div_nhds_zero
 exact hreal.comp tendsto_natCast_atTop_atTop
lemma iw :
  Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
 exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
  tendsto_natCast_atTop_atTop
lemma pO :
  Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
 exact Real.tendsto_sqrt_atTop.comp iw
lemma f9 (A : ℝ) :
  ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
 pO.eventually_ge_atTop A
lemma P7 :
  ∀ᶠ N : ℕ in atTop, aO N ≤ Real.log (N : ℝ) := by
 filter_upwards [f9 1,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have d6 : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans bY).le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have yQ : 1 ≤ Real.log (Real.log (N : ℝ)) := by
  rw [← Real.one_le_sqrt]
  exact hsqrt
 rw [aO]
 rw [Real.sqrt_le_left d6]
 have aaS :
   Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
  exact (div_le_iff₀ c8).2 (by nlinarith [d6, yQ])
 have adH : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
  nlinarith [bY.le]
 exact aaS.trans adH
lemma oM (A : ℝ) (hA : 0 < A) :
  ∀ᶠ N : ℕ in atTop, A ≤ aO N := by
 have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
 have Rd : (0 : ℝ) < 1 / A ^ 2 := by positivity
 have OV : ∀ᶠ N : ℕ in atTop,
   Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
  nS.eventually_lt_const Rd
 filter_upwards [OV, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
  with N hsmall dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have SI :
   Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
  (div_lt_iff₀ gC).1 hsmall
 have adg :
   A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
  have hmul := mul_lt_mul_of_pos_left SI hA2
  field_simp [hA2.ne'] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
 have W8 :
   A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
  (le_div_iff₀ c8).2 adg.le
 rw [aO]
 exact (Real.le_sqrt hA.le (div_nonneg gC.le c8.le)).2 W8
lemma rW (α : ℝ) (N : ℕ) : 0 < bF α N :=
 Real.exp_pos _
lemma oN {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
  bF α N ≤ bF β N := by
 exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (nD N))
lemma Dm {N : ℕ} (hN : 0 < N) (α : ℝ) :
  Real.log ((N : ℝ) * bF α N) = Real.log (N : ℝ) + α * aZ N := by
 have U9 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
 have hL : bF α N ≠ 0 := (rW α N).ne'
 rw [Real.log_mul U9 hL, bF, Real.log_exp]
lemma vE
  {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
  (residueClass q a ∩ residueClass r b).Nonempty ↔
   a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
 constructor
 ·rintro ⟨n, hnq, hnr⟩
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
 ·intro hab
  rw [Int.modEq_iff_dvd] at hab
  rcases hab with ⟨k, hk⟩
  let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
  refine ⟨n, ?_, ?_⟩
  ·rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
   refine ⟨-(Nat.gcdA q r * k), ?_⟩
   simp [n]
   ring
  ·rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
   refine ⟨Nat.gcdB q r * k, ?_⟩
   have alL := Nat.gcd_eq_gcd_ab q r
   calc
    b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
     simp [n]
     ring
    _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
     rw [hk]
    _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
       - (q : ℤ) * Nat.gcdA q r * k := by
     rw [alL]
    _ = (r : ℤ) * (Nat.gcdB q r * k) := by
     ring
lemma Ox
  {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
  Disjoint (residueClass q a) (residueClass r b) ↔
   ¬ a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
 rw [Set.disjoint_iff_inter_eq_empty]
 constructor
 ·intro h hmod
  have hne : (residueClass q a ∩ residueClass r b).Nonempty :=
   (vE hq hr a b).2 hmod
  exact hne.ne_empty h
 ·intro hmod
  ext n
  constructor
  ·intro hn
   exact False.elim (hmod ((vE hq hr a b).1 ⟨n, hn⟩))
  ·intro hn
   cases hn
end cP
namespace cP
open Finset
open scoped BigOperators
def aD (n : ℕ) : Finset ℕ :=
 n.factorization.support
def omega (n : ℕ) : ℕ :=
 (aD n).card
def rad (n : ℕ) : ℕ :=
 ∏ p ∈ aD n, p
def cQ (n : ℕ) : ℕ :=
 ∏ p ∈ aD n, n.factorization p
def cD (C : Finset ℕ) (q : ℕ) : ℕ :=
 ∏ p ∈ C, p ^ q.factorization p
lemma Dp (n : ℕ) : 0 < cQ n := by
 unfold cQ aD
 exact Finset.prod_pos (fun _p hp =>
  Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))
lemma SK : cQ 1 = 1 := by
 simp [cQ, aD]
lemma Ra (n : ℕ) : 0 < (1 : ℝ) / ((cQ n : ℝ) ^ 2) := by
 have hn : 0 < (cQ n : ℝ) := by exact_mod_cast Dp n
 positivity
lemma f7 {n p : ℕ} (hp : p ∈ aD n) : Nat.Prime p := by
 unfold aD at hp
 rw [Nat.support_factorization] at hp
 exact Nat.prime_of_mem_primeFactors hp
lemma k6 {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
  (hpn : p ∣ n) : p ∈ aD n := by
 unfold aD
 rw [Finsupp.mem_support_iff]
 exact hp.factorization_pos_of_dvd hn hpn |>.ne'
lemma Iq {m n : ℕ}
  (hm : m ≠ 0) (hn : n ≠ 0)
  (hdisj : Disjoint (aD m) (aD n)) :
  Nat.Coprime m n := by
 refine Nat.coprime_of_dvd ?_
 intro p hp hpm hpn
 exact (Finset.disjoint_left.1 hdisj)
  (k6 hp hm hpm)
  (k6 hp hn hpn)
lemma dL {m n : ℕ} (hcop : Nat.Coprime m n) :
  Disjoint (aD m) (aD n) := by
 rw [Finset.disjoint_left]
 intro p hpm hpn
 have hp : Nat.Prime p := f7 hpm
 have afX : p ∣ m := Nat.dvd_of_factorization_pos (by
  unfold aD at hpm
  exact Finsupp.mem_support_iff.1 hpm)
 have afY : p ∣ n := Nat.dvd_of_factorization_pos (by
  unfold aD at hpn
  exact Finsupp.mem_support_iff.1 hpn)
 have hp1 : p ∣ 1 := by
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd afX afY
 exact hp.not_dvd_one hp1
lemma g9 {m n : ℕ} (hcop : Nat.Coprime m n) :
  aD (m * n) = aD m ∪ aD n := by
 unfold aD
 rw [Nat.factorization_mul_of_coprime hcop]
 exact Finsupp.support_add_eq (dL hcop)
lemma Kh {m n : ℕ} (hcop : Nat.Coprime m n) :
  omega (m * n) = omega m + omega n := by
 unfold omega
 rw [g9 hcop]
 exact Finset.card_union_of_disjoint (dL hcop)
lemma u6 {m n : ℕ} (hcop : Nat.Coprime m n) :
  cQ (m * n) = cQ m * cQ n := by
 unfold cQ
 rw [g9 hcop]
 rw [Finset.prod_union (dL hcop)]
 congr 1
 ·apply Finset.prod_congr rfl
  intro p hp
  have lK : p ∉ aD n :=
   (Finset.disjoint_left.1 (dL hcop)) hp
  have hnzero : n.factorization p = 0 := by
   unfold aD at lK
   exact Finsupp.notMem_support_iff.1 lK
  rw [Nat.factorization_mul_of_coprime hcop]
  simp [hnzero]
 ·apply Finset.prod_congr rfl
  intro p hp
  have lK : p ∉ aD m :=
   (Finset.disjoint_left.1 (dL hcop).symm) hp
  have hmzero : m.factorization p = 0 := by
   unfold aD at lK
   exact Finsupp.notMem_support_iff.1 lK
  rw [Nat.factorization_mul_of_coprime hcop]
  simp [hmzero]
lemma UK {C : Finset ℕ} {m n : ℕ}
  (h : ∀ p ∈ C, m.factorization p = n.factorization p) :
  cD C m = cD C n := by
 unfold cD
 apply Finset.prod_congr rfl
 intro p hp
 rw [h p hp]
lemma Eb (C : Finset ℕ) (q : ℕ) : cD C q ∣ q := by
 by_cases hq : q = 0
 ·simp [hq]
 ·nth_rw 2 [← Nat.factorization_prod_pow_eq_self hq]
  unfold cD
  have hfilter :
    (∏ p ∈ C, p ^ q.factorization p) =
     ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
      p ^ q.factorization p := by
   refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
   intro p hpC XO
   have W9 : p ∉ q.factorization.support := by
    intro hp
    exact XO (Finset.mem_filter.2 ⟨hpC, hp⟩)
   have hzero : q.factorization p = 0 := by
    by_contra hne
    exact W9 (Finsupp.mem_support_iff.2 hne)
   simp [hzero]
  rw [hfilter]
  exact Finset.prod_dvd_prod_of_subset
   (C.filter (fun p => p ∈ q.factorization.support))
   q.factorization.support
   (fun p => p ^ q.factorization p)
   (by
    intro p hp
    exact (Finset.mem_filter.1 hp).2)
lemma kC {C : Finset ℕ} {q p : ℕ}
  (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
  (cD C q).factorization p = q.factorization p := by
 unfold cD
 have tD : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
  intro x hx
  exact pow_ne_zero _ (hC x hx).ne_zero
 rw [Nat.factorization_prod tD, Finsupp.finset_sum_apply]
 rw [Finset.sum_eq_single p]
 ·rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
 ·intro x hx hxp
  rw [(hC x hx).factorization_pow]
  exact Finsupp.single_eq_of_ne hxp.symm
 ·intro lK
  exact (lK hpC).elim
lemma vG {C : Finset ℕ} {q : ℕ}
  (hC : ∀ p ∈ C, Nat.Prime p)
  (hCq : C ⊆ aD q) :
  aD (cD C q) = C := by
 unfold aD cD
 ext p
 have tD : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
  intro x hx
  exact pow_ne_zero _ (hC x hx).ne_zero
 rw [Nat.factorization_prod tD, Finsupp.mem_support_iff]
 constructor
 ·intro hsum
  by_contra hpC
  apply hsum
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
  intro x hx
  have afZ : x ≠ p := by
   intro hxp
   exact hpC (hxp ▸ hx)
  rw [(hC x hx).factorization_pow]
  exact Finsupp.single_eq_of_ne afZ.symm
 ·intro hpC
  have hp : Nat.Prime p := hC p hpC
  have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
  intro hsum
  rw [Finsupp.finset_sum_apply] at hsum
  have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
  rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
  exact hqpos hterm
lemma QD (C : Finset ℕ) (q : ℕ) :
  cQ (cD C q) ≤ cQ q := by
 by_cases hq : q = 0
 ·simp [cQ, aD, cD, hq]
 ·have hdvd : cD C q ∣ q := Eb C q
  have SM : cD C q ≠ 0 := by
   exact (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)).ne'
  have VK : (cD C q).factorization ≤ q.factorization :=
   (Nat.factorization_le_iff_dvd SM hq).2 hdvd
  have hsub : aD (cD C q) ⊆ aD q := by
   intro p hp
   unfold aD at hp ⊢
   rw [Finsupp.mem_support_iff] at hp ⊢
   exact (Nat.pos_of_ne_zero hp).trans_le (VK p) |>.ne'
  unfold cQ
  have aaT :
    (∏ p ∈ aD (cD C q), (cD C q).factorization p)
     ≤ ∏ p ∈ aD (cD C q), q.factorization p := by
   exact Finset.prod_le_prod' (fun p _hp => VK p)
  have aaU :
    (∏ p ∈ aD (cD C q), q.factorization p)
     ≤ ∏ p ∈ aD q, q.factorization p := by
   exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp aaE => by
    unfold aD at hp
    rw [Finsupp.mem_support_iff] at hp
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
  exact aaT.trans aaU
lemma Ze {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
  cQ m ≤ cQ n := by
 have hm : m ≠ 0 := by
  intro hm0
  subst m
  exact hn (zero_dvd_iff.mp hmn)
 have VK : m.factorization ≤ n.factorization :=
  (Nat.factorization_le_iff_dvd hm hn).2 hmn
 have hsub : aD m ⊆ aD n := by
  intro p hp
  unfold aD at hp ⊢
  rw [Finsupp.mem_support_iff] at hp ⊢
  exact (Nat.pos_of_ne_zero hp).trans_le (VK p) |>.ne'
 unfold cQ
 have aaT :
   (∏ p ∈ aD m, m.factorization p)
    ≤ ∏ p ∈ aD m, n.factorization p := by
  exact Finset.prod_le_prod' (fun p _hp => VK p)
 have aaU :
   (∏ p ∈ aD m, n.factorization p)
    ≤ ∏ p ∈ aD n, n.factorization p := by
  exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp aaE => by
   unfold aD at hp
   rw [Finsupp.mem_support_iff] at hp
   exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
 exact aaT.trans aaU
def dY (P q : ℕ) : Finset ℕ :=
 aD (q / P)
lemma Bq {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
  aD m ⊆ aD n := by
 have hm : m ≠ 0 := by
  intro hm0
  subst m
  exact hn (zero_dvd_iff.mp hmn)
 have hle : m.factorization ≤ n.factorization :=
  (Nat.factorization_le_iff_dvd hm hn).2 hmn
 intro p hp
 unfold aD at hp ⊢
 rw [Finsupp.mem_support_iff] at hp ⊢
 intro hnzero
 exact hp (Nat.eq_zero_of_le_zero (by simpa [hnzero] using hle p))
lemma XZ {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
  omega m ≤ omega n := by
 unfold omega
 exact Finset.card_le_card (Bq hmn hn)
lemma Kj {P q : ℕ} (hPq : P ∣ q) (hq : q ≠ 0) :
  aD (q / P) ⊆ aD q :=
 Bq (by
  refine ⟨P, ?_⟩
  exact (Nat.div_mul_cancel hPq).symm) hq
lemma qw {P q : ℕ}
  (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0) :
  aD q = aD P ∪ aD (q / P) := by
 ext p
 unfold aD
 rw [Finset.mem_union]
 simp only [Finsupp.mem_support_iff]
 constructor
 ·intro akE
  by_cases WC : P.factorization p = 0
  ·right
   have Zj :
     (q / P).factorization p = q.factorization p - P.factorization p := by
    rw [Nat.factorization_div hPq]
    rfl
   rw [Zj, WC, Nat.sub_zero]
   exact akE
  ·exact Or.inl WC
 ·rintro (WC | Zj)
  ·have hle : P.factorization ≤ q.factorization :=
    (Nat.factorization_le_iff_dvd hP hq).2 hPq
   intro ajd
   exact WC (Nat.eq_zero_of_le_zero (by simpa [ajd] using hle p))
  ·have hmem : p ∈ aD (q / P) := by
    unfold aD
    rw [Finsupp.mem_support_iff]
    exact Zj
   have ahj := Kj hPq hq hmem
   unfold aD at ahj
   rwa [Finsupp.mem_support_iff] at ahj
lemma jh {P q p : ℕ} (hPq : P ∣ q) :
  p ∈ dY P q ↔ P.factorization p < q.factorization p := by
 unfold dY aD
 rw [Finsupp.mem_support_iff, Nat.factorization_div hPq]
 exact Nat.sub_ne_zero_iff_lt
lemma Lg {P q : ℕ}
  (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
  (hdisj : Disjoint (aD P) (aD (q / P))) :
  omega q = omega P + omega (q / P) := by
 unfold omega
 rw [qw hPq hP hq, Finset.card_union_of_disjoint hdisj]
lemma xG {P q : ℕ}
  (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
  (hdisj : Disjoint (aD P) (aD (q / P))) :
  omega (q / P) = omega q - omega P := by
 have hsum := Lg hPq hP hq hdisj
 omega
lemma vH {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
  n = 1 := by
 have hsupp : aD n = ∅ := by
  have hcard : (aD n).card = 0 := by simpa [omega] using hω
  exact Finset.card_eq_zero.mp hcard
 unfold aD at hsupp
 have O1 : n.factorization.prod (fun p e => p ^ e) = 1 := by
  unfold Finsupp.prod
  rw [hsupp]
  simp
 have hprod := Nat.factorization_prod_pow_eq_self hn
 rw [← hprod]
 exact O1
lemma DB {P q r : ℕ}
  (hPq : P ∣ q) (hPr : P ∣ r)
  (hP : P ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
  (hdisj : Disjoint (dY P q) (dY P r)) :
  Nat.gcd q r ∣ P := by
 rw [← Nat.factorization_le_iff_dvd (by
   intro hg
   exact hq (Nat.gcd_eq_zero_iff.mp hg).1) hP]
 rw [Nat.factorization_gcd hq hr]
 intro p
 rw [Finsupp.inf_apply]
 have amA : P.factorization p ≤ q.factorization p :=
  (Nat.factorization_le_iff_dvd hP hq).2 hPq p
 have amB : P.factorization p ≤ r.factorization p :=
  (Nat.factorization_le_iff_dvd hP hr).2 hPr p
 by_cases ac5 : P.factorization p < q.factorization p
 ·have akF : ¬ P.factorization p < r.factorization p := by
   intro ahM
   exact (Finset.disjoint_left.1 hdisj)
    ((jh hPq).2 ac5)
    ((jh hPr).2 ahM)
  have alM : r.factorization p ≤ P.factorization p := le_of_not_gt akF
  exact le_trans (min_le_right _ _) alM
 ·have hqle : q.factorization p ≤ P.factorization p := le_of_not_gt ac5
  exact le_trans (min_le_left _ _) hqle
end cP
namespace cP
open Finset
open scoped BigOperators
def jN {α : Type*} [DecidableEq α]
  (A : Finset (Finset α)) (k : ℕ) : Prop :=
 ∀ S ∈ A, S.card = k
def DG {α : Type*} [DecidableEq α]
  (A : Finset (Finset α)) (κ : ℝ) : Prop :=
 ∀ T : Finset α, T.Nonempty →
  ((A.filter fun S => T ⊆ S).card : ℝ) ≤
   (A.card : ℝ) / κ ^ T.card
def p9 {α : Type*} [DecidableEq α]
  (B : Finset (Finset α)) : Prop :=
 ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def aV (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
 X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T
@[simp]
lemma eO {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
  T ∈ aV X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
 simp [aV, mem_powerset]
lemma DH {X : Finset α} {A : Finset (Finset α)}
  (lG : ∀ S ∈ A, S ⊆ X) :
  A ⊆ aV X A := by
 intro S hS
 exact eO.mpr ⟨lG S hS, S, hS, subset_refl _⟩
lemma Iv {X : Finset α} {A : Finset (Finset α)}
  (h : (aV X A).Nonempty) :
  A.Nonempty := by
 rcases h with ⟨T, hT⟩
 rcases eO.mp hT with ⟨_, S, hSA, _⟩
 exact ⟨S, hSA⟩
lemma Oy {X : Finset α} {A : Finset (Finset α)} :
  (∅ : Finset α) ∈ aV X A ↔ (∅ : Finset α) ∈ A := by
 constructor
 ·intro h
  rcases eO.mp h with ⟨_, S, hSA, Jp⟩
  have hS_eq : S = ∅ := by
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro x hx
   simpa using Jp hx
  simpa [hS_eq] using hSA
 ·intro h
  exact eO.mpr ⟨Finset.empty_subset X, ∅, h, subset_refl _⟩
lemma Lh {X : Finset α} {A : Finset (Finset α)} :
  (∅ : Finset α) ∉ aV X A ↔ (∅ : Finset α) ∉ A := by
 rw [Oy]
def dW (X : Finset α) (U : Finset (Finset α)) : Prop :=
 ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U
lemma oR (X : Finset α) (A : Finset (Finset α)) :
  dW X (aV X A) := by
 intro S hS T xO hST
 rcases eO.mp hS with ⟨_, S₀, P9, Xn⟩
 exact eO.mpr ⟨xO, S₀, P9, Xn.trans hST⟩
lemma vI
  {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
  (g4 : dW X U) (hS : S ∈ U) :
  aV X {S} ⊆ U := by
 intro T hT
 rcases eO.mp hT with ⟨xO, R, hR, hRT⟩
 have adI : R = S := by simpa using hR
 exact g4 S hS T xO (by simpa [adI] using hRT)
omit [DecidableEq α] in
lemma Kk {X : Finset α} {U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hU : U.Nonempty) :
  X ∈ U := by
 rcases hU with ⟨S, hS⟩
 exact g4 S hS X (subset_refl X) (hUX S hS)
omit [DecidableEq α] in
lemma Ep {X : Finset α} {U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hEmpty : (∅ : Finset α) ∈ U) :
  U = X.powerset := by
 ext S
 constructor
 ·intro hS
  exact Finset.mem_powerset.mpr (hUX S hS)
 ·intro hS
  exact g4 ∅ hEmpty S (Finset.mem_powerset.mp hS) (Finset.empty_subset S)
def f5 (_X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
 U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S
@[simp]
lemma j6 {X : Finset α} {U : Finset (Finset α)} {S : Finset α} :
  S ∈ f5 X U ↔ S ∈ U ∧ ∀ T ∈ U, ¬ T ⊂ S := by
 simp [f5]
lemma qd {X : Finset α} {U : Finset (Finset α)} :
  f5 X U ⊆ U := by
 intro S hS
 exact (j6.mp hS).1
lemma Er
  {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
  (hS : S ∈ f5 X U) (hT : T ∈ f5 X U) :
  ¬ S ⊂ T := by
 exact (j6.mp hT).2 S ((j6.mp hS).1)
lemma DJ
  {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
  (hS : S ∈ f5 X U) (hT : T ∈ f5 X U)
  (hST : S ⊆ T) :
  S = T := by
 by_contra hne
 exact Er hS hT (hST.ssubset_of_ne hne)
def gR (A : Finset (Finset α)) : Prop :=
 ∀ S ∈ A, ∀ T ∈ A, S ⊆ T → T ⊆ S
lemma Et (X : Finset α) (U : Finset (Finset α)) :
  gR (f5 X U) := by
 intro S hS T hT hST
 have hEq : S = T := DJ hS hT hST
 simp [hEq]
noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
 max 2 ((f5 X U).sup Finset.card)
lemma Ew (X : Finset α) (U : Finset (Finset α)) : 2 ≤ ell X U :=
 le_max_left _ _
lemma ahN (X : Finset α) (U : Finset (Finset α)) : 0 < ell X U :=
 lt_of_lt_of_le (by norm_num) (Ew X U)
lemma Ez
  {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
  (hS : S ∈ f5 X U) :
  S.card ≤ ell X U := by
 unfold ell
 exact (Finset.le_sup (s := f5 X U) (f := Finset.card) hS).trans
  (le_max_right _ _)
lemma yW
  {X : Finset α} {U : Finset (Finset α)}
  {S : Finset α} (hS : S ∈ U) :
  ∃ T ∈ f5 X U, T ⊆ S := by
 classical
 let candidates : Finset (Finset α) := U.filter fun T => T ⊆ S
 have hSc : S ∈ candidates := by
  simp [candidates, hS, subset_refl]
 rcases candidates.exists_min_image Finset.card ⟨S, hSc⟩ with ⟨T₀, hT₀, hmin⟩
 have alN : T₀ ∈ U := (Finset.mem_filter.mp hT₀).1
 have aje : T₀ ⊆ S := (Finset.mem_filter.mp hT₀).2
 refine ⟨T₀, j6.mpr ⟨alN, ?_⟩, aje⟩
 intro T hTU ahk
 have hTS : T ⊆ S := ahk.subset.trans aje
 have ajf : T ∈ candidates := by
  simp [candidates, hTU, hTS]
 have : T₀.card ≤ T.card := hmin T ajf
 have hlt : T.card < T₀.card := Finset.card_lt_card ahk
 exact absurd this (not_le.mpr hlt)
lemma C9
  {X : Finset α} {U : Finset (Finset α)} (hU : U.Nonempty) :
  (f5 X U).Nonempty := by
 rcases hU with ⟨S, hS⟩
 rcases yW (X := X) hS with ⟨T, hT, _⟩
 exact ⟨T, hT⟩
lemma v8
  {X : Finset α} {U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U) :
  aV X (f5 X U) = U := by
 ext S
 constructor
 ·intro hS
  rcases eO.mp hS with ⟨hSX, T, X0, hTS⟩
  exact g4 T (qd X0) S hSX hTS
 ·intro hSU
  rcases yW (X := X) hSU with ⟨T, X0, hTS⟩
  exact eO.mpr ⟨hUX S hSU, T, X0, hTS⟩
lemma pU
  {X : Finset α} {A : Finset (Finset α)}
  (mK : gR A)
  (lG : ∀ S ∈ A, S ⊆ X)
  {S : Finset α} :
  S ∈ f5 X (aV X A) ↔ S ∈ A := by
 constructor
 ·intro hS
  rcases j6.mp hS with ⟨hSup, hmin⟩
  rcases eO.mp hSup with ⟨_, S₀, P9, Xn⟩
  have aaV : S₀ ∈ aV X A :=
   eO.mpr ⟨lG S₀ P9, S₀, P9, subset_refl _⟩
  have Tk : ¬ S₀ ⊂ S := hmin S₀ aaV
  have Xo : S₀ = S := by
   by_contra hne
   exact Tk (Xn.ssubset_of_ne hne)
  simpa [← Xo] using P9
 ·intro hSA
  refine j6.mpr ⟨?_, ?_⟩
  ·exact eO.mpr ⟨lG S hSA, S, hSA, subset_refl _⟩
  ·intro T alO agt
   rcases eO.mp alO with ⟨_, S₀, P9, adJ⟩
   have Xn : S₀ ⊆ S := adJ.trans agt.subset
   have alP : S ⊆ S₀ := mK S₀ P9 S hSA Xn
   have hST : S ⊆ T := alP.trans adJ
   have hTS : T ⊆ S := agt.subset
   have hEq : T = S := le_antisymm hTS hST
   exact agt.ne hEq
lemma qX
  {X : Finset α} {A : Finset (Finset α)}
  (mK : gR A)
  (lG : ∀ S ∈ A, S ⊆ X) :
  f5 X (aV X A) = A := by
 ext S
 exact pU mK lG
theorem Ci
  {X : Finset α} {A : Finset (Finset α)}
  (mK : gR A)
  (lG : ∀ S ∈ A, S ⊆ X) :
  ell X (aV X A) = max 2 (A.sup Finset.card) := by
 unfold ell
 rw [qX mK lG]
lemma DK
  {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
  (j7 : cP.jN A k)
  (lG : ∀ S ∈ A, S ⊆ X)
  {S : Finset α} (hS : S ∈ f5 X (aV X A)) :
  S.card ≤ k := by
 classical
 rcases j6.mp hS with ⟨hSup, hmin⟩
 rcases eO.mp hSup with ⟨hSX, S₀, P9, Xn⟩
 have aaV : S₀ ∈ aV X A :=
  eO.mpr ⟨(lG S₀ P9), S₀, P9, subset_refl _⟩
 have Tk : ¬ S₀ ⊂ S := hmin S₀ aaV
 have Xo : S₀ = S := by
  by_contra hne
  exact Tk (Xn.ssubset_of_ne hne)
 have : S.card = k := Xo ▸ j7 S₀ P9
 exact this.le
theorem Xp {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
  (j7 : cP.jN A k)
  (lG : ∀ S ∈ A, S ⊆ X) :
  ell X (aV X A) ≤ max 2 k := by
 classical
 have ahO : (f5 X (aV X A)).sup Finset.card ≤ k := by
  refine Finset.sup_le ?_
  intro S hS
  exact DK j7 lG hS
 unfold ell
 exact max_le_max le_rfl ahO
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
noncomputable def aF (X S : Finset α) (p : ℝ) : ℝ :=
 p ^ S.card * (1 - p) ^ (X.card - S.card)
noncomputable def dN (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
 ∑ S ∈ X.powerset.filter (· ∈ U), aF X S p
omit [DecidableEq α] in
lemma j8 {X S : Finset α} {p : ℝ}
  (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ aF X S p := by
 unfold aF
 have : 0 ≤ 1 - p := by linarith
 positivity
lemma Rb {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
  (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : dN X U p ≤ dN X V p := by
 refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
 ·intro S hS
  rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
  exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
 ·intros
  exact j8 h0 h1
omit [DecidableEq α] in
lemma lA (X : Finset α) {p : ℝ}
  (h : p + (1 - p) = 1) :
  (∑ S ∈ X.powerset, aF X S p) = 1 := by
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
 unfold aF
 rw [hsum]
 have aeX : (p + (1 - p)) ^ X.card =
   ∑ k ∈ Finset.range (X.card + 1),
    p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
  add_pow p (1 - p) X.card
 have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
 rw [this] at aeX
 have agu :
   (∑ k ∈ Finset.range (X.card + 1),
     (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
    (∑ k ∈ Finset.range (X.card + 1),
     p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
  refine Finset.sum_congr rfl ?_
  intro k _
  ring
 rw [agu, ← aeX]
lemma adK {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (h0 : 0 ≤ p) (h1 : p ≤ 1) : dN X U p ≤ 1 := by
 have hsum := lA (α := α) X (p := p) (by ring)
 have hsub : dN X U p ≤ ∑ S ∈ X.powerset, aF X S p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  ·intro S hS; exact (Finset.mem_filter.mp hS).1
  ·intros; exact j8 h0 h1
 linarith
omit [DecidableEq α] in
lemma r6
  {Ω : Type*} [DecidableEq Ω] (s : Finset Ω)
  (weight : Ω → ℝ) (Good : Ω → Prop) [DecidablePred Good]
  (F : Ω → ℝ) {B : ℝ}
  (ED : ∀ ω ∈ s, 0 ≤ weight ω)
  (Ry : (∑ ω ∈ s, weight ω) = 1)
  (hB : 0 < B)
  (aeY : ∀ ω ∈ s, 0 ≤ F ω)
  (hbad : ∀ ω ∈ s, ¬ Good ω → B ≤ F ω)
  (havg : (∑ ω ∈ s, weight ω * F ω) < B * (1 / 2)) :
  (1 / 2 : ℝ) < ∑ ω ∈ s.filter Good, weight ω := by
 let bad : Finset Ω := s.filter fun ω => ¬ Good ω
 have Zk :
   (∑ ω ∈ bad, weight ω * B) ≤
    ∑ ω ∈ bad, weight ω * F ω := by
  refine Finset.sum_le_sum ?_
  intro ω ahl
  have hωs : ω ∈ s := (Finset.mem_filter.mp ahl).1
  have ajg : ¬ Good ω := (Finset.mem_filter.mp ahl).2
  exact mul_le_mul_of_nonneg_left (hbad ω hωs ajg)
   (ED ω hωs)
 have acs :
   (∑ ω ∈ bad, weight ω * F ω) ≤
    ∑ ω ∈ s, weight ω * F ω := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro ω hωs amL
  exact mul_nonneg (ED ω hωs) (aeY ω hωs)
 have agv :
   (∑ ω ∈ bad, weight ω) * B < B * (1 / 2) := by
  calc
   (∑ ω ∈ bad, weight ω) * B
     = ∑ ω ∈ bad, weight ω * B := by
       rw [Finset.sum_mul]
   _ ≤ ∑ ω ∈ bad, weight ω * F ω := Zk
   _ ≤ ∑ ω ∈ s, weight ω * F ω := acs
   _ < B * (1 / 2) := havg
 have afT :
   (∑ ω ∈ bad, weight ω) < (1 / 2 : ℝ) := by
  have WL :
    (∑ ω ∈ bad, weight ω) * B < (1 / 2 : ℝ) * B := by
   linarith
  exact lt_of_mul_lt_mul_right WL hB.le
 have hsplit :
   (∑ ω ∈ s.filter Good, weight ω) + (∑ ω ∈ bad, weight ω) = 1 := by
  have adL :=
   Finset.sum_filter_add_sum_filter_not
    (s := s) (p := Good) (f := weight)
  unfold bad
  simpa using adL.trans Ry
 linarith
noncomputable def bD (X : Finset α) (n : ℕ) :
  Finset (Fin n → Finset α) :=
 Fintype.piFinset fun _ : Fin n => X.powerset
omit [DecidableEq α] in
lemma jB
  {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α} :
  Ws ∈ bD X n ↔ ∀ i, Ws i ∈ X.powerset := by
 simp [bD, Fintype.mem_piFinset]
noncomputable def aW
  (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ)
  (Ws : Fin n → Finset α) : ℝ :=
 ∏ i, aF X (Ws i) (ρ i)
omit [DecidableEq α] in
lemma Br
  (X : Finset α) {n : ℕ} {ρ : Fin n → ℝ}
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (Ws : Fin n → Finset α) :
  0 ≤ aW X ρ Ws := by
 unfold aW
 exact Finset.prod_nonneg fun i _hi =>
  j8 (mL i) (m7 i)
omit [DecidableEq α] in
lemma oT
  (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ) :
  (∑ Ws ∈ bD X n, aW X ρ Ws) = 1 := by
 unfold bD aW
 rw [Finset.sum_prod_piFinset
  (s := X.powerset)
  (g := fun i W => aF X W (ρ i))]
 simp [lA]
def cE {n : ℕ} (Ws : Fin n → Finset α) : Finset α :=
 (Finset.univ : Finset (Fin n)).biUnion fun i => Ws i
noncomputable def dM {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
 1 - ∏ i, (1 - ρ i)
omit [DecidableEq α] in
lemma Gb {n : ℕ} (ρ : Fin (n + 1) → ℝ) :
  dM ρ =
   1 - (1 - dM (fun i : Fin n => ρ i.castSucc)) *
    (1 - ρ (Fin.last n)) := by
 unfold dM
 rw [Fin.prod_univ_castSucc]
 ring
omit [DecidableEq α] in
lemma DM {n : ℕ} {ρ : Fin n → ℝ}
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1) :
  0 ≤ dM ρ := by
 have ajh : (∏ i, (1 - ρ i)) ≤ (1 : ℝ) := by
  refine Finset.prod_le_one ?_ ?_
  ·intro i _hi
   exact sub_nonneg.mpr (m7 i)
  ·intro i _hi
   linarith [mL i]
 unfold dM
 linarith
omit [DecidableEq α] in
lemma Qa {n : ℕ} {ρ : Fin n → ℝ}
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1) :
  dM ρ ≤ ∑ i, ρ i := by
 induction n with
 | zero =>
   simp [dM]
 | succ n ih =>
   let i7 : Fin n → ℝ := fun i => ρ i.castSucc
   have aeZ : ∀ i : Fin n, 0 ≤ i7 i := fun i => mL i.castSucc
   have ae0 : ∀ i : Fin n, i7 i ≤ 1 := fun i => m7 i.castSucc
   have agw : dM i7 ≤ ∑ i, i7 i :=
    ih aeZ ae0
   have aaW : 0 ≤ dM i7 :=
    DM aeZ ae0
   have aaX : 0 ≤ ρ (Fin.last n) := mL (Fin.last n)
   have hsplit :
     dM ρ ≤ dM i7 + ρ (Fin.last n) := by
    rw [Gb]
    have akl :
      0 ≤ dM i7 * ρ (Fin.last n) :=
     mul_nonneg aaW aaX
    nlinarith
   have hsum :
     (∑ i : Fin (n + 1), ρ i) =
      (∑ i : Fin n, i7 i) + ρ (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
   exact hsplit.trans (by
    rw [hsum]
    have h := add_le_add_right agw (ρ (Fin.last n))
    simpa [add_comm, add_left_comm, add_assoc] using h)
omit [DecidableEq α] in
lemma Km {n : ℕ} {ρ B : Fin n → ℝ}
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (hρB : ∀ i, ρ i ≤ B i) :
  dM ρ ≤ ∑ i, B i := by
 exact (Qa mL m7).trans
  (Finset.sum_le_sum fun i _hi => hρB i)
lemma Oz
  {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α}
  (hWs : Ws ∈ bD X n) :
  cE Ws ⊆ X := by
 intro x hx
 rcases (by simpa [cE] using hx : ∃ i, x ∈ Ws i) with
  ⟨i, hxi⟩
 exact Finset.mem_powerset.mp ((jB.mp hWs) i) hxi
@[simp] lemma QE {n : ℕ}
  (Ws : Fin n → Finset α) (W : Finset α) :
  cE
    (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
   cE Ws ∪ W := by
 ext x
 constructor
 ·intro hx
  rcases (by
   simpa [cE] using hx :
    ∃ i : Fin (n + 1),
     x ∈ (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) i) with
   ⟨i, hi⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  ·exact Finset.mem_union.mpr (Or.inl (by
    simpa [cE] using (Exists.intro j (by simpa using hi))))
  ·exact Finset.mem_union.mpr (Or.inr (by simpa using hi))
 ·intro hx
  rcases Finset.mem_union.mp hx with htail | hlast
  ·rcases (by
    simpa [cE] using htail :
     ∃ i : Fin n, x ∈ Ws i) with ⟨i, hi⟩
   simpa [cE] using
    (Exists.intro (i.castSucc : Fin (n + 1)) (by simpa using hi))
  ·simpa [cE] using
    (Exists.intro (Fin.last n) (by simpa using hlast))
omit [DecidableEq α] in
lemma Fh (X : Finset α) (n : ℕ) :
  bD X (n + 1) =
   (X.powerset ×ˢ bD X n).map
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding := by
 ext Ws
 constructor
 ·intro hWs
  refine Finset.mem_map.mpr ⟨⟨Ws (Fin.last n),
   fun i : Fin n => Ws i.castSucc⟩, ?_, ?_⟩
  ·exact Finset.mem_product.mpr
    ⟨(jB.mp hWs) (Fin.last n),
     jB.mpr fun i =>
      (jB.mp hWs) i.castSucc⟩
  ·exact (Fin.snocEquiv
    (fun _ : Fin (n + 1) => Finset α)).right_inv Ws
 ·intro hWs
  rcases Finset.mem_map.mp hWs with ⟨⟨W, Ws₀⟩, hpair, hEq⟩
  rw [← hEq]
  rcases Finset.mem_product.mp hpair with ⟨hW, alQ⟩
  refine jB.mpr ?_
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  ·simpa using (jB.mp alQ) j
  ·simpa using hW
omit [DecidableEq α] in
@[simp] lemma Qb {n : ℕ}
  (X : Finset α) (ρ : Fin (n + 1) → ℝ)
  (Ws : Fin n → Finset α) (W : Finset α) :
  aW X ρ
    (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
   aW X (fun i : Fin n => ρ i.castSucc) Ws *
    aF X W (ρ (Fin.last n)) := by
 unfold aW
 rw [Fin.prod_univ_castSucc]
 simp
omit [DecidableEq α] in
lemma yZ
  {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
  (L : ℝ) * q * (1 - q) ^ L ≤ 1 - (1 - q) ^ L := by
 let r : ℝ := 1 - q
 have hr0 : 0 ≤ r := by dsimp [r]; linarith
 have hr1 : r ≤ 1 := by dsimp [r]; linarith
 have hq_eq : q = 1 - r := by dsimp [r]; ring
 have ahP :
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
  mul_le_mul_of_nonneg_right ahP (by dsimp [r]; linarith : 0 ≤ 1 - r)
 calc
  (L : ℝ) * q * (1 - q) ^ L
    = ((L : ℝ) * r ^ L) * (1 - r) := by
     dsimp [r]
     ring
  _ ≤ (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := hmul
  _ = 1 - r ^ L := geom_sum_mul_neg r L
  _ = 1 - (1 - q) ^ L := by rfl
omit [DecidableEq α] in
lemma r7
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
lemma Iw
  {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
  1 - (1 - q) ^ L ≤ (L : ℝ) * q := by
 let r : ℝ := 1 - q
 have hr0 : 0 ≤ r := by dsimp [r]; linarith
 have hr1 : r ≤ 1 := by dsimp [r]; linarith
 have Ej :
   (∑ i ∈ Finset.range L, r ^ i) ≤
    ∑ _i ∈ Finset.range L, (1 : ℝ) := by
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact pow_le_one₀ hr0 hr1
 have hmul :=
  mul_le_mul_of_nonneg_right Ej (by dsimp [r]; linarith : 0 ≤ 1 - r)
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
lemma Cj
  {q : ℝ} {n : ℕ} (L : Fin n → ℕ)
  (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
  dM (fun i : Fin n => 1 - (1 - q) ^ L i) ≤
   q * ∑ i : Fin n, (L i : ℝ) := by
 have VN : 0 ≤ 1 - q := by linarith
 have aaY : 1 - q ≤ 1 := by linarith
 have mL :
   ∀ i : Fin n, 0 ≤ 1 - (1 - q) ^ L i := by
  intro i
  have acu : (1 - q) ^ L i ≤ (1 : ℝ) :=
   pow_le_one₀ VN aaY
  linarith
 have m7 :
   ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ 1 := by
  intro i
  have MW : 0 ≤ (1 - q) ^ L i :=
   pow_nonneg VN _
  linarith
 have hbound :
   ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ (L i : ℝ) * q := by
  intro i
  exact Iw hq0 hq1
 calc
  dM (fun i : Fin n => 1 - (1 - q) ^ L i)
    ≤ ∑ i : Fin n, (L i : ℝ) * q :=
     Km mL m7 hbound
  _ = q * ∑ i : Fin n, (L i : ℝ) := by
     rw [← Finset.sum_mul]
     ring
lemma vN
  {X W S : Finset α} {q ρ : ℝ} {L : ℕ}
  (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
  (hρ : ρ = 1 - (1 - q) ^ L)
  (hdisj : Disjoint S W) (Jq : W ∪ S ⊆ X) :
  aF X W ρ * q ^ S.card ≤
   aF X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
 have aji : 0 < ρ := by
  simpa [hρ] using r7 hL hq0 hq1
 have alm : 0 ≤ ρ := aji.le
 have aln : ρ ≤ 1 := by
  rw [hρ]
  have MW : 0 ≤ (1 - q) ^ L := by
   exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
  linarith
 have UN : 0 ≤ 1 - ρ := by linarith
 have hLpos : 0 < (L : ℝ) := by
  have Kp : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  exact_mod_cast Kp
 have nZ : q * (1 - ρ) ≤ ρ * (1 / (L : ℝ)) := by
  have hmain :
    (L : ℝ) * q * (1 - ρ) ≤ ρ := by
   have hraw :=
    yZ
     (q := q) (L := L) hq0.le hq1
   simpa [hρ, mul_assoc, mul_comm, mul_left_comm] using hraw
  rw [← div_eq_mul_one_div]
  rw [le_div_iff₀ hLpos]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
 have acv :
   (q * (1 - ρ)) ^ S.card ≤ (ρ * (1 / (L : ℝ))) ^ S.card :=
  pow_le_pow_left₀ (mul_nonneg hq0.le UN) nZ S.card
 have W3 : (W ∪ S).card = W.card + S.card := by
  rw [Finset.card_union_of_disjoint]
  exact hdisj.symm
 have hWsub : W ⊆ W ∪ S := Finset.subset_union_left
 have alo : W.card ≤ X.card :=
  Finset.card_le_card (hWsub.trans Jq)
 have alp : (W ∪ S).card ≤ X.card :=
  Finset.card_le_card Jq
 have hdiff : X.card - W.card = (X.card - (W ∪ S).card) + S.card := by
  rw [W3]
  omega
 have Zl :
   0 ≤ ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card) := by
  positivity
 calc
  aF X W ρ * q ^ S.card
    = (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
      (q * (1 - ρ)) ^ S.card := by
     unfold aF
     rw [hdiff, pow_add, mul_pow]
     ring
  _ ≤ (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
     (ρ * (1 / (L : ℝ))) ^ S.card :=
    mul_le_mul_of_nonneg_left acv Zl
  _ = aF X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
     unfold aF
     rw [W3, pow_add, mul_pow]
     ring
omit [DecidableEq α] in
lemma Rz (X : Finset α) :
  aF X X (1 : ℝ) = 1 := by
 simp [aF]
omit [DecidableEq α] in
lemma Nb {X S : Finset α}
  (hSX : S ⊆ X) (Tm : S ≠ X) :
  aF X S (1 : ℝ) = 0 := by
 have hlt : S.card < X.card := Finset.card_lt_card (hSX.ssubset_of_ne Tm)
 have hpos : 0 < X.card - S.card := Nat.sub_pos_of_lt hlt
 simp [aF, hpos.ne']
lemma VO {X : Finset α} {U : Finset (Finset α)}
  (hXU : X ∈ U) :
  dN X U (1 : ℝ) = 1 := by
 classical
 unfold dN
 refine Finset.sum_eq_single_of_mem X ?_ ?_ |>.trans (Rz X)
 ·exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl X), hXU⟩
 ·intro S hS Tm
  have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact Nb hSX Tm
lemma Kq {X : Finset α} {U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hU : U.Nonempty) :
  dN X U (1 : ℝ) = 1 :=
 VO (Kk hUX g4 hU)
omit [DecidableEq α] in
lemma Qc (X : Finset α) :
  aF X ∅ (0 : ℝ) = 1 := by
 simp [aF]
omit [DecidableEq α] in
lemma v9 {X S : Finset α}
  (hS : S.Nonempty) :
  aF X S (0 : ℝ) = 0 := by
 simp [aF, hS.card_pos.ne']
lemma R6 {X : Finset α} {U : Finset (Finset α)}
  (hEmpty : (∅ : Finset α) ∈ U) :
  dN X U (0 : ℝ) = 1 := by
 classical
 unfold dN
 refine (Finset.sum_eq_single_of_mem ∅ ?_ ?_).trans (Qc X)
 ·exact Finset.mem_filter.mpr
   ⟨Finset.mem_powerset.mpr (Finset.empty_subset X), hEmpty⟩
 ·intro S hS Tm
  have Gd : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr Tm
  exact v9 Gd
lemma OC {X : Finset α} {U : Finset (Finset α)}
  (hEmpty : (∅ : Finset α) ∉ U) :
  dN X U (0 : ℝ) = 0 := by
 classical
 unfold dN
 refine Finset.sum_eq_zero ?_
 intro S hS
 have hSU : S ∈ U := (Finset.mem_filter.mp hS).2
 have Tm : S ≠ ∅ := by
  intro Iz
  exact hEmpty (by simpa [Iz] using hSU)
 exact v9 (Finset.nonempty_iff_ne_empty.mpr Tm)
lemma Jy
  (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
  (∑ Ws ∈ (bD X 0).filter
   (fun Ws => cE Ws ∈ U),
   aW X ρ Ws) =
   dN X U (0 : ℝ) := by
 by_cases hEmpty : (∅ : Finset α) ∈ U
 ·have hfilter :
    (bD X 0).filter
     (fun Ws : Fin 0 → Finset α => cE Ws ∈ U) =
      bD X 0 := by
   apply Finset.filter_eq_self.mpr
   intro Ws aaZ
   simpa [cE] using hEmpty
  rw [hfilter, oT X ρ,
   R6 hEmpty]
 ·have hfilter :
    (bD X 0).filter
     (fun Ws : Fin 0 → Finset α => cE Ws ∈ U) =
      ∅ := by
   apply Finset.filter_eq_empty_iff.mpr
   intro Ws aaZ
   simpa [cE] using hEmpty
  rw [hfilter]
  simp [OC hEmpty]
lemma Bv
  (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
  (∑ Ws ∈ (bD X 0).filter
   (fun Ws => cE Ws ∈ U),
   aW X ρ Ws) =
   dN X U (dM ρ) := by
 simpa [dM] using Jy X U ρ
lemma OD {X : Finset α} {U : Finset (Finset α)}
  (hU : U = X.powerset) (p : ℝ) :
  dN X U p = 1 := by
 classical
 unfold dN
 have hfilter : X.powerset.filter (fun S => S ∈ U) = X.powerset := by
  apply Finset.filter_eq_self.mpr
  intro S hS
  simpa [hU] using hS
 rw [hfilter]
 exact lA (α := α) X (p := p) (by ring)
lemma Fv {X : Finset α} {U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hEmpty : (∅ : Finset α) ∈ U) (p : ℝ) :
  dN X U p = 1 :=
 OD
  (Ep hUX g4 hEmpty) p
theorem Kr (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
  (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
  dN X (aV X {T₀}) p = p ^ T₀.card := by
 classical
 set Y : Finset α := X \ T₀ with hY
 have ahQ : Y.card = X.card - T₀.card := by
  simp [hY, Finset.card_sdiff_of_subset hT₀]
 have Tv : Disjoint T₀ Y := by
  simp [hY, Finset.disjoint_sdiff]
 let f : Finset α → Finset α := fun S' => T₀ ∪ S'
 have hf_inj : Set.InjOn f (↑Y.powerset) := by
  intro S' hS' R' hR' hfeq
  have aa0 : S' ⊆ Y := Finset.mem_powerset.mp hS'
  have alR : R' ⊆ Y := Finset.mem_powerset.mp hR'
  have agx : Disjoint T₀ S' := Finset.disjoint_of_subset_right aa0 Tv
  have agy : Disjoint T₀ R' := Finset.disjoint_of_subset_right alR Tv
  have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
  have ajj : S' = (T₀ ∪ S') \ T₀ := by
   ext x
   constructor
   ·intro hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
    exact fun N8 => (Finset.disjoint_left.mp agx N8 hx).elim
   ·intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨agz, Yb⟩
    rcases Finset.mem_union.mp agz with N8 | alS
    ·exact (Yb N8).elim
    ·exact alS
  have ajn : R' = (T₀ ∪ R') \ T₀ := by
   ext x
   constructor
   ·intro hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
    exact fun N8 => (Finset.disjoint_left.mp agy N8 hx).elim
   ·intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨agz, Yb⟩
    rcases Finset.mem_union.mp agz with N8 | alT
    ·exact (Yb N8).elim
    ·exact alT
  rw [ajj, ajn, heq]
 have him :
   Y.powerset.image f =
    X.powerset.filter (fun T => T ∈ aV X {T₀}) := by
  ext T
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
   eO, Finset.mem_singleton]
  constructor
  ·rintro ⟨S', aa0, rfl⟩
   have alU : S' ⊆ X := aa0.trans Finset.sdiff_subset
   have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ alU
   refine ⟨hfX, hfX, T₀, rfl, ?_⟩
   exact Finset.subset_union_left
  ·rintro ⟨xO, _, S₀, akG, adJ⟩
   refine ⟨T \ T₀, ?_, ?_⟩
   ·intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, Yb⟩
    exact Finset.mem_sdiff.mpr ⟨xO hxT, Yb⟩
   ·
    have alV : T₀ ⊆ T := by
     have := adJ
     rw [akG] at this
     exact this
    show T₀ ∪ (T \ T₀) = T
    ext x
    constructor
    ·intro hx
     rcases Finset.mem_union.mp hx with N8 | hxd
     ·exact alV N8
     ·exact (Finset.mem_sdiff.mp hxd).1
    ·intro hxT
     by_cases N8 : x ∈ T₀
     ·exact Finset.mem_union.mpr (Or.inl N8)
     ·exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, N8⟩))
 unfold dN
 rw [← him, Finset.sum_image hf_inj]
 have hkey :
   ∀ S' ∈ Y.powerset,
    aF X (f S') p = p ^ T₀.card * aF Y S' p := by
  intro S' hS'
  have aa0 : S' ⊆ Y := Finset.mem_powerset.mp hS'
  have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right aa0 Tv
  have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
   Finset.card_union_of_disjoint hdisj
  have Mh : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
   rw [ahQ]; omega
  show p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
    = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
  show p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
    = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
  rw [hcard, Mh, pow_add, mul_assoc]
 rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
 have : (∑ S' ∈ Y.powerset, aF Y S' p) = 1 :=
  lA (α := α) Y (p := p) (by ring)
 rw [this, mul_one]
lemma wc {X S : Finset α} {a : α} {p : ℝ}
  (ha : a ∉ X) (hS : S ⊆ X) :
  aF (insert a X) S p = (1 - p) * aF X S p := by
 have aa1 : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
 have akH : S.card ≤ X.card := Finset.card_le_card hS
 have hdiff : (insert a X).card - S.card = (X.card - S.card) + 1 := by
  rw [aa1]
  omega
 unfold aF
 rw [hdiff, pow_succ]
 ring
lemma xP {X S : Finset α} {a : α} {p : ℝ}
  (ha : a ∉ X) (hS : S ⊆ X) :
  aF (insert a X) (insert a S) p = p * aF X S p := by
 have haS : a ∉ S := fun h => ha (hS h)
 have aa1 : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
 have hcardS : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
 have akH : S.card ≤ X.card := Finset.card_le_card hS
 have hdiff : (insert a X).card - (S.card + 1) = X.card - S.card := by
  rw [aa1]
  omega
 unfold aF
 rw [hcardS, hdiff, pow_succ]
 ring
lemma qg {X : Finset α} {a : α}
  (ha : a ∉ X) :
  Set.InjOn (fun S : Finset α => insert a S) X.powerset := by
 intro S hS T hT hST
 have haS : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
 have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
 calc
  S = (insert a S).erase a := (Finset.erase_insert haS).symm
  _ = (insert a T).erase a := congrArg (fun U : Finset α => U.erase a) hST
  _ = T := Finset.erase_insert haT
lemma oW {X : Finset α} {a : α}
  (ha : a ∉ X) :
  Disjoint X.powerset (X.powerset.image fun S : Finset α => insert a S) := by
 rw [Finset.disjoint_left]
 intro S hS ahR
 rcases Finset.mem_image.mp ahR with ⟨T, _hT, rfl⟩
 have ae1 : a ∈ insert a T := Finset.mem_insert_self a T
 have aah : a ∉ insert a T := fun h =>
  ha ((Finset.mem_powerset.mp hS) h)
 exact aah ae1
noncomputable def gO (X : Finset α) (U : Finset (Finset α)) :
  Finset (Finset α) :=
 X.powerset.filter fun S => S ∈ U
noncomputable def fF (a : α) (X : Finset α)
  (U : Finset (Finset α)) : Finset (Finset α) :=
 X.powerset.filter fun S => insert a S ∈ U
noncomputable def b9 (X : Finset α)
  (U : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
 X.powerset.filter fun S => S ∪ W ∈ U
lemma fG {X : Finset α} {U : Finset (Finset α)}
  {W S : Finset α} :
  S ∈ b9 X U W ↔ S ⊆ X ∧ S ∪ W ∈ U := by
 simp [b9]
lemma zj
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
  (hW : W ⊆ X) :
  gO X (b9 (insert a X) U W) =
   b9 X (gO X U) W := by
 ext S
 constructor
 ·intro hS
  rcases Finset.mem_filter.mp hS with ⟨hSX, Mj⟩
  rcases fG.mp Mj with ⟨adM, hSU⟩
  exact fG.mpr
   ⟨Finset.mem_powerset.mp hSX,
    Finset.mem_filter.mpr
     ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
      hSU⟩⟩
 ·intro hS
  rcases fG.mp hS with ⟨hSX, aa2⟩
  rcases Finset.mem_filter.mp aa2 with ⟨Xq, hSU⟩
  exact Finset.mem_filter.mpr
   ⟨Finset.mem_powerset.mpr hSX,
    fG.mpr
     ⟨hSX.trans (Finset.subset_insert a X), hSU⟩⟩
lemma Bw
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
  (hW : W ⊆ X) :
  fF a X (b9 (insert a X) U W) =
   b9 X (fF a X U) W := by
 ext S
 constructor
 ·intro hS
  rcases Finset.mem_filter.mp hS with ⟨hSX, Mj⟩
  rcases fG.mp Mj with ⟨ae2, hSU⟩
  have nU : insert a (S ∪ W) = insert a S ∪ W := by
   ext x
   simp [or_comm]
  exact fG.mpr
   ⟨Finset.mem_powerset.mp hSX,
    Finset.mem_filter.mpr
     ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
      by rwa [nU]⟩⟩
 ·intro hS
  rcases fG.mp hS with ⟨hSX, Xr⟩
  rcases Finset.mem_filter.mp Xr with ⟨Xq, hSU⟩
  have nU : insert a S ∪ W = insert a (S ∪ W) := by
   ext x
   simp [or_comm]
  exact Finset.mem_filter.mpr
   ⟨Finset.mem_powerset.mpr hSX,
    fG.mpr
     ⟨Finset.insert_subset (Finset.mem_insert_self a X)
      (hSX.trans (Finset.subset_insert a X)),
      by rwa [nU]⟩⟩
lemma xQ
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
  (hW : W ⊆ X) :
  gO X (b9 (insert a X) U (insert a W)) =
   b9 X (fF a X U) W := by
 ext S
 constructor
 ·intro hS
  rcases Finset.mem_filter.mp hS with ⟨hSX, Mj⟩
  rcases fG.mp Mj with ⟨adM, hSU⟩
  have nU : S ∪ insert a W = insert a (S ∪ W) := by
   ext x
   simp [or_comm]
  exact fG.mpr
   ⟨Finset.mem_powerset.mp hSX,
    Finset.mem_filter.mpr
     ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
      by rwa [← nU]⟩⟩
 ·intro hS
  rcases fG.mp hS with ⟨hSX, Xr⟩
  rcases Finset.mem_filter.mp Xr with ⟨Xq, hSU⟩
  have nU : S ∪ insert a W = insert a (S ∪ W) := by
   ext x
   simp [or_comm]
  exact Finset.mem_filter.mpr
   ⟨Finset.mem_powerset.mpr hSX,
    fG.mpr
     ⟨hSX.trans (Finset.subset_insert a X),
      by rwa [nU]⟩⟩
lemma Aa
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
  (hW : W ⊆ X) :
  fF a X (b9 (insert a X) U (insert a W)) =
   b9 X (fF a X U) W := by
 ext S
 constructor
 ·intro hS
  rcases Finset.mem_filter.mp hS with ⟨hSX, Mj⟩
  rcases fG.mp Mj with ⟨ae2, hSU⟩
  have nU : insert a S ∪ insert a W = insert a (S ∪ W) := by
   ext x
   simp [or_comm]
  exact fG.mpr
   ⟨Finset.mem_powerset.mp hSX,
    Finset.mem_filter.mpr
     ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
      by rwa [← nU]⟩⟩
 ·intro hS
  rcases fG.mp hS with ⟨hSX, Xr⟩
  rcases Finset.mem_filter.mp Xr with ⟨Xq, hSU⟩
  have nU : insert a S ∪ insert a W = insert a (S ∪ W) := by
   ext x
   simp [or_comm]
  exact Finset.mem_filter.mpr
   ⟨Finset.mem_powerset.mpr hSX,
    fG.mpr
     ⟨Finset.insert_subset (Finset.mem_insert_self a X)
       (hSX.trans (Finset.subset_insert a X)),
      by rwa [nU]⟩⟩
lemma tP {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
  (ha : a ∉ X) :
  dN (insert a X) U p =
   (1 - p) * dN X (gO X U) p +
    p * dN X (fF a X U) p := by
 classical
 let ins : Finset α → Finset α := fun S => insert a S
 let A : Finset (Finset α) := X.powerset.filter fun S => S ∈ U
 let B : Finset (Finset α) := (X.powerset.image ins).filter fun S => S ∈ U
 have ae3 :
   Disjoint X.powerset (X.powerset.image ins) := by
  simpa [ins] using oW (X := X) (a := a) ha
 have hdisj : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro S hSA hSB
  exact (Finset.disjoint_left.mp ae3)
   (Finset.mem_filter.mp hSA).1 (Finset.mem_filter.mp hSB).1
 have aai :
   (insert a X).powerset.filter (fun S => S ∈ U) = A ∪ B := by
  calc
   (insert a X).powerset.filter (fun S => S ∈ U)
     = (X.powerset ∪ X.powerset.image ins).filter (fun S => S ∈ U) := by
      rw [Finset.powerset_insert]
   _ = A ∪ B := by
      rw [Finset.filter_union]
 have adN :
   X.powerset.filter (fun S => S ∈ gO X U) = A := by
  ext S
  simp [gO, A]
 have ajo :
   (∑ S ∈ A, aF (insert a X) S p) =
    (1 - p) * dN X (gO X U) p := by
  calc
   (∑ S ∈ A, aF (insert a X) S p)
     = ∑ S ∈ A, (1 - p) * aF X S p := by
      refine Finset.sum_congr rfl ?_
      intro S hSA
      have hSX : S ⊆ X :=
       Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
      exact wc ha hSX
   _ = (1 - p) * ∑ S ∈ A, aF X S p := by
      rw [Finset.mul_sum]
   _ = (1 - p) * dN X (gO X U) p := by
      unfold dN
      rw [adN]
 have agA :
   (X.powerset.filter fun S => ins S ∈ U).image ins = B := by
  ext R
  constructor
  ·intro hR
   rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
   exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩,
     (Finset.mem_filter.mp hS).2⟩
  ·intro hR
   rcases Finset.mem_filter.mp hR with ⟨akI, hRU⟩
   rcases Finset.mem_image.mp akI with ⟨S, hS, rfl⟩
   exact Finset.mem_image.mpr
    ⟨S, Finset.mem_filter.mpr ⟨hS, hRU⟩, rfl⟩
 have hinj :
   Set.InjOn ins (↑(X.powerset.filter fun S => ins S ∈ U)) := by
  exact (qg (X := X) (a := a) ha).mono
   (by intro S hS; exact (Finset.mem_filter.mp hS).1)
 have adO :
   X.powerset.filter (fun S => S ∈ fF a X U) =
    X.powerset.filter fun S => ins S ∈ U := by
  ext S
  simp [fF, ins]
 have ae4 :
   (∑ S ∈ B, aF (insert a X) S p) =
    p * dN X (fF a X U) p := by
  calc
   (∑ S ∈ B, aF (insert a X) S p)
     = ∑ S ∈ (X.powerset.filter fun S => ins S ∈ U).image ins,
       aF (insert a X) S p := by rw [agA]
   _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
       aF (insert a X) (ins S) p := by
      rw [Finset.sum_image hinj]
   _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
       p * aF X S p := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      simpa [ins] using xP (X := X) (S := S)
       (a := a) (p := p) ha hSX
   _ = p * ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
       aF X S p := by
      rw [Finset.mul_sum]
   _ = p * dN X (fF a X U) p := by
      unfold dN
      rw [adO]
 calc
  dN (insert a X) U p
    = ∑ S ∈ A ∪ B, aF (insert a X) S p := by
     unfold dN
     rw [aai]
  _ = (∑ S ∈ A, aF (insert a X) S p) +
    ∑ S ∈ B, aF (insert a X) S p := by
     rw [Finset.sum_union hdisj]
  _ = (1 - p) * dN X (gO X U) p +
    p * dN X (fF a X U) p := by
     rw [ajo, ae4]
lemma Ml
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
  (ha : a ∉ X) (hW : W ⊆ X) :
  dN (insert a X) (b9 (insert a X) U W) p =
   (1 - p) *
     dN X (b9 X (gO X U) W) p +
    p * dN X (b9 X (fF a X U) W) p := by
 rw [tP (X := X)
  (U := b9 (insert a X) U W) (a := a) (p := p) ha]
 rw [zj (a := a) hW,
  Bw (a := a) hW]
lemma Lj
  {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
  (ha : a ∉ X) (hW : W ⊆ X) :
  dN (insert a X) (b9 (insert a X) U (insert a W)) p =
   dN X (b9 X (fF a X U) W) p := by
 rw [tP (X := X)
  (U := b9 (insert a X) U (insert a W)) (a := a) (p := p) ha]
 rw [xQ (a := a) hW,
  Aa (a := a) hW]
 ring
lemma xT
  (X : Finset α) (U : Finset (Finset α)) (θ r : ℝ) :
  (∑ W ∈ X.powerset,
   aF X W r * dN X (b9 X U W) θ) =
   dN X U (1 - (1 - θ) * (1 - r)) := by
 classical
 induction X using Finset.induction generalizing U with
 | empty =>
   by_cases hEmpty : (∅ : Finset α) ∈ U
   ·have Qd :
      ({∅} : Finset (Finset α)).filter
       (fun S => S = ∅ ∧ S ∈ U) = {∅} := by
     apply Finset.filter_eq_self.mpr
     intro S hS
     have Jp : S = ∅ := by simpa using hS
     exact ⟨Jp, by simpa [Jp] using hEmpty⟩
    have N9 :
      ({∅} : Finset (Finset α)).filter
       (fun S => S ∈ U) = {∅} := by
     apply Finset.filter_eq_self.mpr
     intro S hS
     have Jp : S = ∅ := by simpa using hS
     simpa [Jp] using hEmpty
    simp [dN, aF, b9, Qd, N9]
   ·have Qd :
      ({∅} : Finset (Finset α)).filter
       (fun S => S = ∅ ∧ S ∈ U) = ∅ := by
     apply Finset.filter_eq_empty_iff.mpr
     intro S hS hbad
     exact hEmpty (by simpa [hbad.1] using hbad.2)
    have N9 :
      ({∅} : Finset (Finset α)).filter
       (fun S => S ∈ U) = ∅ := by
     apply Finset.filter_eq_empty_iff.mpr
     intro S hS hSU
     have Jp : S = ∅ := by simpa using hS
     exact hEmpty (by simpa [Jp] using hSU)
    simp [dN, aF, b9, Qd, N9]
 | insert a X ha ih =>
   let η : ℝ := 1 - (1 - θ) * (1 - r)
   let ins : Finset α → Finset α := fun S => insert a S
   have hdisj :
     Disjoint X.powerset (X.powerset.image ins) := by
    simpa [ins] using oW
     (X := X) (a := a) ha
   have hinj : Set.InjOn ins (↑X.powerset) := by
    simpa [ins] using qg
     (X := X) (a := a) ha
   have Yc :
     (∑ W ∈ (insert a X).powerset,
      aF (insert a X) W r *
       dN (insert a X) (b9 (insert a X) U W) θ) =
      (∑ W ∈ X.powerset,
       aF (insert a X) W r *
        dN (insert a X) (b9 (insert a X) U W) θ) +
       ∑ W ∈ X.powerset,
        aF (insert a X) (insert a W) r *
         dN (insert a X)
          (b9 (insert a X) U (insert a W)) θ := by
    calc
     (∑ W ∈ (insert a X).powerset,
      aF (insert a X) W r *
       dN (insert a X) (b9 (insert a X) U W) θ)
       = ∑ W ∈ X.powerset ∪ X.powerset.image ins,
         aF (insert a X) W r *
          dN (insert a X) (b9 (insert a X) U W) θ := by
          rw [Finset.powerset_insert]
     _ = (∑ W ∈ X.powerset,
        aF (insert a X) W r *
         dN (insert a X) (b9 (insert a X) U W) θ) +
        ∑ W ∈ X.powerset.image ins,
         aF (insert a X) W r *
          dN (insert a X) (b9 (insert a X) U W) θ := by
          rw [Finset.sum_union hdisj]
     _ = (∑ W ∈ X.powerset,
        aF (insert a X) W r *
         dN (insert a X) (b9 (insert a X) U W) θ) +
        ∑ W ∈ X.powerset,
         aF (insert a X) (insert a W) r *
          dN (insert a X)
           (b9 (insert a X) U (insert a W)) θ := by
          rw [Finset.sum_image hinj]
   have ahS :
     (∑ W ∈ X.powerset,
      aF (insert a X) W r *
       dN (insert a X) (b9 (insert a X) U W) θ) =
      ((1 - r) * (1 - θ)) *
        (∑ W ∈ X.powerset,
         aF X W r *
          dN X (b9 X (gO X U) W) θ) +
       ((1 - r) * θ) *
        (∑ W ∈ X.powerset,
         aF X W r *
          dN X (b9 X (fF a X U) W) θ) := by
    calc
     (∑ W ∈ X.powerset,
      aF (insert a X) W r *
       dN (insert a X) (b9 (insert a X) U W) θ)
       = ∑ W ∈ X.powerset,
         (((1 - r) * (1 - θ)) *
          (aF X W r *
           dN X (b9 X (gO X U) W) θ) +
         ((1 - r) * θ) *
          (aF X W r *
           dN X (b9 X (fF a X U) W) θ)) := by
          refine Finset.sum_congr rfl ?_
          intro W hW
          have Yd : W ⊆ X := Finset.mem_powerset.mp hW
          rw [wc ha Yd,
           Ml (X := X) (U := U)
            (a := a) (W := W) (p := θ) ha Yd]
          ring
     _ = ((1 - r) * (1 - θ)) *
        (∑ W ∈ X.powerset,
         aF X W r *
          dN X (b9 X (gO X U) W) θ) +
       ((1 - r) * θ) *
        (∑ W ∈ X.powerset,
         aF X W r *
          dN X (b9 X (fF a X U) W) θ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
   have agB :
     (∑ W ∈ X.powerset,
      aF (insert a X) (insert a W) r *
       dN (insert a X)
        (b9 (insert a X) U (insert a W)) θ) =
      r *
       (∑ W ∈ X.powerset,
        aF X W r *
         dN X (b9 X (fF a X U) W) θ) := by
    calc
     (∑ W ∈ X.powerset,
      aF (insert a X) (insert a W) r *
       dN (insert a X)
        (b9 (insert a X) U (insert a W)) θ)
       = ∑ W ∈ X.powerset,
         r *
          (aF X W r *
           dN X (b9 X (fF a X U) W) θ) := by
          refine Finset.sum_congr rfl ?_
          intro W hW
          have Yd : W ⊆ X := Finset.mem_powerset.mp hW
          rw [xP ha Yd,
           Lj (X := X) (U := U)
            (a := a) (W := W) (p := θ) ha Yd]
          ring
     _ = r *
       (∑ W ∈ X.powerset,
        aF X W r *
         dN X (b9 X (fF a X U) W) θ) := by
          rw [Finset.mul_sum]
   have agC :=
    ih (gO X U)
   have akJ :=
    ih (fF a X U)
   rw [Yc, ahS, agB, agC, akJ]
   have hsplit :=
    tP (X := X) (U := U) (a := a) (p := η) ha
   change
    ((1 - r) * (1 - θ)) * dN X (gO X U) η +
      ((1 - r) * θ) * dN X (fF a X U) η +
     r * dN X (fF a X U) η =
    dN (insert a X) U η
   rw [hsplit]
   ring
lemma Gh
  (X : Finset α) (U : Finset (Finset α)) {n : ℕ}
  (ρ : Fin n → ℝ) :
  (∑ Ws ∈ (bD X n).filter
   (fun Ws => cE Ws ∈ U),
   aW X ρ Ws) =
   dN X U (dM ρ) := by
 classical
 induction n generalizing U with
 | zero =>
   simpa using Bv X U ρ
 | succ n ih =>
   let e : Finset α × (Fin n → Finset α) ↪
     (Fin (n + 1) → Finset α) :=
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
   let i7 : Fin n → ℝ := fun i => ρ i.castSucc
   let n9 : ℝ := ρ (Fin.last n)
   have hmap :
     (∑ Ws ∈ (bD X (n + 1)).filter
      (fun Ws => cE Ws ∈ U),
      aW X ρ Ws) =
     ∑ P ∈ ((X.powerset ×ˢ bD X n).filter
       (fun P => cE (e P) ∈ U)),
      aW X ρ (e P) := by
    rw [Fh X n, Finset.filter_map]
    rw [Finset.sum_map]
    rfl
   have agD :
     (∑ P ∈ ((X.powerset ×ˢ bD X n).filter
       (fun P => cE (e P) ∈ U)),
      aW X ρ (e P)) =
     ∑ W ∈ X.powerset,
      ∑ Ws ∈ (bD X n).filter
       (fun Ws => cE Ws ∈ b9 X U W),
       aW X ρ (e (W, Ws)) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro W hW
    rw [← Finset.sum_filter]
    have hfilter :
      (bD X n).filter
        (fun Ws => cE (e (W, Ws)) ∈ U) =
       (bD X n).filter
        (fun Ws => cE Ws ∈ b9 X U W) := by
     ext Ws
     by_cases hWs : Ws ∈ bD X n
     ·have alW : cE Ws ⊆ X :=
       Oz hWs
      have ajp :
        cE (e (W, Ws)) ∈ U ↔
         cE Ws ∈ b9 X U W := by
       change
        cE
          (Fin.snoc
           (α := fun _ : Fin (n + 1) => Finset α) Ws W) ∈ U ↔
         cE Ws ∈ b9 X U W
       rw [QE]
       simp [fG, alW]
      simp [hWs, ajp]
     ·simp [hWs]
    rw [hfilter]
   have Me :
     (∑ W ∈ X.powerset,
      ∑ Ws ∈ (bD X n).filter
       (fun Ws => cE Ws ∈ b9 X U W),
       aW X ρ (e (W, Ws))) =
     ∑ W ∈ X.powerset,
      aF X W n9 *
       (∑ Ws ∈ (bD X n).filter
        (fun Ws => cE Ws ∈ b9 X U W),
        aW X i7 Ws) := by
    refine Finset.sum_congr rfl ?_
    intro W hW
    calc
     (∑ Ws ∈ (bD X n).filter
       (fun Ws => cE Ws ∈ b9 X U W),
       aW X ρ (e (W, Ws)))
       = ∑ Ws ∈ (bD X n).filter
         (fun Ws => cE Ws ∈ b9 X U W),
         aW X i7 Ws * aF X W n9 := by
          refine Finset.sum_congr rfl ?_
          intro Ws hWs
          change
           aW X ρ
             (Fin.snoc
              (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
            aW X i7 Ws *
             aF X W n9
          simp [i7, n9]
     _ = (∑ Ws ∈ (bD X n).filter
         (fun Ws => cE Ws ∈ b9 X U W),
         aW X i7 Ws) * aF X W n9 := by
          rw [Finset.sum_mul]
     _ = aF X W n9 *
        (∑ Ws ∈ (bD X n).filter
         (fun Ws => cE Ws ∈ b9 X U W),
         aW X i7 Ws) := by
          ring
   calc
    (∑ Ws ∈ (bD X (n + 1)).filter
     (fun Ws => cE Ws ∈ U),
     aW X ρ Ws)
      = ∑ W ∈ X.powerset,
        aF X W n9 *
         (∑ Ws ∈ (bD X n).filter
          (fun Ws =>
           cE Ws ∈ b9 X U W),
          aW X i7 Ws) := by
         rw [hmap, agD, Me]
    _ = ∑ W ∈ X.powerset,
       aF X W n9 *
        dN X (b9 X U W) (dM i7) := by
         refine Finset.sum_congr rfl ?_
         intro W hW
         rw [ih (b9 X U W) i7]
    _ = dN X U
       (1 - (1 - dM i7) * (1 - n9)) :=
      xT
       X U (dM i7) n9
    _ = dN X U (dM ρ) := by
      rw [Gb]
theorem Ac {X : Finset α} {U : Finset (Finset α)} {p q : ℝ}
  (g4 : dW X U) (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
  dN X U p ≤ dN X U q := by
 classical
 induction X using Finset.induction generalizing U with
 | empty =>
   by_cases hU : (∅ : Finset α) ∈ U
   ·have hfilter :
      ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = {∅} := by
     apply Finset.filter_eq_self.mpr
     intro x hx
     have Zm : x = ∅ := by simpa using hx
     simpa [Zm] using hU
    simp [dN, aF, hfilter]
   ·have hfilter :
      ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = ∅ := by
     apply Finset.filter_eq_empty_iff.mpr
     intro x hx
     have Zm : x = ∅ := by simpa using hx
     simpa [Zm] using hU
    simp [dN, aF, hfilter]
 | insert a X ha ih =>
   let U0 : Finset (Finset α) := gO X U
   let U1 : Finset (Finset α) := fF a X U
   have hp1 : p ≤ 1 := hpq.trans hq1
   have hq0 : 0 ≤ q := hp0.trans hpq
   have ajq : dW X U0 := by
    intro S aa2 T xO hST
    rcases Finset.mem_filter.mp aa2 with ⟨alX, hSU⟩
    have ae5 : T ⊆ insert a X := xO.trans (Finset.subset_insert a X)
    have hTU : T ∈ U := g4 S hSU T ae5 hST
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr xO, hTU⟩
   have ajr : dW X U1 := by
    intro S Xr T xO hST
    rcases Finset.mem_filter.mp Xr with ⟨alX, aa3⟩
    have aa4 : insert a T ⊆ insert a X := by
     intro x hx
     rcases Finset.mem_insert.mp hx with rfl | hxT
     ·simp
     ·exact Finset.mem_insert.mpr (Or.inr (xO hxT))
    have ae6 : insert a S ⊆ insert a T := by
     intro x hx
     rcases Finset.mem_insert.mp hx with rfl | hxS
     ·simp
     ·exact Finset.mem_insert.mpr (Or.inr (hST hxS))
    have ajs : insert a T ∈ U :=
     g4 (insert a S) aa3 (insert a T) aa4 ae6
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr xO, ajs⟩
   have akK : U0 ⊆ U1 := by
    intro S aa2
    rcases Finset.mem_filter.mp aa2 with ⟨ae7, hSU⟩
    have hSX : S ⊆ X := Finset.mem_powerset.mp ae7
    have ajt : insert a S ⊆ insert a X := by
     intro x hx
     rcases Finset.mem_insert.mp hx with rfl | hxS
     ·simp
     ·exact Finset.mem_insert.mpr (Or.inr (hSX hxS))
    have aju : S ⊆ insert a S := Finset.subset_insert a S
    have aa3 : insert a S ∈ U := g4 S hSU (insert a S) ajt aju
    exact Finset.mem_filter.mpr ⟨ae7, aa3⟩
   have hF0 : dN X U0 p ≤ dN X U0 q := ih ajq
   have hF1 : dN X U1 p ≤ dN X U1 q := ih ajr
   have akL : dN X U0 q ≤ dN X U1 q :=
    Rb hq0 hq1 akK
   rw [tP (X := X) (U := U) (a := a) (p := p) ha,
    tP (X := X) (U := U) (a := a) (p := q) ha]
   have hfirst :
     (1 - p) * dN X U0 p + p * dN X U1 p ≤
      (1 - p) * dN X U0 q + p * dN X U1 q := by
    exact add_le_add
     (mul_le_mul_of_nonneg_left hF0 (by linarith))
     (mul_le_mul_of_nonneg_left hF1 hp0)
   have hsecond :
     (1 - p) * dN X U0 q + p * dN X U1 q ≤
      (1 - q) * dN X U0 q + q * dN X U1 q := by
    have adP : 0 ≤ q - p := by linarith
    have hmul := mul_le_mul_of_nonneg_left akL adP
    nlinarith
   exact hfirst.trans hsecond
lemma m8
  {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  (hUX : ∀ T ∈ U, T ⊆ X) (g4 : dW X U) (hS : S ∈ U) :
  p ^ S.card ≤ dN X U p := by
 have hSX : S ⊆ X := hUX S hS
 have hsub : aV X {S} ⊆ U :=
  vI g4 hS
 have hmono :
   dN X (aV X {S}) p ≤ dN X U p :=
  Rb hp0 hp1 hsub
 have nZ : dN X (aV X {S}) p = p ^ S.card :=
  Kr X S hSX hp0 hp1
 simpa [nZ] using hmono
lemma Da
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  (hUX : ∀ T ∈ U, T ⊆ X) (g4 : dW X U) (hU : U.Nonempty) :
  p ^ ell X U ≤ dN X U p := by
 rcases C9 (X := X) hU with ⟨S, hSmin⟩
 have hSU : S ∈ U := qd hSmin
 have hcard : S.card ≤ ell X U := Ez hSmin
 have hpow : p ^ ell X U ≤ p ^ S.card :=
  pow_le_pow_of_le_one hp0 hp1 hcard
 exact hpow.trans (m8 hp0 hp1 hUX g4 hSU)
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def g7 (_X : Finset α) (G U : Finset (Finset α)) : Prop :=
 ∀ S ∈ U, ∃ T ∈ G, T ⊆ S
def g3 (G : Finset (Finset α)) (p : ℝ) : ℝ :=
 ∑ T ∈ G, p ^ T.card
def fO (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
 ∃ G : Finset (Finset α),
  g7 X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)
def BZ (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
 ∀ p : ℝ, q < p → p ≤ 1 → ¬ fO X U p
omit [DecidableEq α] in
lemma aa5 (X : Finset α) (p : ℝ) :
  fO X (∅ : Finset (Finset α)) p := by
 refine ⟨∅, ?_, ?_⟩
 ·intro S hS
  simp at hS
 ·simp
omit [DecidableEq α] in
lemma wT {X : Finset α} {U : Finset (Finset α)}
  {p : ℝ} (h : ¬ fO X U p) :
  U.Nonempty := by
 by_contra hU
 have hUeq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
 exact h (by simpa [hUeq] using aa5 X p)
lemma g7.union {X : Finset α} {G H U V : Finset (Finset α)}
  (hG : g7 X G U) (hH : g7 X H V) :
  g7 X (G ∪ H) (U ∪ V) := by
 intro S hS
 rcases Finset.mem_union.mp hS with hSU | hSV
 ·rcases hG S hSU with ⟨T, Nc, hTS⟩
  exact ⟨T, Finset.mem_union.mpr (Or.inl Nc), hTS⟩
 ·rcases hH S hSV with ⟨T, hTH, hTS⟩
  exact ⟨T, Finset.mem_union.mpr (Or.inr hTH), hTS⟩
lemma DN {X : Finset α} {G U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) :
  g7 X G (aV X U) ↔ g7 X G U := by
 constructor
 ·intro iz S hS
  exact iz S (DH hUX hS)
 ·intro iz S hS
  rcases eO.mp hS with ⟨_, T, hTU, hTS⟩
  rcases iz T hTU with ⟨R, hRG, hRT⟩
  exact ⟨R, hRG, hRT.trans hTS⟩
lemma g7.Tw {X : Finset α} {G U : Finset (Finset α)}
  (hUX : ∀ S ∈ U, S ⊆ X) (iz : g7 X G U) :
  g7 X (G.filter fun T => T ⊆ X) U := by
 intro S hS
 rcases iz S hS with ⟨T, Nc, hTS⟩
 have xO : T ⊆ X := hTS.trans (hUX S hS)
 exact ⟨T, Finset.mem_filter.mpr ⟨Nc, xO⟩, hTS⟩
lemma RD {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hUX : ∀ S ∈ U, S ⊆ X) :
  fO X (aV X U) p ↔ fO X U p := by
 constructor
 ·rintro ⟨G, iz, hsum⟩
  exact ⟨G, (DN hUX).mp iz, hsum⟩
 ·rintro ⟨G, iz, hsum⟩
  exact ⟨G, (DN hUX).mpr iz, hsum⟩
lemma Oa {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hUX : ∀ S ∈ U, S ⊆ X) :
  ¬ fO X (aV X U) p ↔ ¬ fO X U p := by
 rw [RD hUX]
omit [DecidableEq α] in
lemma Gk {X : Finset α} {U G : Finset (Finset α)}
  {p : ℝ} (iz : g7 X G U)
  (hsum : (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)) :
  fO X U p :=
 ⟨G, iz, hsum⟩
lemma Tz {G H : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) :
  g3 (G ∪ H) p ≤ g3 G p + g3 H p := by
 classical
 unfold g3
 let H' : Finset (Finset α) := H \ G
 have hdisj : Disjoint G H' := by
  exact disjoint_sdiff
 have hunion : G ∪ H = G ∪ H' := by
  ext T
  by_cases Nc : T ∈ G <;> simp [H', Nc]
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
lemma fO.UO
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) (tQ : fO X U p) :
  ∃ G : Finset (Finset α),
   (∀ T ∈ G, T ⊆ X) ∧
   g7 X G U ∧
   (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ) := by
 rcases tQ with ⟨G, iz, hsum⟩
 refine ⟨G.filter fun T => T ⊆ X, ?_, ?_, ?_⟩
 ·intro T hT
  exact (Finset.mem_filter.mp hT).2
 ·exact iz.Tw hUX
 ·have adQ :
    (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
     ∑ T ∈ G, p ^ T.card :=
   Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (by intro T _ _; exact pow_nonneg hp0 T.card)
  exact adQ.trans hsum
omit [DecidableEq α] in
lemma vF
  {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
  (h : ¬ fO X U p) (iz : g7 X G U) :
  (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
 exact lt_of_not_ge fun hsum => h (Gk iz hsum)
lemma TD (X : Finset α) (U : Finset (Finset α)) :
  g7 X (f5 X U) U := by
 intro S hS
 exact yW hS
lemma Mr (X : Finset α) (A : Finset (Finset α)) :
  g7 X A (aV X A) := by
 intro S hS
 rcases eO.mp hS with ⟨_, T, hTA, hTS⟩
 exact ⟨T, hTA, hTS⟩
lemma tW
  {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
  (h : ¬ fO X (aV X A) p) :
  (1 / 2 : ℝ) < ∑ T ∈ A, p ^ T.card := by
 exact vF h (Mr X A)
omit [DecidableEq α] in
lemma q8
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
  exact le_of_not_gt fun alY => hnone ⟨x, hx, alY⟩
 have Ej :
   (∑ x ∈ s, w x) ≤
    ∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) :=
  Finset.sum_le_sum hbound
 have aaj : 0 < s.card := hs_nonempty.card_pos
 have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast aaj
 have hconst :
   (∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ))) = 1 / 2 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard_pos.ne']
 linarith
lemma lT
  {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
  (h : ¬ fO X (aV X A) p) :
  ∃ T ∈ A, (1 : ℝ) / (2 * (A.card : ℝ)) < p ^ T.card :=
 q8
  A (fun T => p ^ T.card)
  (tW h)
omit [DecidableEq α] in
lemma UZ {X : Finset α} {U : Finset (Finset α)}
  {p₀ p : ℝ} (h0 : 0 ≤ p₀) (hle : p₀ ≤ p)
  (tQ : fO X U p) : fO X U p₀ := by
 classical
 rcases tQ with ⟨G, iz, hsum⟩
 refine ⟨G, iz, le_trans ?_ hsum⟩
 refine Finset.sum_le_sum ?_
 intro T _
 exact pow_le_pow_left₀ h0 hle T.card
omit [DecidableEq α] in
lemma OE {X : Finset α} {U : Finset (Finset α)}
  {p₀ : ℝ} (adR : 0 ≤ p₀)
  (h : ¬ fO X U p₀) :
  BZ X U p₀ := by
 intro p hgt _ tQ
 exact h (UZ adR hgt.le tQ)
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def i9 (H : Finset (Finset α)) (W : Finset α) :
  Finset (Finset α) :=
 H.image fun S => S \ W
@[simp]
lemma lB {H : Finset (Finset α)} {W T : Finset α} :
  T ∈ i9 H W ↔ ∃ S ∈ H, S \ W = T := by
 simp [i9]
def f6 (H : Finset (Finset α)) (W : Finset α) :
  Finset (Finset α) :=
 f5 (∅ : Finset α) (i9 H W)
@[simp]
lemma TJ {H : Finset (Finset α)} {W T : Finset α} :
  T ∈ f6 H W ↔
   T ∈ i9 H W ∧
    ∀ R ∈ i9 H W, ¬ R ⊂ T := by
 simp [f6]
lemma iG
  (H : Finset (Finset α)) (W : Finset α) :
  f6 H W ⊆ i9 H W :=
 qd
lemma Ob
  {H : Finset (Finset α)} {W T : Finset α}
  (hT : T ∈ i9 H W) :
  Disjoint T W := by
 rcases lB.mp hT with ⟨S, _hS, rfl⟩
 rw [Finset.disjoint_left]
 intro x hx hW
 exact (Finset.mem_sdiff.mp hx).2 hW
lemma Gm
  {H : Finset (Finset α)} {W T : Finset α}
  (hT : T ∈ f6 H W) :
  Disjoint T W :=
 Ob (iG H W hT)
def bU (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
  Finset (Finset α) :=
 (f6 H W).filter fun T => m ≤ T.card
def dK (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
  Finset (Finset α) :=
 (f6 H W).filter fun T => T.card < m
@[simp]
lemma kQ {m : ℕ} {H : Finset (Finset α)}
  {W T : Finset α} :
  T ∈ bU m H W ↔
   T ∈ f6 H W ∧ m ≤ T.card := by
 simp [bU]
lemma jK
  {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
  (hT : T ∈ bU m H W) :
  Disjoint T W :=
 Gm (kQ.mp hT).1
lemma kZ
  {W S : Finset α} (hdisj : Disjoint S W) :
  (W ∪ S) \ S = W := by
 ext x
 constructor
 ·intro hx
  rcases Finset.mem_sdiff.mp hx with ⟨alZ, ajw⟩
  rcases Finset.mem_union.mp alZ with hxW | hxS
  ·exact hxW
  ·exact False.elim (ajw hxS)
 ·intro hxW
  exact Finset.mem_sdiff.mpr
   ⟨Finset.mem_union.mpr (Or.inl hxW),
    fun hxS => (Finset.disjoint_left.mp hdisj) hxS hxW⟩
@[simp]
lemma oq {m : ℕ} {H : Finset (Finset α)}
  {W T : Finset α} :
  T ∈ dK m H W ↔
   T ∈ f6 H W ∧ T.card < m := by
 simp [dK]
lemma Fw
  (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
  dK m H W ∪ bU m H W =
   f6 H W := by
 ext T
 by_cases hT : T ∈ f6 H W
 ·by_cases hsmall : T.card < m
  ·simp [hT, hsmall, bU, dK,
    not_le.mpr hsmall]
  ·have Dq : m ≤ T.card := le_of_not_gt hsmall
   simp [hT, Dq, hsmall, bU, dK]
 ·simp [hT, bU, dK]
lemma RH
  (X : Finset α) (H : Finset (Finset α)) (W : Finset α) :
  g7 X (f6 H W) (i9 H W) := by
 simpa [f6,g7] using
  (TD (X := (∅ : Finset α)) (U := i9 H W))
lemma g7.U4
  {X : Finset α} {G H : Finset (Finset α)} {W : Finset α}
  (iz : g7 X G (f6 H W)) :
  g7 X G H := by
 intro S hS
 have akM : S \ W ∈ i9 H W :=
  lB.mpr ⟨S, hS, rfl⟩
 rcases RH X H W (S \ W) akM with
  ⟨R, adS, Yf⟩
 rcases iz R adS with ⟨T, Nc, hTR⟩
 have adT : S \ W ⊆ S := by
  intro x hx
  exact (Finset.mem_sdiff.mp hx).1
 exact ⟨T, Nc, hTR.trans (Yf.trans adT)⟩
lemma Mt
  {S W V : Finset α} (h : S \ W ⊆ V) :
  S ⊆ W ∪ V := by
 intro x hxS
 by_cases hxW : x ∈ W
 ·exact Finset.mem_union.mpr (Or.inl hxW)
 ·exact Finset.mem_union.mpr
   (Or.inr (h (Finset.mem_sdiff.mpr ⟨hxS, hxW⟩)))
lemma q9
  {H : Finset (Finset α)} {W V : Finset α}
  (h : ∃ R ∈ f6 H W, R ⊆ V) :
  ∃ S ∈ H, S ⊆ W ∪ V := by
 rcases h with ⟨R, hR, hRV⟩
 have aa6 : R ∈ i9 H W :=
  iG H W hR
 rcases lB.mp aa6 with ⟨S, hS, hSR⟩
 refine ⟨S, hS, Mt ?_⟩
 intro x hx
 exact hRV (by simpa [hSR] using hx)
lemma Bz
  {H : Finset (Finset α)} {Z S T : Finset α}
  (hT : T ∈ H) (VY : T ⊆ Z)
  (hSmin : S ∈ f6 H (Z \ S)) :
  S ⊆ T := by
 by_contra hnot
 have aa6 : T \ (Z \ S) ∈ i9 H (Z \ S) :=
  lB.mpr ⟨T, hT, rfl⟩
 have Yf : T \ (Z \ S) ⊆ S := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxT, adU⟩
  by_contra hxS
  exact adU (Finset.mem_sdiff.mpr ⟨VY hxT, hxS⟩)
 have ahT : T \ (Z \ S) ⊂ S := by
  refine Yf.ssubset_of_ne ?_
  intro hEq
  have hST : S ⊆ T := by
   intro x hxS
   have hxR : x ∈ T \ (Z \ S) := by
    simpa [hEq] using hxS
   exact (Finset.mem_sdiff.mp hxR).1
  exact hnot hST
 exact (TJ.mp hSmin).2 (T \ (Z \ S)) aa6 ahT
lemma wW
  {H : Finset (Finset α)} {Z S T : Finset α} {m : ℕ}
  (hT : T ∈ H) (VY : T ⊆ Z)
  (hS : S ∈ bU m H (Z \ S)) :
  S ⊆ T :=
 Bz hT VY
  (kQ.mp hS).1
lemma l7
  {X : Finset α} {H : Finset (Finset α)} {W S : Finset α} {m : ℕ}
  (tZ : ∀ T ∈ H, T ⊆ X)
  (hS : S ∈ bU m H W) :
  S ⊆ X := by
 have aa7 : S ∈ i9 H W :=
  iG H W
   (kQ.mp hS).1
 rcases lB.mp aa7 with ⟨T, hT, rfl⟩
 exact (Finset.sdiff_subset : T \ W ⊆ T).trans (tZ T hT)
def dH
  (H : Finset (Finset α)) (m : ℕ) (Z : Finset α) :
  Finset (Finset α) :=
 Z.powerset.filter fun S => S ∈ bU m H (Z \ S)
@[simp]
lemma rD
  {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α} :
  S ∈ dH H m Z ↔
   S ⊆ Z ∧ S ∈ bU m H (Z \ S) := by
 simp [dH]
lemma Ao
  {m : ℕ} {H : Finset (Finset α)} {W S : Finset α}
  (hS : S ∈ bU m H W) :
  S ∈ dH H m (W ∪ S) := by
 have hdisj : Disjoint S W := jK hS
 have ajx : (W ∪ S) \ S = W :=
  kZ hdisj
 rw [rD]
 constructor
 ·exact Finset.subset_union_right
 ·simpa [ajx] using hS
lemma rE
  {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
  (hT : T ∈ H) (VY : T ⊆ Z) :
  dH H m Z ⊆
   T.powerset.filter fun S => m ≤ S.card := by
 intro S hS
 rcases rD.mp hS with ⟨am8, EH⟩
 have hST : S ⊆ T :=
  wW hT VY EH
 exact Finset.mem_filter.mpr
  ⟨Finset.mem_powerset.mpr hST, (kQ.mp EH).2⟩
lemma wX
  {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α}
  (hS : S ∈ dH H m Z) :
  ∃ T ∈ H, T ⊆ Z := by
 rcases rD.mp hS with ⟨hSZ, EH⟩
 have aa7 : S ∈ i9 H (Z \ S) :=
  iG H (Z \ S)
   (kQ.mp EH).1
 rcases lB.mp aa7 with ⟨T, hT, hdiff⟩
 refine ⟨T, hT, ?_⟩
 intro x hxT
 by_contra hxZ
 have adU : x ∉ Z \ S := by
  intro hx
  exact hxZ (Finset.mem_sdiff.mp hx).1
 have hxS : x ∈ S := by
  have hx : x ∈ T \ (Z \ S) :=
   Finset.mem_sdiff.mpr ⟨hxT, adU⟩
  simpa [hdiff] using hx
 exact hxZ (hSZ hxS)
lemma rS
  {H : Finset (Finset α)} {m : ℕ} {Z : Finset α}
  (hno : ¬ ∃ T ∈ H, T ⊆ Z) :
  dH H m Z = ∅ := by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro S hS
 exact hno (wX hS)
lemma Aw
  {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
  (w : Finset α → ℝ) (hw : ∀ S, 0 ≤ w S)
  (hT : T ∈ H) (VY : T ⊆ Z) :
  (∑ S ∈ dH H m Z, w S) ≤
   ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), w S :=
 Finset.sum_le_sum_of_subset_of_nonneg
  (rE hT VY)
  (by intro S _ _; exact hw S)
omit [DecidableEq α] in
lemma wY
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
lemma u9
  (T : Finset α) (m : ℕ) {a : ℝ}
  (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
  (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
   (2 : ℝ) ^ T.card * a ^ m := by
 have hsum :=
  wY T m ha0 ha1
 have vY :
   (T.powerset.filter fun S => m ≤ S.card).card ≤ T.powerset.card :=
  Finset.card_le_card (Finset.filter_subset _ _)
 have qC :
   (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
    (2 : ℝ) ^ T.card := by
  have hcast : (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
    (T.powerset.card : ℝ) := by
   exact_mod_cast vY
  simpa using hcast
 have hmul :
   (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) ≤
    (2 : ℝ) ^ T.card * a ^ m :=
  mul_le_mul_of_nonneg_right qC (pow_nonneg ha0 m)
 exact hsum.trans hmul
lemma tj
  {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α} {a : ℝ}
  (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
  (hT : T ∈ H) (VY : T ⊆ Z) :
  (∑ S ∈ dH H m Z, a ^ S.card) ≤
   (2 : ℝ) ^ T.card * a ^ m := by
 have adV :
   (∑ S ∈ dH H m Z, a ^ S.card) ≤
    ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card :=
  Aw
   (fun S => a ^ S.card) (fun S => pow_nonneg ha0 S.card) hT VY
 exact adV.trans
  (u9 T m ha0 ha1)
def gP
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
  Finset (Finset α × Finset α) :=
 X.powerset.biUnion fun W =>
  (bU m H W).image fun S => (W, S)
lemma Gp
  {H : Finset (Finset α)} {m : ℕ} {W W' : Finset α}
  (hWW' : W ≠ W') :
  Disjoint
   ((bU m H W).image fun S => (W, S))
   ((bU m H W').image fun S => (W', S)) := by
 rw [Finset.disjoint_left]
 intro P hP hP'
 rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
 rcases Finset.mem_image.mp hP' with ⟨S', al0, agE⟩
 have hfirst : W = W' := by
  calc
   W = (W, S).1 := rfl
   _ = P.1 := congrArg Prod.fst hEq
   _ = (W', S').1 := (congrArg Prod.fst agE).symm
   _ = W' := rfl
 exact hWW' hfirst
lemma zU
  (H : Finset (Finset α)) (m : ℕ) :
  (X : Finset (Finset α)) →
   ∀ W ∈ X, ∀ W' ∈ X, W ≠ W' →
    Disjoint
     ((bU m H W).image fun S => (W, S))
     ((bU m H W').image fun S => (W', S)) :=
 fun _ W _ W' _ hWW' =>
  Gp (H := H) (m := m) (W := W) (W' := W') hWW'
@[simp]
lemma qH
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
  {P : Finset α × Finset α} :
  P ∈ gP X H m ↔
   P.1 ⊆ X ∧ P.2 ∈ bU m H P.1 := by
 constructor
 ·intro hP
  rcases Finset.mem_biUnion.mp hP with ⟨W, ajy, adW⟩
  rcases Finset.mem_image.mp adW with ⟨S, hS, hEq⟩
  have hP1 : P.1 = W := (congrArg Prod.fst hEq).symm
  have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
  exact ⟨by simpa [hP1] using Finset.mem_powerset.mp ajy,
   by simpa [hP1, hP2] using hS⟩
 ·intro h
  rcases P with ⟨W, S⟩
  exact Finset.mem_biUnion.mpr
   ⟨W, Finset.mem_powerset.mpr h.1,
    Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩
def jt
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
  Finset (Finset α × Finset α) :=
 X.powerset.biUnion fun Z =>
  (dH H m Z).image fun S => (Z, S)
lemma IG
  {H : Finset (Finset α)} {m : ℕ} {Z Z' : Finset α}
  (agF : Z ≠ Z') :
  Disjoint
   ((dH H m Z).image fun S => (Z, S))
   ((dH H m Z').image fun S => (Z', S)) := by
 rw [Finset.disjoint_left]
 intro P hP hP'
 rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
 rcases Finset.mem_image.mp hP' with ⟨S', al0, agE⟩
 have hfirst : Z = Z' := by
  calc
   Z = (Z, S).1 := rfl
   _ = P.1 := congrArg Prod.fst hEq
   _ = (Z', S').1 := (congrArg Prod.fst agE).symm
   _ = Z' := rfl
 exact agF hfirst
lemma AH
  (H : Finset (Finset α)) (m : ℕ) :
  (X : Finset (Finset α)) →
   ∀ Z ∈ X, ∀ Z' ∈ X, Z ≠ Z' →
    Disjoint
     ((dH H m Z).image fun S => (Z, S))
     ((dH H m Z').image fun S => (Z', S)) :=
 fun _ Z _ Z' _ agF =>
  IG (H := H) (m := m) (Z := Z) (Z' := Z') agF
@[simp]
lemma R8
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
  {P : Finset α × Finset α} :
  P ∈ jt X H m ↔
   P.1 ⊆ X ∧ P.2 ∈ dH H m P.1 := by
 constructor
 ·intro hP
  rcases Finset.mem_biUnion.mp hP with ⟨Z, ajz, adW⟩
  rcases Finset.mem_image.mp adW with ⟨S, hS, hEq⟩
  have hP1 : P.1 = Z := (congrArg Prod.fst hEq).symm
  have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
  exact ⟨by simpa [hP1] using Finset.mem_powerset.mp ajz,
   by simpa [hP1, hP2] using hS⟩
 ·intro h
  rcases P with ⟨Z, S⟩
  exact Finset.mem_biUnion.mpr
   ⟨Z, Finset.mem_powerset.mpr h.1,
    Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩
def jf
  (P : Finset α × Finset α) : Finset α × Finset α :=
 (P.1 ∪ P.2, P.2)
lemma Kt
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
  (tZ : ∀ T ∈ H, T ⊆ X)
  {P : Finset α × Finset α}
  (hP : P ∈ gP X H m) :
  jf P ∈ jt X H m := by
 rcases P with ⟨W, S⟩
 rcases qH.mp hP with ⟨Yd, hS⟩
 rw [R8]
 constructor
 ·exact Finset.union_subset Yd (l7 tZ hS)
 ·exact Ao hS
lemma IQ
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ} :
  Set.InjOn (jf : Finset α × Finset α → Finset α × Finset α)
   (↑(gP X H m)) := by
 intro P hP Q hQ hEq
 rcases P with ⟨W, S⟩
 rcases Q with ⟨W', S'⟩
 have hS_eq : S = S' := by
  exact congrArg Prod.snd hEq
 have ae8 : W ∪ S = W' ∪ S' := by
  exact congrArg Prod.fst hEq
 rcases qH.mp hP with ⟨am9, EH⟩
 rcases qH.mp hQ with ⟨am2, agG⟩
 have hW_eq : W = W' := by
  have hleft :
    (W ∪ S) \ S = W :=
   kZ
    (jK EH)
  have hright :
    (W' ∪ S') \ S' = W' :=
   kZ
    (jK agG)
  calc
   W = (W ∪ S) \ S := hleft.symm
   _ = (W' ∪ S') \ S' := by rw [ae8, hS_eq]
   _ = W' := hright
 simp [hW_eq, hS_eq]
lemma BG
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
  (tZ : ∀ T ∈ H, T ⊆ X) :
  (gP X H m).image jf ⊆
   jt X H m := by
 intro Q hQ
 rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
 exact Kt tZ hP
lemma rF
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
  (tZ : ∀ T ∈ H, T ⊆ X)
  (w : Finset α × Finset α → ℝ)
  (hw : ∀ P, 0 ≤ w P) :
  (∑ P ∈ gP X H m, w (jf P)) ≤
   ∑ Q ∈ jt X H m, w Q := by
 have Bj := BG
  (X := X) (H := H) (m := m) tZ
 calc
  (∑ P ∈ gP X H m, w (jf P))
    = ∑ Q ∈ (gP X H m).image jf, w Q := by
     rw [Finset.sum_image (IQ
      (X := X) (H := H) (m := m))]
  _ ≤ ∑ Q ∈ jt X H m, w Q :=
    Finset.sum_le_sum_of_subset_of_nonneg Bj
     (by intro Q _ _; exact hw Q)
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
noncomputable def tq (X : Finset α) (U : Finset (Finset α)) :
  Finset (Finset (Finset α)) :=
 by
  classical
  exact X.powerset.powerset.filter fun G => g7 X G U
omit [DecidableEq α] in
lemma Gq (X : Finset α) (U : Finset (Finset α)) :
  g7 X ({∅} : Finset (Finset α)) U := by
 intro S _hS
 exact ⟨∅, by simp, Finset.empty_subset S⟩
omit [DecidableEq α] in
lemma QG (X : Finset α) (U : Finset (Finset α)) :
  (tq X U).Nonempty := by
 refine ⟨{∅}, ?_⟩
 classical
 rw [tq, Finset.mem_filter]
 constructor
 ·rw [Finset.mem_powerset]
  intro T hT
  have hT_empty : T = ∅ := by simpa using hT
  subst hT_empty
  exact Finset.mem_powerset.mpr (Finset.empty_subset X)
 ·exact Gq X U
omit [DecidableEq α] in
lemma DQ {X : Finset α} {U G : Finset (Finset α)} :
  G ∈ tq X U ↔
   (∀ T ∈ G, T ⊆ X) ∧ g7 X G U := by
 classical
 rw [tq, Finset.mem_filter]
 constructor
 ·intro h
  constructor
  ·intro T Nc
   exact Finset.mem_powerset.mp (Finset.mem_powerset.mp h.1 Nc)
  ·exact h.2
 ·rintro ⟨hGX, iz⟩
  refine ⟨?_, iz⟩
  exact Finset.mem_powerset.mpr (by
   intro T Nc
   exact Finset.mem_powerset.mpr (hGX T Nc))
noncomputable def n8 (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
  Finset ℝ :=
 by
  classical
  exact (tq X U).image fun G => g3 G p
omit [DecidableEq α] in
lemma zY
  (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
  (n8 X U p).Nonempty :=
 (QG X U).image _
noncomputable def cV
  (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
 (n8 X U p).min' (zY X U p)
omit [DecidableEq α] in
lemma jC
  {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
  (hGX : ∀ T ∈ G, T ⊆ X) (iz : g7 X G U) :
  cV X U p ≤ g3 G p := by
 unfold cV n8
 exact Finset.min'_le _ _ (Finset.mem_image.mpr
  ⟨G, (DQ.mpr ⟨hGX, iz⟩), rfl⟩)
omit [DecidableEq α] in
lemma Qe
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) :
  0 ≤ cV X U p := by
 unfold cV n8
 refine Finset.le_min' _ _ _ ?_
 intro w hw
 rcases Finset.mem_image.mp hw with ⟨G, _hG, rfl⟩
 unfold g3
 exact Finset.sum_nonneg fun T _ => pow_nonneg hp0 T.card
omit [DecidableEq α] in
lemma jE
  (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
  ∃ G : Finset (Finset α),
   (∀ T ∈ G, T ⊆ X) ∧
   g7 X G U ∧
   cV X U p = g3 G p := by
 unfold cV n8
 have hmem :=
  Finset.min'_mem ((tq X U).image fun G => g3 G p)
   (zY X U p)
 rcases Finset.mem_image.mp hmem with ⟨G, hG, hEq⟩
 rcases DQ.mp hG with ⟨hGX, iz⟩
 exact ⟨G, hGX, iz, hEq.symm⟩
omit [DecidableEq α] in
lemma Nh (p : ℝ) :
  g3 ({∅} : Finset (Finset α)) p = 1 := by
 simp [g3]
omit [DecidableEq α] in
lemma Xt (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
  cV X U p ≤ 1 := by
 have hle := jC
  (X := X) (U := U) (G := ({∅} : Finset (Finset α))) (p := p)
  (by
   intro T hT
   have hT_empty : T = ∅ := by simpa using hT
   subst hT_empty
   exact Finset.empty_subset X)
  (Gq X U)
 simpa [Nh] using hle
omit [DecidableEq α] in
lemma acw (X : Finset α) (U : Finset (Finset α)) :
  g7 X U U := by
 intro S hS
 exact ⟨S, hS, subset_refl S⟩
omit [DecidableEq α] in
lemma Lk
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hUX : ∀ T ∈ U, T ⊆ X) :
  cV X U p ≤ g3 U p :=
 jC hUX (acw X U)
omit [DecidableEq α] in
lemma QH
  (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
  cV X (∅ : Finset (Finset α)) p = 0 := by
 have hle : cV X (∅ : Finset (Finset α)) p ≤ 0 := by
  have hcover : g7 X (∅ : Finset (Finset α))
    (∅ : Finset (Finset α)) := by
   intro S hS
   simp at hS
  have ahU : ∀ T ∈ (∅ : Finset (Finset α)), T ⊆ X := by
   intro T hT
   simp at hT
  simpa [g3] using
   (jC (X := X)
    (U := (∅ : Finset (Finset α)))
    (G := (∅ : Finset (Finset α))) (p := p) ahU hcover)
 exact le_antisymm hle (Qe hp0)
omit [DecidableEq α] in
lemma Lq
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
  1 ≤ cV X U p := by
 unfold cV n8
 refine Finset.le_min' _ _ _ ?_
 intro w hw
 rcases Finset.mem_image.mp hw with ⟨G, hG, rfl⟩
 rcases DQ.mp hG with ⟨al3, iz⟩
 rcases iz ∅ hEmpty with ⟨T, Nc, akN⟩
 have hT_empty : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simpa using akN hx
 have nZ :
   p ^ T.card ≤ g3 G p := by
  unfold g3
  exact Finset.single_le_sum
   (s := G) (f := fun S : Finset α => p ^ S.card)
   (fun S _ => pow_nonneg hp0 S.card) Nc
 have hterm : p ^ T.card = 1 := by
  subst hT_empty
  simp
 linarith
omit [DecidableEq α] in
lemma Ly
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
  cV X U p = 1 :=
 le_antisymm (Xt X U p)
  (Lq hp0 hEmpty)
omit [DecidableEq α] in
lemma zA
  {U : Finset (Finset α)}
  (hcard : ∀ S ∈ U, S.card = 0)
  (hEmpty : (∅ : Finset α) ∉ U) :
  U = ∅ := by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro S hS
 have Iz : S = ∅ := Finset.card_eq_zero.mp (hcard S hS)
 exact hEmpty (by simpa [Iz] using hS)
omit [DecidableEq α] in
lemma vh
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p)
  (hcard : ∀ S ∈ U, S.card = 0) :
  0 < cV X U p ↔ (∅ : Finset α) ∈ U := by
 constructor
 ·intro hpos
  by_contra hEmpty
  have agH : U = ∅ :=
   zA hcard hEmpty
  have aax : cV X U p = 0 := by
   rw [agH]
   exact QH X hp0
  linarith
 ·intro hEmpty
  rw [Ly hp0 hEmpty]
  norm_num
theorem QI
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
  fO X U p ↔ cV X U p ≤ (1 / 2 : ℝ) := by
 constructor
 ·intro tQ
  rcases fO.UO hp0 hUX tQ with
   ⟨G, hGX, iz, hsum⟩
  exact (jC hGX iz).trans hsum
 ·intro akO
  rcases jE X U p with
   ⟨G, al3, iz, hEq⟩
  exact ⟨G, iz, by simpa [hEq,g3] using akO⟩
lemma IT
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
  ¬ fO X U p ↔ (1 / 2 : ℝ) < cV X U p := by
 rw [QI hp0 hUX]
 exact not_le
lemma VZ
  {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) :
  cV X (U ∪ V) p ≤ cV X U p + cV X V p := by
 rcases jE X U p with
  ⟨G, hGX, ahV, al4⟩
 rcases jE X V p with
  ⟨H, tZ, ahW, al5⟩
 have aa8 : ∀ T ∈ G ∪ H, T ⊆ X := by
  intro T hT
  rcases Finset.mem_union.mp hT with Nc | hTH
  ·exact hGX T Nc
  ·exact tZ T hTH
 have acy : g7 X (G ∪ H) (U ∪ V) :=
  ahV.union ahW
 calc
  cV X (U ∪ V) p ≤ g3 (G ∪ H) p :=
   jC aa8 acy
  _ ≤ g3 G p + g3 H p := Tz hp0
  _ = cV X U p + cV X V p := by
   rw [al4, al5]
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
lemma Lz
  (X : Finset α) (H : Finset (Finset α)) (W : Finset α) (p : ℝ) :
  cV X H p ≤ cV X (f6 H W) p := by
 rcases jE X (f6 H W) p with
  ⟨G, hGX, iz, hEq⟩
 exact (jC hGX iz.U4).trans_eq
  hEq.symm
lemma wA
  (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
  {p : ℝ} (hp0 : 0 ≤ p) :
  cV X H p ≤
   cV X (dK m H W) p +
    cV X (bU m H W) p := by
 have ajA :
   cV X H p ≤ cV X (f6 H W) p :=
  Lz X H W p
 have hpartition :
   dK m H W ∪ bU m H W =
    f6 H W :=
  Fw m H W
 have ahX :
   cV X (dK m H W ∪ bU m H W) p ≤
    cV X (dK m H W) p +
     cV X (bU m H W) p :=
  VZ hp0
 calc
  cV X H p ≤ cV X (f6 H W) p := ajA
  _ = cV X
     (dK m H W ∪ bU m H W) p := by
    rw [hpartition]
  _ ≤ cV X (dK m H W) p +
    cV X (bU m H W) p := ahX
lemma EI
  {H : Finset (Finset α)} {W T : Finset α}
  (hT : T ∈ dK 1 H W) :
  T.card = 0 := by
 exact Nat.lt_one_iff.mp (oq.mp hT).2
lemma qo
  (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
  {p : ℝ} (hp0 : 0 ≤ p) :
  0 < cV X (dK 1 H W) p ↔
   ∃ S ∈ H, S ⊆ W := by
 rw [vh
  (X := X) (U := dK 1 H W) (p := p) hp0
  (fun T hT => EI hT)]
 simp
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
def dQ : List (ℕ × Finset α) → Finset α
 | [] => ∅
 | step :: steps => step.2 ∪ dQ steps
def bZ (H : Finset (Finset α)) :
  List (ℕ × Finset α) → Finset (Finset α)
 | [] => H
 | step :: steps =>
   bZ
    (dK step.1 H step.2) steps
noncomputable def bR
  (X : Finset α) (p : ℝ) (H : Finset (Finset α)) :
  List (ℕ × Finset α) → ℝ
 | [] => 0
 | step :: steps =>
   cV X (bU step.1 H step.2) p +
    bR X p
     (dK step.1 H step.2) steps
def aP :
  {n : ℕ} → (Fin n → ℕ) → (Fin n → Finset α) → List (ℕ × Finset α)
 | 0, ac6, _Ws => []
 | n + 1, cutoff, Ws =>
   aP
    (fun i : Fin n => cutoff i.castSucc)
    (fun i : Fin n => Ws i.castSucc) ++
    [(cutoff (Fin.last n), Ws (Fin.last n))]
omit [DecidableEq α] in
lemma Ni {n : ℕ}
  (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
  (W : Finset α) :
  aP cutoff
    (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
   aP
    (fun i : Fin n => cutoff i.castSucc) Ws ++
    [(cutoff (Fin.last n), W)] := by
 simp [aP]
lemma IU
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
  (w : Finset α × Finset α → ℝ) :
  (∑ P ∈ gP X H m, w P) =
   ∑ W ∈ X.powerset,
    ∑ S ∈ bU m H W, w (W, S) := by
 unfold gP
 rw [Finset.sum_biUnion (zU H m X.powerset)]
 refine Finset.sum_congr rfl ?_
 intro W _hW
 rw [Finset.sum_image]
 intro S _hS T _hT hEq
 exact congrArg Prod.snd hEq
lemma vO
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
  (ρ q : ℝ) :
  (∑ W ∈ X.powerset,
   aF X W ρ * g3 (bU m H W) q) =
   ∑ P ∈ gP X H m,
    aF X P.1 ρ * q ^ P.2.card := by
 rw [IU]
 unfold g3
 refine Finset.sum_congr rfl ?_
 intro W _hW
 rw [Finset.mul_sum]
lemma JE
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
  (w : Finset α × Finset α → ℝ) :
  (∑ P ∈ jt X H m, w P) =
   ∑ Z ∈ X.powerset,
    ∑ S ∈ dH H m Z, w (Z, S) := by
 unfold jt
 rw [Finset.sum_biUnion (AH H m X.powerset)]
 refine Finset.sum_congr rfl ?_
 intro Z _hZ
 rw [Finset.sum_image]
 intro S _hS T _hT hEq
 exact congrArg Prod.snd hEq
lemma BK
  (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
  {ρ q : ℝ} (mL : 0 ≤ ρ) (m7 : ρ ≤ 1)
  (tZ : ∀ S ∈ H, S ⊆ X) :
  (∑ W ∈ X.powerset,
   aF X W ρ *
    cV X (bU m H W) q) ≤
   ∑ P ∈ gP X H m,
    aF X P.1 ρ * q ^ P.2.card := by
 calc
  (∑ W ∈ X.powerset,
   aF X W ρ *
    cV X (bU m H W) q)
    ≤ ∑ W ∈ X.powerset,
      aF X W ρ *
       g3 (bU m H W) q := by
     refine Finset.sum_le_sum ?_
     intro W _hW
     have aax :
       cV X (bU m H W) q ≤
        g3 (bU m H W) q :=
      Lk
       (fun T hT => l7 tZ hT)
     exact mul_le_mul_of_nonneg_left aax
      (j8 mL m7)
  _ = ∑ P ∈ gP X H m,
     aF X P.1 ρ * q ^ P.2.card :=
    vO X H m ρ q
lemma Db
  (X : Finset α) (H : Finset (Finset α)) (m L : ℕ)
  {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
  (hρ : ρ = 1 - (1 - q) ^ L)
  (tZ : ∀ S ∈ H, S ⊆ X) :
  (∑ P ∈ gP X H m,
   aF X P.1 ρ * q ^ P.2.card) ≤
   ∑ Q ∈ jt X H m,
    aF X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card := by
 have mL : 0 ≤ ρ := by
  have adX : 0 < ρ := by
   simpa [hρ] using r7 hL hq0 hq1
  exact adX.le
 have m7 : ρ ≤ 1 := by
  rw [hρ]
  have MW : 0 ≤ (1 - q) ^ L := by
   exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
  linarith
 have hLpos : 0 < (L : ℝ) := by
  have Kp : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  exact_mod_cast Kp
 let w : Finset α × Finset α → ℝ :=
  fun Q => aF X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card
 have hterm :
   (∑ P ∈ gP X H m,
    aF X P.1 ρ * q ^ P.2.card) ≤
    ∑ P ∈ gP X H m, w (jf P) := by
  refine Finset.sum_le_sum ?_
  intro P hP
  rcases P with ⟨W, S⟩
  rcases qH.mp hP with ⟨Yd, EH⟩
  have hdisj : Disjoint S W :=
   jK EH
  have Jq : W ∪ S ⊆ X :=
   Finset.union_subset Yd (l7 tZ EH)
  exact vN
   (X := X) (W := W) (S := S) (q := q) (ρ := ρ) (L := L)
   hL hq0 hq1 hρ hdisj Jq
 have ae9 : ∀ Q, 0 ≤ w Q := by
  intro Q
  exact mul_nonneg (j8 mL m7)
   (pow_nonneg (by positivity : 0 ≤ (1 / (L : ℝ))) Q.2.card)
 exact hterm.trans
  (rF tZ w ae9)
lemma EK
  (X : Finset α) (H : Finset (Finset α)) (m ell : ℕ)
  {ρ a : ℝ} (mL : 0 ≤ ρ) (m7 : ρ ≤ 1)
  (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
  (Mc : ∀ T ∈ H, T.card ≤ ell) :
  (∑ Q ∈ jt X H m,
   aF X Q.1 ρ * a ^ Q.2.card) ≤
   dN X (aV X H) ρ * ((2 : ℝ) ^ ell * a ^ m) := by
 let B : ℝ := (2 : ℝ) ^ ell * a ^ m
 have alq : 0 ≤ B := by
  dsimp [B]
  positivity
 have acz :
   ∀ Z ∈ X.powerset, Z ∉ aV X H →
    (∑ S ∈ dH H m Z,
     aF X Z ρ * a ^ S.card) = 0 := by
  intro Z _hZ akP
  have hno : ¬ ∃ T ∈ H, T ⊆ Z := by
   intro h
   exact akP (eO.mpr
    ⟨Finset.mem_powerset.mp _hZ, h⟩)
  rw [rS hno]
  simp
 have aa9 :
   ∀ Z ∈ X.powerset, Z ∈ aV X H →
    (∑ S ∈ dH H m Z,
     aF X Z ρ * a ^ S.card) ≤
     aF X Z ρ * B := by
  intro Z _hZ hZU
  rcases eO.mp hZU with ⟨ana, T, hT, VY⟩
  have Ej :
    (∑ S ∈ dH H m Z, a ^ S.card) ≤
     (2 : ℝ) ^ T.card * a ^ m :=
   tj ha0 ha1 hT VY
  have adG : T.card ≤ ell := Mc T hT
  have agI : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ ell :=
   pow_le_pow_right₀ (by norm_num) adG
  have abb :
    (2 : ℝ) ^ T.card * a ^ m ≤ B := by
   exact mul_le_mul_of_nonneg_right agI (pow_nonneg ha0 m)
  calc
   (∑ S ∈ dH H m Z,
     aF X Z ρ * a ^ S.card)
     = aF X Z ρ *
       ∑ S ∈ dH H m Z, a ^ S.card := by
      rw [Finset.mul_sum]
   _ ≤ aF X Z ρ * ((2 : ℝ) ^ T.card * a ^ m) :=
      mul_le_mul_of_nonneg_left Ej
       (j8 mL m7)
   _ ≤ aF X Z ρ * B :=
      mul_le_mul_of_nonneg_left abb
       (j8 mL m7)
 calc
  (∑ Q ∈ jt X H m,
   aF X Q.1 ρ * a ^ Q.2.card)
    = ∑ Z ∈ X.powerset,
      ∑ S ∈ dH H m Z,
       aF X Z ρ * a ^ S.card := by
     rw [JE]
  _ = ∑ Z ∈ X.powerset,
      if Z ∈ aV X H then
       ∑ S ∈ dH H m Z,
        aF X Z ρ * a ^ S.card
      else 0 := by
     refine Finset.sum_congr rfl ?_
     intro Z hZ
     by_cases hZU : Z ∈ aV X H
     ·simp [hZU]
     ·simp [hZU, acz Z hZ hZU]
  _ = ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ aV X H),
      ∑ S ∈ dH H m Z,
       aF X Z ρ * a ^ S.card := by
     rw [Finset.sum_filter]
  _ ≤ ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ aV X H),
      aF X Z ρ * B := by
     refine Finset.sum_le_sum ?_
     intro Z hZ
     exact aa9 Z (Finset.mem_filter.mp hZ).1
      (Finset.mem_filter.mp hZ).2
  _ = dN X (aV X H) ρ * B := by
     unfold dN
     rw [← Finset.sum_mul]
lemma r8
  (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
  {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
  (hρ : ρ = 1 - (1 - q) ^ L)
  (tZ : ∀ S ∈ H, S ⊆ X)
  (Mc : ∀ S ∈ H, S.card ≤ ell) :
  (∑ W ∈ X.powerset,
   aF X W ρ *
    cV X (bU m H W) q) ≤
   dN X (aV X H) ρ *
    ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) := by
 have mL : 0 ≤ ρ := by
  have adX : 0 < ρ := by
   simpa [hρ] using r7 hL hq0 hq1
  exact adX.le
 have m7 : ρ ≤ 1 := by
  rw [hρ]
  have MW : 0 ≤ (1 - q) ^ L := by
   exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
  linarith
 have hLpos : 0 < (L : ℝ) := by
  have Kp : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  exact_mod_cast Kp
 have akQ : 0 ≤ (1 / (L : ℝ)) := by positivity
 have akR : (1 / (L : ℝ)) ≤ 1 := by
  rw [div_le_one hLpos]
  exact_mod_cast hL
 calc
  (∑ W ∈ X.powerset,
   aF X W ρ *
    cV X (bU m H W) q)
    ≤ ∑ P ∈ gP X H m,
      aF X P.1 ρ * q ^ P.2.card :=
     BK X H m mL m7 tZ
  _ ≤ ∑ Q ∈ jt X H m,
     aF X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card :=
     Db
      X H m L hL hq0 hq1 hρ tZ
  _ ≤ dN X (aV X H) ρ *
    ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) :=
     EK
      X H m ell mL m7 akQ akR Mc
lemma pI
  (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) :
  dQ (steps ++ [step]) =
   dQ steps ∪ step.2 := by
 induction steps with
 | nil =>
   simp [dQ]
 | cons head steps ih =>
   simp [dQ, ih, Finset.union_assoc]
lemma mO
  {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
  dQ (aP cutoff Ws) =
   cE Ws := by
 induction n with
 | zero =>
   ext x
   simp [aP, dQ, cE]
 | succ n ih =>
   rw [aP]
   rw [pI]
   rw [ih]
   ext x
   constructor
   ·intro hx
    rcases Finset.mem_union.mp hx with abd | abe
    ·rcases (by
      simpa [cE] using abd :
       ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
     simpa [cE] using
      (Exists.intro (i.castSucc : Fin (n + 1)) hi)
    ·simpa [cE] using
      (Exists.intro (Fin.last n) abe)
   ·intro hx
    rcases (by
     simpa [cE] using hx :
      ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    ·exact Finset.mem_union.mpr (Or.inl (by
      simpa [cE] using (Exists.intro j hi)))
    ·exact Finset.mem_union.mpr (Or.inr hi)
lemma Gt
  {X : Finset α} {n : ℕ} {cutoff : Fin (n + 1) → ℕ}
  {Ws : Fin (n + 1) → Finset α}
  (hWs : Ws ∈ bD X (n + 1))
  (hlast : cutoff (Fin.last n) = 1) :
  ∃ steps V,
   aP cutoff Ws = steps ++ [(1, V)] ∧
   dQ steps ∪ V ⊆ X := by
 refine ⟨aP
   (fun i : Fin n => cutoff i.castSucc)
   (fun i : Fin n => Ws i.castSucc),
  Ws (Fin.last n), ?_, ?_⟩
 ·simp [aP, hlast]
 ·rw [mO]
  intro x hx
  rcases Finset.mem_union.mp hx with abd | abe
  ·rcases (by
    simpa [cE] using abd :
     ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
   exact Finset.mem_powerset.mp ((jB.mp hWs) i.castSucc) hi
  ·exact Finset.mem_powerset.mp
    ((jB.mp hWs) (Fin.last n)) abe
lemma pJ
  (H : Finset (Finset α)) (steps : List (ℕ × Finset α))
  (step : ℕ × Finset α) :
  bZ H (steps ++ [step]) =
   dK step.1 (bZ H steps) step.2 := by
 induction steps generalizing H with
 | nil =>
   simp [bZ]
 | cons head steps ih =>
   simp [bZ, ih]
lemma EO
  {X : Finset α} {H : Finset (Finset α)} {m : ℕ} {W : Finset α}
  (tZ : ∀ S ∈ H, S ⊆ X) :
  ∀ T ∈ dK m H W, T ⊆ X := by
 intro T hT x hx
 rcases oq.mp hT with ⟨X0, amC⟩
 rcases lB.mp
   (iG H W X0) with
  ⟨S, hS, rfl⟩
 exact tZ S hS (Finset.mem_sdiff.mp hx).1
lemma DU
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α))
  (tZ : ∀ S ∈ H, S ⊆ X) :
  ∀ T ∈ bZ H steps, T ⊆ X := by
 induction steps generalizing H with
 | nil =>
   simpa [bZ] using tZ
 | cons step steps ih =>
   simpa [bZ] using
    ih (H := dK step.1 H step.2)
     (EO (X := X) tZ)
lemma Nj
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
  0 ≤ bR X p H steps := by
 induction steps generalizing H with
 | nil =>
   simp [bR]
 | cons step steps ih =>
   have aax :
     0 ≤ cV X (bU step.1 H step.2) p :=
    Qe hp0
   have hrest :
     0 ≤ bR X p
      (dK step.1 H step.2) steps :=
    ih (H := dK step.1 H step.2)
   simpa [bR] using add_nonneg aax hrest
lemma Dd
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) {p : ℝ} :
  bR X p H (steps ++ [step]) =
   bR X p H steps +
    cV X
     (bU step.1 (bZ H steps) step.2) p := by
 induction steps generalizing H with
 | nil =>
   simp [bR, bZ]
 | cons head steps ih =>
   simp [bR, bZ, ih, add_assoc]
lemma uj
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
  (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
  (W : Finset α) :
  bR X p H
    (aP cutoff
     (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
   bR X p H
    (aP
     (fun i : Fin n => cutoff i.castSucc) Ws) +
    cV X
     (bU (cutoff (Fin.last n))
      (bZ H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)) W) p := by
 rw [Ni]
 simpa using
  Dd
   (X := X) (H := H)
   (steps := aP
    (fun i : Fin n => cutoff i.castSucc) Ws)
   (step := (cutoff (Fin.last n), W)) (p := p)
lemma rG
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
  (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ) :
  (∑ Ω ∈ bD X (n + 1),
   aW X ρ Ω *
    bR X p H (aP cutoff Ω)) =
   ∑ W ∈ X.powerset,
    ∑ Ws ∈ bD X n,
     (aW X (fun i : Fin n => ρ i.castSucc) Ws *
       aF X W (ρ (Fin.last n))) *
      (bR X p H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws) +
       cV X
        (bU (cutoff (Fin.last n))
         (bZ H
          (aP
           (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
 classical
 let e : Finset α × (Fin n → Finset α) ↪
   (Fin (n + 1) → Finset α) :=
  (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
 calc
  (∑ Ω ∈ bD X (n + 1),
   aW X ρ Ω *
    bR X p H (aP cutoff Ω))
    = ∑ P ∈ (X.powerset ×ˢ bD X n),
      aW X ρ (e P) *
       bR X p H
        (aP cutoff (e P)) := by
      rw [Fh X n, Finset.sum_map]
  _ = ∑ W ∈ X.powerset,
    ∑ Ws ∈ bD X n,
     (aW X (fun i : Fin n => ρ i.castSucc) Ws *
       aF X W (ρ (Fin.last n))) *
      (bR X p H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws) +
       cV X
        (bU (cutoff (Fin.last n))
         (bZ H
          (aP
           (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
     rw [Finset.sum_product]
     refine Finset.sum_congr rfl ?_
     intro W _hW
     refine Finset.sum_congr rfl ?_
     intro Ws aaZ
     change
      aW X ρ
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) *
       bR X p H
        (aP cutoff
         (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
      (aW X (fun i : Fin n => ρ i.castSucc) Ws *
        aF X W (ρ (Fin.last n))) *
       (bR X p H
         (aP
          (fun i : Fin n => cutoff i.castSucc) Ws) +
        cV X
         (bU (cutoff (Fin.last n))
          (bZ H
           (aP
            (fun i : Fin n => cutoff i.castSucc) Ws)) W) p)
     rw [Qb,
      uj]
lemma kR
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
  (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
  (B : (Fin n → Finset α) → ℝ)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (hfinal :
   ∀ Ws ∈ bD X n,
    (∑ W ∈ X.powerset,
     aF X W (ρ (Fin.last n)) *
      cV X
       (bU (cutoff (Fin.last n))
        (bZ H
         (aP
          (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) ≤
     B Ws) :
  (∑ Ω ∈ bD X (n + 1),
   aW X ρ Ω *
    bR X p H (aP cutoff Ω)) ≤
   ∑ Ws ∈ bD X n,
    (aW X (fun i : Fin n => ρ i.castSucc) Ws *
      bR X p H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws) +
     aW X (fun i : Fin n => ρ i.castSucc) Ws * B Ws) := by
 classical
 rw [rG]
 rw [Finset.sum_comm]
 refine Finset.sum_le_sum ?_
 intro Ws hWs
 let i7 : Fin n → ℝ := fun i => ρ i.castSucc
 let n9 : ℝ := ρ (Fin.last n)
 let loss : ℝ :=
  bR X p H
   (aP
    (fun i : Fin n => cutoff i.castSucc) Ws)
 let s7 : Finset α → ℝ := fun W =>
  cV X
   (bU (cutoff (Fin.last n))
    (bZ H
     (aP
      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p
 let wt : ℝ := aW X i7 Ws
 have al6 : 0 ≤ wt := by
  dsimp [wt, i7]
  exact Br X
   (fun i : Fin n => mL i.castSucc)
   (fun i : Fin n => m7 i.castSucc) Ws
 have afa :
   (∑ W ∈ X.powerset,
    (wt * aF X W n9) * (loss + s7 W)) =
    wt * loss +
     wt * (∑ W ∈ X.powerset,
      aF X W n9 * s7 W) := by
  calc
   (∑ W ∈ X.powerset,
    (wt * aF X W n9) * (loss + s7 W))
     = ∑ W ∈ X.powerset,
      (  aF X W n9 * (wt * loss) +
        wt * (aF X W n9 * s7 W)) := by
       refine Finset.sum_congr rfl ?_
       intro W _hW
       ring
   _ = (∑ W ∈ X.powerset, aF X W n9) * (wt * loss) +
      wt * (∑ W ∈ X.powerset,
       aF X W n9 * s7 W) := by
       rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
   _ = wt * loss +
      wt * (∑ W ∈ X.powerset,
       aF X W n9 * s7 W) := by
       rw [lA (α := α) X (p := n9) (by ring)]
       ring
 calc
  (∑ W ∈ X.powerset,
   (aW X (fun i : Fin n => ρ i.castSucc) Ws *
     aF X W (ρ (Fin.last n))) *
    (bR X p H
      (aP
       (fun i : Fin n => cutoff i.castSucc) Ws) +
     cV X
      (bU (cutoff (Fin.last n))
       (bZ H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws)) W) p))
    = wt * loss +
     wt * (∑ W ∈ X.powerset,
      aF X W n9 * s7 W) := by
      simpa [wt, loss, s7, i7, n9] using afa
  _ ≤ wt * loss + wt * B Ws := by
     have WA :
       wt * (∑ W ∈ X.powerset,
        aF X W n9 * s7 W) ≤ wt * B Ws :=
      mul_le_mul_of_nonneg_left (by
       simpa [s7, n9] using hfinal Ws hWs) al6
     linarith
  _ = aW X (fun i : Fin n => ρ i.castSucc) Ws *
     bR X p H
      (aP
       (fun i : Fin n => cutoff i.castSucc) Ws) +
    aW X (fun i : Fin n => ρ i.castSucc) Ws * B Ws := by
     simp [wt, loss, i7]
lemma jT
  (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
  {q : ℝ} {n : ℕ}
  (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
  (ajC : ρ (Fin.last n) = 1 - (1 - q) ^ L)
  (tZ : ∀ S ∈ H, S ⊆ X)
  (Oc :
   ∀ Ws ∈ bD X n,
    ∀ S ∈ bZ H
     (aP
      (fun i : Fin n => cutoff i.castSucc) Ws),
     S.card ≤ ell) :
  (∑ Ω ∈ bD X (n + 1),
   aW X ρ Ω *
    bR X q H (aP cutoff Ω)) ≤
   (∑ Ws ∈ bD X n,
    aW X (fun i : Fin n => ρ i.castSucc) Ws *
     bR X q H
      (aP
       (fun i : Fin n => cutoff i.castSucc) Ws)) +
    ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
 classical
 let i7 : Fin n → ℝ := fun i => ρ i.castSucc
 let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
 have hC0 : 0 ≤ C := by
  dsimp [C]
  positivity
 have hfinal :
   ∀ Ws ∈ bD X n,
    (∑ W ∈ X.powerset,
     aF X W (ρ (Fin.last n)) *
      cV X
       (bU (cutoff (Fin.last n))
        (bZ H
         (aP
          (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
     C := by
  intro Ws hWs
  have Dq :
    (∑ W ∈ X.powerset,
     aF X W (ρ (Fin.last n)) *
      cV X
       (bU (cutoff (Fin.last n))
        (bZ H
         (aP
          (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
     dN X
      (aV X
       (bZ H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws)))
      (ρ (Fin.last n)) * C := by
   simpa [C] using
    r8
     X
     (bZ H
      (aP
       (fun i : Fin n => cutoff i.castSucc) Ws))
     (cutoff (Fin.last n)) ell L hL hq0 hq1 ajC
     (DU X H
      (aP
       (fun i : Fin n => cutoff i.castSucc) Ws) tZ)
     (Oc Ws hWs)
  have hmu_le :
    dN X
     (aV X
      (bZ H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)))
     (ρ (Fin.last n)) ≤ 1 :=
   adK (mL (Fin.last n)) (m7 (Fin.last n))
  have ahY :
    dN X
     (aV X
      (bZ H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)))
     (ρ (Fin.last n)) * C ≤ C := by
   have := mul_le_mul_of_nonneg_right hmu_le hC0
   simpa using this
  exact Dq.trans ahY
 have hbase :=
  kR
   X H ρ cutoff (fun _Ws => C) mL m7 hfinal
 have Mh :
   (∑ Ws ∈ bD X n,
     (aW X i7 Ws *
       bR X q H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws) +
      aW X i7 Ws * C)) =
    (∑ Ws ∈ bD X n,
     aW X i7 Ws *
      bR X q H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
  calc
   (∑ Ws ∈ bD X n,
     (aW X i7 Ws *
       bR X q H
        (aP
         (fun i : Fin n => cutoff i.castSucc) Ws) +
      aW X i7 Ws * C))
     =
    (∑ Ws ∈ bD X n,
     aW X i7 Ws *
      bR X q H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)) +
     ∑ Ws ∈ bD X n,
      aW X i7 Ws * C := by
      rw [Finset.sum_add_distrib]
   _ =
    (∑ Ws ∈ bD X n,
     aW X i7 Ws *
      bR X q H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)) +
     (∑ Ws ∈ bD X n,
      aW X i7 Ws) * C := by
      rw [Finset.sum_mul]
   _ =
    (∑ Ws ∈ bD X n,
     aW X i7 Ws *
      bR X q H
       (aP
        (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
      rw [oT X i7]
      ring
 exact hbase.trans_eq Mh
lemma pW
  (H : Finset (Finset α)) {n : ℕ}
  (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
  ∀ T ∈ bZ H (aP cutoff Ws),
   T.card < cutoff (Fin.last n) := by
 intro T hT
 rw [aP, pJ] at hT
 exact (oq.mp hT).2
lemma pZ
  (H : Finset (Finset α)) {n : ℕ}
  (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
  ∀ T ∈ bZ H (aP cutoff Ws),
   T.card ≤ cutoff (Fin.last n) := by
 intro T hT
 exact Nat.le_of_lt
  (pW H cutoff Ws T hT)
def jw :
  {n : ℕ} → ℕ → (Fin n → ℕ) → ℕ
 | 0, ell, ac6 => ell
 | n + 1, al7, cutoff => cutoff (Fin.last n)
noncomputable def g8 :
  {n : ℕ} → ℕ → (Fin n → ℕ) → (Fin n → ℕ) → ℝ
 | 0, al7, ac6, _L => 0
 | n + 1, ell, cutoff, L =>
   g8 ell
    (fun i : Fin n => cutoff i.castSucc)
    (fun i : Fin n => L i.castSucc) +
    (2 : ℝ) ^
      jw ell
       (fun i : Fin n => cutoff i.castSucc) *
     (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)
lemma lP
  (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
  {q : ℝ} {n : ℕ}
  (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
  (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
  (tZ : ∀ S ∈ H, S ⊆ X)
  (Mc : ∀ S ∈ H, S.card ≤ ell) :
  (∑ Ws ∈ bD X n,
   aW X ρ Ws *
    bR X q H (aP cutoff Ws)) ≤
   g8 ell cutoff L := by
 classical
 induction n with
 | zero =>
   simp [g8, bD, aW,
    aP, bR]
 | succ n ih =>
   let i7 : Fin n → ℝ := fun i => ρ i.castSucc
   let oX : Fin n → ℕ := fun i => cutoff i.castSucc
   let adY : Fin n → ℕ := fun i => L i.castSucc
   have htail :
     (∑ Ws ∈ bD X n,
      aW X i7 Ws *
       bR X q H
        (aP oX Ws)) ≤
      g8 ell oX adY := by
    exact ih i7 oX adY
     (fun i => mL i.castSucc)
     (fun i => m7 i.castSucc)
     (fun i => hL i.castSucc)
     (fun i => hρ i.castSucc)
   have Oc :
     ∀ Ws ∈ bD X n,
      ∀ S ∈ bZ H
       (aP oX Ws),
       S.card ≤ jw ell oX := by
    cases n with
    | zero =>
      intro Ws aaZ S hS
      simpa [jw, aP,
       bZ] using Mc S hS
    | succ m =>
      intro Ws aaZ S hS
      exact
       pZ
        H oX Ws S hS
   have akS :
     (∑ Ω ∈ bD X (n + 1),
      aW X ρ Ω *
       bR X q H (aP cutoff Ω)) ≤
      (∑ Ws ∈ bD X n,
       aW X i7 Ws *
        bR X q H
         (aP oX Ws)) +
       ((2 : ℝ) ^ jw ell oX *
        (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
    exact
     jT
      X H (jw ell oX) (L (Fin.last n))
      ρ cutoff mL m7 (hL (Fin.last n)) hq0 hq1
      (hρ (Fin.last n)) tZ Oc
   have hadd := add_le_add_right htail
    ((2 : ℝ) ^ jw ell oX *
     (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
   exact akS.trans (by
    simpa [g8, oX, adY, add_comm,
     add_left_comm, add_assoc] using hadd)
lemma p7
  {H : Finset (Finset α)} {steps : List (ℕ × Finset α)} {V : Finset α}
  (h : ∃ T ∈ bZ H steps, T ⊆ V) :
  ∃ S ∈ H, S ⊆ dQ steps ∪ V := by
 induction steps generalizing H V with
 | nil =>
   simpa [bZ, dQ] using h
 | cons step steps ih =>
   rcases ih (H := dK step.1 H step.2) h with
    ⟨R, ahZ, Yf⟩
   have adS : R ∈ f6 H step.2 :=
    (oq.mp ahZ).1
   rcases q9
     (H := H) (W := step.2)
     (V := dQ steps ∪ V)
     ⟨R, adS, Yf⟩ with
    ⟨S, hS, hSsub⟩
   exact ⟨S, hS, by
    simpa [dQ, Finset.union_assoc] using hSsub⟩
lemma rH
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
  cV X H p ≤
   cV X (bZ H steps) p +
    bR X p H steps := by
 induction steps generalizing H with
 | nil =>
   simp [bZ, bR]
 | cons step steps ih =>
   let H' : Finset (Finset α) :=
    dK step.1 H step.2
   let L : Finset (Finset α) :=
    bU step.1 H step.2
   have hstep :
     cV X H p ≤ cV X H' p + cV X L p := by
    simpa [H', L] using
     wA
      X step.1 H step.2 hp0
   have hih :
     cV X H' p ≤
      cV X (bZ H' steps) p +
       bR X p H' steps :=
    ih (H := H')
   have agJ :
     cV X H' p + cV X L p ≤
      cV X (bZ H' steps) p +
       (cV X L p + bR X p H' steps) := by
    linarith
   exact hstep.trans (by
    simpa [bZ, bR, H', L,
     add_assoc, add_comm, add_left_comm] using agJ)
lemma qI
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p)
  (WE : bR X p H steps < cV X H p) :
  0 < cV X (bZ H steps) p := by
 have hle :=
  rH
   X H steps hp0
 linarith
lemma oC
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) (V : Finset α)
  {p : ℝ} (hp0 : 0 ≤ p)
  (hpos :
   0 < cV X (bZ H (steps ++ [(1, V)])) p) :
  ∃ S ∈ H, S ⊆ dQ steps ∪ V := by
 have hpos' :
   0 < cV X
    (dK 1 (bZ H steps) V) p := by
  simpa [pJ] using hpos
 rcases
   (qo
    X (bZ H steps) V hp0).mp hpos' with
  ⟨T, hT, hTV⟩
 exact p7
  (H := H) (steps := steps) (V := V) ⟨T, hT, hTV⟩
lemma qz
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) (V : Finset α)
  {p : ℝ} (hp0 : 0 ≤ p)
  (WE :
   bR X p H (steps ++ [(1, V)]) < cV X H p) :
  ∃ S ∈ H, S ⊆ dQ steps ∪ V := by
 have hpos :
   0 < cV X (bZ H (steps ++ [(1, V)])) p :=
  qI
   X H (steps ++ [(1, V)]) hp0 WE
 exact oC
  X H steps V hp0 hpos
lemma o9
  (X : Finset α) (H : Finset (Finset α))
  (steps : List (ℕ × Finset α)) (V : Finset α)
  {p : ℝ} (hp0 : 0 ≤ p)
  (Jq : dQ steps ∪ V ⊆ X)
  (WE :
   bR X p H (steps ++ [(1, V)]) < cV X H p) :
  dQ steps ∪ V ∈ aV X H := by
 rcases qz
   X H steps V hp0 WE with
  ⟨S, hS, hSsub⟩
 exact eO.mpr ⟨Jq, S, hS, hSsub⟩
lemma xW
  {X : Finset α} {H : Finset (Finset α)} {q : ℝ}
  (hq0 : 0 ≤ q) (tZ : ∀ S ∈ H, S ⊆ X)
  (e9 : ¬ fO X (aV X H) q) :
  (1 / 2 : ℝ) < cV X H q := by
 have adZ : ¬ fO X H q :=
  (Oa tZ).mp e9
 exact (IT hq0 tZ).mp adZ
lemma qu
  {Ω : Type*} [DecidableEq Ω]
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
  (s : Finset Ω) (weight : Ω → ℝ)
  (zC : Ω → List (ℕ × Finset α))
  (hp0 : 0 ≤ p)
  (qP : 0 < cV X H p)
  (ED : ∀ ω ∈ s, 0 ≤ weight ω)
  (Ry : (∑ ω ∈ s, weight ω) = 1)
  (hshape :
   ∀ ω ∈ s,
    ∃ steps V,
     zC ω = steps ++ [(1, V)] ∧
     dQ steps ∪ V ⊆ X)
  (havg :
   (∑ ω ∈ s,
    weight ω * bR X p H (zC ω)) <
     cV X H p * (1 / 2)) :
  (1 / 2 : ℝ) <
   ∑ ω ∈ s.filter
    (fun ω => dQ (zC ω) ∈ aV X H),
    weight ω := by
 refine r6
  s weight
  (fun ω => dQ (zC ω) ∈ aV X H)
  (fun ω => bR X p H (zC ω))
  ED Ry qP ?_ ?_ havg
 ·intro ω anc
  exact Nj X H (zC ω) hp0
 ·intro ω hωs hbad
  rcases hshape ω hωs with ⟨steps, V, afb, Jq⟩
  exact le_of_not_gt fun WE =>
   hbad (by
    have hmem :=
     o9
      X H steps V hp0 Jq (by
       simpa [afb] using WE)
    simpa [afb, pI] using hmem)
lemma oD
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
  {n : ℕ} (ρ : Fin n → ℝ)
  (zC : (Fin n → Finset α) → List (ℕ × Finset α))
  (hp0 : 0 ≤ p)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (qP : 0 < cV X H p)
  (hshape :
   ∀ Ws ∈ bD X n,
    ∃ steps V,
     zC Ws = steps ++ [(1, V)] ∧
     dQ steps ∪ V ⊆ X)
  (havg :
   (∑ Ws ∈ bD X n,
    aW X ρ Ws *
     bR X p H (zC Ws)) <
     cV X H p * (1 / 2)) :
  (1 / 2 : ℝ) <
   ∑ Ws ∈ (bD X n).filter
    (fun Ws => dQ (zC Ws) ∈ aV X H),
    aW X ρ Ws := by
 exact qu
  X H (bD X n) (aW X ρ) zC
  hp0 qP
  (fun Ws aaZ => Br X mL m7 Ws)
  (oT X ρ)
  hshape havg
lemma oF
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
  {n : ℕ} (ρ : Fin (n + 1) → ℝ)
  (cutoff : Fin (n + 1) → ℕ)
  (hp0 : 0 ≤ p)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (qP : 0 < cV X H p)
  (hlast : cutoff (Fin.last n) = 1)
  (havg :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X p H (aP cutoff Ws)) <
     cV X H p * (1 / 2)) :
  (1 / 2 : ℝ) <
   ∑ Ws ∈ (bD X (n + 1)).filter
    (fun Ws => cE Ws ∈ aV X H),
    aW X ρ Ws := by
 have hhalf :=
  oD
   X H ρ (fun Ws => aP cutoff Ws)
   hp0 mL m7 qP
   (fun Ws hWs => Gt hWs hlast)
   havg
 simpa [mO] using hhalf
lemma m4
  (X : Finset α) (H : Finset (Finset α)) {p θ : ℝ}
  {n : ℕ} (ρ : Fin (n + 1) → ℝ)
  (cutoff : Fin (n + 1) → ℕ)
  (hp0 : 0 ≤ p)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (qP : 0 < cV X H p)
  (hlast : cutoff (Fin.last n) = 1)
  (agK :
   (∑ Ws ∈ (bD X (n + 1)).filter
    (fun Ws => cE Ws ∈ aV X H),
    aW X ρ Ws) =
     dN X (aV X H) θ)
  (havg :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X p H (aP cutoff Ws)) <
     cV X H p * (1 / 2)) :
  (1 / 2 : ℝ) < dN X (aV X H) θ := by
 have hhalf :=
  oF
   X H ρ cutoff hp0 mL m7 qP hlast havg
 rw [← agK]
 simpa [aV] using hhalf
lemma vk
  (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
  {n : ℕ} (ρ : Fin (n + 1) → ℝ)
  (cutoff : Fin (n + 1) → ℕ)
  (hp0 : 0 ≤ p)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (qP : 0 < cV X H p)
  (hlast : cutoff (Fin.last n) = 1)
  (havg :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X p H (aP cutoff Ws)) <
     cV X H p * (1 / 2)) :
  (1 / 2 : ℝ) <
   dN X (aV X H) (dM ρ) := by
 exact m4
  X H ρ cutoff hp0 mL m7 qP hlast
  (Gh X (aV X H) ρ)
  havg
lemma m9
  (X : Finset α) (H : Finset (Finset α)) {q : ℝ}
  {n : ℕ} (ρ : Fin (n + 1) → ℝ)
  (cutoff : Fin (n + 1) → ℕ)
  (hq0 : 0 < q)
  (mL : ∀ i, 0 ≤ ρ i) (m7 : ∀ i, ρ i ≤ 1)
  (tZ : ∀ S ∈ H, S ⊆ X)
  (e9 : ¬ fO X (aV X H) q)
  (hlast : cutoff (Fin.last n) = 1)
  (havg :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X q H (aP cutoff Ws)) <
     (1 / 4 : ℝ)) :
  (1 / 2 : ℝ) <
   dN X (aV X H) (dM ρ) := by
 have akT :
   (1 / 2 : ℝ) < cV X H q :=
  xW hq0.le tZ e9
 have qP : 0 < cV X H q := by linarith
 have Mv :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X q H (aP cutoff Ws)) <
     cV X H q * (1 / 2) := by
  nlinarith
 exact vk
  X H ρ cutoff hq0.le mL m7 qP hlast Mv
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
universe u
section TK
variable {α : Type*} [DecidableEq α]
def tw (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
 0 ≤ p ∧ p ≤ 1 ∧ dN X U p ≥ 1 / 2
lemma tw.agL {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmu : dN X U p ≥ 1 / 2) :
  tw X U p :=
 ⟨hp0, hp1, hmu⟩
lemma tw.V0
  {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hU : U.Nonempty) (hpow : (1 / 2 : ℝ) ≤ p ^ ell X U) :
  tw X U p := by
 have Nk : p ^ ell X U ≤ dN X U p :=
  Da hp0 hp1 hUX g4 hU
 exact tw.agL hp0 hp1 (hpow.trans Nk)
end TK
lemma wB
  {α : Type*} [DecidableEq α]
  (bT : ℝ) (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (hEmpty : (∅ : Finset α) ∈ U) :
  dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 have hmu : dN X U (bT * q * Real.log (ell X U)) = 1 :=
  Fv hUX g4 hEmpty _
 rw [hmu]
 norm_num
lemma nQ
  {α : Type*} [DecidableEq α]
  {bT q : ℝ} {X : Finset α} {U : Finset (Finset α)}
  (ad0 : (2 / Real.log 2 : ℝ) ≤ bT)
  (hq1 : q ≤ 1)
  (ju : bT * q * Real.log (ell X U) ≤ 1) :
  q < 1 := by
 by_contra hnot
 have afc : (1 : ℝ) ≤ q := le_of_not_gt hnot
 have afd : q = 1 := le_antisymm hq1 afc
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have wC : 2 ≤ ell X U := Ew X U
 have Gv : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast wC
 have qA : Real.log 2 ≤ Real.log (ell X U) :=
  Real.log_le_log (by norm_num) Gv
 have d5 : 0 < bT := lt_of_lt_of_le (by positivity) ad0
 have ajD :
   bT * Real.log 2 ≤ bT * Real.log (ell X U) :=
  mul_le_mul_of_nonneg_left qA d5.le
 have I7 : (2 : ℝ) ≤ bT * Real.log 2 := by
  have hmul := mul_le_mul_of_nonneg_right ad0 jA.le
  have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
   field_simp [jA.ne']
  linarith
 have ahm : bT * Real.log (ell X U) ≤ 1 := by
  simpa [afd] using ju
 linarith
lemma xZ
  {α : Type*} [DecidableEq α]
  {bT q : ℝ} {X : Finset α} {U : Finset (Finset α)}
  (ad0 : (2 / Real.log 2 : ℝ) ≤ bT)
  (hq1 : q ≤ 1)
  (c9 : bT * q * Real.log (ell X U) < 1) :
  q < 1 :=
 nQ ad0 hq1 c9.le
def Kw (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  bT * q * Real.log (ell X U) < 1 →
  (∀ S ∈ U, S ⊆ X) →
  dW X U →
  (∅ : Finset α) ∉ U →
  ¬ fO X U q →
  dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2
def I8 (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  bT * q * Real.log (ell X U) < 1 →
  (bT * q * Real.log (ell X U)) ^ ell X U < 1 / 2 →
  (∀ S ∈ U, S ⊆ X) →
  dW X U →
  (∅ : Finset α) ∉ U →
  ¬ fO X U q →
  dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2
def r9 (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  bT * q * Real.log (ell X (aV X A)) < 1 →
  (bT * q * Real.log (ell X (aV X A))) ^
    ell X (aV X A) < 1 / 2 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  (∅ : Finset α) ∉ aV X A →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log (ell X (aV X A))) ≥ 1 / 2
def sw (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  A.Nonempty →
  (∅ : Finset α) ∉ A →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def oY (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  A.Nonempty →
  1 < A.card →
  (∅ : Finset α) ∉ A →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def oZ (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  A.Nonempty →
  2 < A.card →
  (∅ : Finset α) ∉ A →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def oG (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  A.Nonempty →
  2 < A.card →
  (∅ : Finset α) ∉ A →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def oH (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  A.Nonempty →
  2 < A.card →
  (∅ : Finset α) ∉ A →
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def l8 (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  (∅ : Finset α) ∉ A →
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
    max 2 (A.sup Finset.card) < 1 / 2 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def nV (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  (∅ : Finset α) ∉ A →
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  dN X (aV X A)
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2
def jU
  (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  (∅ : Finset α) ∉ A →
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
   (∀ i, 0 ≤ ρ i) ∧
   (∀ i, ρ i ≤ 1) ∧
   cutoff (Fin.last n) = 1 ∧
   dM ρ ≤
    bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X q A (aP cutoff Ws)) <
    (1 / 4 : ℝ)
def jY
  (bT : ℝ) (α : Type*) [DecidableEq α] : Prop :=
 ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
  0 < q → q < 1 →
  (∀ S ∈ A, S ⊆ X) →
  gR A →
  (∅ : Finset α) ∉ A →
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
  (∀ S ∈ A,
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     S.card < 1 / 2) →
  ¬ fO X (aV X A) q →
  ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
   (∀ i, 1 ≤ L i) ∧
   cutoff (Fin.last n) = 1 ∧
   q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
    bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
   g8 (max 2 (A.sup Finset.card)) cutoff L <
    (1 / 4 : ℝ)
def j5 (bT : ℝ) : Prop :=
 ∀ m : ℕ, 2 ≤ m →
  ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
   (∀ i, 1 ≤ L i) ∧
   cutoff (Fin.last n) = 1 ∧
   (∑ i : Fin (n + 1), (L i : ℝ)) ≤ bT * Real.log (m : ℝ) ∧
   g8 m cutoff L < (1 / 4 : ℝ)
noncomputable def iO (a n : ℕ) (i : Fin (n + 1)) : ℕ :=
 2 ^ (a + (n - i.1))
lemma RJ (a n : ℕ) :
  (fun i : Fin (n + 1) => iO a (n + 1) i.castSucc) =
   iO (a + 1) n := by
 funext i
 have hi : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
 simp [iO]
 have hsub : n + 1 - i.1 = n - i.1 + 1 := by omega
 rw [hsub]
 omega
lemma Gw (a n : ℕ) :
  iO a n (Fin.last n) = 2 ^ a := by
 simp [iO]
lemma CJ (a : ℕ) : a + 1 ≤ 2 ^ a := by
 induction a with
 | zero => norm_num
 | succ a ih =>
   rw [Nat.pow_succ]
   nlinarith
lemma uq (c b : ℕ) (hb : b ≤ 2 * c) :
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
lemma sI
  (ell a n : ℕ) (hfirst : ell ≤ 2 * 2 ^ (a + n)) :
  g8 ell (iO a n)
    (fun _ : Fin (n + 1) => 64) ≤
   ∑ j ∈ Finset.range (n + 1),
    (1 / 16 : ℝ) ^ (2 ^ (a + (n - j))) := by
 induction n generalizing a with
 | zero =>
   have hterm := uq (2 ^ a) ell hfirst
   simpa [g8, jw, iO]
    using hterm
 | succ n ih =>
   have acA : ell ≤ 2 * 2 ^ ((a + 1) + n) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
   have htail := ih (a + 1) acA
   have agM :
     jw ell (iO (a + 1) n) =
      2 ^ (a + 1) := by
    simp [jw, iO]
   have acB : 2 ^ (a + 1) ≤ 2 * 2 ^ a := by
    rw [Nat.pow_succ]
    omega
   have hterm :=
    uq (2 ^ a) (2 ^ (a + 1)) acB
   calc
    g8 ell (iO a (n + 1))
      (fun _ : Fin (n + 1 + 1) => 64)
      ≤ (∑ j ∈ Finset.range (n + 1),
         (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
        (1 / 16 : ℝ) ^ (2 ^ a) := by
       rw [g8]
       simp only [RJ]
       have ajE :
         (fun i : Fin (n + 1) =>
          (fun _ : Fin (n + 1 + 1) => 64) i.castSucc) =
          (fun _ : Fin (n + 1) => 64) := rfl
       rw [ajE]
       have agN :
         iO a (n + 1) (Fin.last (n + 1)) = 2 ^ a :=
        Gw a (n + 1)
       rw [agN, agM]
       exact add_le_add htail hterm
    _ = ∑ j ∈ Finset.range (n + 1 + 1),
       (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))) := by
       conv_rhs => rw [Finset.sum_range_succ]
       congr 1
       ·refine Finset.sum_congr rfl ?_
        intro j hj
        have al8 : j ≤ n :=
         Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : n + 1 - j = n - j + 1 := by omega
        rw [hsub]
        congr 2
        omega
       ·simp
lemma R9 (a n : ℕ) :
  (∑ j ∈ Finset.range (n + 1),
   (1 / 16 : ℝ) ^ (2 ^ (a + (n - j)))) ≤
   (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
 induction n generalizing a with
 | zero =>
   have Zn : a + 1 ≤ 2 ^ a := CJ a
   have hpow_le :
     (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) Zn
   have hden_pos : 0 < (1 - (1 / 16 : ℝ)) := by norm_num
   have hx : 0 ≤ (1 / 16 : ℝ) ^ (a + 1) := by positivity
   have ah0 :
     (1 / 16 : ℝ) ^ (a + 1) ≤
      (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
   simpa using hpow_le.trans ah0
 | succ n ih =>
   have htail := ih (a + 1)
   have Zn : a + 1 ≤ 2 ^ a := CJ a
   have agO :
     (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) Zn
   calc
    (∑ j ∈ Finset.range (n + 1 + 1),
     (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))))
      = (∑ j ∈ Finset.range (n + 1),
        (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
       (1 / 16 : ℝ) ^ (2 ^ a) := by
        conv_lhs => rw [Finset.sum_range_succ]
        congr 1
        ·refine Finset.sum_congr rfl ?_
         intro j hj
         have al8 : j ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
         have hsub : n + 1 - j = n - j + 1 := by omega
         rw [hsub]
         congr 2
         omega
        ·simp
    _ ≤ (1 / 16 : ℝ) ^ ((a + 1) + 1) /
       (1 - (1 / 16 : ℝ)) +
       (1 / 16 : ℝ) ^ (a + 1) := by
        exact add_le_add htail agO
    _ = (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
       ring_nf
lemma Fy (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1),
   (1 / 16 : ℝ) ^ (2 ^ (0 + (n - j)))) < (1 / 4 : ℝ) := by
 have h := R9 0 n
 have hconst :
   (1 / 16 : ℝ) ^ (0 + 1) / (1 - (1 / 16 : ℝ)) < (1 / 4 : ℝ) := by
  norm_num
 exact lt_of_le_of_lt h hconst
lemma EU (m : ℕ) (hm : 2 ≤ m) :
  (((Nat.log 2 m + 1 : ℕ) : ℝ)) ≤
   2 * Real.log (m : ℝ) / Real.log 2 := by
 have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have ah1 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
 have aak : Real.log 2 ≤ Real.log (m : ℝ) :=
  Real.log_le_log (by norm_num) ah1
 have Vg : (1 : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  exact (le_div_iff₀ tK).2 (by simpa using aak)
 have W0 :
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
theorem yA :
  j5 (128 / Real.log 2) := by
 intro m hm
 let n : ℕ := Nat.log 2 m
 let L : Fin (n + 1) → ℕ := fun _ => 64
 let cutoff : Fin (n + 1) → ℕ := iO 0 n
 refine ⟨n, L, cutoff, ?_, ?_, ?_, ?_⟩
 ·intro i
  norm_num [L]
 ·simpa [cutoff] using Gw 0 n
 ·have Mh :
    (∑ i : Fin (n + 1), (L i : ℝ)) =
     64 * (((n + 1 : ℕ) : ℝ)) := by
   simp [L]
   ring
  have SX := EU m hm
  have hmul :=
   mul_le_mul_of_nonneg_left SX (by norm_num : (0 : ℝ) ≤ 64)
  calc
   (∑ i : Fin (n + 1), (L i : ℝ))
     = 64 * (((n + 1 : ℕ) : ℝ)) := Mh
   _ ≤ 64 * (2 * Real.log (m : ℝ) / Real.log 2) := by
    simpa [n, mul_assoc] using hmul
   _ = (128 / Real.log 2) * Real.log (m : ℝ) := by ring
 ·have hfirst : m ≤ 2 * 2 ^ (0 + n) := by
   have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two m
   have hle : m ≤ 2 ^ (Nat.log 2 m + 1) := Nat.le_of_lt hlt
   simpa [n, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hle
  have ad1 :=
   sI m 0 n hfirst
  have agP := Fy n
  exact lt_of_le_of_lt (by simpa [cutoff, L, n] using ad1) agP
theorem Cu :
  ∃ bT : ℝ, 0 < bT ∧ (2 / Real.log 2 : ℝ) ≤ bT ∧
   j5 bT := by
 refine ⟨128 / Real.log 2, ?_, ?_, yA⟩
 ·positivity
 ·have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 128)
   tK.le
theorem m5
  {bT : ℝ} {α : Type*} [DecidableEq α]
  (Sd : j5 bT) :
  jY bT α := by
 intro X A q hq0 ane al9 amU ama akU afe
  alr akV
 let m : ℕ := max 2 (A.sup Finset.card)
 have ajF : 2 ≤ m := by
  dsimp [m]
  exact le_max_left _ _
 rcases Sd m ajF with
  ⟨n, L, cutoff, hL, hlast, hsum, Mv⟩
 have hdensity :
   q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
    bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_left hsum hq0.le
  simpa [m, mul_assoc, mul_comm, mul_left_comm] using hmul
 exact ⟨n, L, cutoff, hL, hlast, hdensity, by simpa [m] using Mv⟩
theorem nC
  {bT : ℝ} {α : Type*} [DecidableEq α]
  (Se : jY bT α) :
  jU bT α := by
 intro X A q hq0 hq1 lG mK kF qQ c9
  l9 e9
 rcases Se X A q hq0 hq1 lG mK kF qQ
   c9 l9 e9 with
  ⟨n, L, cutoff, hL, hlast, hdensity, Mv⟩
 let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
 have ZS : q ≤ 1 := hq1.le
 have VN : 0 ≤ 1 - q := by linarith
 have aaY : 1 - q ≤ 1 := by linarith
 have mL : ∀ i, 0 ≤ ρ i := by
  intro i
  have acu : (1 - q) ^ L i ≤ (1 : ℝ) :=
   pow_le_one₀ VN aaY
  dsimp [ρ]
  linarith
 have m7 : ∀ i, ρ i ≤ 1 := by
  intro i
  have MW : 0 ≤ (1 - q) ^ L i :=
   pow_nonneg VN _
  dsimp [ρ]
  linarith
 have ajG :
   dM ρ ≤
    bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  have afg :
    dM ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
   simpa [ρ] using
    Cj L hq0.le ZS
  exact afg.trans hdensity
 let m : ℕ := max 2 (A.sup Finset.card)
 have abf : ∀ S ∈ A, S.card ≤ m := by
  intro S hS
  exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
   (le_max_right _ _)
 have ah2 :
   (∑ Ws ∈ bD X (n + 1),
    aW X ρ Ws *
     bR X q A (aP cutoff Ws)) ≤
    g8 m cutoff L := by
  exact lP
   X A m ρ cutoff L mL m7 hL hq0 ZS
   (fun i => rfl) lG abf
 refine ⟨n, ρ, cutoff, mL, m7, hlast, ajG, ?_⟩
 exact ah2.trans_lt (by simpa [m] using Mv)
theorem p8
  {bT : ℝ} {α : Type*} [DecidableEq α]
  (ad2 : jU bT α) :
  nV bT α := by
 intro X A q hq0 hq1 lG mK kF qQ c9
  l9 e9
 let θ : ℝ :=
  bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
 rcases ad2 X A q hq0 hq1 lG mK kF qQ
   c9 l9 e9 with
  ⟨n, ρ, cutoff, mL, m7, hlast, abg, havg⟩
 have hhalf :
   (1 / 2 : ℝ) <
    dN X (aV X A) (dM ρ) :=
  m9
   X A ρ cutoff hq0 mL m7 lG e9 hlast havg
 have aal : 0 ≤ dM ρ :=
  DM mL m7
 have aam : θ ≤ 1 := by
  dsimp [θ]
  exact c9.le
 have hmono :
   dN X (aV X A) (dM ρ) ≤
    dN X (aV X A) θ :=
  Ac (oR X A)
   aal (by simpa [θ] using abg) aam
 exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)
theorem rT
  {α : Type*} [DecidableEq α] {bT q : ℝ}
  (d5 : 0 < bT) (hq0 : 0 < q)
  {X : Finset α} {U : Finset (Finset α)}
  (c9 : bT * q * Real.log (ell X U) < 1)
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (e9 : ¬ fO X U q)
  (hpow : (1 / 2 : ℝ) ≤
   (bT * q * Real.log (ell X U)) ^ ell X U) :
  dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have wC : 2 ≤ ell X U := Ew X U
 have Gv : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast wC
 have gC : 0 < Real.log (ell X U) :=
  lt_of_lt_of_le jA (Real.log_le_log (by norm_num) Gv)
 have hp0 : 0 ≤ bT * q * Real.log (ell X U) := by positivity
 have hp1 : bT * q * Real.log (ell X U) ≤ 1 := c9.le
 have hU : U.Nonempty := wT e9
 exact (tw.V0 hp0 hp1 hUX g4 hU hpow).2.2
theorem EW
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (d5 : 0 < bT) (gG : I8 bT α) :
  Kw bT α := by
 intro X U q hq0 hq1 c9 hUX g4 hEmpty e9
 by_cases hpow :
   (1 / 2 : ℝ) ≤ (bT * q * Real.log (ell X U)) ^ ell X U
 ·exact rT
   d5 hq0 c9 hUX g4 e9 hpow
 ·exact gG X U q hq0 hq1 c9
   (lt_of_not_ge hpow) hUX g4 hEmpty e9
theorem AO
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (gG : r9 bT α) :
  I8 bT α := by
 intro X U q hq0 hq1 c9 s8 hUX g4 hEmpty e9
 let A : Finset (Finset α) := f5 X U
 have lG : ∀ S ∈ A, S ⊆ X := by
  intro S hS
  exact hUX S (qd hS)
 have mK : gR A := by
  simpa [A] using Et X U
 have Gz : aV X A = U := by
  simpa [A] using v8 hUX g4
 have Qg :
   bT * q * Real.log (ell X (aV X A)) < 1 := by
  simpa [Gz] using c9
 have abh :
   (bT * q * Real.log (ell X (aV X A))) ^
     ell X (aV X A) < 1 / 2 := by
  simpa [Gz] using s8
 have agQ : (∅ : Finset α) ∉ aV X A := by
  simpa [Gz] using hEmpty
 have acC : ¬ fO X (aV X A) q := by
  simpa [Gz] using e9
 have hmu :=
  gG X A q hq0 hq1 Qg abh lG mK agQ acC
 simpa [Gz] using hmu
theorem uO
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (gG : sw bT α) :
  r9 bT α := by
 intro X A q hq0 hq1 c9 s8 lG mK hEmpty e9
 have kG : A.Nonempty :=
  Iv (wT e9)
 have kF : (∅ : Finset α) ∉ A :=
  Lh.mp hEmpty
 have agR :
   ell X (aV X A) = max 2 (A.sup Finset.card) :=
  Ci mK lG
 have Qg :
   bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 := by
  simpa [agR] using c9
 have abh :
   (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
     max 2 (A.sup Finset.card) < 1 / 2 := by
  simpa [agR] using s8
 have hmu :=
  gG X A q hq0 hq1 lG mK kG kF
   Qg abh e9
 simpa [agR] using hmu
theorem wZ
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : oY bT α) :
  sw bT α := by
 intro X A q hq0 hq1 lG mK kG kF
  c9 abj e9
 by_cases afh : A.card = 1
 ·rcases Finset.card_eq_one.mp afh with ⟨S, anf⟩
  subst A
  have hSX : S ⊆ X := lG S (by simp)
  have iz : g7 X {S} (aV X {S}) := by
   intro T hT
   rcases eO.mp hT with ⟨_, R, hR, hRT⟩
   have adI : R = S := by simpa using hR
   exact ⟨S, by simp, by simpa [adI] using hRT⟩
  have agS : (1 / 2 : ℝ) < q ^ S.card := by
   by_contra hnot
   have hle : q ^ S.card ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
   have tQ : fO X (aV X {S}) q :=
    Gk iz (by simpa using hle)
   exact e9 tQ
  have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have d5 : 0 < bT := lt_of_lt_of_le (by positivity) eo
  have nO : 2 ≤ max 2 S.card := le_max_left _ _
  have wD : (2 : ℝ) ≤ ((max 2 S.card : ℕ) : ℝ) := by
   exact_mod_cast nO
  have qA : Real.log 2 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
   Real.log_le_log (by norm_num) wD
  have d6 : 0 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
   le_trans jA.le qA
  have I7 : (2 : ℝ) ≤ bT * Real.log 2 := by
   have hmul := mul_le_mul_of_nonneg_right eo jA.le
   have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
    field_simp [jA.ne']
   linarith
  have Xv :
    (1 : ℝ) ≤ bT * Real.log ((max 2 S.card : ℕ) : ℝ) := by
   have hmono :
     bT * Real.log 2 ≤ bT * Real.log ((max 2 S.card : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left qA d5.le
   linarith
  have abk :
    q ≤ bT * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by
   calc
    q = q * 1 := by ring
    _ ≤ q * (bT * Real.log ((max 2 S.card : ℕ) : ℝ)) :=
     mul_le_mul_of_nonneg_left Xv hq0.le
    _ = bT * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by ring
  have hp0 : 0 ≤ bT * q * Real.log ((max 2 S.card : ℕ) : ℝ) :=
   mul_nonneg (mul_nonneg d5.le hq0.le) d6
  have abl :
    bT * q * Real.log ((max 2 S.card : ℕ) : ℝ) < 1 := by
   simpa using c9
  have hp1 : bT * q * Real.log ((max 2 S.card : ℕ) : ℝ) ≤ 1 :=
   abl.le
  have afi :
    q ^ S.card ≤
     (bT * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
   pow_le_pow_left₀ hq0.le abk S.card
  have hmu :
    (1 / 2 : ℝ) ≤
     dN X (aV X {S})
      (bT * q * Real.log ((max 2 S.card : ℕ) : ℝ)) := by
   have hstrict :
     (1 / 2 : ℝ) <
      (bT * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
    agS.trans_le afi
   have nZ :
     dN X (aV X {S})
       (bT * q * Real.log ((max 2 S.card : ℕ) : ℝ)) =
      (bT * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
    Kr X S hSX hp0 hp1
   rw [nZ]
   exact hstrict.le
  simpa using hmu
 ·have V5 : 1 < A.card := by
   have hpos : 0 < A.card := kG.card_pos
   omega
  exact gG X A q hq0 hq1 lG mK kG V5 kF
   c9 abj e9
theorem tA
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : oZ bT α) :
  oY bT α := by
 intro X A q hq0 hq1 lG mK kG V5 kF
  c9 s8 e9
 by_cases afj : A.card = 2
 ·rcases A.exists_min_image Finset.card kG with ⟨S, hSA, ajH⟩
  have iz : g7 X A (aV X A) := by
   intro T hT
   rcases eO.mp hT with ⟨_, R, hRA, hRT⟩
   exact ⟨R, hRA, hRT⟩
  have ah3 :
    (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card :=
   vF e9 iz
  have hterm : ∀ R ∈ A, q ^ R.card ≤ q ^ S.card := by
   intro R hRA
   exact pow_le_pow_of_le_one hq0.le hq1.le (ajH R hRA)
  have Ej :
    (∑ R ∈ A, q ^ R.card) ≤ ∑ R ∈ A, q ^ S.card :=
   Finset.sum_le_sum hterm
  have hconst :
    (∑ R ∈ A, q ^ S.card) = (A.card : ℝ) * q ^ S.card := by
   rw [Finset.sum_const, nsmul_eq_mul]
  have aiL : (1 / 4 : ℝ) < q ^ S.card := by
   have ajI : (1 / 2 : ℝ) < (2 : ℝ) * q ^ S.card := by
    calc
     (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card := ah3
     _ ≤ ∑ R ∈ A, q ^ S.card := Ej
     _ = (A.card : ℝ) * q ^ S.card := hconst
     _ = (2 : ℝ) * q ^ S.card := by simp [afj]
   linarith
  have Gd : S.Nonempty := by
   by_contra Iz
   have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp Iz
   exact kF (by simpa [hS_eq] using hSA)
  have akm : 0 < S.card := Gd.card_pos
  let m : ℕ := max 2 (A.sup Finset.card)
  let p : ℝ := bT * q * Real.log ((m : ℕ) : ℝ)
  have nO : 2 ≤ m := by
   dsimp [m]
   exact le_max_left _ _
  have wD : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast nO
  have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have qA : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
   Real.log_le_log (by norm_num) wD
  have d6 : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
   le_trans jA.le qA
  have d5 : 0 < bT := lt_of_lt_of_le (by positivity) eo
  have I7 : (2 : ℝ) ≤ bT * Real.log 2 := by
   have hmul := mul_le_mul_of_nonneg_right eo jA.le
   have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
    field_simp [jA.ne']
   linarith
  have Xw : (2 : ℝ) ≤ bT * Real.log ((m : ℕ) : ℝ) := by
   have hmono :
     bT * Real.log 2 ≤ bT * Real.log ((m : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left qA d5.le
   linarith
  have ad3 : 2 * q ≤ p := by
   calc
    2 * q = q * 2 := by ring
    _ ≤ q * (bT * Real.log ((m : ℕ) : ℝ)) :=
     mul_le_mul_of_nonneg_left Xw hq0.le
    _ = p := by simp [p]; ring
  have abm : 0 ≤ 2 * q := by positivity
  have ahn : (2 : ℝ) ≤ (2 : ℝ) ^ S.card := by
   cases hcard : S.card with
   | zero =>
     omega
   | succ n =>
     have Rr : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact one_le_pow₀ (by norm_num)
     calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (2 : ℝ) ^ n := by nlinarith
      _ = (2 : ℝ) ^ Nat.succ n := by rw [pow_succ]; ring
  have WM : (1 / 2 : ℝ) < (2 * q) ^ S.card := by
   rw [mul_pow]
   have ZT : 0 < q ^ S.card := pow_pos hq0 _
   have WO : (1 / 2 : ℝ) < 2 * q ^ S.card := by
    linarith
   have abo :
     2 * q ^ S.card ≤ (2 : ℝ) ^ S.card * q ^ S.card := by
    nlinarith
   exact WO.trans_le abo
  have abp : (1 / 2 : ℝ) ≤ p ^ S.card := by
   have hpow_le : (2 * q) ^ S.card ≤ p ^ S.card :=
    pow_le_pow_left₀ abm ad3 S.card
   exact (WM.trans_le hpow_le).le
  have hp0 : 0 ≤ p := by
   dsimp [p]
   exact mul_nonneg (mul_nonneg d5.le hq0.le) d6
  have hp1 : p ≤ 1 := by
   dsimp [p, m]
   exact c9.le
  have ad4 : S ∈ aV X A := DH lG hSA
  have hUX : ∀ T ∈ aV X A, T ⊆ X := by
   intro T hT
   exact (eO.mp hT).1
  have Nk :
    p ^ S.card ≤ dN X (aV X A) p :=
   m8 hp0 hp1 hUX
    (oR X A) ad4
  have hmu : (1 / 2 : ℝ) ≤ dN X (aV X A) p :=
   abp.trans Nk
  simpa [p, m] using hmu
 ·have GO : 2 < A.card := by omega
  exact gG X A q hq0 hq1 lG mK kG GO kF
   c9 s8 e9
theorem sK
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : oG bT α) :
  oZ bT α := by
 intro X A q hq0 hq1 lG mK kG GO kF
  c9 s8 e9
 let m : ℕ := max 2 (A.sup Finset.card)
 let p : ℝ := bT * q * Real.log ((m : ℕ) : ℝ)
 have nO : 2 ≤ m := by
  dsimp [m]
  exact le_max_left _ _
 have wD : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast nO
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have qA : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
  Real.log_le_log (by norm_num) wD
 have d6 : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
  le_trans jA.le qA
 have d5 : 0 < bT := lt_of_lt_of_le (by positivity) eo
 have hp0 : 0 ≤ p := by
  dsimp [p]
  exact mul_nonneg (mul_nonneg d5.le hq0.le) d6
 have hp1 : p ≤ 1 := by
  dsimp [p, m]
  exact c9.le
 by_cases afk : ∃ S ∈ A, (1 / 2 : ℝ) ≤ p ^ S.card
 ·rcases afk with ⟨S, hSA, agT⟩
  have ad4 : S ∈ aV X A := DH lG hSA
  have hUX : ∀ T ∈ aV X A, T ⊆ X := by
   intro T hT
   exact (eO.mp hT).1
  have Nk : p ^ S.card ≤ dN X (aV X A) p :=
   m8 hp0 hp1 hUX
    (oR X A) ad4
  exact agT.trans Nk
 ·have l9 : ∀ S ∈ A, p ^ S.card < 1 / 2 := by
   intro S hSA
   exact lt_of_not_ge fun hge => afk ⟨S, hSA, hge⟩
  exact gG X A q hq0 hq1 lG mK kG GO kF
   (by simpa [p, m] using c9)
   (by simpa [p, m] using s8)
   (by simpa [p, m] using l9)
   e9
theorem sO
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : Kw bT α)
  (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
  (hq0 : 0 < q) (hq1 : q ≤ 1)
  (c9 : bT * q * Real.log (ell X U) < 1)
  (hUX : ∀ S ∈ U, S ⊆ X) (g4 : dW X U)
  (e9 : ¬ fO X U q) :
  dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 by_cases hEmpty : (∅ : Finset α) ∈ U
 ·exact wB bT X U q hUX g4 hEmpty
 ·have V6 : q < 1 :=
   xZ eo hq1 c9
  exact gG X U q hq0 V6 c9 hUX g4 hEmpty e9
theorem pC
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], I8 bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 refine ⟨bT, d5, ?_⟩
 intro α _ X U q hq0 hq1 c9 hUX g4 e9
 exact sO eo
  (EW (α := α) d5 (gG (α := α)))
  X U q hq0 hq1 c9 hUX g4 e9
theorem oI
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], r9 bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact pC
  d5 eo
  (fun {α} _ => AO (gG (α := α)))
theorem oK
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], sw bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact oI
  d5 eo
  (fun {α} _ => uO
   (gG (α := α)))
theorem mo
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], oY bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact oK
  d5 eo
  (fun {α} _ => wZ
   eo (gG (α := α)))
theorem mC
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], oZ bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact mo
  d5 eo
  (fun {α} _ => tA
   eo (gG (α := α)))
theorem lU
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], oG bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact mC
  d5 eo
  (fun {α} _ => sK
   eo (gG (α := α)))
lemma w5
  {α : Type*} [DecidableEq α] {bT q : ℝ}
  {X : Finset α} {A : Finset (Finset α)}
  (d5 : 0 < bT) (hq0 : 0 < q)
  (l9 :
   ∀ S ∈ A,
    (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
      S.card < 1 / 2)
  (e9 : ¬ fO X (aV X A) q) :
  ∃ S ∈ A,
   (bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^ S.card <
    (A.card : ℝ) := by
 rcases lT
   e9 with ⟨S, hSA, afl⟩
 have kG : A.Nonempty := ⟨S, hSA⟩
 have Zo : 0 < A.card := kG.card_pos
 have Yh : 0 < (A.card : ℝ) := by exact_mod_cast Zo
 have ZT : 0 < q ^ S.card := pow_pos hq0 _
 have nO : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
 have wD : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  exact_mod_cast nO
 have d6 :
   0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
  (Real.log_pos (lt_of_lt_of_le (by norm_num) wD)).le
 let L : ℝ := bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
 have afm : 0 ≤ L := by
  dsimp [L]
  exact mul_nonneg d5.le d6
 have htarget :
   (L * q) ^ S.card < 1 / 2 := by
  have h := l9 S hSA
  simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
 have ah4 : L ^ S.card * q ^ S.card < 1 / 2 := by
  simpa [mul_pow] using htarget
 have qQ : L ^ S.card < (A.card : ℝ) := by
  by_contra hnot
  have afn : (A.card : ℝ) ≤ L ^ S.card := le_of_not_gt hnot
  have ah5 :
    (A.card : ℝ) * q ^ S.card ≤ L ^ S.card * q ^ S.card :=
   mul_le_mul_of_nonneg_right afn ZT.le
  have acD : (1 / 2 : ℝ) < (A.card : ℝ) * q ^ S.card := by
   have hden_pos : 0 < 2 * (A.card : ℝ) := by positivity
   rw [div_lt_iff₀ hden_pos] at afl
   nlinarith
  have : (1 / 2 : ℝ) < L ^ S.card * q ^ S.card :=
   acD.trans_le ah5
  exact not_lt_of_ge ah4.le this
 exact ⟨S, hSA, by simpa [L] using qQ⟩
lemma QJ
  {α : Type*} [DecidableEq α] {bT q : ℝ}
  {X : Finset α} {A : Finset (Finset α)}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT) (hq0 : 0 < q)
  (kF : (∅ : Finset α) ∉ A)
  (l9 :
   ∀ S ∈ A,
    (bT * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
      S.card < 1 / 2)
  (e9 : ¬ fO X (aV X A) q) :
  bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) := by
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have d5 : 0 < bT := lt_of_lt_of_le (by positivity) eo
 rcases w5 d5 hq0
   l9 e9 with ⟨S, hSA, aan⟩
 let L : ℝ := bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
 have nO : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
 have wD : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  exact_mod_cast nO
 have qA : Real.log 2 ≤
   Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
  Real.log_le_log (by norm_num) wD
 have alu : (2 : ℝ) ≤ L := by
  have hmul := mul_le_mul_of_nonneg_left qA d5.le
  have I7 : (2 : ℝ) ≤ bT * Real.log 2 := by
   have am3 := mul_le_mul_of_nonneg_right eo jA.le
   have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
    field_simp [jA.ne']
   linarith
  dsimp [L]
  linarith
 have afm : 0 ≤ L := by linarith
 have afo : (1 : ℝ) ≤ L := by linarith
 have Gd : S.Nonempty := by
  by_contra Iz
  have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp Iz
  exact kF (by simpa [hS_eq] using hSA)
 have afq : L ≤ L ^ S.card := by
  cases hcard : S.card with
  | zero =>
    have hbad : S.card ≠ 0 := Gd.card_pos.ne'
    exact False.elim (hbad hcard)
  | succ n =>
    have Rr : (1 : ℝ) ≤ L ^ n := one_le_pow₀ afo
    rw [pow_succ]
    nlinarith
 exact lt_of_le_of_lt afq (by simpa [L] using aan)
theorem qU
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (gG : l8 bT α) :
  oH bT α := by
 intro X A q hq0 hq1 lG mK ajJ ajK kF
  qQ c9 s8 l9 e9
 exact gG X A q hq0 hq1 lG mK kF qQ
  c9 s8 l9 e9
theorem qJ
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (gG : nV bT α) :
  l8 bT α := by
 intro X A q hq0 hq1 lG mK kF qQ c9
  abj l9 e9
 exact gG X A q hq0 hq1 lG mK kF qQ
  c9 l9 e9
theorem rV
  {α : Type*} [DecidableEq α] {bT : ℝ}
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : oH bT α) :
  oG bT α := by
 intro X A q hq0 hq1 lG mK kG GO kF
  c9 s8 l9 e9
 have qQ :
   bT * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) :=
  QJ eo hq0 kF l9 e9
 exact gG X A q hq0 hq1 lG mK kG GO kF
  qQ c9 s8 l9 e9
theorem lV
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α], oH bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact lU
  d5 eo
  (fun {α} _ => rV
   eo (gG (α := α)))
theorem k5
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α],
   l8 bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact lV
  d5 eo
  (fun {α} _ => qU
   (gG (α := α)))
theorem lQ
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (gG : ∀ {α : Type u} [DecidableEq α],
   nV bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact k5
  d5 eo
  (fun {α} _ => qJ
   (gG (α := α)))
theorem nP
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (ad2 : ∀ {α : Type u} [DecidableEq α],
   jU bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact lQ
  d5 eo
  (fun {α} _ => p8
   (ad2 (α := α)))
theorem nW
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (Se : ∀ {α : Type u} [DecidableEq α],
   jY bT α) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact nP
  d5 eo
  (fun {α} _ =>
   nC
    (Se (α := α)))
theorem lW
  {bT : ℝ} (d5 : 0 < bT)
  (eo : (2 / Real.log 2 : ℝ) ≤ bT)
  (Sd : j5 bT) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact nW
  d5 eo
  (fun {α} _ =>
   m5
    (α := α) Sd)
theorem kO
  (Sd :
   ∃ bT : ℝ, 0 < bT ∧ (2 / Real.log 2 : ℝ) ≤ bT ∧
    j5 bT) :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type u} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 rcases Sd with ⟨bT, d5, eo, Se⟩
 exact lW
  d5 eo Se
theorem BL :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type*} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 exact kO
  Cu
theorem DX :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type*} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) ≤ 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    ¬ fO X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 rcases BL with ⟨bT, d5, abq⟩
 refine ⟨bT, d5, ?_⟩
 intro α _ X U q hq0 hq1 ju hUX g4 e9
 by_cases c9 : bT * q * Real.log (ell X U) < 1
 ·exact abq X U q hq0 hq1 c9 hUX g4 e9
 ·have WQ : bT * q * Real.log (ell X U) = 1 :=
   le_antisymm ju (le_of_not_gt c9)
  have acE : U.Nonempty := wT e9
  have ah6 : dN X U (1 : ℝ) = 1 :=
   Kq hUX g4 acE
  rw [WQ, ah6]
  norm_num
theorem LD :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type*} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q ≤ 1 →
    bT * q * Real.log (ell X U) ≤ 1 →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    BZ X U q →
    dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 := by
 rcases DX with ⟨C0, ac8, V7⟩
 let bT : ℝ := max (2 * C0) (2 / Real.log 2)
 have jA : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have d5 : 0 < bT := by
  exact lt_of_lt_of_le (mul_pos (by norm_num) ac8) (le_max_left _ _)
 have RK : 2 * C0 ≤ bT := le_max_left _ _
 have Zp : 2 / Real.log 2 ≤ bT := le_max_right _ _
 refine ⟨bT, d5, ?_⟩
 intro α _ X U q hq0 hq1 ju hUX g4 WH
 have wC : 2 ≤ ell X U := Ew X U
 have Gv : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast wC
 have amb : 0 < (ell X U : ℝ) := by positivity
 have qA : Real.log 2 ≤ Real.log (ell X U) :=
  Real.log_le_log (by norm_num) Gv
 have d6 : 0 ≤ Real.log (ell X U) :=
  le_trans jA.le qA
 have Eo : 0 ≤ bT * q * Real.log (ell X U) := by positivity
 by_cases ah7 : q ≤ (1 / 2 : ℝ)
 ·let q' : ℝ := 2 * q
  have ah8 : 0 < q' := by dsimp [q']; positivity
  have Yj : q' ≤ 1 := by dsimp [q']; linarith
  have agU : q < q' := by dsimp [q']; linarith
  have V8 : ¬ fO X U q' :=
   WH q' agU Yj
  have Cv :
    C0 * q' * Real.log (ell X U) ≤ 1 := by
   have Zq : C0 * q' ≤ bT * q := by
    dsimp [q']
    nlinarith [RK, hq0.le]
   have hle :
     C0 * q' * Real.log (ell X U) ≤
      bT * q * Real.log (ell X U) := by
    exact mul_le_mul_of_nonneg_right Zq d6
   exact hle.trans ju
  have Xx :
    dN X U (C0 * q' * Real.log (ell X U)) ≥ 1 / 2 :=
   V7 X U q' ah8 Yj Cv hUX g4 V8
  have Od :
    0 ≤ C0 * q' * Real.log (ell X U) := by positivity
  have Xy :
    C0 * q' * Real.log (ell X U) ≤
     bT * q * Real.log (ell X U) := by
   have Zq : C0 * q' ≤ bT * q := by
    dsimp [q']
    nlinarith [RK, hq0.le]
   exact mul_le_mul_of_nonneg_right Zq d6
  have hmono :
    dN X U (C0 * q' * Real.log (ell X U)) ≤
     dN X U (bT * q * Real.log (ell X U)) :=
   Ac g4 Od Xy ju
  exact Xx.trans hmono
 ·have ad5 : (1 / 2 : ℝ) < q := lt_of_not_ge ah7
  have V6 : q < 1 :=
   nQ Zp hq1 ju
  have V8 : ¬ fO X U (1 : ℝ) :=
   WH 1 V6 le_rfl
  have Ol :
    C0 * 1 * Real.log (ell X U) ≤
     bT * q * Real.log (ell X U) := by
   have acF : C0 * 1 ≤ bT * q := by
    nlinarith [RK, ad5, ac8.le]
   exact mul_le_mul_of_nonneg_right acF d6
  have Cv :
    C0 * 1 * Real.log (ell X U) ≤ 1 :=
   Ol.trans ju
  have Xx :
    dN X U (C0 * 1 * Real.log (ell X U)) ≥ 1 / 2 :=
   V7 X U 1 (by norm_num) le_rfl Cv hUX g4 V8
  have Od :
    0 ≤ C0 * 1 * Real.log (ell X U) := by positivity
  have hmono :
    dN X U (C0 * 1 * Real.log (ell X U)) ≤
     dN X U (bT * q * Real.log (ell X U)) :=
   Ac g4 Od Ol ju
  exact Xx.trans hmono
theorem Oe :
  ∃ bT : ℝ, 0 < bT ∧
   ∀ {α : Type*} [DecidableEq α]
    (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
    0 < q → q ≤ 1 →
    0 ≤ p → p ≤ 1 →
    bT * q * Real.log (ell X U) ≤ p →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    BZ X U q →
    dN X U p ≥ 1 / 2 := by
 rcases LD with ⟨bT, d5, abr⟩
 refine ⟨bT, d5, ?_⟩
 intro α _ X U q p hq0 hq1 hp0 hp1 TQ hUX g4 tQ
 have GZ : (1 : ℝ) ≤ (ell X U : ℝ) := by
  exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (Ew X U))
 have d6 : 0 ≤ Real.log (ell X U) := Real.log_nonneg GZ
 have WR :
   0 ≤ bT * q * Real.log (ell X U) := by positivity
 have ju :
   bT * q * Real.log (ell X U) ≤ 1 := TQ.trans hp1
 have hAt :
   dN X U (bT * q * Real.log (ell X U)) ≥ 1 / 2 :=
  abr X U q hq0 hq1 ju hUX g4 tQ
 have hmono :
   dN X U (bT * q * Real.log (ell X U)) ≤ dN X U p :=
  Ac g4 WR TQ hp1
 exact hAt.trans hmono
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
variable {α : Type*}
section
variable [DecidableEq α]
theorem TU
  {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
  (hA : A.Nonempty) (_hk : 1 ≤ k)
  (alv : cP.jN A k)
  (Mw : cP.DG A κ)
  (hκ : 1 < κ)
  (lG : ∀ S ∈ A, S ⊆ X) :
  ¬ fO X (aV X A) (κ⁻¹) := by
 classical
 intro tQ
 rcases tQ with ⟨G, iz, hsum⟩
 have V9 : 0 < κ := by linarith
 have Yh : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
 have ah9 : ∀ S ∈ A, ∃ T ∈ G, T ⊆ S := by
  intro S hSA
  have hSup : S ∈ aV X A :=
   eO.mpr ⟨lG S hSA, S, hSA, subset_refl _⟩
  exact iz S hSup
 have aia : A ⊆ G.biUnion fun T => A.filter fun S => T ⊆ S := by
  intro S hSA
  rcases ah9 S hSA with ⟨T, Nc, hTS⟩
  exact Finset.mem_biUnion.mpr ⟨T, Nc, Finset.mem_filter.mpr ⟨hSA, hTS⟩⟩
 have abt :
   A.card ≤ ∑ T ∈ G, (A.filter fun S => T ⊆ S).card :=
  (Finset.card_le_card aia).trans Finset.card_biUnion_le
 have agV :
   (A.card : ℝ) ≤ ∑ T ∈ G, ((A.filter fun S => T ⊆ S).card : ℝ) := by
  have h := abt
  have : ((A.card : ℕ) : ℝ) ≤
    (((∑ T ∈ G, (A.filter fun S => T ⊆ S).card : ℕ) : ℝ)) := by
   exact_mod_cast h
  rw [Nat.cast_sum] at this
  exact this
 have hbound : ∀ T ∈ G,
   ((A.filter fun S => T ⊆ S).card : ℝ) ≤ (A.card : ℝ) * (κ ^ T.card)⁻¹ := by
  intro T _
  by_cases hTne : T.Nonempty
  ·have := Mw T hTne
   rw [div_eq_mul_inv] at this
   exact this
  ·have heq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
   subst heq
   have ad6 : (A.filter fun S => (∅ : Finset α) ⊆ S) = A := by
    apply Finset.filter_eq_self.mpr
    intro S _
    exact Finset.empty_subset S
   rw [ad6]
   simp
 have aho :
   (A.card : ℝ) ≤ ∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹ :=
  agV.trans (Finset.sum_le_sum hbound)
 have hkey :
   (∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹) =
    (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [← inv_pow]
 rw [hkey] at aho
 have akn : (1 : ℝ) ≤ ∑ T ∈ G, (κ⁻¹) ^ T.card := by
  have ajL : (A.card : ℝ) * 1 ≤
    (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
   simpa using aho
  exact le_of_mul_le_mul_left ajL Yh
 linarith
noncomputable def CQ (bT : ℝ) : ℝ :=
 max 10 (8 * bT)
lemma ZV (bT : ℝ) : 0 < CQ bT := by
 unfold CQ
 refine lt_of_lt_of_le ?_ (le_max_left _ _)
 norm_num
lemma abw (bT : ℝ) : (10 : ℝ) ≤ CQ bT := le_max_left _ _
lemma Xz {bT : ℝ} (d5 : 0 < bT) :
  2 * bT ≤ CQ bT := by
 unfold CQ
 refine le_trans ?_ (le_max_right _ _)
 linarith
private lemma Mz
  (bT Qj : ℝ) (d5 : 0 < bT) (ajM : 2 * bT ≤ Qj)
  {rJ κ : ℝ} {r k : ℕ}
  (hr : 2 ≤ r) (hk : 1 ≤ k)
  (Oi : 0 < rJ)
  (GZ : 1 ≤ rJ)
  (ad7 : rJ ≤ Real.exp 1 * (k : ℝ))
  (V9 : 0 < κ)
  (hκ : Qj * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
  bT * κ⁻¹ * Real.log rJ ≤ (1 : ℝ) / (2 * (r : ℝ)) := by
 have Sj : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
 have acG : (0 : ℝ) < (r : ℝ) := by linarith
 have ME : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
 have aib : 0 < Real.exp 1 * (k : ℝ) := by
  have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one ME
  positivity
 have ako : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
  have he : (1 : ℝ) < Real.exp 1 := by
   have := Real.exp_one_gt_d9; linarith
  have abx : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
   nlinarith [Real.exp_pos (1 : ℝ)]
  refine Real.log_pos ?_
  linarith
 have acH : Real.log rJ ≤ Real.log (Real.exp 1 * (k : ℝ)) :=
  Real.log_le_log Oi ad7
 have ahp : 0 ≤ Real.log rJ := Real.log_nonneg GZ
 have afr : 0 ≤ 2 * bT * (r : ℝ) := by positivity
 have agW : 2 * bT * (r : ℝ) * Real.log rJ ≤ κ := by
  have s1 : 2 * bT * (r : ℝ) * Real.log rJ ≤
    2 * bT * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
   mul_le_mul_of_nonneg_left acH afr
  have s2 : 2 * bT * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤
    Qj * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
   have amc : 0 ≤ (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
    positivity
   nlinarith
  linarith
 have Zr : (0 : ℝ) < 2 * (r : ℝ) := by linarith
 have aic : bT * κ⁻¹ * Real.log rJ =
   bT * Real.log rJ / κ := by ring
 rw [aic, div_le_div_iff₀ V9 Zr]
 have heq : bT * Real.log rJ * (2 * (r : ℝ)) =
   2 * bT * (r : ℝ) * Real.log rJ := by ring
 rw [heq, one_mul]
 exact agW
theorem w6
  (bT : ℝ) (d5 : 0 < bT)
  (TW :
   ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
    0 < q → q ≤ 1 →
    0 ≤ p → p ≤ 1 →
    bT * q * Real.log (ell X U) ≤ p →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    BZ X U q →
    dN X U p ≥ 1 / 2)
  {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
  (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
  (j7 : cP.jN A k)
  (Mw : cP.DG A κ)
  (lG : ∀ S ∈ A, S ⊆ X)
  (hκ : CQ bT * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
  dN X (aV X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
 set U := aV X A with afs
 have Sj : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
 have acG : (0 : ℝ) < (r : ℝ) := by linarith
 have ME : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
 have akp : (0 : ℝ) < (k : ℝ) := by linarith
 have alw : (2 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9; linarith
 have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
 have aib : (0 : ℝ) < Real.exp 1 * (k : ℝ) := by positivity
 have abx : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
  have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (k : ℝ) :=
   mul_le_mul_of_nonneg_left ME he_pos.le
  simpa using h1
 have Zt : (1 : ℝ) ≤ Real.log (Real.exp 1 * (k : ℝ)) := by
  have h := Real.log_le_log he_pos abx
  simpa [Real.log_exp] using h
 have acI : (10 : ℝ) ≤ CQ bT := abw bT
 have aby : 0 < CQ bT := ZV bT
 have acJ :
   (20 : ℝ) ≤ CQ bT * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
  have h1 : (10 : ℝ) * 2 ≤ CQ bT * (r : ℝ) :=
   mul_le_mul acI Sj (by norm_num) aby.le
  have h2 :
    CQ bT * (r : ℝ) * 1 ≤
     CQ bT * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
   mul_le_mul_of_nonneg_left Zt (by positivity)
  linarith
 have amd : (20 : ℝ) ≤ κ := le_trans acJ hκ
 have V9 : 0 < κ := by linarith
 have ZW : 1 < κ := by linarith
 have afu : (1 : ℝ) ≤ κ := ZW.le
 have Yk : (0 : ℝ) < κ⁻¹ := inv_pos.mpr V9
 have aao : κ⁻¹ ≤ 1 := by
  have h := inv_anti₀ (by linarith : (0 : ℝ) < 1) afu
  simpa using h
 have g4 : dW X U := oR X A
 have amf : ∀ S ∈ U, S ⊆ X := by
  intro S hS
  have hS' : S ∈ aV X A := by simpa [afs] using hS
  exact (eO.mp hS').1
 have e9 : ¬ fO X U (κ⁻¹) :=
  TU hA hk j7 Mw ZW lG
 have WH : BZ X U (κ⁻¹) :=
  OE Yk.le e9
 have abz : 0 < ell X U := ahN X U
 have Oi : (0 : ℝ) < (ell X U : ℝ) := by exact_mod_cast abz
 have GZ : (1 : ℝ) ≤ (ell X U : ℝ) := by
  have h := Ew X U
  have h1 : 1 ≤ ell X U := le_trans (by norm_num) h
  exact_mod_cast h1
 have acK : ell X U ≤ max 2 k := Xp j7 lG
 have ad8 : ((max 2 k : ℕ) : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
  rcases Nat.lt_or_ge k 2 with hk2 | h2k
  ·interval_cases k
   ·have : (max 2 1 : ℕ) = 2 := by decide
    rw [this]
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this]
    linarith
  ·have hmax : max 2 k = k := max_eq_right h2k
   rw [hmax]
   have alx : (1 : ℝ) ≤ Real.exp 1 := by linarith
   nlinarith
 have Yl : (ell X U : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
  have h1 : ((ell X U : ℕ) : ℝ) ≤ ((max 2 k : ℕ) : ℝ) := by exact_mod_cast acK
  exact h1.trans ad8
 have Ym :
   bT * κ⁻¹ * Real.log (ell X U) ≤ (1 : ℝ) / (2 * (r : ℝ)) :=
  Mz bT (CQ bT) d5
   (Xz d5)
   hr hk Oi GZ Yl V9 hκ
 have Zr : (0 : ℝ) < 2 * (r : ℝ) := by linarith
 have ajN : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)) := by positivity
 have ad9 : (1 : ℝ) / (2 * (r : ℝ)) ≤ 1 := by
  rw [div_le_one Zr]
  linarith
 have hgoal :
   dN X U ((1 : ℝ) / (2 * (r : ℝ))) ≥ 1 / 2 :=
  TW X U (κ⁻¹) ((1 : ℝ) / (2 * (r : ℝ)))
   Yk aao ajN ad9 Ym amf g4 WH
 simpa [afs] using hgoal
end
end jX
end cP
namespace cP
namespace jX
open Finset
open scoped BigOperators
section
variable {α : Type*} [DecidableEq α]
abbrev Coloring (X : Finset α) (m : ℕ) :=
 {x // x ∈ X} → Fin m
noncomputable def g6 {X : Finset α} {m : ℕ} (c : Coloring X m)
  (i : Fin m) : Finset α :=
 Finset.image Subtype.val (X.attach.filter (fun x => c x = i))
lemma rO {X : Finset α} {m : ℕ} (c : Coloring X m)
  (i : Fin m) {x : α} :
  x ∈ g6 c i ↔ ∃ hx : x ∈ X, c ⟨x, hx⟩ = i := by
 simp [g6]
lemma Qk {X : Finset α} {m : ℕ} (c : Coloring X m)
  (i : Fin m) :
  g6 c i ⊆ X := by
 intro x hx
 rcases (rO c i).1 hx with ⟨hxX, _⟩
 exact hxX
lemma Nl {X : Finset α} {m : ℕ} (c : Coloring X m)
  {i j : Fin m} (hij : i ≠ j) :
  Disjoint (g6 c i) (g6 c j) := by
 rw [Finset.disjoint_left]
 intro x hxi hxj
 rcases (rO c i).1 hxi with ⟨hxX, amg⟩
 rcases (rO c j).1 hxj with ⟨_, amh⟩
 exact hij (amg.symm.trans amh)
lemma Ja {X T : Finset α} (xO : T ⊆ X) {m : ℕ}
  (c : Coloring X m) (i : Fin m) :
  g6 c i = T ↔ ∀ x : {x // x ∈ X}, (x.1 ∈ T ↔ c x = i) := by
 constructor
 ·intro h x
  constructor
  ·intro hxT
   have abA : x.1 ∈ g6 c i := by simpa [h] using hxT
   rcases (rO c i).1 abA with ⟨hxX, ami⟩
   have hx_eq : (⟨x.1, hxX⟩ : {x // x ∈ X}) = x := by ext; rfl
   simpa [hx_eq] using ami
  ·intro hci
   have abA : x.1 ∈ g6 c i :=
    (rO c i).2 ⟨x.2, hci⟩
   simpa [h] using abA
 ·intro h
  ext a
  constructor
  ·intro ha
   rcases (rO c i).1 ha with ⟨haX, hci⟩
   exact (h ⟨a, haX⟩).2 hci
  ·intro haT
   have haX : a ∈ X := xO haT
   exact (rO c i).2 ⟨haX, (h ⟨a, haX⟩).1 haT⟩
noncomputable def U5 {X T : Finset α} (xO : T ⊆ X)
  {m : ℕ} (i : Fin m) :
  {c : Coloring X m // g6 c i = T} ≃
   ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) where
 toFun c x := by
  refine ⟨c.1 ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩, ?_⟩
  intro hc
  have hxT : x.1 ∈ T :=
   ((Ja xO c.1 i).1 c.2
    ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩).2 hc
  exact (Finset.mem_sdiff.1 x.2).2 hxT
 invFun g := by
  refine ⟨(fun x =>
   if hxT : x.1 ∈ T then i
   else (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1), ?_⟩
  rw [Ja xO]
  intro x
  constructor
  ·intro hxT
   simp [hxT]
  ·intro WI
   by_contra hxT
   have hg_ne : (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1 ≠ i :=
    (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).2
   simp [hxT] at WI
   exact hg_ne WI
 left_inv c := by
  ext x
  by_cases hxT : x.1 ∈ T
  ·have WI : c.1 x = i :=
    ((Ja xO c.1 i).1 c.2 x).1 hxT
   simp [hxT, WI]
  ·simp [hxT]
 right_inv g := by
  funext x
  apply Subtype.ext
  have hxT : x.1 ∉ T := (Finset.mem_sdiff.1 x.2).2
  simp [hxT]
lemma TY {X T : Finset α} (xO : T ⊆ X)
  {m : ℕ} (i : Fin m) :
  ((Finset.univ : Finset (Coloring X m)).filter
    (fun c => g6 c i = T)).card =
   (m - 1) ^ (X.card - T.card) := by
 classical
 have hleft :
   Fintype.card {c : Coloring X m // g6 c i = T} =
    ((Finset.univ : Finset (Coloring X m)).filter
     (fun c => g6 c i = T)).card := by
  exact Fintype.card_ofFinset _ (by
   intro c
   change c ∈ ((Finset.univ : Finset (Coloring X m)).filter
     (fun c => g6 c i = T)) ↔ g6 c i = T
   simp)
 have hcongr :
   Fintype.card {c : Coloring X m // g6 c i = T} =
    Fintype.card ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) :=
  Fintype.card_congr (U5 xO i)
 have amj : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
  have hcompl := Fintype.card_subtype_compl (fun j : Fin m => j = i)
  simp [Fintype.card_fin] at hcompl ⊢
 have hdom : Fintype.card {x // x ∈ X \ T} = X.card - T.card := by
  calc
   Fintype.card {x // x ∈ X \ T} = (X \ T).card := by
     exact Fintype.card_ofFinset _ (by
      intro x
      change x ∈ X \ T ↔ x ∈ X \ T
      rfl)
   _ = X.card - T.card := Finset.card_sdiff_of_subset xO
 rw [← hleft, hcongr, Fintype.card_fun, amj, hdom]
lemma Uw (X : Finset α) (m : ℕ) :
  Fintype.card (Coloring X m) = m ^ X.card := by
 rw [Fintype.card_fun, Fintype.card_fin]
 congr
 exact Fintype.card_coe X
omit [DecidableEq α] in
lemma Kz {X T : Finset α} (xO : T ⊆ X)
  {m : ℕ} (hm : 0 < m) :
  ((m : ℝ) ^ X.card) *
    aF X T ((1 : ℝ) / m) =
   ((m - 1 : ℕ) : ℝ) ^ (X.card - T.card) := by
 have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
 have O4 : T.card ≤ X.card := Finset.card_le_card xO
 have hsplit : X.card = T.card + (X.card - T.card) :=
  (Nat.add_sub_of_le O4).symm
 have hone :
   (1 : ℝ) - (1 : ℝ) / m = ((m - 1 : ℕ) : ℝ) / m := by
  have hm1 : 1 ≤ m := hm
  rw [Nat.cast_sub hm1]
  field_simp [hmR]
  ring
 unfold aF
 rw [hone, hsplit, Nat.add_sub_cancel_left, pow_add]
 rw [div_pow, div_pow]
 field_simp [hmR]
 ring
noncomputable def dS {X : Finset α} {m : ℕ}
  (A : Finset (Finset α)) (c : Coloring X m) : Finset (Fin m) :=
 Finset.univ.filter fun i => ∃ S ∈ A, S ⊆ g6 c i
lemma sP {X : Finset α} {m : ℕ}
  {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
  i ∈ dS A c ↔ ∃ S ∈ A, S ⊆ g6 c i := by
 simp [dS]
lemma kS {X : Finset α} {m : ℕ}
  {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
  i ∈ dS A c ↔ g6 c i ∈ aV X A := by
 rw [sP, eO]
 exact ⟨fun h => ⟨Qk c i, h⟩, fun h => h.2⟩
lemma OH (X : Finset α) (A : Finset (Finset α))
  {m : ℕ} (i : Fin m) :
  ((Finset.univ : Finset (Coloring X m)).filter
    (fun c => i ∈ dS A c)).card =
   ∑ T ∈ X.powerset.filter (fun T => T ∈ aV X A),
    (m - 1) ^ (X.card - T.card) := by
 classical
 let s : Finset (Coloring X m) :=
  (Finset.univ : Finset (Coloring X m)).filter
   (fun c => i ∈ dS A c)
 let t : Finset (Finset α) :=
  X.powerset.filter (fun T => T ∈ aV X A)
 have hmaps : Set.MapsTo (fun c : Coloring X m => g6 c i) (↑s) (↑t) := by
  intro c hc
  have hsucc : i ∈ dS A c := by
   simpa [s] using hc
  exact Finset.mem_filter.2
   ⟨Finset.mem_powerset.2 (Qk c i),
    (kS).1 hsucc⟩
 calc
  ((Finset.univ : Finset (Coloring X m)).filter
    (fun c => i ∈ dS A c)).card
    = s.card := rfl
  _ = ∑ T ∈ t, {c ∈ s | g6 c i = T}.card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  _ = ∑ T ∈ t, (m - 1) ^ (X.card - T.card) := by
    apply Finset.sum_congr rfl
    intro T hT
    have xO : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
    have hTU : T ∈ aV X A := (Finset.mem_filter.1 hT).2
    have Wa :
      {c ∈ s | g6 c i = T} =
       (Finset.univ : Finset (Coloring X m)).filter
        (fun c => g6 c i = T) := by
     ext c
     constructor
     ·intro hc
      exact Finset.mem_filter.2 ⟨Finset.mem_univ c, (Finset.mem_filter.1 hc).2⟩
     ·intro hc
      have hct : g6 c i = T := (Finset.mem_filter.1 hc).2
      have hsucc : i ∈ dS A c := by
       rw [kS, hct]
       exact hTU
      exact Finset.mem_filter.2
       ⟨by simpa [s] using hsucc, hct⟩
    rw [Wa, TY xO i]
lemma KD (X : Finset α) (A : Finset (Finset α))
  {m : ℕ} (hm : 0 < m) (i : Fin m) :
  (((Finset.univ : Finset (Coloring X m)).filter
    (fun c => i ∈ dS A c)).card : ℝ) =
   (Fintype.card (Coloring X m) : ℝ) *
    dN X (aV X A) ((1 : ℝ) / m) := by
 classical
 rw [OH X A i, Uw]
 unfold dN
 rw [Nat.cast_sum]
 calc
  (∑ T ∈ X.powerset.filter (fun T => T ∈ aV X A),
    (((m - 1) ^ (X.card - T.card) : ℕ) : ℝ))
    = ∑ T ∈ X.powerset.filter (fun T => T ∈ aV X A),
      ((m : ℝ) ^ X.card) *
       aF X T ((1 : ℝ) / m) := by
      apply Finset.sum_congr rfl
      intro T hT
      have xO : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
      simpa [Nat.cast_pow] using (Kz xO hm).symm
  _ = (m : ℝ) ^ X.card *
     (∑ T ∈ X.powerset.filter (fun T => T ∈ aV X A),
      aF X T ((1 : ℝ) / m)) := by
      rw [Finset.mul_sum]
  _ = ↑(m ^ X.card) *
     (∑ T ∈ X.powerset.filter (fun T => T ∈ aV X A),
      aF X T ((1 : ℝ) / m)) := by
      norm_num
  _ = ↑(m ^ X.card) * dN X (aV X A) ((1 : ℝ) / m) := rfl
lemma OI (X : Finset α) (A : Finset (Finset α)) (m : ℕ) :
  (∑ c : Coloring X m, (dS A c).card) =
   ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
    (fun c => i ∈ dS A c)).card := by
 calc
  (∑ c : Coloring X m, (dS A c).card)
    = ∑ c : Coloring X m, ∑ i : Fin m,
      if i ∈ dS A c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.card_filter]
      simp [dS]
  _ = ∑ i : Fin m, ∑ c : Coloring X m,
      if i ∈ dS A c then 1 else 0 := by
      rw [Finset.sum_comm]
  _ = ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
    (fun c => i ∈ dS A c)).card := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.card_filter]
theorem AY
  (X : Finset α) (A : Finset (Finset α)) (r : ℕ) (hr : 2 ≤ r)
  (hmu : dN X (aV X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2) :
  ∃ c : Coloring X (2 * r), r ≤ (dS A c).card := by
 classical
 let m := 2 * r
 have hm : 0 < m := by dsimp [m]; omega
 let C : ℕ := Fintype.card (Coloring X m)
 have afv : 0 < C := by
  dsimp [C]
  rw [Uw]
  exact Nat.pow_pos (a := m) (n := X.card) hm
 have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast afv
 have Mh :
   ((∑ c : Coloring X m, (dS A c).card : ℕ) : ℝ) =
    (m : ℝ) * (C : ℝ) * dN X (aV X A) ((1 : ℝ) / m) := by
  rw [OI X A m]
  rw [Nat.cast_sum]
  calc
   (∑ i : Fin m,
     (((Finset.univ : Finset (Coloring X m)).filter
      (fun c => i ∈ dS A c)).card : ℝ))
     = ∑ _i : Fin m,
       (C : ℝ) * dN X (aV X A) ((1 : ℝ) / m) := by
       apply Finset.sum_congr rfl
       intro i _
       dsimp [C]
       exact KD X A hm i
   _ = (m : ℝ) * (C : ℝ) * dN X (aV X A) ((1 : ℝ) / m) := by
       simp [Fintype.card_fin, mul_assoc]
 have akW :
   (r : ℝ) * (C : ℝ) ≤
    ((∑ c : Coloring X m, (dS A c).card : ℕ) : ℝ) := by
  rw [Mh]
  have hm_eq : (m : ℝ) = 2 * (r : ℝ) := by simp [m]
  have amk :
    (1 / 2 : ℝ) ≤ dN X (aV X A) ((1 : ℝ) / m) := by
   simpa [m] using hmu
  have hmul :
    (C : ℝ) * (1 / 2 : ℝ) ≤
     (C : ℝ) * dN X (aV X A) ((1 : ℝ) / m) :=
   mul_le_mul_of_nonneg_left amk hCpos.le
  calc
   (r : ℝ) * (C : ℝ) =
     (m : ℝ) * ((C : ℝ) * (1 / 2 : ℝ)) := by
      rw [hm_eq]
      ring
   _ ≤ (m : ℝ) *
     ((C : ℝ) * dN X (aV X A) ((1 : ℝ) / m)) := by
      exact mul_le_mul_of_nonneg_left hmul (by positivity)
   _ = (m : ℝ) * (C : ℝ) *
     dN X (aV X A) ((1 : ℝ) / m) := by
      ring
 by_contra hnone
 have agX : ∀ c : Coloring X m, (dS A c).card ≤ r - 1 := by
  intro c
  have hnot : ¬ r ≤ (dS A c).card := by
   intro hc
   exact hnone ⟨c, hc⟩
  omega
 have acL :
   (∑ c : Coloring X m, (dS A c).card : ℕ) ≤
    ∑ _c : Coloring X m, (r - 1) := by
  exact Finset.sum_le_sum (fun c _ => agX c)
 have Ej :
   ((∑ c : Coloring X m, (dS A c).card : ℕ) : ℝ) ≤
    (C : ℝ) * (r - 1 : ℕ) := by
  calc
   ((∑ c : Coloring X m, (dS A c).card : ℕ) : ℝ)
     ≤ ((∑ _c : Coloring X m, (r - 1) : ℕ) : ℝ) := by
      exact_mod_cast acL
   _ = (C : ℝ) * (r - 1 : ℕ) := by
      simp [C]
 have hlt : (C : ℝ) * (r - 1 : ℕ) < (r : ℝ) * (C : ℝ) := by
  have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
   rw [Nat.cast_sub (by omega : 1 ≤ r)]
   norm_num
  rw [hsub]
  nlinarith
 nlinarith
noncomputable def uW {X : Finset α} {m : ℕ}
  (A : Finset (Finset α)) (c : Coloring X m) (i : Fin m) : Finset α :=
 if h : i ∈ dS A c then
  Classical.choose ((sP).1 h)
 else
  ∅
lemma T8 {X : Finset α} {m : ℕ}
  {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
  (hi : i ∈ dS A c) :
  uW A c i ∈ A := by
 unfold uW
 rw [dif_pos hi]
 exact (Classical.choose_spec ((sP).1 hi)).1
lemma G7 {X : Finset α} {m : ℕ}
  {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
  (hi : i ∈ dS A c) :
  uW A c i ⊆ g6 c i := by
 unfold uW
 rw [dif_pos hi]
 exact (Classical.choose_spec ((sP).1 hi)).2
lemma Oj
  {A : Finset (Finset α)} {S : Finset α} {k : ℕ}
  (hk : 1 ≤ k) (j7 : cP.jN A k) (hS : S ∈ A) :
  S.Nonempty := by
 have hcard : S.card = k := j7 S hS
 exact Finset.card_pos.1 (by omega)
theorem zD {X : Finset α} {m r k : ℕ}
  {A : Finset (Finset α)} (c : Coloring X m)
  (hk : 1 ≤ k) (j7 : cP.jN A k)
  (agY : r ≤ (dS A c).card) :
  ∃ B : Finset (Finset α),
   B ⊆ A ∧ B.card = r ∧ cP.p9 B := by
 classical
 rcases Finset.exists_subset_card_eq agY with ⟨I, Yn, hI_card⟩
 let pick : Fin m → Finset α := uW A c
 let B : Finset (Finset α) := I.image pick
 have Z1 : ∀ i ∈ I, pick i ∈ A := by
  intro i hi
  exact T8 (Yn hi)
 have KI : ∀ i ∈ I, pick i ⊆ g6 c i := by
  intro i hi
  exact G7 (Yn hi)
 have afw : Set.InjOn pick I := by
  intro i hi j hj agZ
  by_contra hij
  have hnonempty : (pick i).Nonempty :=
   Oj hk j7 (Z1 i hi)
  rcases hnonempty with ⟨x, hx⟩
  have hxi : x ∈ g6 c i := KI i hi hx
  have hxj : x ∈ g6 c j := by
   have hx' : x ∈ pick j := by simpa [agZ] using hx
   exact KI j hj hx'
  exact (Finset.disjoint_left.1 (Nl c hij) hxi) hxj
 refine ⟨B, ?_, ?_, ?_⟩
 ·intro S hS
  rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
  exact Z1 i hi
 ·calc
   B.card = I.card := Finset.card_image_of_injOn afw
   _ = r := hI_card
 ·intro S hS T hT hST
  rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.1 hT with ⟨j, hj, rfl⟩
  have hij : i ≠ j := by
   intro hij
   exact hST (by simp [hij])
  exact (Disjoint.mono (KI i hi) (KI j hj)
   (Nl c hij))
end
theorem Dh :
  ∀ {α : Type*} [DecidableEq α]
   (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
   A.Nonempty →
   2 ≤ r →
   1 ≤ k →
   cP.jN A k →
   (∀ S ∈ A, S ⊆ X) →
   dN X (aV X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
   ∃ B : Finset (Finset α),
    B ⊆ A ∧ B.card = r ∧ cP.p9 B := by
 intro α _ X A r k _hA hr hk j7 al9 hmu
 rcases AY X A r hr hmu with ⟨c, hc⟩
 exact zD c hk j7 hc
section
variable {α : Type*} [DecidableEq α]
theorem Nm :
  ∃ Qj : ℝ, 0 < Qj ∧
   ∀ {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
    A.Nonempty →
    2 ≤ r →
    1 ≤ k →
    cP.jN A k →
    cP.DG A κ →
    Qj * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
    ∃ B : Finset (Finset α),
     B ⊆ A ∧ B.card = r ∧ cP.p9 B := by
 rcases Oe with ⟨bT, d5, TW⟩
 refine ⟨CQ bT, ZV bT, ?_⟩
 intro α _ A r k κ hA hr hk j7 Mw hκ
 let X : Finset α := A.biUnion id
 have lG : ∀ S ∈ A, S ⊆ X := by
  intro S hSA x hxS
  exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
 have acM :
   ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
    0 < q → q ≤ 1 →
    0 ≤ p → p ≤ 1 →
    bT * q * Real.log (ell X U) ≤ p →
    (∀ S ∈ U, S ⊆ X) →
    dW X U →
    BZ X U q →
    dN X U p ≥ 1 / 2 := by
  intro X U q p hq0 hq1 hp0 hp1 TQ hUX g4 tQ
  exact TW X U q p hq0 hq1 hp0 hp1 TQ hUX g4 tQ
 have hmu :
   dN X (aV X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
  w6
   bT d5 acM hA hr hk j7 Mw lG hκ
 exact Dh X A r k hA hr hk j7 lG hmu
end
end jX
end cP
namespace cP
open Finset
open scoped BigOperators
universe u
theorem CX :
 ∃ Qj : ℝ, 0 < Qj ∧
  ∀ {α : Type*} [DecidableEq α]
   (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
   A.Nonempty →
   2 ≤ r →
   1 ≤ k →
   jN A k →
   DG A κ →
   Qj * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
   ∃ B : Finset (Finset α),
    B ⊆ A ∧ B.card = r ∧ p9 B :=
 cP.jX.Nm
theorem w7 :
  ∃ C0 : ℝ, 0 < C0 ∧
   ∀ {α : Type u} [DecidableEq α]
    (A : Finset (Finset α)) (k K : ℕ),
    A.Nonempty →
    1 ≤ k → k ≤ K →
    jN A k →
    (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
    ∃ C : Finset α,
     C.Nonempty ∧
     ((A.filter fun S => C ⊆ S).card : ℝ) >
      (A.card : ℝ) /
       (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := by
 classical
 let Qj : ℝ := Classical.choose (CX.{u})
 have hspec := Classical.choose_spec (CX.{u})
 have aby : 0 < Qj := hspec.1
 refine ⟨Qj * 2, by positivity, ?_⟩
 intro α _ A k K hA hk_pos hkK j7 T9
 let κ : ℝ := (Qj * 2) * Real.log (Real.exp 1 * (K : ℝ))
 by_contra aie
 have Mw : DG A κ := by
  intro T hT
  exact le_of_not_gt (by
   intro hgt
   exact aie ⟨T, hT, hgt⟩)
 have hκ : Qj * (2 : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ := by
  have XB : 0 < Real.exp 1 * (k : ℝ) := by positivity
  have Zu : Real.exp 1 * (k : ℝ) ≤ Real.exp 1 * (K : ℝ) := by
   gcongr
  have R5 : Real.log (Real.exp 1 * (k : ℝ)) ≤
    Real.log (Real.exp 1 * (K : ℝ)) :=
   Real.log_le_log XB Zu
  have Ql : 0 ≤ Qj * 2 := by positivity
  exact mul_le_mul_of_nonneg_left R5 Ql
 rcases hspec.2 (A := A) (r := 2) (k := k) (κ := κ)
   hA (by norm_num) hk_pos j7 Mw hκ with
  ⟨B, hBA, amV, ajO⟩
 have aml : 1 < B.card := by omega
 rcases Finset.one_lt_card.mp aml with ⟨S, hS, T, hT, hST⟩
 exact T9 S (hBA hS) T (hBA hT) hST (ajO S hS T hT hST)
end cP
namespace cP
open Filter Finset
open scoped BigOperators
noncomputable def gd (N : ℕ) : ℝ :=
 Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))
lemma j9
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
private lemma eD (n : ℕ) :
  aD n = n.primeFactors := by
 unfold aD
 rw [Nat.support_factorization]
private lemma jF (n : ℕ) :
  rad n = ∏ p ∈ n.primeFactors, p := by
 unfold rad
 rw [eD]
private lemma LQ (n : ℕ) : Squarefree (rad n) := by
 rw [jF]
 classical
 have tD : (∏ p ∈ n.primeFactors, p) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
   (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
 refine (Nat.squarefree_iff_factorization_le_one tD).2 ?_
 intro q
 by_cases hq : q ∈ n.primeFactors
 ·have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  rw [Nat.factorization_prod]
  ·rw [Finsupp.finset_sum_apply]
   calc
    ∑ x ∈ n.primeFactors, x.factorization q
      = q.factorization q := by
        refine Finset.sum_eq_single q ?_ ?_
        ·intro x hx hxq
         have LV : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
         rw [← pow_one x, LV.factorization_pow]
         simp [hxq]
        ·intro hnot
         exact (hnot hq).elim
    _ = 1 := by
        rw [← pow_one q, hqprime.factorization_pow]
        simp
    _ ≤ 1 := le_rfl
  ·intro x hx
   exact (Nat.prime_of_mem_primeFactors hx).ne_zero
 ·rw [Nat.factorization_prod]
  ·rw [Finsupp.finset_sum_apply]
   calc
    ∑ x ∈ n.primeFactors, x.factorization q = 0 := by
     refine Finset.sum_eq_zero ?_
     intro x hx
     have LV : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
     rw [← pow_one x, LV.factorization_pow]
     have hxq : x ≠ q := by
      intro h
      exact hq (h ▸ hx)
     simp [hxq]
    _ ≤ 1 := by norm_num
  ·intro x hx
   exact (Nat.prime_of_mem_primeFactors hx).ne_zero
private lemma O2 (n : ℕ) : rad n ∣ n := by
 rw [jF]
 exact Nat.prod_primeFactors_dvd n
private lemma Ih (n : ℕ) :
  aD (rad n) = aD n := by
 calc
  aD (rad n) = (rad n).primeFactors := eD _
  _ = (∏ p ∈ n.primeFactors, p).primeFactors := by rw [jF]
  _ = n.primeFactors := by
   exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
  _ = aD n := (eD n).symm
private lemma Vc (n : ℕ) : omega (rad n) = omega n := by
 unfold omega
 rw [Ih]
lemma k7
  (z : ℝ) (hz : 0 ≤ z) {n : ℕ} (hn : n ≠ 0) :
  z ^ omega n ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
 classical
 have hmem : rad n ∈ n.divisors.filter Squarefree := by
  rw [Finset.mem_filter]
  exact ⟨Nat.mem_divisors.mpr ⟨O2 n, hn⟩, LQ n⟩
 have hnonneg :
   ∀ d ∈ n.divisors.filter Squarefree, 0 ≤ z ^ omega d := by
  intro d hd
  exact pow_nonneg hz _
 have nZ :
   z ^ omega (rad n) ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d :=
  Finset.single_le_sum hnonneg hmem
 simpa [Vc] using nZ
lemma nI (y d : ℕ) (hd : 0 < d) :
  ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
 classical
 calc
  ((Finset.Icc 1 y).filter fun n => d ∣ n).card
    ≤ (Finset.Icc 1 (y / d)).card := by
     refine Finset.card_le_card_of_injOn
      (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
      (t := Finset.Icc 1 (y / d))
      (fun n : ℕ => n / d) ?_ ?_
     ·intro n hn
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
     ·intro a ha b hb hab
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
lemma jP
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
     exact k7 z hz
      (by
       have hnIcc := Finset.mem_Icc.mp hn
       exact Nat.ne_of_gt hnIcc.1)
  _ ≤ ∑ n ∈ Finset.Icc 1 y,
      ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ d ∣ n),
       z ^ omega d := by
     refine Finset.sum_le_sum ?_
     intro n hn
     refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
     ·intro d hd
      rw [Finset.mem_filter] at hd ⊢
      have XP : d ∈ n.divisors := hd.1
      have af0 : Squarefree d := hd.2
      have hnIcc := Finset.mem_Icc.mp hn
      have Ec : 0 < d := Nat.pos_of_mem_divisors XP
      have XQ : d ∣ n := (Nat.mem_divisors.mp XP).1
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
      have aaB : d ≤ y := (Nat.le_of_dvd hnpos XQ).trans hnIcc.2
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt Ec, aaB⟩, af0, XQ⟩
     ·intro d hd QX
      exact pow_nonneg hz _
  _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
     (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
     simp_rw [Finset.sum_filter]
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro d hd
     by_cases hsq : Squarefree d
     ·calc
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
     ·simp [hsq]
lemma jW
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
     jP y z hz
  _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
      ((y : ℝ) / (d : ℝ)) * z ^ omega d := by
     refine Finset.sum_le_sum ?_
     intro d hd
     rw [Finset.mem_filter] at hd
     have nJ := Finset.mem_Icc.mp hd.1
     have Ec : 0 < d := lt_of_lt_of_le Nat.zero_lt_one nJ.1
     have vY :
       ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d :=
      nI y d Ec
     have qC :
       (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) ≤
        (y : ℝ) / (d : ℝ) := by
      exact (Nat.cast_le.mpr vY).trans Nat.cast_div_le
     exact mul_le_mul_of_nonneg_right qC (pow_nonneg hz _)
  _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
      (y : ℝ) * (z ^ omega d / (d : ℝ)) := by
     apply Finset.sum_congr rfl
     intro d hd
     rw [Finset.mem_filter] at hd
     have nJ := Finset.mem_Icc.mp hd.1
     have SM : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one nJ.1))
     field_simp [SM]
  _ = (y : ℝ) *
     ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
     rw [Finset.mul_sum]
lemma jL
  (z : ℝ) {d : ℕ} (hsq : Squarefree d) :
  z ^ omega d / (d : ℝ) =
   ∏ p ∈ aD d, z / (p : ℝ) := by
 classical
 have Vd : ∏ p ∈ aD d, p = d := by
  rw [eD]
  exact Nat.prod_primeFactors_of_squarefree hsq
 have SN : (d : ℝ) = ∏ p ∈ aD d, (p : ℝ) := by
  calc
   (d : ℝ) = ((∏ p ∈ aD d, p : ℕ) : ℝ) := by
    exact_mod_cast Vd.symm
   _ = ∏ p ∈ aD d, (p : ℝ) := by
    norm_num
 have hpow : z ^ omega d = ∏ p ∈ aD d, z := by
  simp [omega, Finset.prod_const]
 calc
  z ^ omega d / (d : ℝ)
    = (∏ p ∈ aD d, z) / (∏ p ∈ aD d, (p : ℝ)) := by
     rw [hpow, SN]
  _ = ∏ p ∈ aD d, z / (p : ℝ) := by
     rw [Finset.prod_div_distrib]
private lemma k8
  {d y : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
  aD d ⊆ (Finset.Icc 1 y).filter Nat.Prime := by
 intro p hp
 rw [Finset.mem_filter]
 have jM : Nat.Prime p := f7 hp
 have adh : p ∈ d.primeFactors := by
  simpa [eD] using hp
 have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors adh
 have YP : p ≤ d :=
  Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hd1) hpdvd
 exact ⟨Finset.mem_Icc.mpr ⟨jM.one_le, YP.trans hdy⟩, jM⟩
lemma kV
  (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
  (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ)) ≤
   ((Finset.Icc 1 y).filter Nat.Prime).prod
    (fun p => (1 : ℝ) + z / (p : ℝ)) := by
 classical
 let S : Finset ℕ := (Finset.Icc 1 y).filter Squarefree
 let P : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
 let term : Finset ℕ → ℝ := fun T => (∏ p ∈ T, z / (p : ℝ))
 have hinj :
   ∀ d ∈ S, ∀ e ∈ S, aD d = aD e → d = e := by
  intro d hd e he hsupport
  simp [S] at hd he
  have hdprod : ∏ p ∈ aD d, p = d := by
   rw [eD]
   exact Nat.prod_primeFactors_of_squarefree hd.2
  have aaC : ∏ p ∈ aD e, p = e := by
   rw [eD]
   exact Nat.prod_primeFactors_of_squarefree he.2
  calc
   d = ∏ p ∈ aD d, p := hdprod.symm
   _ = ∏ p ∈ aD e, p := by rw [hsupport]
   _ = e := aaC
 have Bj : S.image aD ⊆ P.powerset := by
  intro T hT
  rw [Finset.mem_powerset]
  rcases Finset.mem_image.mp hT with ⟨d, hdS, rfl⟩
  simp [S] at hdS
  have nJ := hdS.1
  exact k8 nJ.1 nJ.2
 have tJ :
   ∀ T ∈ P.powerset, 0 ≤ term T := by
  intro T hT
  rw [Finset.mem_powerset] at hT
  refine Finset.prod_nonneg ?_
  intro p hpT
  have hpP : p ∈ P := hT hpT
  simp [P] at hpP
  have jM : Nat.Prime p := hpP.2
  exact div_nonneg hz (by exact_mod_cast jM.pos.le)
 calc
  (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ))
    = ∑ d ∈ S, term (aD d) := by
     apply Finset.sum_congr
     ·simp [S]
     ·intro d hd
      simp [S] at hd
      exact jL z hd.2
  _ = ∑ T ∈ S.image aD, term T := by
     rw [Finset.sum_image]
     intro d hd e he hsupport
     exact hinj d hd e he hsupport
  _ ≤ ∑ T ∈ P.powerset, term T := by
     exact Finset.sum_le_sum_of_subset_of_nonneg Bj
      (by
       intro T hTP QX
       exact tJ T hTP)
  _ = P.prod (fun p => (1 : ℝ) + z / (p : ℝ)) := by
     rw [Finset.prod_one_add]
  _ = ((Finset.Icc 1 y).filter Nat.Prime).prod
     (fun p => (1 : ℝ) + z / (p : ℝ)) := by
     rfl
lemma lN
  (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
  (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
   (y : ℝ) *
    ((Finset.Icc 1 y).filter Nat.Prime).prod
     (fun p => (1 : ℝ) + z / (p : ℝ)) := by
 exact (jW y z hz).trans
  (mul_le_mul_of_nonneg_left
   (kV y z hz)
   (by positivity))
lemma j3 :
  ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
   (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
 refine ⟨Real.log 4 + 1, ?_, ?_⟩
 ·have aeD : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith
 ·have hreal :
    ∀ᶠ x : ℝ in atTop,
     (Nat.primeCounting (Nat.floor x) : ℝ) ≤
      (Real.log 4 + 1) * x / Real.log x :=
   Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with n hn
  simpa using hn
lemma k9 {m : ℕ} (hm : 1 ≤ m) :
  (1 : ℝ) / (m + 1 : ℕ) ≤
   Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
 have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
 have Ij : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
 have h :=
  Real.one_sub_inv_le_log_of_pos
   (div_pos Ij hmpos)
 rw [Real.log_div Ij.ne' hmpos.ne'] at h
 have hleft :
   1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  field_simp [hmpos.ne', Ij.ne']
  norm_num
 calc
  (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
    = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
  _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h
lemma oA (m : ℕ) :
  (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
   1 + Real.log (m : ℝ) := by
 induction m with
 | zero =>
   simp
 | succ m ih =>
   by_cases hm0 : m = 0
   ·subst m
    simp
   ·have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
    have Xb : m + 1 ∉ Finset.Icc 1 m := by
     simp
    have hIcc :
      Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
     ext k
     simp
     omega
    have hterm := k9 (m := m) hm
    calc
     (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
       = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
         (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          rw [hIcc, Finset.sum_insert Xb]
          ring
     _ ≤ (1 + Real.log (m : ℝ)) +
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
         simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
     _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
         linarith
     _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
         rfl
lemma kL (n : ℕ) :
  ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
 have hset :
   (Finset.Icc 1 n).filter Nat.Prime =
    (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  constructor
  ·intro hp
   rw [Finset.mem_filter] at hp ⊢
   have adi := Finset.mem_Icc.mp hp.1
   exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le adi.2), hp.2⟩
  ·intro hp
   rw [Finset.mem_filter] at hp ⊢
   exact ⟨Finset.mem_Icc.mpr
    ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
 calc
  ((Finset.Icc 1 n).filter Nat.Prime).card
    = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
  _ = Nat.count Nat.Prime (n + 1) := by
     exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
  _ = Nat.primeCounting n := rfl
lemma lO (k : ℕ) :
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ)) ≤
   (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
 classical
 let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
 have n7 : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
 have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
  intro p hp
  simp [S] at hp
  have Xc : 2 ^ k ≤ p := hp.1.1
  have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast Xc
  exact one_div_le_one_div_of_le n7 hlow
 have O4 :
   S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
  rw [← kL]
  refine Finset.card_le_card ?_
  intro p hp
  simp [S] at hp
  rw [Finset.mem_filter]
  have adk := hp.1
  have jM : Nat.Prime p := hp.2
  exact ⟨Finset.mem_Icc.mpr ⟨jM.one_le, adk.2.le⟩, jM⟩
 calc
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ))
    = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
  _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     exact Finset.sum_le_sum hpoint
  _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
     exact div_le_div_of_nonneg_right (by exact_mod_cast O4) n7.le
lemma iF
  (B : ℝ) {k : ℕ}
  (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
   B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
    Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ)) ≤
   (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
 have n7 : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
 have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
 calc
  (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
    (1 : ℝ) / (p : ℝ))
    ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
      ((2 ^ k : ℕ) : ℝ) :=
     lO k
  _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
     Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
      ((2 ^ k : ℕ) : ℝ) := by
     exact div_le_div_of_nonneg_right hπ n7.le
  _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
     have Ve :
       (((2 ^ (k + 1) : ℕ) : ℝ)) =
        (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
      norm_num [pow_succ, mul_comm]
     have Xd :
       Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
      rw [Real.log_pow]
     rw [Xd, Ve]
     field_simp [n7.ne', tK.ne', hkpos.ne']
lemma je :
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
   (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
     (1 : ℝ) / (p : ℝ)) ≤
    D / ((k + 1 : ℕ) : ℝ) := by
 rcases j3 with ⟨B, Om, YQ⟩
 refine ⟨2 * B / Real.log 2, ?_, ?_⟩
 ·positivity
 ·have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
   exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have adl := hpw.eventually YQ
  filter_upwards [adl] with k hk
  exact iF B hk
lemma jG :
  ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
   (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
     (1 : ℝ) / (p : ℝ)) ≤
    D / ((k + 1 : ℕ) : ℝ) := by
 classical
 rcases je with
  ⟨D, XR, YS⟩
 rcases eventually_atTop.1 YS with ⟨K, hK⟩
 let block : ℕ → ℝ := fun k =>
  ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
   (1 : ℝ) / (p : ℝ)
 let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
 refine ⟨D + extra + 1, ?_, ?_⟩
 ·have NU : 0 ≤ extra := by
   refine Finset.sum_nonneg ?_
   intro k hk
   exact mul_nonneg (by positivity)
    (by
     refine Finset.sum_nonneg ?_
     intro p hp
     exact div_nonneg zero_le_one (by positivity))
  linarith
 ·intro k
  have n7 : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  by_cases Dq : K ≤ k
  ·have af2 : D ≤ D + extra + 1 := by
    have NU : 0 ≤ extra := by
     refine Finset.sum_nonneg ?_
     intro j hj
     exact mul_nonneg (by positivity)
      (by
       refine Finset.sum_nonneg ?_
       intro p hp
       exact div_nonneg zero_le_one (by positivity))
    linarith
   calc
    block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k Dq
    _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right af2 n7.le
  ·have hkle : k ≤ K := Nat.le_of_not_ge Dq
   have hk_mem : k ∈ Finset.Icc 0 K := by
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
   have tJ :
     ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
    intro j hj
    exact mul_nonneg (by positivity)
     (by
      refine Finset.sum_nonneg ?_
      intro p hp
      exact div_nonneg zero_le_one (by positivity))
   have nZ :
     ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
    Finset.single_le_sum tJ hk_mem
   have hmul :
     block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
    calc
     block k * ((k + 1 : ℕ) : ℝ)
       = ((k + 1 : ℕ) : ℝ) * block k := by ring
     _ ≤ extra := nZ
     _ ≤ D + extra + 1 := by linarith
   exact (le_div_iff₀ n7).2 hmul
lemma ko
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
 have Vf :
   ∀ k ∈ T,
    (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
      (1 : ℝ) / (p : ℝ)) ≤
     ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) := by
  intro k hk
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  ·intro p hp
   simp [S] at hp ⊢
   have jM : Nat.Prime p := hp.1.2
   have hpne : p ≠ 0 := jM.ne_zero
   have hlog : Nat.log 2 p = k := hp.2
   exact ⟨⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
    by simpa [hlog, Nat.succ_eq_add_one] using
     Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩, jM⟩
  ·intro p hp QX
   exact div_nonneg zero_le_one (by positivity)
 have Rg :
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
  have SO :
    (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
     = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
   rw [Finset.sum_image]
   intro a ha b hb hab
   exact hinj ha hb hab
  calc
   (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
     = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
      exact SO.symm
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
     Finset.sum_le_sum Vf
  _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := Rg
  _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro k hk
     ring
  _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
     rw [hsum_shift]
  _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
     exact mul_le_mul_of_nonneg_left
      (oA (Nat.log 2 N + 1))
      (by
       have hD0 := hD 0
       have LW :
         0 ≤
          (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
           (1 : ℝ) / (p : ℝ)) := by
        refine Finset.sum_nonneg ?_
        intro p hp
        exact div_nonneg zero_le_one (by positivity)
       have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
       nlinarith [hD0, LW])
lemma jS :
  ∀ᶠ N : ℕ in atTop,
   1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
    ≤ 2 * Real.log (Real.log (N : ℝ)) := by
 let C : ℝ := 2 / Real.log 2
 have tK : 0 < Real.log 2 := Real.log_pos (by norm_num)
 have hCpos : 0 < C := by positivity
 have NV :
   ∀ᶠ N : ℕ in atTop,
    1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
  iw.eventually_ge_atTop (1 + Real.log C)
 filter_upwards [NV,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N aeE dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have LX : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have aaD : Real.log 2 < 1 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
 have NW : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
 have Vg : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
  have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
   simpa using NW
  exact (le_div_iff₀ tK).2 this
 have W0 :
   ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have h := Real.log2_le_logb N
  simpa [Nat.log2_eq_log_two, Real.logb] using h
 have LY :
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
 have Vh : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
 have adn : 0 < C * Real.log (N : ℝ) := mul_pos hCpos LX
 have SX :
   Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
    ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
  calc
   Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
     ≤ Real.log (C * Real.log (N : ℝ)) :=
      Real.log_le_log Vh LY
   _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
      rw [Real.log_mul hCpos.ne' LX.ne']
 linarith
theorem qv :
  ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
   (((Finset.Icc 1 N).filter Nat.Prime).sum
     (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
    ≤ A * Real.log (Real.log (N : ℝ)) + C := by
 rcases jG with ⟨D, XR, hD⟩
 refine ⟨2 * D, 0, by positivity, ?_⟩
 filter_upwards [jS] with N YV
 calc
  (((Finset.Icc 1 N).filter Nat.Prime).sum
    (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
    ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
     ko D hD N
  _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
     mul_le_mul_of_nonneg_left YV XR.le
  _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring
theorem nT :
  ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
   ∀ y : ℕ, y ≤ N →
    (∑ n ∈ Finset.Icc 1 y, (gd N) ^ omega n)
     ≤ (y : ℝ) *
       Real.exp (gd N *
        (A * Real.log (Real.log (N : ℝ)) + C)) := by
 rcases qv with ⟨A, C, hA, Xf⟩
 refine ⟨A, C, hA, ?_⟩
 filter_upwards [Xf,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N Vi dG
 intro y hy
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have sW : 0 ≤ gd N := by
  rw [gd]
  exact div_nonneg (Real.sqrt_nonneg _) c8.le
 let Py : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
 let PN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
 have SY : Py ⊆ PN := by
  intro p hp
  simp [Py, PN] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hy⟩, hp.2⟩
 have Rh :
   Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
    PN.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg SY
   (by
    intro p hpN aaE
    simp [PN] at hpN
    exact div_nonneg zero_le_one (by exact_mod_cast hpN.2.pos.le))
 have O5 :
   Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
    A * Real.log (Real.log (N : ℝ)) + C := by
  exact Rh.trans (by simpa [PN] using Vi)
 have aaF : ∀ p ∈ Py, 0 < (p : ℝ) := by
  intro p hp
  simp [Py] at hp
  exact_mod_cast hp.2.pos
 have Vk :
   Py.prod (fun p : ℕ => (1 : ℝ) + gd N / (p : ℝ)) ≤
    Real.exp (gd N *
     Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
  j9 Py sW aaF
 have hprod_bound :
   Py.prod (fun p : ℕ => (1 : ℝ) + gd N / (p : ℝ)) ≤
    Real.exp (gd N *
     (A * Real.log (Real.log (N : ℝ)) + C)) := by
  exact Vk.trans
   (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left O5 sW))
 exact (lN y (gd N) sW).trans
  (mul_le_mul_of_nonneg_left (by simpa [Py] using hprod_bound) (by positivity))
lemma kW
  (A C ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   gd N * (A * Real.log (Real.log (N : ℝ)) + C) ≤ ε * aZ N := by
 let R : ℝ := max (4 * (A + 1) / ε) (max 1 |C|)
 filter_upwards [f9 R,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have d6 : 0 ≤ Real.log (N : ℝ) := gC.le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have f8 : 0 ≤ Real.log (Real.log (N : ℝ)) := c8.le
 have oO : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
 have ahx : 0 < A + 1 := by linarith
 have SZ : 4 * (A + 1) / ε ≤ R := le_max_left _ _
 have Dr : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
 have Vm : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
 have NY :
   4 * (A + 1) / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  SZ.trans hsqrt
 have aaG : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  Dr.trans hsqrt
 have O6 : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  Vm.trans hsqrt
 have LZ : |C| ≤ Real.log (Real.log (N : ℝ)) := by
  calc
   |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := O6
   _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
   _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt f8
 have S5 :
   2 * (A + 1) ≤
    ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hfour :
    4 * (A + 1) ≤
     ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
   simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (div_le_iff₀ hε).1 NY
  linarith
 have O7 : 0 ≤ gd N := by
  rw [gd]
  exact div_nonneg oO f8
 have S6 :
   A * Real.log (Real.log (N : ℝ)) + C ≤
    (A + 1) * Real.log (Real.log (N : ℝ)) := by
  calc
   A * Real.log (Real.log (N : ℝ)) + C
     ≤ A * Real.log (Real.log (N : ℝ)) + |C| := by
      nlinarith [le_abs_self C]
   _ ≤ A * Real.log (Real.log (N : ℝ)) +
      Real.log (Real.log (N : ℝ)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
       add_le_add_left LZ
        (A * Real.log (Real.log (N : ℝ)))
   _ = (A + 1) * Real.log (Real.log (N : ℝ)) := by ring
 have Ri :
   gd N * (A * Real.log (Real.log (N : ℝ)) + C) ≤
    gd N * ((A + 1) * Real.log (Real.log (N : ℝ))) :=
  mul_le_mul_of_nonneg_left S6 O7
 have aaH := gN c7
 have hbound :
   gd N * ((A + 1) * Real.log (Real.log (N : ℝ))) ≤
    ε * aZ N := by
  rw [gd, aaH]
  calc
   Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
     ((A + 1) * Real.log (Real.log (N : ℝ)))
     = (A + 1) * Real.sqrt (Real.log (N : ℝ)) := by
      field_simp [c8.ne']
   _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
      Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
      calc
       (A + 1) * Real.sqrt (Real.log (N : ℝ))
         ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
           Real.sqrt (Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
             (by linarith [S5]) oO
       _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
          Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
 exact Ri.trans hbound
theorem pQ :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y : ℕ, y ≤ N →
    (∑ n ∈ Finset.Icc 1 y, (gd N) ^ omega n)
     ≤ (y : ℝ) * Real.exp (ε * aZ N) := by
 intro ε hε
 rcases nT with ⟨A, C, hA, hC⟩
 filter_upwards [hC, kW A C ε hA hε]
  with N Vq cQ y hy
 have Wz :
   Real.exp (gd N * (A * Real.log (Real.log (N : ℝ)) + C)) ≤
    Real.exp (ε * aZ N) :=
  Real.exp_le_exp.2 cQ
 exact (Vq y hy).trans
  (mul_le_mul_of_nonneg_left Wz (by positivity))
end cP
namespace cP
open Filter Finset
open scoped BigOperators
lemma qK {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
  (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
 (Nat.le_floor_iff hx).2 hm
lemma tL (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
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
     intro n aiP ab7
     exact pow_nonneg hz0 (omega n)
lemma m6
  (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
  (Xg : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
  (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
   ≤ (y : ℝ) * B / z ^ t := by
 classical
 have Vr : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
 have htail := tL y t hz
 have WA : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
   ≤ (y : ℝ) * B :=
  htail.trans Xg
 exact (le_div_iff₀ Vr).2 WA
lemma lZ
  (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
  (hX : 0 ≤ X)
  (Xg : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
  (N5 : (y : ℝ) * B / z ^ t ≤ X) :
  ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
 refine qK hX ?_
 exact (m6 y t hz Xg).trans N5
private lemma kM :
  Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
    Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
 have hreal :
   Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
  have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
    fun x : ℝ => Real.log x :=
   Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact hsmall.tendsto_div_nhds_zero
 exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
private lemma l6
  (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ N : ℕ in atTop,
   Real.log (Real.log (Real.log (N : ℝ))) ≤
    δ * Real.log (Real.log (N : ℝ)) := by
 have hsmall :
   ∀ᶠ N : ℕ in atTop,
    Real.log (Real.log (Real.log (N : ℝ))) /
     Real.log (Real.log (N : ℝ)) < δ :=
  kM.eventually_lt_const hδ
 filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
  with N YZ dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 exact ((div_lt_iff₀ c8).1 YZ).le
private lemma kB {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
  0 < gd N := by
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 hN
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 rw [gd]
 exact div_pos (Real.sqrt_pos.2 gC) c8
private lemma kP
  (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ N : ℕ in atTop,
   ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (gd N) := by
 filter_upwards [l6 δ hδ,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N alB dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have d6 : 0 ≤ Real.log (N : ℝ) := gC.le
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have MY : 0 < Real.sqrt (Real.log (N : ℝ)) :=
  Real.sqrt_pos.2 gC
 have Vt :
   Real.log (gd N) =
    Real.log (Real.log (N : ℝ)) / 2 -
     Real.log (Real.log (Real.log (N : ℝ))) := by
  rw [gd, Real.log_div MY.ne' c8.ne',
   Real.log_sqrt d6]
 rw [Vt]
 nlinarith
private lemma wO :
  ∀ᶠ N : ℕ in atTop, 1 ≤ gd N := by
 filter_upwards [kP ((1 : ℝ) / 4) (by norm_num),
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N JX dG
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have hzpos : 0 < gd N := kB c7
 have d6 : 0 ≤ Real.log (gd N) := by
  nlinarith
 have hone : Real.exp 0 ≤ gd N :=
  (Real.le_log_iff_exp_le hzpos).1 d6
 simpa using hone
private lemma qL
  (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ N : ℕ in atTop,
   ∀ t : ℕ, (t : ℝ) ≤ 3 * aO N →
    Real.exp ((ε / 2) * aZ N) / (gd N) ^ t
     ≤ Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N) := by
 let δ : ℝ := ε / 6
 have hδ : 0 < δ := by dsimp [δ]; positivity
 filter_upwards [kP δ hδ,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N JX dG t ht
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hMpos : 0 < aO N := g5 c7
 have O8 : 0 ≤ aZ N := nD N
 have hzpos : 0 < gd N := kB c7
 have hLL :
   Real.log (Real.log (N : ℝ)) = aZ N / aO N :=
  (j4 c7).symm
 have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
 have af3 :
   (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
    ≤ (t : ℝ) * Real.log (gd N) :=
  mul_le_mul_of_nonneg_left JX ht_nonneg
 have Vv : (t : ℝ) / aO N ≤ 3 := by
  exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
 have S7 : δ * ((t : ℝ) / aO N) ≤ ε / 2 := by
  calc
   δ * ((t : ℝ) / aO N) ≤ δ * 3 := by
    exact mul_le_mul_of_nonneg_left Vv hδ.le
   _ = ε / 2 := by
    dsimp [δ]
    ring
 have Y0 :
   (ε / 2) * aZ N - (t : ℝ) * Real.log (gd N)
    ≤ (-((t : ℝ) / aO N) / 2 + ε) * aZ N := by
  have hmain :
    (ε / 2) * aZ N -
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
     ≤ (-((t : ℝ) / aO N) / 2 + ε) * aZ N := by
   rw [hLL]
   have ahy :
     (δ * ((t : ℝ) / aO N)) * aZ N ≤ (ε / 2) * aZ N :=
    mul_le_mul_of_nonneg_right S7 O8
   have nU :
     (t : ℝ) * (((1 : ℝ) / 2 - δ) * (aZ N / aO N)) =
      (((1 : ℝ) / 2 - δ) * ((t : ℝ) / aO N)) * aZ N := by
    field_simp [hMpos.ne']
   rw [nU]
   nlinarith
  nlinarith
 have ado :
   (gd N) ^ t = Real.exp ((t : ℝ) * Real.log (gd N)) := by
  calc
   (gd N) ^ t = (Real.exp (Real.log (gd N))) ^ t := by
    rw [Real.exp_log hzpos]
   _ = Real.exp ((t : ℝ) * Real.log (gd N)) := by
    rw [← Real.exp_nat_mul]
 rw [ado, ← Real.exp_sub]
 exact Real.exp_le_exp.2 Y0
theorem wP :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * aO N →
    let α : ℝ := (t : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-α / 2 + ε) * aZ N)) := by
 intro ε hε
 have hε2 : 0 < ε / 2 := by positivity
 filter_upwards [pQ (ε / 2) hε2,
   qL ε hε, wO]
  with N MZ RU O9
 intro y t hy ht
 dsimp only
 refine lZ (y := y) (t := t)
  (z := gd N) (B := Real.exp ((ε / 2) * aZ N))
  (X := (y : ℝ) *
   Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N))
  O9 ?_ (MZ y hy) ?_
 ·positivity
 ·have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
  calc
   (y : ℝ) * Real.exp ((ε / 2) * aZ N) / (gd N) ^ t
     = (y : ℝ) *
       (Real.exp ((ε / 2) * aZ N) / (gd N) ^ t) := by
       ring
   _ ≤ (y : ℝ) *
       Real.exp ((-((t : ℝ) / aO N) / 2 + ε) * aZ N) := by
       exact mul_le_mul_of_nonneg_left (RU t ht) hy_nonneg
end cP
namespace cP
open Filter Finset
open scoped BigOperators
lemma KO (y t : ℕ) :
  (Finset.Icc 1 y).filter (fun n => omega n = t)
   ⊆ (Finset.Icc 1 y).filter (fun n => t ≤ omega n) := by
 intro n hn
 exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.ge⟩
lemma LG (y t : ℕ) :
  ((Finset.Icc 1 y).filter (fun n => omega n = t)).card
   ≤ ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card :=
 Finset.card_le_card (KO y t)
private lemma Np {N y K W : ℕ} (ε : ℝ)
  (hN : Real.exp 1 < (N : ℝ)) (hWK : W ≤ K) :
  (y : ℝ) *
    Real.exp ((-(((K - W : ℕ) : ℝ) / aO N) / 2 + ε) * aZ N)
   =
  (y : ℝ) *
    Real.exp ((-((K : ℝ) / aO N) / 2 + ε) * aZ N) *
    Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
 have hMpos : 0 < aO N := g5 hN
 have abB : aZ N / aO N = Real.log (Real.log (N : ℝ)) :=
  j4 hN
 have hcast : (((K - W : ℕ) : ℝ)) = (K : ℝ) - (W : ℝ) := by
  exact_mod_cast (Nat.cast_sub hWK : ((K - W : ℕ) : ℝ) = (K : ℝ) - (W : ℝ))
 have hexp :
   ((-(((K - W : ℕ) : ℝ) / aO N) / 2 + ε) * aZ N)
    =
   ((-((K : ℝ) / aO N) / 2 + ε) * aZ N) +
    (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  rw [hcast, ← abB]
  field_simp [hMpos.ne']
  ring
 rw [hexp, Real.exp_add]
 ring
theorem QN :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
 intro ε hε
 filter_upwards [wP ε hε,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hTail dG
 intro y K W hy hWK hK
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have aea := LG y (K - W)
 have abC : ((K - W : ℕ) : ℝ) ≤ (K : ℝ) := by
  exact_mod_cast Nat.sub_le K W
 have ht_bound : ((K - W : ℕ) : ℝ) ≤ 3 * aO N := abC.trans hK
 have Wb := hTail y (K - W) hy ht_bound
 have htarget :=
  Np (N := N) (y := y) (K := K) (W := W) ε c7 hWK
 dsimp only at Wb ⊢
 exact aea.trans (by simpa [htarget] using Wb)
end cP
namespace cP
open Filter Finset
open scoped BigOperators
theorem QO :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
 QN
end cP
namespace cP
open Filter Finset
open scoped BigOperators
structure bC (N : ℕ) where
 Q : Finset ℕ
 z6 : Q.Nonempty
 a : gJ Q
 admissible : Admissible N Q
 pairwise_disjoint : d7 Q a
 K : ℕ
 K_pos : 1 ≤ K
 Bk : ∀ q ∈ Q, (N : ℝ) * bF (-2) N ≤ (q : ℝ)
 q6 : ∀ q ∈ Q, q ≤ N
 Ee : ∀ q ∈ Q, (cQ q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
 L9 : ∀ q ∈ Q, omega q = K
 yD : (K : ℝ) ≤ 3 * aO N
 Bm : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r
lemma bC.card_pos {N : ℕ} (D : bC N) : 0 < D.Q.card :=
 D.z6.card_pos
lemma bC.N_pos {N : ℕ} (D : bC N) : 0 < N := by
 rcases D.z6 with ⟨q, hq⟩
 exact lt_of_lt_of_le (D.admissible.1 q hq).1 (D.q6 q hq)
lemma bC.abD {N : ℕ} (D : bC N) :
  D.Q ⊆ Finset.Icc 1 N := by
 intro q hq
 exact Finset.mem_Icc.2 (D.admissible.1 q hq)
lemma bC.afx {N : ℕ} (D : bC N) :
  D.Q.card ≤ N := by
 have hcard := Finset.card_le_card D.abD
 have hIcc : (Finset.Icc 1 N).card = N := by
  rw [Nat.card_Icc]
  omega
 simpa [hIcc] using hcard
theorem Sl :
 ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
  ∀ y K W : ℕ,
   y ≤ N →
   W ≤ K →
   (K : ℝ) ≤ 3 * aO N →
   let d : ℝ := (K : ℝ) / aO N
   ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
    ≤ Nat.floor
      ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
       * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
 QO
end cP
namespace cP
open Filter Finset
open scoped BigOperators
lemma vP {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
  (h : m ≤ Nat.floor x) : (m : ℝ) ≤ x := by
 exact (Nat.le_floor_iff hx).1 h
lemma LL {α : Type*} [DecidableEq α] (I : Finset α)
  (N w : α → ℝ) (hI : I.Nonempty)
  (hw : ∀ i ∈ I, 0 < w i) :
  ∃ i ∈ I, (∑ j ∈ I, N j) * w i / (∑ j ∈ I, w j) ≤ N i := by
 classical
 let zE := ∑ j ∈ I, N j
 let KQ := ∑ j ∈ I, w j
 have acN : 0 < KQ := Finset.sum_pos hw hI
 by_contra h
 push_neg at h
 have hlt : ∀ i ∈ I, N i < zE * w i / KQ := by
  intro i hi
  simpa [zE, KQ] using h i hi
 have aii : ∑ i ∈ I, N i < ∑ i ∈ I, zE * w i / KQ := by
  exact Finset.sum_lt_sum_of_nonempty hI hlt
 have ag0 : (∑ i ∈ I, zE * w i / KQ) = zE := by
  calc
   (∑ i ∈ I, zE * w i / KQ) =
     ∑ i ∈ I, (zE / KQ) * w i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
   _ = (zE / KQ) * KQ := by rw [Finset.mul_sum]
   _ = zE := div_mul_cancel₀ zE acN.ne'
 have : zE < zE := by
  change (∑ i ∈ I, N i) < zE
  rw [← ag0]
  exact aii
 exact lt_irrefl _ this
lemma Nq {α β : Type*} [DecidableEq α] [DecidableEq β]
  (S : Finset α) (B : α → β) (w : β → ℝ) (hS : S.Nonempty)
  (hw : ∀ b ∈ S.image B, 0 < w b) :
  ∃ b ∈ S.image B,
   (S.card : ℝ) * w b / (∑ c ∈ S.image B, w c) ≤
    ((S.filter fun a => B a = b).card : ℝ) := by
 classical
 have ajP : (S.image B).Nonempty := hS.image B
 rcases LL (S.image B)
   (fun b => ((S.filter fun a => B a = b).card : ℝ)) w ajP hw with
  ⟨b, hb, Zv⟩
 refine ⟨b, hb, ?_⟩
 have KR :
   (∑ b ∈ S.image B, (S.filter fun a => B a = b).card) = S.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  ·intro h
   exact h.1
  ·intro ha
   exact ⟨ha, a, ha, rfl⟩
 have Jb :
   (∑ b ∈ S.image B, ((S.filter fun a => B a = b).card : ℝ)) =
    (S.card : ℝ) := by
  exact_mod_cast KR
 simpa [Jb] using Zv
lemma Nr {α β : Type*} [DecidableEq α] [DecidableEq β]
  {S : Finset α} {B : α → β} {b : β} (hb : b ∈ S.image B) :
  (S.filter fun a => B a = b).Nonempty := by
 rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
 exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
lemma Qm {α β : Type*} [DecidableEq α] [Fintype β]
  [DecidableEq β] (S : Finset α) (r : α → β) (hS : S.Nonempty) :
  ∃ b : β,
   (S.card : ℝ) / (Fintype.card β : ℝ) ≤
    ((S.filter fun a => r a = b).card : ℝ) := by
 classical
 haveI : Nonempty β := by
  rcases hS with ⟨a, _ha⟩
  exact ⟨r a⟩
 have akX : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
 rcases LL (Finset.univ : Finset β)
   (fun b => ((S.filter fun a => r a = b).card : ℝ)) (fun _ => (1 : ℝ))
   akX (by intro _b _hb; norm_num) with ⟨b, _hb, Zv⟩
 refine ⟨b, ?_⟩
 have KR :
   (∑ b ∈ (Finset.univ : Finset β), (S.filter fun a => r a = b).card) =
    S.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp
 have Jb :
   (∑ b ∈ (Finset.univ : Finset β),
     ((S.filter fun a => r a = b).card : ℝ)) = (S.card : ℝ) := by
  exact_mod_cast KR
 have abE :
   (∑ _b ∈ (Finset.univ : Finset β), (1 : ℝ)) =
    (Fintype.card β : ℝ) := by
  simp
 simpa [Jb, abE] using Zv
lemma LJ (T : Finset ℕ) (P : ℕ) [NeZero P]
  (r : ℕ → ZMod P) (hT : T.Nonempty) :
  ∃ b : ZMod P,
   (T.card : ℝ) / (P : ℝ) ≤ ((T.filter fun q => r q = b).card : ℝ) := by
 rcases Qm T r hT with ⟨b, hb⟩
 exact ⟨b, by simpa [ZMod.card] using hb⟩
lemma List.WS {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
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
private lemma List.aap {l : List ℕ}
  (hpos : ∀ a ∈ l, 0 < a) : 0 < l.foldr (· * ·) 1 := by
 induction l with
 | nil => simp
 | cons a l ih =>
   simp only [List.foldr_cons]
   exact Nat.mul_pos (hpos a (by simp)) (ih (by
    intro b hb
    exact hpos b (by simp [hb])))
private lemma List.Nt
  {P : ℕ} {Ps : List ℕ} (abF : ∀ Q ∈ Ps, Nat.Coprime P Q) :
  Nat.Coprime P (Ps.foldr (· * ·) 1) := by
 induction Ps with
 | nil =>
   simp
 | cons Q Qs ih =>
   simp only [List.foldr_cons]
   exact Nat.Coprime.mul_right (abF Q (by simp)) (ih (by
    intro R hR
    exact abF R (by simp [hR])))
private lemma QS (m : ℕ) :
  ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
 have Y1 : ∀ m : ℕ, 1 ≤ m →
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
 ·simp [hm]
 ·have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
  exact (Y1 m hm1).trans (by
   have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
   linarith)
private lemma U6 {ι : Type*} [Fintype ι] (f : ι → ℕ) :
  (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
   ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
 simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]
structure aE (N : ℕ) (D : bC N) where
 r : ℕ
 blocks : List ℕ
 blocks_length : blocks.length = r
 gQ : Finset ℕ
 iE : gQ ⊆ D.Q
 zF : gQ.Nonempty
 W : ℕ
 aR : ℕ
 A8 : aR = (blocks.foldr (· * ·) 1)
 blocks_pos : ∀ P ∈ blocks, 0 < P
 jZ : 0 < aR
 A9 : blocks.Pairwise Nat.Coprime
 iW : ∀ q ∈ gQ, aR ∣ q
 ow :
  ∀ q ∈ gQ, ∀ p ∈ aD aR,
   p ∉ aD (q / aR)
 EY :
  ∀ qi ∈ gQ, ∀ rj ∈ gQ,
   ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
    D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (aR : ℤ)]
 XC : W = omega aR
 Nu : W ≤ D.K
def aE.gI {N : ℕ} {D : bC N}
  (S : aE N D) : Prop :=
 ∀ P ∈ S.blocks, 1 ≤ omega P
lemma aE.Nv {N : ℕ} {D : bC N}
  (S : aE N D) {q : ℕ} (hq : q ∈ S.gQ) :
  S.aR ≤ q := by
 have qZ : q ∈ D.Q := S.iE hq
 have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1
 exact Nat.le_of_dvd hqpos (S.iW q hq)
lemma aE.U7 {N : ℕ} {D : bC N}
  (S : aE N D) :
  (cQ S.aR : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
 rcases S.zF with ⟨q, hq⟩
 have qZ : q ∈ D.Q := S.iE hq
 have XD : q ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1).ne'
 have Zw : cQ S.aR ≤ cQ q :=
  Ze (S.iW q hq) XD
 have XE : (cQ S.aR : ℝ) ≤ (cQ q : ℝ) := by
  exact_mod_cast Zw
 exact XE.trans (D.Ee q qZ)
lemma aE.Wd {N : ℕ} {D : bC N}
  (S : aE N D) {B : ℕ} (hB : B ∈ S.blocks) : B ∣ S.aR := by
 rw [S.A8]
 exact List.WS hB
lemma aE.qV {N : ℕ} {D : bC N}
  (S : aE N D) {q : ℕ} (hq : q ∈ S.gQ) :
  Disjoint (aD S.aR) (dY S.aR q) := by
 rw [Finset.disjoint_left]
 intro p hpP Yo
 exact S.ow q hq p hpP Yo
lemma aE.lC {N : ℕ} {D : bC N}
  (S : aE N D) {q : ℕ} (hq : q ∈ S.gQ) :
  (dY S.aR q).card = D.K - S.W := by
 have qZ : q ∈ D.Q := S.iE hq
 have hqpos : q ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1).ne'
 have yF :
   omega (q / S.aR) = omega q - omega S.aR :=
  xG (S.iW q hq)
   S.jZ.ne' hqpos (S.qV hq)
 calc
  (dY S.aR q).card = omega (q / S.aR) := by
   simp [dY, omega]
  _ = omega q - omega S.aR := yF
  _ = D.K - S.W := by
   rw [D.L9 q qZ, ← S.XC]
lemma aE.Cw {N : ℕ} {D : bC N}
  (S : aE N D) {q r : ℕ} (hq : q ∈ S.gQ) (hr : r ∈ S.gQ)
  (hdisj : Disjoint (dY S.aR q) (dY S.aR r)) :
  Nat.gcd q r ∣ S.aR := by
 have qZ : q ∈ D.Q := S.iE hq
 have Wf : r ∈ D.Q := S.iE hr
 have hqpos : q ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1).ne'
 have hrpos : r ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 r Wf).1).ne'
 exact DB
  (S.iW q hq) (S.iW r hr)
  S.jZ.ne' hqpos hrpos hdisj
lemma aE.EZ {N : ℕ} {D : bC N}
  (S : aE N D) {q r : ℕ} (hq : q ∈ S.gQ) (hr : r ∈ S.gQ)
  (hqr : q ≠ r) :
  ¬ Disjoint (dY S.aR q) (dY S.aR r) := by
 intro hdisj
 have qZ : q ∈ D.Q := S.iE hq
 have Wf : r ∈ D.Q := S.iE hr
 have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1
 have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (D.admissible.1 r Wf).1
 have hgcd_dvd : Nat.gcd q r ∣ S.aR :=
  S.Cw hq hr hdisj
 have ahr := S.EY q hq r hr qZ Wf
 have akY :
   D.a ⟨q, qZ⟩ ≡ D.a ⟨r, Wf⟩ [ZMOD (Nat.gcd q r : ℤ)] := by
  rw [Int.modEq_iff_dvd] at ahr ⊢
  have abG : (Nat.gcd q r : ℤ) ∣ (S.aR : ℤ) := by
   exact_mod_cast hgcd_dvd
  exact dvd_trans abG ahr
 have afy :
   Disjoint (residueClass q (D.a ⟨q, qZ⟩))
    (residueClass r (D.a ⟨r, Wf⟩)) :=
  D.pairwise_disjoint ⟨q, qZ⟩ ⟨r, Wf⟩ (by
   intro hsub
   exact hqr (Subtype.ext_iff.mp hsub))
 exact ((Ox hqpos hrpos
  (D.a ⟨q, qZ⟩) (D.a ⟨r, Wf⟩)).1 afy) akY
def aE.cO {N : ℕ} {D : bC N}
  (S : aE N D) : Finset (Finset ℕ) :=
 S.gQ.image (fun q => dY S.aR q)
lemma aE.JG {N : ℕ} {D : bC N}
  (S : aE N D) : S.cO.Nonempty := by
 rcases S.zF with ⟨q, hq⟩
 exact ⟨dY S.aR q, Finset.mem_image.2 ⟨q, hq, rfl⟩⟩
lemma aE.MJ {N : ℕ} {D : bC N}
  (S : aE N D) :
  Set.InjOn (fun q => dY S.aR q) S.gQ := by
 intro q hq r hr hqr
 have qZ : q ∈ D.Q := S.iE hq
 have Wf : r ∈ D.Q := S.iE hr
 have XD : q ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1).ne'
 have hrne : r ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 r Wf).1).ne'
 have ajQ :
   aD q = aD S.aR ∪ dY S.aR q :=
  qw (S.iW q hq) S.jZ.ne' XD
 have ajR :
  aD r = aD S.aR ∪ dY S.aR r :=
  qw (S.iW r hr) S.jZ.ne' hrne
 have hsupp : aD q = aD r := by
  change dY S.aR q = dY S.aR r at hqr
  rw [ajQ, ajR, hqr]
 have hrad : rad q = rad r := by
  unfold rad
  rw [hsupp]
 exact D.Bm q qZ r Wf hrad
lemma aE.KV {N : ℕ} {D : bC N}
  (S : aE N D) :
  S.cO.card = S.gQ.card := by
 rw [aE.cO]
 exact Finset.card_image_of_injOn (fun q hq r hr hqr =>
  S.MJ hq hr hqr)
def aE.aY {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) : Finset ℕ :=
 S.gQ.filter fun q => C ⊆ dY S.aR q
def aE.cZ {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) : Finset ℕ :=
 (S.aY C).image (fun q => cD C q)
lemma aE.JH {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ)
  (gG : (S.aY C).Nonempty) :
  ∃ P ∈ S.cZ C,
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ) := by
 classical
 rw [aE.cZ]
 exact Nq (S.aY C) (fun q => cD C q)
  (fun P => (1 : ℝ) / ((cQ P : ℝ) ^ 2)) gG (by
   intro P _hP
   exact Ra P)
def aE.H7 {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) : Finset ℕ :=
 (S.aY C).image (fun q => q / S.aR)
lemma aE.vQ {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  (S.cO.filter fun A => C ⊆ A) ⊆
   (S.aY C).image (fun q => dY S.aR q) := by
 intro A hA
 rw [aE.cO] at hA
 rw [Finset.mem_filter] at hA
 rcases Finset.mem_image.mp hA.1 with ⟨q, hq, rfl⟩
 exact Finset.mem_image.2 ⟨q, by
  rw [aE.aY, Finset.mem_filter]
  exact ⟨hq, hA.2⟩, rfl⟩
lemma aE.kJ {N : ℕ}
  {D : bC N} (S : aE N D) (C : Finset ℕ) :
  (S.cO.filter fun A => C ⊆ A).card ≤
   (S.aY C).card := by
 exact (Finset.card_le_card (S.vQ C)).trans
  Finset.card_image_le
lemma aE.Ud {N : ℕ} {D : bC N}
  (S : aE N D) :
  Set.InjOn (fun q => q / S.aR) S.gQ := by
 intro q hq r hr hqr
 have akZ := Nat.div_mul_cancel (S.iW q hq)
 have ak0 := Nat.div_mul_cancel (S.iW r hr)
 calc
  q = (q / S.aR) * S.aR := akZ.symm
  _ = (r / S.aR) * S.aR := by
   exact congrArg (fun x => x * S.aR) hqr
  _ = r := ak0
lemma aE.Wg {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  (S.H7 C).card = (S.aY C).card := by
 rw [aE.H7]
 exact Finset.card_image_of_injOn fun q hq r hr hqr =>
  S.Ud (Finset.mem_filter.1 hq).1
   (Finset.mem_filter.1 hr).1 hqr
lemma aE.JI {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  S.H7 C ⊆
   (Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W) := by
 intro n hn
 rw [aE.H7] at hn
 rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
 have lX : q ∈ S.gQ := (Finset.mem_filter.1 hq).1
 have qZ : q ∈ D.Q := S.iE lX
 rw [Finset.mem_filter, Finset.mem_Icc]
 exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (S.Nv lX) S.jZ),
   (Nat.div_le_self q S.aR).trans (D.q6 q qZ)⟩,
  S.lC lX⟩
lemma aE.Je {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  (S.aY C).card ≤
   ((Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W)).card := by
 rw [← S.Wg C]
 exact Finset.card_le_card (S.JI C)
lemma aE.Dj
  {N : ℕ} {D : bC N} (S : aE N D) (C : Finset ℕ)
  (ε : ℝ)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  (S.aY C).card ≤
   Nat.floor
    ((N : ℝ) * Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
     * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
 exact (S.Je C).trans
  (lD N D.K S.W le_rfl S.Nu D.yD)
lemma aE.zG
  {N : ℕ} {D : bC N} (S : aE N D) (C : Finset ℕ)
  (ε : ℝ)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  ((S.aY C).card : ℝ) ≤
   (N : ℝ) * Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
     * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
 apply vP
 ·positivity
 ·exact S.Dj C ε lD
lemma aE.gT {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  S.aY C ⊆ S.gQ := by
 intro q hq
 exact (Finset.mem_filter.1 hq).1
lemma aE.jD {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  C ⊆ dY S.aR q :=
 (Finset.mem_filter.1 hq).2
lemma aE.wI {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  cD C q = cD C (q / S.aR) := by
 have lX : q ∈ S.gQ := S.gT C hq
 have hC : C ⊆ dY S.aR q :=
  S.jD hq
 apply UK
 intro p hpC
 have Yo : p ∈ dY S.aR q := hC hpC
 have Wh : p ∉ aD S.aR := by
  intro hpP
  exact (Finset.disjoint_left.1 (S.qV lX)) hpP Yo
 have abH : S.aR.factorization p = 0 := by
   unfold aD at Wh
   exact Finsupp.notMem_support_iff.1 Wh
 rw [Nat.factorization_div (S.iW q lX)]
 simp [Finsupp.coe_tsub, abH]
lemma aE.Cz {N : ℕ} {D : bC N}
  (S : aE N D) {q : ℕ} (hq : q ∈ S.gQ) :
  0 < q / S.aR := by
 exact Nat.div_pos (S.Nv hq) S.jZ
lemma aE.oL {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  cD C q ∣ q / S.aR := by
 rw [S.wI hq]
 exact Eb C (q / S.aR)
lemma aE.w8 {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  0 < cD C q := by
 exact Nat.pos_of_dvd_of_pos (S.oL hq)
  (S.Cz (S.gT C hq))
lemma aE.kD {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  aD (cD C q) = C := by
 have hC : C ⊆ dY S.aR q :=
  S.jD hq
 rw [S.wI hq]
 exact vG
  (fun p hp => f7 (hC hp))
  hC
lemma aE.DY {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  omega (cD C q) = C.card := by
 simp [omega, S.kD hq]
lemma aE.Fz {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  S.aR * cD C q ∣ q := by
 have lX : q ∈ S.gQ := S.gT C hq
 rcases S.oL hq with ⟨t, ht⟩
 refine ⟨t, ?_⟩
 have hdiv := Nat.div_mul_cancel (S.iW q lX)
 calc
  q = q / S.aR * S.aR := hdiv.symm
  _ = cD C q * t * S.aR := by rw [ht]
  _ = S.aR * cD C q * t := by ring
lemma aE.E0 {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {q : ℕ}
  (hq : q ∈ S.aY C) :
  Nat.Coprime S.aR (cD C q) := by
 have lX : q ∈ S.gQ := S.gT C hq
 have hC : C ⊆ dY S.aR q :=
  S.jD hq
 have hsupport : aD (cD C q) = C :=
  S.kD hq
 refine Iq S.jZ.ne'
  (S.w8 hq).ne' ?_
 rw [hsupport]
 rw [Finset.disjoint_left]
 intro p hpP hpC
 exact (Finset.disjoint_left.1 (S.qV lX)) hpP (hC hpC)
lemma aE.vW {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : 0 < P := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 exact S.w8 hq
lemma aE.jO {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : Nat.Coprime S.aR P := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 exact S.E0 hq
lemma aE.Fj {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : omega P = C.card := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 exact S.DY hq
lemma aE.oz {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : aD P = C := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 exact S.kD hq
lemma aE.kT {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P q : ℕ}
  (hq : q ∈ (S.aY C).filter fun q => cD C q = P) :
  S.aR * P ∣ q := by
 have Nw : q ∈ S.aY C := (Finset.mem_filter.1 hq).1
 have hP : cD C q = P := (Finset.mem_filter.1 hq).2
 simpa [hP] using S.Fz Nw
lemma aE.lH
  {N : ℕ} {D : bC N} (S : aE N D)
  {C : Finset ℕ} {P q : ℕ}
  (hq : q ∈ (S.aY C).filter fun q => cD C q = P) :
  ∀ p ∈ aD (S.aR * P), p ∉ aD (q / (S.aR * P)) := by
 intro p ahs Yo
 have Nw : q ∈ S.aY C := (Finset.mem_filter.1 hq).1
 have hP : cD C q = P := (Finset.mem_filter.1 hq).2
 have lX : q ∈ S.gQ := S.gT C Nw
 have qZ : q ∈ D.Q := S.iE lX
 have XD : q ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1).ne'
 have aay : P ∈ S.cZ C := by
  rw [aE.cZ]
  exact Finset.mem_image.2 ⟨q, Nw, hP⟩
 have hcop : Nat.Coprime S.aR P := S.jO aay
 have aij : S.aR * P ∣ q := S.kT hq
 have Yp : (S.aR * P).factorization p < q.factorization p :=
  (jh aij).1 Yo
 have acO :
   aD (S.aR * P) = aD S.aR ∪ aD P :=
  g9 hcop
 have ac9 : (S.aR * P).factorization p =
   S.aR.factorization p + P.factorization p := by
  rw [Nat.factorization_mul_of_coprime hcop]
  rfl
 rw [acO, Finset.mem_union] at ahs
 cases ahs with
 | inl aaz =>
   have acP : p ∉ aD (q / S.aR) :=
    S.ow q lX p aaz
   have afz : ¬ S.aR.factorization p < q.factorization p := by
    intro hlt
    exact acP
     ((jh (S.iW q lX)).2 hlt)
   have ajS : S.aR.factorization p ≤ q.factorization p :=
    (Nat.factorization_le_iff_dvd S.jZ.ne' XD).2
     (S.iW q lX) p
   have afA : q.factorization p ≤ S.aR.factorization p :=
    le_of_not_gt afz
   have ajT : S.aR.factorization p = q.factorization p :=
    le_antisymm ajS afA
   have Wh : p ∉ aD P :=
    (Finset.disjoint_left.1 (dL hcop)) aaz
   have abH : P.factorization p = 0 := by
    unfold aD at Wh
    exact Finsupp.notMem_support_iff.1 Wh
   rw [ac9, abH, add_zero, ajT] at Yp
   exact lt_irrefl _ Yp
 | inr hpP =>
   have afB : aD P = C := by
    rw [← hP]
    exact S.kD Nw
   have hpC : p ∈ C := by
    simpa [afB] using hpP
   have abI : p ∉ aD S.aR := by
    intro aaz
    exact (Finset.disjoint_left.1 (dL hcop)) aaz hpP
   have ag1 : S.aR.factorization p = 0 := by
    unfold aD at abI
    exact Finsupp.notMem_support_iff.1 abI
   have aik : ∀ r ∈ C, Nat.Prime r := by
    intro r hr
    exact f7 (S.jD Nw hr)
   have WC : P.factorization p = q.factorization p := by
    rw [← hP]
    exact kC aik hpC
   rw [ac9, ag1, zero_add, WC] at Yp
   exact lt_irrefl _ Yp
lemma aE.z4 {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : C.card ≤ D.K - S.W := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 exact (Finset.card_le_card (S.jD hq)).trans_eq
  (S.lC (S.gT C hq))
lemma aE.z5 {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) :
  omega (S.aR * P) = S.W + C.card := by
 rw [Kh (S.jO hP), ← S.XC,
  S.Fj hP]
lemma aE.vT
  {N : ℕ} {D : bC N} (S : aE N D)
  {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.cZ C) (ε : ℝ)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  ((((S.aY C).filter fun q => cD C q = P).card : ℕ) : ℝ) ≤
   ((N / (S.aR * P) : ℕ) : ℝ) *
    Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
    Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
 classical
 let T : Finset ℕ := (S.aY C).filter fun q => cD C q = P
 let dP : ℕ := S.aR * P
 let quotient : ℕ → ℕ := fun q => q / dP
 have ada : 0 < dP := by
  dsimp [dP]
  exact Nat.mul_pos S.jZ (S.vW hP)
 have hWle : S.W + C.card ≤ D.K := by
  have hcard := S.z4 hP
  have hWK := S.Nu
  omega
 have hinj : Set.InjOn quotient T := by
  intro q hq r hr hqr
  have hq_dvd : dP ∣ q := by
   dsimp [dP]
   exact S.kT (by simpa [T] using hq)
  have ajU : dP ∣ r := by
   dsimp [dP]
   exact S.kT (by simpa [T] using hr)
  calc
   q = quotient q * dP := (Nat.div_mul_cancel hq_dvd).symm
   _ = quotient r * dP := by rw [hqr]
   _ = r := Nat.div_mul_cancel ajU
 have hsubset :
   T.image quotient ⊆
    (Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card)) := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨q, hqT, rfl⟩
  have ag2 : q ∈ (S.aY C).filter fun q => cD C q = P := by
   simpa [T] using hqT
  have Nw : q ∈ S.aY C := (Finset.mem_filter.1 ag2).1
  have lX : q ∈ S.gQ := S.gT C Nw
  have qZ : q ∈ D.Q := S.iE lX
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q qZ).1
  have XD : q ≠ 0 := hqpos.ne'
  have hdvd : dP ∣ q := by
   dsimp [dP]
   exact S.kT ag2
  have hdisj : Disjoint (aD dP) (aD (q / dP)) := by
   rw [Finset.disjoint_left]
   intro p hp ak1
   exact S.lH ag2 p (by simpa [dP] using hp)
    (by simpa [dP] using ak1)
  have yF :
    omega (q / dP) = D.K - (S.W + C.card) := by
   calc
    omega (q / dP) = omega q - omega dP :=
     xG hdvd ada.ne' XD hdisj
    _ = D.K - (S.W + C.card) := by
     rw [D.L9 q qZ, show omega dP = S.W + C.card by
      dsimp [dP]
      exact S.z5 hP]
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hdvd) ada),
   Nat.div_le_div_right (D.q6 q qZ)⟩, yF⟩
 have hcard : T.card ≤
   ((Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card))).card := by
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsubset
 have hcount := lD (N / dP) D.K (S.W + C.card) (Nat.div_le_self N dP) hWle D.yD
 dsimp only at hcount
 have hfloor :
   T.card ≤ Nat.floor
    (((N / dP : ℕ) : ℝ) *
     Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
     Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
      Real.log (Real.log (N : ℝ)))) :=
  hcard.trans hcount
 simpa [T, dP] using vP (by positivity) hfloor
lemma aE.zH
  {N : ℕ} {D : bC N} (S : aE N D)
  {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.cZ C) (ε : ℝ)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  ((((S.aY C).filter fun q => cD C q = P).card : ℕ) : ℝ) ≤
   ((N : ℝ) / (S.aR * P : ℝ)) *
    Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
    Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
 have hdiv := S.vT hP ε lD
 have hquot :
   ((N / (S.aR * P) : ℕ) : ℝ) ≤ (N : ℝ) / (S.aR * P : ℝ) :=
  by
   simpa [Nat.cast_mul] using
    (Nat.cast_div_le (m := N) (n := S.aR * P) : ((N / (S.aR * P) : ℕ) : ℝ) ≤
     (N : ℝ) / ((S.aR * P : ℕ) : ℝ))
 have ML :
   0 ≤ Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
    Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  positivity
 calc
  ((((S.aY C).filter fun q => cD C q = P).card : ℕ) : ℝ)
    ≤ ((N / (S.aR * P) : ℕ) : ℝ) *
      Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
      Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
       Real.log (Real.log (N : ℝ))) := hdiv
  _ = ((N / (S.aR * P) : ℕ) : ℝ) *
      (Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
       Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
        Real.log (Real.log (N : ℝ)))) := by ring
  _ ≤ ((N : ℝ) / (S.aR * P : ℝ)) *
      (Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
       Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
        Real.log (Real.log (N : ℝ)))) := by
     exact mul_le_mul_of_nonneg_right hquot ML
  _ = ((N : ℝ) / (S.aR * P : ℝ)) *
      Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
      Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
       Real.log (Real.log (N : ℝ))) := by ring
lemma aE.OJ {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : S.W + C.card ≤ D.K := by
 have hcard := S.z4 hP
 have hW := S.Nu
 omega
lemma aE.Sm {N : ℕ} {D : bC N}
  (S : aE N D) (hW : S.W = D.K) {q : ℕ} (hq : q ∈ S.gQ) :
  S.aR = q := by
 have qZ : q ∈ D.Q := S.iE hq
 have ag3 : q / S.aR ≠ 0 := (S.Cz hq).ne'
 have ag4 : (dY S.aR q).card = 0 := by
  rw [S.lC hq, hW]
  simp
 have yF : omega (q / S.aR) = 0 := by
  simpa [dY, omega] using ag4
 have hquot : q / S.aR = 1 := vH ag3 yF
 have hdiv := Nat.div_mul_cancel (S.iW q hq)
 calc
  S.aR = 1 * S.aR := by simp
  _ = q / S.aR * S.aR := by rw [hquot]
  _ = q := hdiv
lemma aE.Qo {N : ℕ} {D : bC N}
  (S : aE N D) (hW : S.W = D.K) :
  (N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) := by
 rcases S.zF with ⟨q, hq⟩
 have qZ : q ∈ D.Q := S.iE hq
 have hpq := S.Sm hW hq
 rw [hpq]
 exact D.Bk q qZ
lemma aE.QV {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : (P :: S.blocks).Pairwise Nat.Coprime := by
 rw [List.pairwise_cons]
 constructor
 ·intro B hB
  exact Nat.Coprime.of_dvd_right (S.Wd hB)
   (S.jO hP).symm
 ·exact S.A9
lemma aE.XF {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ} {wJ : Finset ℕ}
  (hP : P ∈ S.cZ C)
  (KX : wJ.Nonempty)
  (pL : wJ ⊆ (S.aY C).filter fun q => cD C q = P)
  (Ue :
   ∀ qi ∈ wJ, ∀ rj ∈ wJ,
    ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
     D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) :
  ∃ S' : aE N D,
   S'.blocks = P :: S.blocks ∧ S'.r = S.r + 1 ∧ S'.aR = P * S.aR ∧
    S'.gQ = wJ ∧ S'.W = S.W + C.card := by
 classical
 refine ⟨{
  r := S.r + 1
  blocks := P :: S.blocks
  blocks_length := by simp [S.blocks_length]
  gQ := wJ
  iE := ?_
  zF := KX
  W := S.W + C.card
  aR := P * S.aR
  A8 := by simp [S.A8]
  blocks_pos := ?_
  jZ := ?_
  A9 := S.QV hP
  iW := ?_
  ow := ?_
  EY := ?_
  XC := ?_
  Nu := S.OJ hP
 }, rfl, rfl, rfl, rfl, rfl⟩
 ·intro q hq
  exact S.iE (S.gT C
   (Finset.mem_filter.1 (pL hq)).1)
 ·intro B hB
  rw [List.mem_cons] at hB
  cases hB with
  | inl h =>
    subst B
    exact S.vW hP
  | inr h => exact S.blocks_pos B h
 ·exact mul_pos (S.vW hP) S.jZ
 ·intro q hq
  have Wa := pL hq
  have hdvd := S.kT Wa
  simpa [Nat.mul_comm] using hdvd
 ·intro q hq p hp
  have Wa := pL hq
  have hno := S.lH Wa p
  simpa [Nat.mul_comm] using hno (by simpa [Nat.mul_comm] using hp)
 ·intro qi hqi rj hrj Qr Qt
  have ail : qi ∈ S.aY C :=
   (Finset.mem_filter.1 (pL hqi)).1
  have aio : rj ∈ S.aY C :=
   (Finset.mem_filter.1 (pL hrj)).1
  have aip : qi ∈ S.gQ := S.gT C ail
  have aiq : rj ∈ S.gQ := S.gT C aio
  have amm := S.EY qi aip rj aiq Qr Qt
  have hNew := Ue qi hqi rj hrj Qr Qt
  have air : (S.aR : ℤ).natAbs.Coprime (P : ℤ).natAbs := by
   simpa using S.jO hP
  have ak2 :
    D.a ⟨qi, Qr⟩ ≡ D.a ⟨rj, Qt⟩ [ZMOD (S.aR : ℤ)] ∧
    D.a ⟨qi, Qr⟩ ≡ D.a ⟨rj, Qt⟩ [ZMOD (P : ℤ)] := ⟨amm, hNew⟩
  have hMul := (Int.modEq_and_modEq_iff_modEq_mul air).1 ak2
  simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
 ·rw [Nat.mul_comm]
  exact (S.z5 hP).symm
lemma aE.Qv {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) :
  ∃ wJ : Finset ℕ,
   wJ.Nonempty ∧
   wJ ⊆ ((S.aY C).filter fun q => cD C q = P) ∧
   (∀ qi ∈ wJ, ∀ rj ∈ wJ,
    ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
     D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) ∧
   (((S.aY C).filter fun q => cD C q = P).card : ℝ) /
     (P : ℝ) ≤ (wJ.card : ℝ) := by
 classical
 let T : Finset ℕ := (S.aY C).filter fun q => cD C q = P
 let residue : ℕ → ZMod P :=
  fun q => if hq : q ∈ D.Q then (D.a ⟨q, hq⟩ : ZMod P) else 0
 have hPpos : 0 < P := S.vW hP
 haveI : NeZero P := ⟨hPpos.ne'⟩
 have Yq : T.Nonempty := by
  dsimp [T]
  rw [aE.cZ] at hP
  exact Nr (S := S.aY C)
   (B := fun q => cD C q) hP
 rcases LJ T P residue Yq with ⟨b, hb⟩
 let wJ : Finset ℕ := T.filter fun q => residue q = b
 refine ⟨wJ, ?_, ?_, ?_, ?_⟩
 ·have Uh : 0 < (T.card : ℝ) / (P : ℝ) := by
   have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast Yq.card_pos
   have ajV : 0 < (P : ℝ) := by exact_mod_cast hPpos
   exact div_pos hTcard ajV
  have Wi : 0 < (wJ.card : ℝ) := lt_of_lt_of_le Uh hb
  exact Finset.card_pos.1 (by exact_mod_cast Wi)
 ·intro q hq
  exact (Finset.mem_filter.1 hq).1
 ·intro qi hqi rj hrj Qr Qt
  have aec : residue qi = b := (Finset.mem_filter.1 hqi).2
  have aed : residue rj = b := (Finset.mem_filter.1 hrj).2
  have ais : ((D.a ⟨qi, Qr⟩ : ℤ) : ZMod P) = b := by
   simpa [residue, Qr] using aec
  have ait : ((D.a ⟨rj, Qt⟩ : ℤ) : ZMod P) = b := by
   simpa [residue, Qt] using aed
  have hcast : ((D.a ⟨qi, Qr⟩ : ℤ) : ZMod P) =
    ((D.a ⟨rj, Qt⟩ : ℤ) : ZMod P) := ais.trans ait.symm
  exact (ZMod.intCast_eq_intCast_iff
   (D.a ⟨qi, Qr⟩) (D.a ⟨rj, Qt⟩) P).1 hcast
 ·simpa [T, wJ] using hb
lemma aE.OL {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) :
  ∃ S' : aE N D,
   S'.blocks = P :: S.blocks ∧
   S'.r = S.r + 1 ∧
   S'.aR = P * S.aR ∧
   S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P) ∧
   S'.gQ.card ≤ ((S.aY C).filter fun q => cD C q = P).card ∧
   S'.W = S.W + C.card ∧
   (((S.aY C).filter fun q => cD C q = P).card : ℝ) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ) := by
 rcases S.Qv hP with
  ⟨wJ, KX, pL, Ue, hcard⟩
 rcases S.XF hP KX pL Ue with
  ⟨S', o8, hr, hprod, afC, hW⟩
 have hsubset : S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P) := by
  intro q hq
  rw [afC] at hq
  exact pL hq
 exact ⟨S', o8, hr, hprod, hsubset, Finset.card_le_card hsubset, hW,
  by simpa [afC] using hcard⟩
lemma aE.FH {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ}
  (gG : (S.aY C).Nonempty) :
  ∃ P : ℕ, ∃ S' : aE N D,
   P ∈ S.cZ C ∧
   S'.blocks = P :: S.blocks ∧
   S'.r = S.r + 1 ∧
   S'.aR = P * S.aR ∧
   S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P) ∧
   S'.gQ.card ≤ ((S.aY C).filter fun q => cD C q = P).card ∧
   S'.W = S.W + C.card ∧
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ) ∧
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ) := by
 rcases S.JH C gG with ⟨P, hP, afD⟩
 rcases S.OL hP with
  ⟨S', o8, hr, hprod, DA, Ny, hW, hcard⟩
 refine ⟨P, S', hP, o8, hr, hprod, DA, Ny, hW, afD, ?_⟩
 have aaq : 0 ≤ (P : ℝ) := by positivity
 have aee :
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤
    ((((S.aY C).filter fun q => cD C q = P).card : ℝ) /
     (P : ℝ)) := by
  exact div_le_div_of_nonneg_right afD aaq
 exact aee.trans hcard
lemma aE.zK {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) :
  S.cZ C ⊆
   (Finset.Icc 1 N).filter (fun n => omega n = C.card) := by
 intro B hB
 rw [aE.cZ] at hB
 rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
 have lX : q ∈ S.gQ := S.gT C hq
 have qZ : q ∈ D.Q := S.iE lX
 have Wj :
   cD C q ≤ q / S.aR :=
  Nat.le_of_dvd (S.Cz lX) (S.oL hq)
 have acQ : cD C q ≤ N := by
  exact Wj.trans ((Nat.div_le_self q S.aR).trans (D.q6 q qZ))
 rw [Finset.mem_filter, Finset.mem_Icc]
 exact ⟨⟨Nat.succ_le_of_lt (S.w8 hq), acQ⟩,
  S.DY hq⟩
lemma aE.Sz {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : P ≤ N := by
 have hmem := S.zK C hP
 exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hmem).1).2
lemma aE.Uj {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) :
  (cQ P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
 have lX : q ∈ S.gQ := S.gT C hq
 have qZ : q ∈ D.Q := S.iE lX
 have Zw : cQ (cD C q) ≤ cQ q := QD C q
 have XE : (cQ (cD C q) : ℝ) ≤ (cQ q : ℝ) := by
  exact_mod_cast Zw
 exact XE.trans (D.Ee q qZ)
lemma aE.JK {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ}
  (gG : (S.aY C).Nonempty) : C.card ≤ D.K := by
 rcases gG with ⟨q, hq⟩
 have hle := Finset.card_le_card (S.jD hq)
 have heq := S.lC (S.gT C hq)
 omega
lemma aE.OO {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ}
  (gG : (S.aY C).Nonempty) :
  (C.card : ℝ) ≤ 3 * aO N := by
 have hCK : (C.card : ℝ) ≤ (D.K : ℝ) := by
  exact_mod_cast S.JK gG
 exact hCK.trans D.yD
lemma aE.FU {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) (ε : ℝ)
  (gG : (S.aY C).Nonempty)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  (S.cZ C).card ≤
   Nat.floor
    ((N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N)) := by
 have hsubset := S.zK C
 have hcard : (S.cZ C).card ≤
   ((Finset.Icc 1 N).filter (fun n => omega n = C.card)).card :=
  Finset.card_le_card hsubset
 have hcount := lD N C.card 0 le_rfl (Nat.zero_le _) (S.OO gG)
 dsimp only at hcount
 have ak3 :
   Nat.floor
    ((N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N)
     * Real.exp (((0 : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) =
   Nat.floor
    ((N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N)) := by
  simp
 exact hcard.trans (by simpa [ak3] using hcount)
lemma aE.BT {N : ℕ} {D : bC N}
  (S : aE N D) (C : Finset ℕ) (ε : ℝ)
  (gG : (S.aY C).Nonempty)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  ((S.cZ C).card : ℝ) ≤
   (N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N) := by
 apply vP
 ·positivity
 ·exact S.FU C ε gG lD
lemma aE.KY {N : ℕ} {D : bC N}
  (S : aE N D) :
  jN S.cO (D.K - S.W) := by
 intro A hA
 rw [aE.cO] at hA
 rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
 exact S.lC hq
lemma aE.E4 {N : ℕ} {D : bC N}
  (S : aE N D) :
  ∀ A ∈ S.cO, ∀ B ∈ S.cO,
   A ≠ B → ¬ Disjoint A B := by
 intro A hA B hB hAB
 rw [aE.cO] at hA hB
 rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
 rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
 exact S.EZ hq hr (by
  intro hqr
  subst r
  exact hAB rfl)
lemma aE.BU {N : ℕ} {D : bC N}
  (S : aE N D) (wL : S.W < D.K) : 1 ≤ D.K - S.W := by
 omega
lemma aE.Jg {N : ℕ} {D : bC N}
  (S : aE N D) : D.K - S.W ≤ D.K :=
 Nat.sub_le D.K S.W
lemma aE.DZ {N : ℕ} {D : bC N}
  (S : aE N D) (wL : S.W < D.K) :
  S.cO.Nonempty ∧
   1 ≤ D.K - S.W ∧
   D.K - S.W ≤ D.K ∧
   jN S.cO (D.K - S.W) ∧
   (∀ A ∈ S.cO, ∀ B ∈ S.cO,
    A ≠ B → ¬ Disjoint A B) :=
 ⟨S.JG,
  S.BU wL,
  S.Jg,
  S.KY,
  S.E4⟩
noncomputable def mD : ℝ :=
 Classical.choose (w7.{0})
lemma zL : 0 < mD :=
 (Classical.choose_spec (w7.{0})).1
lemma Jh
  (A : Finset (Finset ℕ)) (k K : ℕ) :
  A.Nonempty →
  1 ≤ k → k ≤ K →
  jN A k →
  (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
  ∃ C : Finset ℕ,
   C.Nonempty ∧
   ((A.filter fun S => C ⊆ S).card : ℝ) >
    (A.card : ℝ) /
     (mD * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card :=
 (Classical.choose_spec (w7.{0})).2 A k K
noncomputable def jz {N : ℕ} (D : bC N) : ℝ :=
 mD * Real.log (Real.exp 1 * (D.K : ℝ))
noncomputable def cW {N : ℕ} (D : bC N) : ℝ :=
 2 * jz D
lemma E5 {N : ℕ} (D : bC N) : 0 < jz D := by
 have ajW : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
 have aiu : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
  nlinarith [Real.exp_pos 1, ajW]
 have acR : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
  have hlog := Real.log_le_log (Real.exp_pos 1) aiu
  simpa using hlog
 exact mul_pos zL (zero_lt_one.trans_le acR)
lemma wM {N : ℕ} (D : bC N) : 0 < cW D := by
 dsimp [cW]
 exact mul_pos (by norm_num) (E5 D)
lemma aE.JL {N : ℕ} {D : bC N}
  (S : aE N D) (wL : S.W < D.K) :
  ∃ C : Finset ℕ,
   C.Nonempty ∧
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card := by
 rcases S.DZ wL with
  ⟨hA, hk, hkK, j7, T9⟩
 rcases Jh S.cO (D.K - S.W) D.K
   hA hk hkK j7 T9 with ⟨C, hC⟩
 exact ⟨C, by simpa [jz] using hC⟩
lemma aE.zV
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ}
  (hpos : 0 < (((S.cO.filter fun A => C ⊆ A).card : ℕ) : ℝ)) :
  (S.aY C).Nonempty := by
 have acS : 0 < (S.cO.filter fun A => C ⊆ A).card := by
  exact_mod_cast hpos
 have hle := S.kJ C
 have aef : 0 < (S.aY C).card := lt_of_lt_of_le acS hle
 exact Finset.card_pos.1 aef
lemma aE.wN
  {N : ℕ} {D : bC N} (S : aE N D) (wL : S.W < D.K) :
  ∃ C : Finset ℕ,
   C.Nonempty ∧ (S.aY C).Nonempty ∧
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card := by
 rcases S.JL wL with ⟨C, hC, hbound⟩
 have abJ : 0 ≤ jz D := (E5 D).le
 have acT :
   0 ≤ (S.cO.card : ℝ) / (jz D) ^ C.card := by
  exact div_nonneg (by positivity) (pow_nonneg abJ _)
 have hpos : 0 < (((S.cO.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
  lt_of_le_of_lt acT hbound
 exact ⟨C, hC, S.zV hpos, hbound⟩
lemma aE.D4
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ} {A : ℝ}
  (hbound : A < ((S.cO.filter fun B => C ⊆ B).card : ℝ)) :
  A < ((S.aY C).card : ℝ) := by
 have hle : ((S.cO.filter fun B => C ⊆ B).card : ℝ) ≤
   ((S.aY C).card : ℝ) := by
  exact_mod_cast S.kJ C
 exact hbound.trans_le hle
lemma aE.lY
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ} {Λ : ℝ}
  (hbound :
   ((S.cO.card : ℝ) / Λ ^ C.card) <
    ((S.cO.filter fun B => C ⊆ B).card : ℝ)) :
  ((S.gQ.card : ℝ) / Λ ^ C.card) <
   ((S.aY C).card : ℝ) := by
 have h := S.D4 hbound
 simpa [S.KV] using h
lemma aE.D6
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ}
  (gG : (S.aY C).Nonempty) : (S.cZ C).Nonempty := by
 rw [aE.cZ]
 exact gG.image _
lemma aE.CY
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ}
  (gG : (S.aY C).Nonempty) :
  0 < ∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2) := by
 exact Finset.sum_pos (fun B _hB => Ra B)
  (S.D6 gG)
lemma aE.qB
  {N : ℕ} {D : bC N} (S : aE N D) {C : Finset ℕ}
  (hC : C.Nonempty) :
  (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
   (2 : ℝ) ^ C.card := by
 classical
 let Index := {p : ℕ // p ∈ C}
 let E : Finset (Index → ℕ) :=
  Fintype.piFinset fun _ : Index => Finset.range N
 let vec : ℕ → Index → ℕ := fun B p => B.factorization p.1 - 1
 let term : (Index → ℕ) → ℝ :=
  fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
 have Xj : ∀ B ∈ S.cZ C, vec B ∈ E := by
  intro B hB
  rw [Fintype.mem_piFinset]
  intro p
  rw [Finset.mem_range]
  have hsupport : aD B = C := S.oz hB
  have gX : p.1 ∈ aD B := by
   simp [hsupport, p.2]
  have Xh : B ≠ 0 := by
   intro hzero
   subst B
   simp [aD] at gX
  have aaI : 1 ≤ B.factorization p.1 := by
   unfold aD at gX
   exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
  have alz : B.factorization p.1 ≤ N := by
   exact (Nat.factorization_lt p.1 Xh).le.trans (S.Sz hB)
  dsimp [vec]
  omega
 have Xk : Set.InjOn vec (S.cZ C) := by
  intro B hB R hR hBR
  have Wk : aD B = C := S.oz hB
  have Wm : aD R = C := S.oz hR
  have Xh : B ≠ 0 := by
   rcases hC with ⟨p, hp⟩
   have gX : p ∈ aD B := by simpa [Wk] using hp
   intro hzero
   subst B
   simp [aD] at gX
  have amn : R ≠ 0 := by
   rcases hC with ⟨p, hp⟩
   have gX : p ∈ aD R := by simpa [Wm] using hp
   intro hzero
   subst R
   simp [aD] at gX
  apply Nat.eq_of_factorization_eq Xh amn
  intro p
  by_cases hp : p ∈ C
  ·have aaK := congrFun hBR ⟨p, hp⟩
   dsimp [vec] at aaK
   have Om : 1 ≤ B.factorization p := by
    have gX : p ∈ aD B := by simpa [Wk] using hp
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   have Yr : 1 ≤ R.factorization p := by
    have gX : p ∈ aD R := by simpa [Wm] using hp
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   omega
  ·have hpB : p ∉ aD B := by simpa [Wk] using hp
   have hpR : p ∉ aD R := by simpa [Wm] using hp
   rw [Finsupp.notMem_support_iff.1 hpB, Finsupp.notMem_support_iff.1 hpR]
 have Xl :
   ∀ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2) = term (vec B) := by
  intro B hB
  have hsupport : aD B = C := S.oz hB
  have adq :
    cQ B = ∏ p : Index, B.factorization p.1 := by
   calc
    cQ B = ∏ p ∈ C, B.factorization p := by
     simp [cQ, hsupport]
    _ = ∏ p : Index, B.factorization p.1 := by
     rw [Finset.prod_coe_sort]
  have hsucc : ∀ p : Index, vec B p + 1 = B.factorization p.1 := by
   intro p
   have gX : p.1 ∈ aD B := by simp [hsupport, p.2]
   have hpos : 1 ≤ B.factorization p.1 := by
    unfold aD at gX
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 gX))
   dsimp [vec]
   omega
  rw [adq, U6]
  dsimp [term]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [hsucc p]
 calc
  (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))
    = ∑ B ∈ S.cZ C, term (vec B) := by
      apply Finset.sum_congr rfl
      intro B hB
      exact Xl B hB
  _ = ∑ e ∈ (S.cZ C).image vec, term e := by
      rw [Finset.sum_image]
      intro B hB R hR hEq
      exact Xk hB hR hEq
  _ ≤ ∑ e ∈ E, term e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
       (by
        intro e he
        rcases Finset.mem_image.mp he with ⟨B, hB, rfl⟩
        exact Xj B hB)
       (by
        intro e alD aiU
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
        simpa [Nat.cast_add, Nat.cast_one] using QS N)
  _ = (2 : ℝ) ^ C.card := by
      simp [Index]
noncomputable def jg : List ℕ → ℕ
 | [] => 0
 | _P :: Ps => omega (Ps.foldr (· * ·) 1) + jg Ps
noncomputable def dV {N : ℕ} {D : bC N} (S : aE N D) : ℕ :=
 jg S.blocks
private lemma zO
  (blocks : List ℕ) (hpos : ∀ P ∈ blocks, 0 < P) :
  jg blocks ≤ blocks.length * omega (blocks.foldr (· * ·) 1) := by
 induction blocks with
 | nil =>
   simp [jg, omega, aD]
 | cons P Ps ih =>
   simp only [jg, List.foldr_cons, List.length_cons]
   have adb : ∀ B ∈ Ps, 0 < B := by
    intro B hB
    exact hpos B (by simp [hB])
   have Uz :
     omega (Ps.foldr (· * ·) 1) ≤ omega (P * Ps.foldr (· * ·) 1) := by
    apply XZ
    ·exact dvd_mul_left (Ps.foldr (· * ·) 1) P
    ·exact (Nat.mul_pos (hpos P (by simp)) (List.aap adb)).ne'
   calc
    omega (Ps.foldr (· * ·) 1) + jg Ps
      ≤ omega (P * Ps.foldr (· * ·) 1) +
        Ps.length * omega (Ps.foldr (· * ·) 1) := by
       exact Nat.add_le_add Uz (ih adb)
    _ ≤ omega (P * Ps.foldr (· * ·) 1) +
        Ps.length * omega (P * Ps.foldr (· * ·) 1) := by
       exact Nat.add_le_add_left
        (Nat.mul_le_mul_left Ps.length Uz) _
    _ = (Ps.length + 1) * omega (P * Ps.foldr (· * ·) 1) := by
       rw [Nat.add_mul, Nat.one_mul]
       omega
private lemma vq
  (blocks : List ℕ)
  (hpair : blocks.Pairwise Nat.Coprime)
  (Yt : ∀ P ∈ blocks, 1 ≤ omega P) :
  (((jg blocks + omega (blocks.foldr (· * ·) 1) : ℕ) : ℝ) * 2) ≤
   2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
    (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
 induction blocks with
 | nil =>
   simp [jg, omega, aD]
 | cons P Ps ih =>
   rw [List.pairwise_cons] at hpair
   have ag5 : Ps.Pairwise Nat.Coprime := hpair.2
   have afE : ∀ B ∈ Ps, 1 ≤ omega B := by
    intro B hB
    exact Yt B (by simp [hB])
   have aiv : 1 ≤ omega P := Yt P (by simp)
   have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
    List.Nt hpair.1
   have yF :
     omega (P * Ps.foldr (· * ·) 1) =
      omega P + omega (Ps.foldr (· * ·) 1) :=
    Kh hcop
   have hih := ih ag5 afE
   have abK : (1 : ℝ) ≤ (omega P : ℝ) := by
    exact_mod_cast aiv
   have acU : 0 ≤ (Ps.length : ℝ) := by positivity
   simp only [jg, List.foldr_cons, List.length_cons]
   rw [yF]
   norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
   nlinarith [hih, abK, acU]
lemma aE.WT {N : ℕ} {D : bC N}
  (S : aE N D) :
  dV S ≤ S.r * S.W := by
 have h := zO S.blocks S.blocks_pos
 simpa [dV, S.blocks_length, ← S.A8, S.XC] using h
lemma aE.WV {N : ℕ} {D : bC N}
  (S : aE N D) :
  dV S ≤ S.r * D.K := by
 exact (S.WT).trans (Nat.mul_le_mul_left S.r S.Nu)
lemma aE.G8 {N : ℕ} {D : bC N}
  (S : aE N D) (o8 : S.gI) :
  ((((dV S + S.W : ℕ) : ℝ) * 2)) ≤
   2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
 have h := vq
  S.blocks S.A9 o8
 simpa [dV, S.blocks_length, ← S.A8, S.XC] using h
lemma aE.Zy {N : ℕ} {D : bC N}
  (S : aE N D) {P : ℕ} {S' : aE N D}
  (o8 : S'.blocks = P :: S.blocks) :
  dV S' = S.W + dV S := by
 calc
  dV S' = omega (S.blocks.foldr (· * ·) 1) + jg S.blocks := by
   simp [dV, o8, jg]
  _ = S.W + dV S := by
   rw [← S.A8, ← S.XC]
   rfl
noncomputable def jR {N : ℕ} {D : bC N}
  (Λ : ℝ) (S : aE N D) : ℝ :=
 (D.Q.card : ℝ) /
  ((S.aR : ℝ) * (cQ S.aR : ℝ) ^ 2 * Λ ^ S.W)
def aE.fD {N : ℕ} {D : bC N}
  (Λ : ℝ) (S : aE N D) : Prop :=
 jR Λ S ≤ (S.gQ.card : ℝ)
private lemma Nz
  {a q c w p h κ : ℝ} {n : ℕ}
  (D7 : 0 ≤ q) (K3 : 0 < w)
  (hp : 0 < p) (hh : 0 < h) (hκ : 0 < κ)
  (haq : a ≤ q) (hdense : q / κ ^ n < c) (Zz : w ≤ (2 : ℝ) ^ n) :
  a / (p * h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) / p := by
 have Yv : 0 < κ ^ n := pow_pos hκ _
 have ZD : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
 have Yw : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
 have aeg : q < c * κ ^ n := by
  have hmul := mul_lt_mul_of_pos_right hdense Yv
  rwa [div_mul_cancel₀ _ Yv.ne'] at hmul
 have abL : a * w ≤ q * (2 : ℝ) ^ n :=
  mul_le_mul haq Zz K3.le D7
 have htarget : a * w ≤ c * (2 * κ) ^ n := by
  calc
   a * w ≤ q * (2 : ℝ) ^ n := abL
   _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
      (mul_lt_mul_of_pos_right aeg ZD).le
   _ = c * (2 * κ) ^ n := by
      rw [mul_pow]
      ring
 calc
  a / (p * h * (2 * κ) ^ n)
    = (a * w) / ((p * h * (2 * κ) ^ n) * w) := by
      field_simp [K3.ne']
  _ ≤ (c * (2 * κ) ^ n) / ((p * h * (2 * κ) ^ n) * w) := by
      exact div_le_div_of_nonneg_right htarget
       (mul_nonneg
        (mul_nonneg (mul_pos hp hh).le Yw.le)
        K3.le)
  _ = (c * (1 / h) / w) / p := by
      field_simp [hp.ne', hh.ne', Yw.ne', K3.ne']
private lemma NA
  {a q c w h κ : ℝ} {n : ℕ}
  (D7 : 0 ≤ q) (K3 : 0 < w)
  (hh : 0 < h) (hκ : 0 < κ)
  (haq : a ≤ q) (hdense : q / κ ^ n < c) (Zz : w ≤ (2 : ℝ) ^ n) :
  a / (h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) := by
 have Yv : 0 < κ ^ n := pow_pos hκ _
 have ZD : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
 have Yw : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
 have aeg : q < c * κ ^ n := by
  have hmul := mul_lt_mul_of_pos_right hdense Yv
  rwa [div_mul_cancel₀ _ Yv.ne'] at hmul
 have abL : a * w ≤ q * (2 : ℝ) ^ n :=
  mul_le_mul haq Zz K3.le D7
 have htarget : a * w ≤ c * (2 * κ) ^ n := by
  calc
   a * w ≤ q * (2 : ℝ) ^ n := abL
   _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
      (mul_lt_mul_of_pos_right aeg ZD).le
   _ = c * (2 * κ) ^ n := by
      rw [mul_pow]
      ring
 calc
  a / (h * (2 * κ) ^ n)
    = (a * w) / ((h * (2 * κ) ^ n) * w) := by
      field_simp [K3.ne']
  _ ≤ (c * (2 * κ) ^ n) / ((h * (2 * κ) ^ n) * w) := by
      exact div_le_div_of_nonneg_right htarget
       (mul_nonneg (mul_pos hh Yw).le K3.le)
  _ = c * (1 / h) / w := by
      field_simp [hh.ne', Yw.ne', K3.ne']
lemma aE.E9
  {N : ℕ} {D : bC N} (S : aE N D)
  {Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : aE N D}
  (hP : P ∈ S.cZ C)
  (hprod : S'.aR = P * S.aR)
  (hW : S'.W = S.W + C.card) :
  jR Λ S' =
   jR Λ S / ((P : ℝ) * (cQ P : ℝ) ^ 2 * Λ ^ C.card) := by
 rw [jR, jR, hprod, hW,
  u6 (S.jO hP).symm, pow_add]
 norm_num [Nat.cast_mul]
 ring_nf
lemma aE.K5
  {N : ℕ} {D : bC N} (S : aE N D)
  {κ Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : aE N D}
  (hκ : 0 < κ) (hΛ : Λ = 2 * κ)
  (hP : P ∈ S.cZ C)
  (o7 : S.fD Λ)
  (D8 :
   ((S.gQ.card : ℝ) / κ ^ C.card) <
    ((S.aY C).card : ℝ))
  (OT :
   (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (2 : ℝ) ^ C.card)
  (XS :
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ))
  (hprod : S'.aR = P * S.aR)
  (hW : S'.W = S.W + C.card) :
  S'.fD Λ := by
 rw [aE.fD]
 rw [S.E9 hP hprod hW, hΛ]
 have gG : (S.aY C).Nonempty := by
  have aay := hP
  rw [aE.cZ] at aay
  rcases Finset.mem_image.mp aay with ⟨q, hq, _hP⟩
  exact ⟨q, hq⟩
 have RM :
   0 < ∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2) :=
  S.CY gG
 have acV : 0 < (P : ℝ) := by
  exact_mod_cast S.vW hP
 have Wn : 0 < (cQ P : ℝ) := by exact_mod_cast Dp P
 have abM : 0 < ((cQ P : ℝ) ^ 2) := sq_pos_of_pos Wn
 have D7 : 0 ≤ (S.gQ.card : ℝ) := by positivity
 have hstep :
   jR (2 * κ) S /
     ((P : ℝ) * ((cQ P : ℝ) ^ 2) * (2 * κ) ^ C.card) ≤
    (((S.aY C).card : ℝ) *
      ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) :=
  Nz
   D7 RM acV abM hκ
   (by simpa [aE.fD, hΛ] using o7)
   D8 OT
 exact hstep.trans XS
lemma aE.F3
  {N : ℕ} {D : bC N} (S : aE N D)
  {C : Finset ℕ} {P : ℕ}
  (K6 : C.Nonempty)
  (hP : P ∈ S.cZ C)
  (o7 : S.fD (cW D))
  (D8 :
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card)
  (MO :
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ)) :
  (D.Q.card : ℝ) /
    ((S.aR : ℝ) * (cQ (S.aR * P) : ℝ) ^ 2 *
     (cW D) ^ (S.W + C.card)) ≤
   (((S.aY C).filter fun q => cD C q = P).card : ℝ) := by
 have gG : (S.aY C).Nonempty := by
  rw [aE.cZ] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, _hP⟩
  exact ⟨q, hq⟩
 have ZE :
   ((S.gQ.card : ℝ) / (jz D) ^ C.card) <
    ((S.aY C).card : ℝ) :=
  S.lY (Λ := jz D)
   (by simpa using D8)
 have OT :
   (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (2 : ℝ) ^ C.card :=
  S.qB K6
 have RM :
   0 < ∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2) :=
  S.CY gG
 have Wn : 0 < (cQ P : ℝ) := by exact_mod_cast Dp P
 have abM : 0 < ((cQ P : ℝ) ^ 2) := sq_pos_of_pos Wn
 have D7 : 0 ≤ (S.gQ.card : ℝ) := by positivity
 have hstep :
   jR (2 * jz D) S /
     (((cQ P : ℝ) ^ 2) * (2 * jz D) ^ C.card) ≤
    (((S.aY C).card : ℝ) *
      ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) :=
  NA
   D7 RM abM (E5 D)
   (by simpa [aE.fD, cW] using o7)
   ZE OT
 have ajX :
   jR (cW D) S /
     (((cQ P : ℝ) ^ 2) * (cW D) ^ C.card) ≤
    (((S.aY C).card : ℝ) *
      ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) := by
  simpa [cW] using hstep
 have hleft :
   jR (cW D) S /
     (((cQ P : ℝ) ^ 2) * (cW D) ^ C.card) =
    (D.Q.card : ℝ) /
     ((S.aR : ℝ) * (cQ (S.aR * P) : ℝ) ^ 2 *
      (cW D) ^ (S.W + C.card)) := by
  rw [jR,
   u6 (S.jO hP), pow_add]
  norm_num [Nat.cast_mul]
  ring_nf
 rw [← hleft]
 exact ajX.trans MO
lemma aE.JM
  {N : ℕ} {D : bC N} (S : aE N D)
  {C : Finset ℕ} {P : ℕ} {S' : aE N D}
  (q5 : S.gI)
  (K6 : C.Nonempty)
  (hP : P ∈ S.cZ C)
  (o8 : S'.blocks = P :: S.blocks) :
  S'.gI := by
 intro B hB
 rw [o8] at hB
 rcases List.mem_cons.1 hB with hBP | ajY
 ·subst B
  rw [S.Fj hP]
  exact Nat.succ_le_of_lt K6.card_pos
 ·exact q5 B ajY
noncomputable def i6 (N : ℕ) (D : bC N) : aE N D where
 r := 0
 blocks := []
 blocks_length := by simp
 gQ := D.Q
 iE := by intro q hq; exact hq
 zF := D.z6
 W := 0
 aR := 1
 A8 := by simp
 blocks_pos := by intro P hP; simp at hP
 jZ := by norm_num
 A9 := by simp
 iW := by intro q _hq; exact one_dvd q
 ow := by
  intro _q _hq _p hp
  simp [aD] at hp
 EY := by
  intro qi ang rj anh Qr Qt
  rw [Int.modEq_iff_dvd]
  exact one_dvd (D.a ⟨rj, Qt⟩ - D.a ⟨qi, Qr⟩)
 XC := by simp [omega, aD]
 Nu := by omega
lemma RO (N : ℕ) (D : bC N) :
  (i6 N D).W < D.K := by
 simp [i6]
 exact D.K_pos
lemma Jj (N : ℕ) (D : bC N) :
  (i6 N D).gI := by
 intro P hP
 simp [i6] at hP
lemma JN {N : ℕ} (D : bC N) (Λ : ℝ) :
  aE.fD Λ (i6 N D) := by
 rw [aE.fD, jR]
 simp [i6, SK]
theorem Dk
  {N : ℕ} {D : bC N} (S : aE N D)
  (wL : S.W < D.K)
  (o7 : S.fD (cW D)) :
  ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : aE N D,
   C.Nonempty ∧
   P ∈ S.cZ C ∧
   S'.blocks = P :: S.blocks ∧
   S'.r = S.r + 1 ∧
   S.W < S'.W ∧
   S'.aR = P * S.aR ∧
   S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P) ∧
   S'.gQ.card ≤ ((S.aY C).filter fun q => cD C q = P).card ∧
   S'.W = S.W + C.card ∧
   dV S' = S.W + dV S ∧
   S'.fD (cW D) ∧
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ) ∧
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ) ∧
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card := by
 rcases S.wN wL with
  ⟨C, K6, gG, D8⟩
 rcases S.FH gG with
  ⟨P, S', hP, o8, hr, hprod, DA, Ny, hW, abN, hcard⟩
 have Fd : S.W < S'.W := by
  rw [hW]
  exact Nat.lt_add_of_pos_right K6.card_pos
 have ZE :
   ((S.gQ.card : ℝ) / (jz D) ^ C.card) <
    ((S.aY C).card : ℝ) :=
  S.lY (Λ := jz D)
   (by simpa using D8)
 have OT :
   (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (2 : ℝ) ^ C.card :=
  S.qB K6
 have Jt : S'.fD (cW D) := by
  apply S.K5
   (κ := jz D) (Λ := cW D)
   (hκ := E5 D) (hΛ := by rfl)
   (hP := hP) (o7 := o7) (D8 := ZE)
   (OT := OT) (XS := hcard)
   (hprod := hprod) (hW := hW)
 exact ⟨C, P, S', K6, hP, o8, hr, Fd, hprod, DA, Ny, hW,
  S.Zy o8, Jt, abN, hcard, D8⟩
lemma aE.Fe {N : ℕ} {D : bC N}
  (S : aE N D) {C : Finset ℕ} {P : ℕ}
  (hP : P ∈ S.cZ C) : (S.aY C).Nonempty := by
 rw [aE.cZ] at hP
 rcases Finset.mem_image.mp hP with ⟨q, hq, _⟩
 exact ⟨q, hq⟩
theorem uY
  {N : ℕ} {D : bC N} (S : aE N D)
  (ε : ℝ)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
  (wL : S.W < D.K)
  (o7 : S.fD (cW D)) :
  ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : aE N D,
   C.Nonempty ∧
   P ∈ S.cZ C ∧
   S'.blocks = P :: S.blocks ∧
   S'.r = S.r + 1 ∧
   S.W < S'.W ∧
   S'.aR = P * S.aR ∧
   S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P) ∧
   S'.gQ.card ≤ ((S.aY C).filter fun q => cD C q = P).card ∧
   S'.W = S.W + C.card ∧
   dV S' = S.W + dV S ∧
   S'.fD (cW D) ∧
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ) ∧
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ) ∧
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card ∧
   ((S.aY C).card : ℝ) ≤
    (N : ℝ) * Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
     * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
   ((S.cZ C).card : ℝ) ≤
    (N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N) ∧
   P ≤ N ∧
   (cQ P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
 rcases Dk S wL o7 with
  ⟨C, P, S', K6, hP, o8, hr, Fd, hprod, DA, Ny,
   hW, hT, Jt, abN, afF, D8⟩
 have gG : (S.aY C).Nonempty := S.Fe hP
 exact ⟨C, P, S', K6, hP, o8, hr, Fd, hprod, DA, Ny,
  hW, hT, Jt,
  abN, afF, D8,
  S.zG C ε lD,
  S.BT C ε gG lD,
  S.Sz hP, S.Uj hP⟩
noncomputable def fq {N : ℕ} {D : bC N}
  (ε : ℝ) (_S S' : aE N D) : ℝ :=
 (N : ℝ) / (D.Q.card : ℝ)
  * Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
  * Real.exp (((S'.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
  * (cQ S'.aR : ℝ) ^ 2
  * (cW D) ^ S'.W
noncomputable def dD {N : ℕ} {D : bC N}
  (ε : ℝ) (S : aE N D) : ℝ :=
 ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
  * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
  * Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
  * Real.exp (2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)))
  * (cW D) ^ (dV S + S.W)
lemma JO {N : ℕ} {D : bC N}
  (ε : ℝ) (S S' : aE N D) : 0 ≤ fq ε S S' := by
 rw [fq]
 have hΛ : 0 ≤ cW D := (wM D).le
 positivity
lemma JQ {N : ℕ} {D : bC N}
  (ε : ℝ) (S : aE N D) :
  Real.log (dD ε S) =
   (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
    (S.r : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N +
    ((((dV S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
    2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
    ((dV S + S.W : ℕ) : ℝ) * Real.log (cW D) := by
 rw [dD]
 set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
 set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N
 set b : ℝ := (((dV S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))
 set c : ℝ := 2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ))
 set Λ : ℝ := cW D
 have hq_pos : 0 < q := by
  dsimp [q]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  positivity
 have ajZ : 0 < Λ := by
  dsimp [Λ]
  exact wM D
 have Uk : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
 have Um : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
 have XG : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
 have abO : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
 have ag6 : Λ ^ (dV S + S.W) ≠ 0 := pow_ne_zero _ ajZ.ne'
 rw [Real.log_mul
    (mul_ne_zero (mul_ne_zero (mul_ne_zero Uk Um) XG) abO)
    ag6,
   Real.log_mul (mul_ne_zero (mul_ne_zero Uk Um) XG) abO,
   Real.log_mul (mul_ne_zero Uk Um) XG,
   Real.log_mul Uk Um,
   Real.log_pow, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_pow]
lemma Bc {N : ℕ} (D : bC N) (ε : ℝ) :
  ((i6 N D).aR : ℝ) ≤
   dD ε (i6 N D) := by
 simp [dD, i6, dV, jg]
lemma uZ
  {N : ℕ} {D : bC N} {ε : ℝ} {S S' : aE N D}
  (hr : S'.r = S.r + 1)
  (hT : dV S' = S.W + dV S)
  (OP : (S.aR : ℝ) ≤ dD ε S)
  (hStep :
   (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S') :
  (S'.aR : ℝ) ≤ dD ε S' := by
 have abP : 0 ≤ fq ε S S' :=
  JO ε S S'
 have afG : (cQ S'.aR : ℝ) ≤
   Real.exp (Real.sqrt (Real.log (N : ℝ))) :=
  S'.U7
 have aj0 :
   (cQ S'.aR : ℝ) ^ 2 ≤
    Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
  have hnonneg : 0 ≤ (cQ S'.aR : ℝ) := by positivity
  calc
   (cQ S'.aR : ℝ) ^ 2
     ≤ (Real.exp (Real.sqrt (Real.log (N : ℝ)))) ^ 2 :=
      sq_le_sq₀ hnonneg (Real.exp_pos _).le |>.2 afG
   _ = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
      rw [sq, ← Real.exp_add]
      ring_nf
 calc
  (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S' := hStep
  _ ≤ dD ε S * fq ε S S' := by
     exact mul_le_mul_of_nonneg_right OP abP
  _ ≤ dD ε S' := by
     rw [dD, fq,
      dD, hr, hT]
     set q : ℝ := (N : ℝ) / (D.Q.card : ℝ) with hq
     set a : ℝ := -((D.K : ℝ) / aO N) / 2 + ε with ha
     set l : ℝ := Real.log (Real.log (N : ℝ)) with hl
     set u : ℝ := Real.sqrt (Real.log (N : ℝ)) with hu
     have ag7 : 0 ≤ cW D := (wM D).le
     calc
      (q ^ S.r * Real.exp ((S.r : ℝ) * a * aZ N) *
         Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * l) *
         Real.exp (2 * (S.r : ℝ) * u) *
         (cW D) ^ (dV S + S.W)) *
        (q * Real.exp (a * aZ N) * Real.exp (((S'.W : ℝ) / 2) * l) *
         (cQ S'.aR : ℝ) ^ 2 * (cW D) ^ S'.W)
        ≤
       (q ^ S.r * Real.exp ((S.r : ℝ) * a * aZ N) *
         Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * l) *
         Real.exp (2 * (S.r : ℝ) * u) *
         (cW D) ^ (dV S + S.W)) *
        (q * Real.exp (a * aZ N) * Real.exp (((S'.W : ℝ) / 2) * l) *
         Real.exp (2 * u) * (cW D) ^ S'.W) := by
          exact mul_le_mul_of_nonneg_left
           (by
            exact mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_left aj0 (by positivity))
             (pow_nonneg ag7 _))
           (by positivity)
      _ = q ^ (S.r + 1) *
         Real.exp (((S.r + 1 : ℕ) : ℝ) * a * aZ N) *
         Real.exp ((((S.W + dV S + S'.W : ℕ) : ℝ) / 2) * l) *
         Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
         (cW D) ^ (S.W + dV S + S'.W) := by
          rw [pow_succ]
          calc
           (q ^ S.r * Real.exp ((S.r : ℝ) * a * aZ N) *
              Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * l) *
              Real.exp (2 * (S.r : ℝ) * u) *
              (cW D) ^ (dV S + S.W)) *
             (q * Real.exp (a * aZ N) *
              Real.exp (((S'.W : ℝ) / 2) * l) *
              Real.exp (2 * u) * (cW D) ^ S'.W)
             =
            q ^ S.r * q *
             (Real.exp ((S.r : ℝ) * a * aZ N) *
              Real.exp (a * aZ N)) *
             (Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * l) *
              Real.exp (((S'.W : ℝ) / 2) * l)) *
             (Real.exp (2 * (S.r : ℝ) * u) * Real.exp (2 * u)) *
             ((cW D) ^ (dV S + S.W) *
              (cW D) ^ S'.W) := by ring
           _ =
            q ^ S.r * q *
             Real.exp (((S.r + 1 : ℕ) : ℝ) * a * aZ N) *
             Real.exp ((((S.W + dV S + S'.W : ℕ) : ℝ) / 2) * l) *
             Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
             (cW D) ^ (S.W + dV S + S'.W) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
               ← pow_add]
              have hA :
                Real.exp ((S.r : ℝ) * a * aZ N + a * aZ N) =
                 Real.exp (((S.r + 1 : ℕ) : ℝ) * a * aZ N) := by
               congr 1
               norm_num
               ring
              have hL :
                Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) * l +
                  ((S'.W : ℝ) / 2) * l) =
                 Real.exp ((((S.W + dV S + S'.W : ℕ) : ℝ) / 2) *
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
theorem w9
  {N : ℕ} {D : bC N} (ε : ℝ)
  (hStep :
   ∀ S : aE N D,
    S.fD (cW D) →
    S.gI →
    S.W < D.K →
    ∃ S' : aE N D,
     S'.r = S.r + 1 ∧
     S.W < S'.W ∧
     dV S' = S.W + dV S ∧
     S'.fD (cW D) ∧
     S'.gI ∧
     (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S')
  (S : aE N D)
  (o7 : S.fD (cW D))
  (q5 : S.gI)
  (OP : (S.aR : ℝ) ≤ dD ε S) :
  ∃ qW : aE N D,
   S.r ≤ qW.r ∧
   qW.r ≤ S.r + (D.K - S.W) ∧
   qW.W = D.K ∧
   qW.fD (cW D) ∧
   qW.gI ∧
   (qW.aR : ℝ) ≤ dD ε qW := by
 classical
 let motive : ℕ → Prop := fun n =>
  ∀ S : aE N D,
   D.K - S.W = n →
   S.fD (cW D) →
   S.gI →
   (S.aR : ℝ) ≤ dD ε S →
   ∃ qW : aE N D,
    S.r ≤ qW.r ∧
    qW.r ≤ S.r + (D.K - S.W) ∧
    qW.W = D.K ∧
    qW.fD (cW D) ∧
    qW.gI ∧
    (qW.aR : ℝ) ≤ dD ε qW
 have hmain : ∀ n, motive n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn ade abQ afH
    by_cases aeh : S.W = D.K
    ·refine ⟨S, le_rfl, ?_, aeh, ade, abQ, afH⟩
     rw [aeh]
     simp
    ·have wL : S.W < D.K := lt_of_le_of_ne S.Nu aeh
     rcases hStep S ade abQ wL with
      ⟨S', hr, Fd, hT, Jt, XH, afI⟩
     have aj1 : (S'.aR : ℝ) ≤ dD ε S' :=
      uZ hr hT afH afI
     have hlt : D.K - S'.W < n := by
      rw [← hn]
      omega
     rcases ih (D.K - S'.W) hlt S' rfl Jt XH aj1 with
      ⟨qW, Wq, Uq, aiw, acW, abR,
       aei⟩
     refine ⟨qW, ?_, ?_, aiw, acW, abR, aei⟩
     ·have hstep : S.r ≤ S'.r := by
       rw [hr]
       omega
      exact hstep.trans Wq
     ·have Mv :
        S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
       rw [hr]
       omega
      exact Uq.trans Mv
 exact hmain (D.K - S.W) S rfl o7 q5 OP
theorem vV
  (N : ℕ) (D : bC N) (ε : ℝ)
  (hStep :
   ∀ S : aE N D,
    S.fD (cW D) →
    S.gI →
    S.W < D.K →
    ∃ S' : aE N D,
     S'.r = S.r + 1 ∧
     S.W < S'.W ∧
     dV S' = S.W + dV S ∧
     S'.fD (cW D) ∧
     S'.gI ∧
     (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S') :
  ∃ R : ℕ, ∃ S : aE N D,
   S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
   ((N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) ∨ S.W = D.K) ∧
   S.fD (cW D) ∧
   S.gI ∧
   (S.aR : ℝ) ≤ dD ε S := by
 let S0 := i6 N D
 have aj2 : S0.W < D.K := by
  simpa [S0] using RO N D
 have aix : S0.fD (cW D) := by
  simpa [S0] using JN D (cW D)
 have ag8 : S0.gI := by
  simpa [S0] using Jj N D
 have aj3 : (S0.aR : ℝ) ≤ dD ε S0 := by
  simpa [S0] using Bc D ε
 rcases hStep S0 aix ag8 aj2 with
  ⟨S1, hr1, akq, amp, aiy, ag9, aej⟩
 have aj4 : (S1.aR : ℝ) ≤ dD ε S1 :=
  uZ hr1 amp aj3 aej
 rcases w9 ε hStep S1 aiy ag9 aj4 with
  ⟨S, Wq, Uq, hW, o7, q5, OP⟩
 refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, o7, q5, OP⟩
 ·have aha : S1.r = 1 := by
   rw [hr1]
   simp [S0, i6]
  exact aha ▸ Wq
 ·have aha : S1.r = 1 := by
   rw [hr1]
   simp [S0, i6]
  have amq : 0 < S1.W := by
   have anj : S0.W = 0 := rfl
   omega
  calc
   S.r ≤ S1.r + (D.K - S1.W) := Uq
   _ ≤ D.K := by
    rw [aha]
    omega
theorem JR
  {N : ℕ} {D : bC N} (S : aE N D)
  (ε : ℝ) (_hε : 0 < ε)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
  (amX : S.W < D.K)
  (o7 : S.fD (cW D))
  (amr : S.gI)
  {C : Finset ℕ} {P : ℕ} {S' : aE N D}
  (K6 : C.Nonempty)
  (hP : P ∈ S.cZ C)
  (abS : S'.aR = P * S.aR)
  (aj5 : S'.W = S.W + C.card)
  (akr : S'.fD (cW D))
  (aiz :
   S'.gQ ⊆ ((S.aY C).filter fun q => cD C q = P))
  (aht :
   S'.gQ.card ≤ ((S.aY C).filter fun q => cD C q = P).card)
  (MO :
   ((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ))
  (ak4 :
   (((S.aY C).card : ℝ) * ((1 : ℝ) / ((cQ P : ℝ) ^ 2)) /
     (∑ B ∈ S.cZ C, (1 : ℝ) / ((cQ B : ℝ) ^ 2))) /
     (P : ℝ) ≤ (S'.gQ.card : ℝ))
  (D8 :
   ((S.cO.filter fun A => C ⊆ A).card : ℝ) >
    (S.cO.card : ℝ) / (jz D) ^ C.card)
  (W5 :
   ((S.aY C).card : ℝ) ≤
    (N : ℝ) * Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
     * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
  (Wr :
   ((S.cZ C).card : ℝ) ≤
    (N : ℝ) * Real.exp ((-((C.card : ℝ) / aO N) / 2 + ε) * aZ N))
  (abT : P ≤ N)
  (abV : (cQ P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))) :
  (P : ℝ) ≤ fq ε S S' := by
 have acX :
   (D.Q.card : ℝ) /
     ((S.aR : ℝ) * (cQ (S.aR * P) : ℝ) ^ 2 *
      (cW D) ^ (S.W + C.card)) ≤
    (((S.aY C).filter fun q => cD C q = P).card : ℝ) :=
  S.F3 K6 hP o7 D8 MO
 have acY :
   ((((S.aY C).filter fun q => cD C q = P).card : ℕ) : ℝ) ≤
    ((N : ℝ) / (S.aR * P : ℝ)) *
     Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
     Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
      Real.log (Real.log (N : ℝ))) :=
  S.zH hP ε lD
 have acZ :
   (P : ℝ) ≤
    ((N : ℝ) / (D.Q.card : ℝ)) *
     Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
     Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
      Real.log (Real.log (N : ℝ))) *
     (cQ (S.aR * P) : ℝ) ^ 2 *
     (cW D) ^ (S.W + C.card) := by
  have abW := acX.trans acY
  have aj6 : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  have Ek : 0 < (S.aR : ℝ) := by exact_mod_cast S.jZ
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast S.vW hP
  have aaw : 0 < (cQ (S.aR * P) : ℝ) ^ 2 := by
   have h : 0 < (cQ (S.aR * P) : ℝ) := by exact_mod_cast Dp (S.aR * P)
   exact sq_pos_of_pos h
  have ak5 : 0 < (cW D) ^ (S.W + C.card) :=
   pow_pos (wM D) _
  have hEpos :
    0 < Real.exp ((-((D.K : ℝ) / aO N) / 2 + ε) * aZ N) *
     Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
      Real.log (Real.log (N : ℝ))) := by
   positivity
  field_simp [Ek.ne', hPpos.ne', aaw.ne', ak5.ne'] at abW
  have hmain :
    (D.Q.card : ℝ) * (P : ℝ) ≤
     (N : ℝ) *
      Real.exp ((-((D.K : ℝ) / aO N) + 2 * ε) * aZ N / 2) *
      Real.exp (((S.W + C.card : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) / 2) *
      ((cQ (S.aR * P) : ℝ) ^ 2) *
      (cW D) ^ (S.W + C.card) := by
   have hmul := mul_le_mul_of_nonneg_right abW aaw.le
   rw [div_mul_cancel₀ _ aaw.ne'] at hmul
   nlinarith [hmul]
  field_simp [aj6.ne']
  nlinarith [hmain]
 rw [fq, aj5, abS]
 simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using acZ
theorem aek
  {N : ℕ} {D : bC N} (S : aE N D)
  (ε : ℝ) (_hε : 0 < ε)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
  (wL : S.W < D.K)
  (o7 : S.fD (cW D))
  (q5 : S.gI) :
  ∃ S' : aE N D,
   S'.r = S.r + 1 ∧
   S.W < S'.W ∧
   dV S' = S.W + dV S ∧
   S'.fD (cW D) ∧
   S'.gI ∧
   (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S' := by
 rcases uY S ε lD wL o7 with
  ⟨C, P, S', K6, hP, o8, hr, Fd, hprod, afJ, ael,
   _hW, hT, Jt, Yx, aem, aiA, W5, Wr,
   abT, abV⟩
 have XH : S'.gI :=
  S.JM q5 K6 hP o8
 refine ⟨S', hr, Fd, hT, Jt, XH, ?_⟩
 have aiB : (P : ℝ) ≤ fq ε S S' :=
  JR S ε _hε lD wL o7 q5
   K6 hP hprod _hW Jt afJ ael Yx aem aiA
   W5 Wr abT abV
 rw [hprod]
 calc
  ((P * S.aR : ℕ) : ℝ) = (P : ℝ) * (S.aR : ℝ) := by norm_num
  _ ≤ fq ε S S' * (S.aR : ℝ) := by
     exact mul_le_mul_of_nonneg_right aiB (by positivity)
  _ = (S.aR : ℝ) * fq ε S S' := by ring
theorem XL
  (N : ℕ) (D : bC N) (ε : ℝ) (_hε : 0 < ε)
  (lD :
   ∀ y K W : ℕ,
    y ≤ N →
    W ≤ K →
    (K : ℝ) ≤ 3 * aO N →
    let d : ℝ := (K : ℝ) / aO N
    ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
     ≤ Nat.floor
       ((y : ℝ) * Real.exp ((-d / 2 + ε) * aZ N)
        * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
  ∃ R : ℕ, ∃ S : aE N D,
   S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
   ((N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) ∨ S.W = D.K) ∧
   S.gI ∧
   (S.aR : ℝ) ≤
    ((N : ℝ) / (D.Q.card : ℝ)) ^ R
    * Real.exp ((R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N)
    * Real.exp ((((dV S + S.W : ℕ) : ℝ) / 2) *
      Real.log (Real.log (N : ℝ)))
    * Real.exp (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)))
    * (cW D) ^ (dV S + S.W) := by
 have hStep :
   ∀ S : aE N D,
    S.fD (cW D) →
    S.gI →
    S.W < D.K →
    ∃ S' : aE N D,
     S'.r = S.r + 1 ∧
     S.W < S'.W ∧
     dV S' = S.W + dV S ∧
     S'.fD (cW D) ∧
     S'.gI ∧
     (S'.aR : ℝ) ≤ (S.aR : ℝ) * fq ε S S' := by
  intro S o7 q5 wL
  exact aek S ε _hε lD wL o7 q5
 rcases vV N D ε hStep with
  ⟨R, S, hR, Yr, aen, Yy, amD, q5, OP⟩
 refine ⟨R, S, hR, Yr, aen, Yy, q5, ?_⟩
 simpa [dD, hR] using OP
end cP
namespace cP
open Filter
open Asymptotics
open scoped BigOperators
lemma aeo (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := by
 nlinarith [sq_nonneg (c / 2 - σ)]
private lemma ND
  (M R K σ ε : ℝ) (hM : M ≠ 0) :
  R * σ + R * (-(K / M) / 2 + ε) +
    (2 * R * K - R * (R - 1)) / (4 * M) =
   R * σ - (R * (R - 1)) / (4 * M) + R * ε := by
 field_simp [hM]
 ring
private lemma Wt (M : ℝ) (hM : M ≠ 0) :
  1 - 2 / M = (M - 2) / M := by
 field_simp [hM]
private lemma QW
  (M R σ ε Ie vX : ℝ) (hM : M ≠ 0) :
  (R * σ - (R * (R - 1)) / (4 * M) + R * ε + Ie + vX) / M =
   (R / M) * σ - (R / M) ^ 2 / 4 + (R / M) / (4 * M) + (R / M) * ε +
    Ie / M + vX / M := by
 field_simp [hM]
 ring
private lemma D9
  (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
  ∀ᶠ x : ℝ in atTop, Real.log (A * x) ≤ δ * x := by
 have ak6 : Tendsto (fun x : ℝ => A * x) atTop atTop :=
  tendsto_id.const_mul_atTop hA
 have aiC :
   (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => A * x :=
  Real.isLittleO_log_id_atTop.comp_tendsto ak6
 have hbig : (fun x : ℝ => A * x) =O[atTop] fun x : ℝ => x :=
  isBigO_const_mul_self A (fun x : ℝ => x) atTop
 have hsmall : (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => x :=
  aiC.trans_isBigO hbig
 filter_upwards [isLittleO_iff.mp hsmall hδ, eventually_gt_atTop (0 : ℝ)]
  with x hx hxpos
 calc
  Real.log (A * x) ≤ ‖Real.log (A * x)‖ := le_abs_self _
  _ ≤ δ * ‖x‖ := hx
  _ = δ * x := by rw [Real.norm_of_nonneg hxpos.le]
private lemma Bd
  (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ N : ℕ in atTop,
   ∀ D : bC N,
    Real.log (cW D) ≤ δ * Real.log (Real.log (N : ℝ)) := by
 let B : ℝ := |Real.log (3 * Real.exp 1)| + 1
 let A : ℝ := 2 * mD * B
 have Om : 0 < B := by
  dsimp [B]
  positivity
 have aep : 0 < A := by
  dsimp [A]
  exact mul_pos (mul_pos (by norm_num) zL) Om
 have aer := D9 A δ aep hδ
 have ak7 :
   ∀ᶠ N : ℕ in atTop,
    Real.log (A * Real.log (Real.log (N : ℝ))) ≤
     δ * Real.log (Real.log (N : ℝ)) :=
  iw.eventually aer
 filter_upwards [ak7, P7, f9 1,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
  N aiD amt Rq dG D
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans c7
 have bY : 1 < Real.log (N : ℝ) :=
  (Real.lt_log_iff_exp_lt hNpos).2 c7
 have gC : 0 < Real.log (N : ℝ) := zero_lt_one.trans bY
 have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
  Real.log_pos bY
 have yQ : 1 ≤ Real.log (Real.log (N : ℝ)) := by
  rw [← Real.one_le_sqrt]
  exact Rq
 have ahb : (D.K : ℝ) ≤ 3 * Real.log (N : ℝ) := by
  nlinarith [D.yD, amt]
 have aes : 0 < (D.K : ℝ) := by exact_mod_cast D.K_pos
 have XB : 0 < Real.exp 1 * (D.K : ℝ) :=
  mul_pos (Real.exp_pos 1) aes
 have Zu :
   Real.exp 1 * (D.K : ℝ) ≤ Real.exp 1 * (3 * Real.log (N : ℝ)) := by
  exact mul_le_mul_of_nonneg_left ahb (Real.exp_pos 1).le
 have ac0 :
   Real.log (Real.exp 1 * (D.K : ℝ)) ≤
    Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) :=
  Real.log_le_log XB Zu
 have ZG : 0 < 3 * Real.exp 1 := by positivity
 have ahc :
   Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) =
    Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := by
  have hmul :
    Real.exp 1 * (3 * Real.log (N : ℝ)) =
     (3 * Real.exp 1) * Real.log (N : ℝ) := by ring
  rw [hmul, Real.log_mul ZG.ne' gC.ne']
 have abX :
   Real.log (Real.exp 1 * (D.K : ℝ)) ≤
    B * Real.log (Real.log (N : ℝ)) := by
  calc
   Real.log (Real.exp 1 * (D.K : ℝ))
     ≤ Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) := ac0
   _ = Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := ahc
   _ ≤ B * Real.log (Real.log (N : ℝ)) := by
      dsimp [B]
      have afK : Real.log (3 * Real.exp 1) ≤ |Real.log (3 * Real.exp 1)| :=
       le_abs_self _
      have aeu :
        |Real.log (3 * Real.exp 1)| ≤
         |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) :=
       le_mul_of_one_le_right (abs_nonneg _) yQ
      calc
       Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ))
         ≤ |Real.log (3 * Real.exp 1)| + Real.log (Real.log (N : ℝ)) := by
          exact add_le_add afK le_rfl
       _ ≤ |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) +
          Real.log (Real.log (N : ℝ)) := by
          exact add_le_add aeu le_rfl
       _ = (|Real.log (3 * Real.exp 1)| + 1) *
          Real.log (Real.log (N : ℝ)) := by ring
 have aev :
   cW D ≤ A * Real.log (Real.log (N : ℝ)) := by
  rw [cW, jz]
  calc
   2 * (mD * Real.log (Real.exp 1 * (D.K : ℝ)))
     = 2 * mD * Real.log (Real.exp 1 * (D.K : ℝ)) := by ring
   _ ≤ 2 * mD * (B * Real.log (Real.log (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_left abX
       (mul_nonneg (by norm_num) zL.le)
   _ = A * Real.log (Real.log (N : ℝ)) := by
      dsimp [A]
      ring
 exact (Real.log_le_log (wM D) aev).trans aiD
noncomputable def jc (N : ℕ) (gY : ℕ) : ℝ :=
 Real.log ((N : ℝ) / (gY : ℝ)) / aZ N
lemma aar {N gY : ℕ}
  (ak8 : 0 < gY) (aew : gY ≤ N) (hZ : 0 < aZ N) :
  0 ≤ jc N gY := by
 have aex : 0 < (gY : ℝ) := Nat.cast_pos.mpr ak8
 have aey : (gY : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr aew
 have hone : 1 ≤ (N : ℝ) / (gY : ℝ) :=
  (one_le_div aex).2 aey
 rw [jc]
 exact div_nonneg (Real.log_nonneg hone) hZ.le
private lemma NR {N : ℕ} {D : bC N}
  {S : aE N D}
  (Yy : (N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) ∨ S.W = D.K) :
  (N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) := by
 rcases Yy with OP | hW
 ·exact OP
 ·exact S.Qo hW
private lemma RP
  {η δ σ : ℝ} (afL : 0 ≤ η) (Wv : η ≤ 1)
  (hδ_le : δ ≤ η) (afM : 0 ≤ σ)
  (hsq : 1 - δ ≤ σ ^ 2) :
  1 - η ≤ σ := by
 have Yz : 0 ≤ 1 - η := by linarith
 have abY : (1 - η) ^ 2 ≤ 1 - δ := by
  have aiM : (1 - η) ^ 2 ≤ 1 - η := by
   nlinarith [afL, Wv]
  linarith
 have aiE : (1 - η) ^ 2 ≤ σ ^ 2 := abY.trans hsq
 exact (sq_le_sq₀ Yz afM).1 aiE
lemma RQ {η : ℝ} {N gY : ℕ}
  (hN : 0 < N) (hQ : 0 < gY) (hZ : 0 < aZ N)
  (aj7 : 1 - η ≤ jc N gY) :
  (gY : ℝ) ≤ (N : ℝ) * bF (-(1 - η)) N := by
 have Wi : 0 < (gY : ℝ) := by exact_mod_cast hQ
 have U9 : 0 < (N : ℝ) := by exact_mod_cast hN
 have Uh : 0 < (N : ℝ) / (gY : ℝ) := div_pos U9 Wi
 have hlog :
   (1 - η) * aZ N ≤ Real.log ((N : ℝ) / (gY : ℝ)) := by
  have hmul := mul_le_mul_of_nonneg_right aj7 hZ.le
  rw [jc, div_mul_cancel₀ _ hZ.ne'] at hmul
  exact hmul
 have aas :
   Real.exp ((1 - η) * aZ N) ≤ (N : ℝ) / (gY : ℝ) :=
  (Real.le_log_iff_exp_le Uh).1 hlog
 have ak9 :
   (gY : ℝ) * Real.exp ((1 - η) * aZ N) ≤ (N : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_right aas Wi.le
  rw [div_mul_cancel₀ _ Wi.ne'] at hmul
  simpa [mul_comm] using hmul
 have hcancel :
   Real.exp ((1 - η) * aZ N) *
     Real.exp (-((1 - η) * aZ N)) = 1 := by
  rw [← Real.exp_add]
  ring_nf
  simp
 calc
  (gY : ℝ)
    = ((gY : ℝ) * Real.exp ((1 - η) * aZ N)) *
      Real.exp (-((1 - η) * aZ N)) := by
     rw [mul_assoc, hcancel, mul_one]
  _ ≤ (N : ℝ) * Real.exp (-((1 - η) * aZ N)) := by
     exact mul_le_mul_of_nonneg_right ak9 (Real.exp_pos _).le
  _ = (N : ℝ) * bF (-(1 - η)) N := by
     rw [bF]
     congr 1
     ring_nf
set_option maxHeartbeats 2000000 in
theorem WX :
  ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
   ∀ gY : ℕ, 1 ≤ gY →
    (∃ D : bC N, D.Q.card = gY) →
    1 - η ≤ jc N gY := by
 intro η hη
 let ε : ℝ := η / 8
 have hε : 0 < ε := by
  dsimp [ε]
  positivity
 filter_upwards [Sl ε hε,
   Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
   oM (8 / η) (by positivity),
   f9 (96 / η),
   Bd (η / 144) (by positivity)] with
  N lD dG aiF Qw YA
 have c7 : Real.exp 1 < (N : ℝ) :=
  lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast dG)
 have Ov : 0 < aZ N := lJ c7
 have hMpos : 0 < aO N := g5 c7
 have hMZ : aO N * aZ N = Real.log (N : ℝ) :=
  tB c7
 have abB : aZ N / aO N = Real.log (Real.log (N : ℝ)) :=
  j4 c7
 intro gY aiG hD
 rcases hD with ⟨D, hDcard⟩
 have UC : 0 ≤ jc N gY := by
  have aew : gY ≤ N := by
   rw [← hDcard]
   exact D.afx
  exact aar (Nat.succ_le_iff.mp aiG) aew Ov
 rcases XL N D ε hε lD with
  ⟨R, S, hR, Yr, aen, Yy, q5, aez⟩
 have aeA : (N : ℝ) * bF (-2) N ≤ (S.aR : ℝ) :=
  NR Yy
 have YB : (S.aR : ℝ) ≤ dD ε S := by
  simpa [dD, hR] using aez
 have ac1 :
   Real.log ((N : ℝ) * bF (-2) N) ≤
    Real.log (dD ε S) := by
  have afN : 0 < (N : ℝ) * bF (-2) N := by
   exact mul_pos (by exact_mod_cast D.N_pos) (rW (-2) N)
  exact Real.log_le_log afN (aeA.trans YB)
 have LO :
   Real.log (N : ℝ) - 2 * aZ N ≤
    Real.log (dD ε S) := by
  have afO :
    Real.log ((N : ℝ) * bF (-2) N) =
     Real.log (N : ℝ) - 2 * aZ N := by
   rw [Dm D.N_pos (-2)]
   ring
  rwa [afO] at ac1
 have WZ :
   Real.log (N : ℝ) - 2 * aZ N ≤
    (R : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
     (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N +
     ((((dV S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
     2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
     ((dV S + S.W : ℕ) : ℝ) * Real.log (cW D) := by
  rw [JQ ε S] at LO
  simpa [hR] using LO
 have afP :
   Real.log ((N : ℝ) / (D.Q.card : ℝ)) =
    jc N gY * aZ N := by
  rw [jc, ← hDcard]
  field_simp [Ov.ne']
 have U8 :
   aO N - 2 ≤
    (R : ℝ) * jc N gY +
     (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
     ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) +
     (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / aZ N +
     (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) / aZ N := by
  have ZH :
    Real.log (N : ℝ) - 2 * aZ N ≤
     (R : ℝ) * (jc N gY * aZ N) +
      (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N +
      ((((dV S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
      2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
      ((dV S + S.W : ℕ) : ℝ) * Real.log (cW D) := by
   simpa [afP] using WZ
  have h :
    (aO N - 2) * aZ N ≤
     ((R : ℝ) * jc N gY +
      (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
      ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) +
      (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / aZ N +
      (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) / aZ N) *
       aZ N := by
   calc
    (aO N - 2) * aZ N
      = Real.log (N : ℝ) - 2 * aZ N := by
        rw [← hMZ]
        ring
    _ ≤ (R : ℝ) * (jc N gY * aZ N) +
       (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) * aZ N +
       ((((dV S + S.W : ℕ) : ℝ) / 2) *
        Real.log (Real.log (N : ℝ))) +
       2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
       ((dV S + S.W : ℕ) : ℝ) * Real.log (cW D) :=
      ZH
    _ = ((R : ℝ) * jc N gY +
       (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
       ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) +
       (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / aZ N +
       (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) /
        aZ N) * aZ N := by
      rw [← abB]
      field_simp [hMpos.ne', Ov.ne']
  have hdiv := div_le_div_of_nonneg_right h Ov.le
  field_simp [Ov.ne'] at hdiv
  field_simp [hMpos.ne']
  nlinarith [hdiv, hMpos]
 have aiH : dV S ≤ S.r * D.K := S.WV
 have amu : dV S ≤ R * D.K := by
  simpa [hR] using aiH
 have aj8 : ((((dV S + S.W : ℕ) : ℝ) * 2)) ≤
   2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) :=
  S.G8 q5
 have adf : ((((dV S + S.W : ℕ) : ℝ) * 2)) ≤
   2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1) := by
  have hWle : (S.W : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast S.Nu
  have abZ : 0 ≤ (R : ℝ) := by positivity
  rw [← hR]
  nlinarith [aj8, hWle, abZ]
 have aj9 :
   ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) ≤
    (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
     (4 * aO N) := by
  calc
   ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N)
     = (((dV S + S.W : ℕ) : ℝ) * 2) * (1 / (4 * aO N)) := by
       field_simp [hMpos.ne']
       ring
   _ ≤ (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) *
      (1 / (4 * aO N)) := by
       exact mul_le_mul_of_nonneg_right adf (by positivity)
   _ = (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
      (4 * aO N) := by ring
 let Ie : ℝ := (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / aZ N
 let vX : ℝ :=
  (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) / aZ N
 have Ww :
   aO N - 2 ≤
    (R : ℝ) * jc N gY -
     ((R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) +
     (R : ℝ) * ε + Ie + vX := by
  calc
   aO N - 2
     ≤ (R : ℝ) * jc N gY +
       (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
       ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) +
       Ie + vX :=
      U8
   _ ≤ (R : ℝ) * jc N gY +
       (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
       (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
        (4 * aO N) + Ie + vX := by
      let A : ℝ :=
       (R : ℝ) * jc N gY +
        (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε)
      let B : ℝ := Ie + vX
      have hmid :
        A + ((((dV S + S.W : ℕ) : ℝ) / 2) / aO N) ≤
         A + (2 * (R : ℝ) * (D.K : ℝ) -
          (R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) :=
       by
        have am4 := add_le_add_left aj9 A
        linarith
      have ala := add_le_add_right hmid B
      dsimp [A, B] at ala
      linarith
   _ = (R : ℝ) * jc N gY -
      ((R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) +
      (R : ℝ) * ε + Ie + vX := by
      have hbase :
        (R : ℝ) * jc N gY +
          (R : ℝ) * (-((D.K : ℝ) / aO N) / 2 + ε) +
          (2 * (R : ℝ) * (D.K : ℝ) -
            (R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) =
         (R : ℝ) * jc N gY -
          ((R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) +
          (R : ℝ) * ε :=
       ND (aO N) (R : ℝ) (D.K : ℝ)
        (jc N gY) ε hMpos.ne'
      rw [hbase]
 let c : ℝ := (R : ℝ) / aO N
 have hc_pos : 0 < c := by
  dsimp [c]
  have aeB : 0 < (R : ℝ) := by exact_mod_cast Yr
  exact div_pos aeB hMpos
 have W7 : c ≤ 3 := by
  dsimp [c]
  have Ur : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast aen
  have YC : (R : ℝ) ≤ 3 * aO N := Ur.trans D.yD
  exact (div_le_iff₀ hMpos).2 YC
 let mJ : ℝ := Ie / aO N
 let jV : ℝ := vX / aO N
 have ZI :
   (aO N - 2) / aO N ≤
    c * jc N gY - c ^ 2 / 4 + c / (4 * aO N) + c * ε +
     mJ + jV := by
  have hdiv := div_le_div_of_nonneg_right Ww hMpos.le
  calc
   (aO N - 2) / aO N
     ≤ ((R : ℝ) * jc N gY -
      ((R : ℝ) * ((R : ℝ) - 1)) / (4 * aO N) +
      (R : ℝ) * ε + Ie + vX) / aO N := hdiv
   _ = c * jc N gY - c ^ 2 / 4 + c / (4 * aO N) + c * ε +
      mJ + jV := by
       dsimp [c, mJ, jV]
       exact QW (aO N) (R : ℝ) (jc N gY)
        ε Ie vX hMpos.ne'
 have YH :
   (aO N - 2) / aO N ≤
    (jc N gY) ^ 2 + c / (4 * aO N) + c * ε +
     mJ + jV := by
  calc
   (aO N - 2) / aO N
     ≤ c * jc N gY - c ^ 2 / 4 + c / (4 * aO N) + c * ε +
       mJ + jV :=
      ZI
   _ ≤ (jc N gY) ^ 2 + c / (4 * aO N) + c * ε +
       mJ + jV := by
      simpa [add_assoc] using
       add_le_add_right (aeo c (jc N gY))
        (c / (4 * aO N) + c * ε + mJ + jV)
 have SD :
   (aO N - 2) / aO N ≤
    (jc N gY) ^ 2 + 3 / (4 * aO N) + 3 * ε +
     mJ + jV := by
  have aiI : c / (4 * aO N) ≤ 3 / (4 * aO N) := by
   exact div_le_div_of_nonneg_right W7 (by positivity)
  have aiJ : c * ε ≤ 3 * ε :=
   mul_le_mul_of_nonneg_right W7 hε.le
  calc
   (aO N - 2) / aO N
     ≤ (jc N gY) ^ 2 + c / (4 * aO N) + c * ε +
       mJ + jV :=
      YH
   _ ≤ (jc N gY) ^ 2 + 3 / (4 * aO N) + 3 * ε +
       mJ + jV := by
      have ank :
        c / (4 * aO N) + c * ε ≤
         3 / (4 * aO N) + 3 * ε :=
       add_le_add aiI aiJ
      linarith
 have YI :
   1 - (2 / aO N + 3 / (4 * aO N) + 3 * ε +
     mJ + jV) ≤
    (jc N gY) ^ 2 := by
  have hleft : (aO N - 2) / aO N = 1 - 2 / aO N :=
   (Wt (aO N) hMpos.ne').symm
  linarith [SD, hleft]
 by_cases akb : 1 ≤ η
 ·have htarget : 1 - η ≤ 0 := by linarith
  exact htarget.trans UC
 have Wv : η ≤ 1 := le_of_lt (not_le.mp akb)
 let δN : ℝ :=
  2 / aO N + 3 / (4 * aO N) + 3 * ε + mJ + jV
 have XM (hδN : δN ≤ η) : 1 - η ≤ jc N gY := by
  exact RP hη.le Wv hδN UC (by
   simpa [δN] using YI)
 have akc : δN ≤ η := by
  have aep : 0 < (8 : ℝ) / η := by positivity
  have afQ : 1 / aO N ≤ 1 / (8 / η) :=
   one_div_le_one_div_of_le aep aiF
  have ahu : 1 / aO N ≤ η / 8 := by
   convert afQ using 1
   field_simp [hη.ne']
  dsimp [δN, ε]
  have ae4 : 2 / aO N ≤ η / 4 := by
   calc
    2 / aO N = 2*(1/aO N) := by ring
    _ ≤ 2*(η/8) := mul_le_mul_of_nonneg_left ahu (by norm_num)
    _ = _ := by ring
  have amZ : 3 / (4 * aO N) ≤ 3 * η / 32 := by
   calc
    3 / (4 * aO N) = (3/4) * (1/aO N) := by rw [div_mul_eq_div_div]; ring
    _ ≤ (3/4) * (η/8) := mul_le_mul_of_nonneg_left ahu (by norm_num)
    _ = _ := by ring
  have c8 : 0 < Real.log (Real.log (N : ℝ)) :=
   Real.log_pos ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans c7)).2 c7)
  have ab0 : 0 < Real.sqrt (Real.log (N : ℝ)) := by
   have gC : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans c7)).2 c7)
   rw [Real.sqrt_pos]
   exact gC
  have YJ :
    0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := by
   have aeC : 0 < (96 : ℝ) / η := by positivity
   exact aeC.trans_le Qw
  have YC : (R : ℝ) ≤ 3 * aO N := by
   have Ur : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast aen
   exact Ur.trans D.yD
  have ab3 : mJ ≤ η / 16 := by
   have ML :
     0 ≤ 2 * Real.sqrt (Real.log (N : ℝ)) / (aZ N * aO N) := by
    positivity
   calc
    mJ
      = (R : ℝ) *
        (2 * Real.sqrt (Real.log (N : ℝ)) / (aZ N * aO N)) := by
       dsimp [mJ, Ie]
       field_simp [Ov.ne', hMpos.ne']
    _ ≤ (3 * aO N) *
       (2 * Real.sqrt (Real.log (N : ℝ)) / (aZ N * aO N)) := by
       exact mul_le_mul_of_nonneg_right YC ML
    _ = 6 / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
       rw [gN c7]
       field_simp [hMpos.ne', ab0.ne', YJ.ne']
       ring
    _ ≤ 6 / (96 / η) := by
       exact div_le_div_of_nonneg_left (by norm_num)
        (by positivity) Qw
    _ = η / 16 := by
       field_simp [hη.ne']
       ring
  have ab4 :
    (((dV S + S.W : ℕ) : ℝ)) ≤ (R : ℝ) * (D.K : ℝ) := by
   have aat : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast Yr
   have ab5 : 0 ≤ (R : ℝ) * ((R : ℝ) - 1) := by
    nlinarith [aat]
   have alb :
     (((dV S + S.W : ℕ) : ℝ) * 2) ≤
      2 * (R : ℝ) * (D.K : ℝ) := by
    nlinarith [adf, ab5]
   nlinarith
  have aau :
    (((dV S + S.W : ℕ) : ℝ)) ≤ 9 * (aO N) ^ 2 := by
   have akd : (D.K : ℝ) ≤ 3 * aO N := D.yD
   have abZ : 0 ≤ (R : ℝ) := by positivity
   have ahd : 0 ≤ (D.K : ℝ) := by positivity
   have ake : (R : ℝ) * (D.K : ℝ) ≤ (3 * aO N) * (3 * aO N) :=
    mul_le_mul YC akd ahd (by positivity)
   nlinarith [ab4, ake]
  have aav :
    Real.log (cW D) ≤
     (η / 144) * Real.log (Real.log (N : ℝ)) :=
   YA D
  have ZJ : jV ≤ η / 16 := by
   have Ql :
     0 ≤ (η / 144) * Real.log (Real.log (N : ℝ)) := by positivity
   have ahe : 0 ≤ (((dV S + S.W : ℕ) : ℝ)) := by positivity
   have aiK :
     (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) ≤
      (9 * (aO N) ^ 2) *
       ((η / 144) * Real.log (Real.log (N : ℝ))) := by
    have ac2 :
      (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) ≤
       (((dV S + S.W : ℕ) : ℝ) *
        ((η / 144) * Real.log (Real.log (N : ℝ)))) :=
     mul_le_mul_of_nonneg_left aav ahe
    have afR :
      (((dV S + S.W : ℕ) : ℝ) *
        ((η / 144) * Real.log (Real.log (N : ℝ)))) ≤
       (9 * (aO N) ^ 2) *
        ((η / 144) * Real.log (Real.log (N : ℝ))) :=
     mul_le_mul_of_nonneg_right aau Ql
    exact ac2.trans afR
   have SH := gW c7
   calc
    jV
      = (((dV S + S.W : ℕ) : ℝ) * Real.log (cW D)) /
        (aZ N * aO N) := by
       dsimp [jV, vX]
       field_simp [Ov.ne', hMpos.ne']
    _ ≤ ((9 * (aO N) ^ 2) *
        ((η / 144) * Real.log (Real.log (N : ℝ)))) /
        (aZ N * aO N) := by
       exact div_le_div_of_nonneg_right aiK
        (mul_nonneg Ov.le hMpos.le)
    _ = η / 16 := by
       rw [← SH]
       field_simp [hMpos.ne', c8.ne']
       ring
  have ahf :
    2 / aO N + 3 / (4 * aO N) + 3 * (η / 8) ≤
     (23 / 32) * η := by
   calc
    2 / aO N + 3 / (4 * aO N) + 3 * (η / 8)
     ≤ η / 4 + 3 * η / 32 + 3 * (η / 8) := by
      gcongr
    _ = (23 / 32) * η := by ring
  calc
   2 / aO N + 3 / (4 * aO N) + 3 * (η / 8) + mJ + jV
     ≤ (23 / 32) * η + η / 16 + η / 16 := by
      linarith [ahf, ab3, ZJ]
   _ = (27 / 32) * η := by ring
   _ ≤ η := by
      exact mul_le_of_le_one_left hη.le (by norm_num)
 exact XM akc
end cP
open Filter cP
private lemma wS (N : ℕ) (c : ℝ) : scaleL N ^ c = bF c N := by
 rw [scaleL, ← Real.exp_mul, mul_comm]
 rfl
theorem solve : OMA.R2.H2 := by
 intro ε he
 filter_upwards [WX ε he, eventually_gt_atTop (Nat.ceil (Real.exp 1))]
  with N hs hN T a K hr hd hg
 by_cases ht : T.Nonempty
 ·obtain ⟨hk,hK,good,inj⟩ := hg
  have disj : d7 T (fun i => a i.val) := by
   intro i j hne
   apply Set.disjoint_left.mpr
   intro z hi hj
   exact hd i.val i.property j.val j.property (fun h => hne (Subtype.ext h)) ⟨z,hi,hj⟩
  let D : bC N := {
   Q := T
   z6 := ht
   a := fun i => a i.val
   admissible := ⟨hr,_,disj⟩
   pairwise_disjoint := disj
   K := K
   K_pos := hk
   Bk := fun q hq => by simpa only [wS] using (good q hq).1
   q6 := fun q hq => (hr q hq).2
   Ee := fun q hq => by simpa only [cQ,aD,Nat.support_factorization] using (good q hq).2.1
   L9 := fun q hq => by simpa only [omega,aD,Nat.support_factorization] using (good q hq).2.2
   yD := hK
   Bm := by simpa only [rad,aD,Nat.support_factorization] using inj
  }
  have hN' : Real.exp 1 < (N:ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hN)
  have hh := RQ D.N_pos ht.card_pos (lJ hN')
   (hs T.card ht.card_pos ⟨D,rfl⟩)
  rw [wS]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply oN
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
 ·rw [Finset.not_nonempty_iff_eq_empty.mp ht]
  simp only [Finset.card_empty,Nat.cast_zero,wS]
  exact mul_nonneg (by positivity) (Real.exp_pos _).le
end OMA.L2

namespace OMA.L3
namespace OMA.Aux
open Filter Real Finset
noncomputable def tt (M : ℕ) : ℝ := sqrt (log M * log (log M))
lemma YM (M : ℕ) (x : ℝ) : scaleL M ^ x = Real.exp (x * tt M) := by
 unfold scaleL tt
 rw [← Real.exp_mul, mul_comm]
lemma UF (m : ℕ) (hm : 16 ≤ m) : Real.exp 1 ≤ log m := by
 have h1 : log 16 = 4 * log 2 := by
  rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
 have h2 : log 16 ≤ log m := by
  apply Real.log_le_log (by norm_num)
  exact_mod_cast hm
 have := Real.log_two_gt_d9
 have := Real.exp_one_lt_d9
 linarith
lemma ahg (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
  a * log a ≤ b * log b ∧ b ≤ b * log b := by
 have hapos : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
 have hbpos : 0 < b := lt_of_lt_of_le hapos hab
 have hla : 1 ≤ log a := by
  rw [Real.le_log_iff_exp_le hapos]; exact ha
 have anl : log a ≤ log b := Real.log_le_log hapos hab
 constructor
 ·calc a * log a ≤ b * log a := by nlinarith
   _ ≤ b * log b := by nlinarith
 ·nlinarith
lemma ald (m k : ℕ) (hm : 16 ≤ m) :
  tt m ≤ tt (2 ^ (k+1) * m) ∧ sqrt (((k:ℝ)+1) * log 2) ≤ tt (2 ^ (k+1) * m) := by
 have hm0 : (0:ℝ) < m := by positivity
 have ahv : log ((2 ^ (k+1) * m : ℕ) : ℝ) = ((k:ℝ)+1) * log 2 + log m := by
  push_cast
  rw [Real.log_mul (by positivity) hm0.ne', Real.log_pow]; push_cast; ring
 have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
 have hge := UF m hm
 have hle : log m ≤ log ((2 ^ (k+1) * m : ℕ) : ℝ) := by
  rw [ahv]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) hl2.le]
 obtain ⟨h1, h2⟩ := ahg _ _ hge hle
 constructor
 ·exact Real.sqrt_le_sqrt h1
 ·apply Real.sqrt_le_sqrt
  rw [ahv] at h2 ⊢
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) hl2.le, Real.exp_pos 1, hge]
lemma akf (m k : ℕ) (hm : 16 ≤ m) (c θ : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
  Real.exp (-c * tt (2 ^ (k+1) * m)) ≤
   Real.exp (-c * (1 - θ) * tt m) * Real.exp (-(c * θ) * sqrt (((k:ℝ)+1) * log 2)) := by
 obtain ⟨h1, h2⟩ := ald m k hm
 rw [← Real.exp_add]
 apply Real.exp_le_exp.2
 have a1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hθ1)
 have a2 := mul_le_mul_of_nonneg_left h2 hθ0
 have : (1 - θ) * tt m + θ * sqrt (((k:ℝ)+1) * log 2) ≤ tt (2 ^ (k+1) * m) := by nlinarith
 nlinarith [mul_le_mul_of_nonneg_left this hc.le]
lemma ale (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
  Summable (fun k : ℕ => Real.exp (-a * sqrt (((k:ℝ)+1) * L))) := by
 have hs : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ)) ^ 2) :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num))
 refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
  (fun k => ?_) (hs.mul_left (24 / ((a^2 * L)^2)))
 have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
 set y := a * sqrt (((k:ℝ)+1) * L) with hy
 have hypos : 0 < y := by positivity
 have hy2 : y ^ 2 = a^2 * (((k:ℝ)+1) * L) := by
  rw [hy, mul_pow, Real.sq_sqrt (by positivity)]
 have hy4 : y ^ 4 = (a^2 * L)^2 * ((k:ℝ)+1)^2 := by
  have : y ^ 4 = (y^2)^2 := by ring
  rw [this, hy2]; ring
 have hexp := Real.pow_div_factorial_le_exp y hypos.le 4
 have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
 rw [hf] at hexp
 have hmain : Real.exp (-y) ≤ 24 / y ^ 4 := by
  rw [le_div_iff₀ (by positivity)]
  have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h24 : y ^ 4 / 24 ≤ Real.exp y := hexp
  nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_left h24 (Real.exp_pos (-y)).le]
 have : -a * sqrt (((k:ℝ)+1) * L) = -y := by rw [hy]; ring
 rw [this]
 refine hmain.trans (le_of_eq ?_)
 rw [hy4]
 push_cast
 field_simp
lemma afS (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
  0 < sqrt 3 / 2 - δ / 2 ∧ 0 ≤ δ / (4 * (sqrt 3 / 2 - δ / 2)) ∧
  δ / (4 * (sqrt 3 / 2 - δ / 2)) ≤ 1 ∧
  (sqrt 3 / 2 - δ / 2) * (δ / (4 * (sqrt 3 / 2 - δ / 2))) = δ / 4 := by
 have h3 : 1 ≤ sqrt 3 := by
  rw [show (1:ℝ) = sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
 have hc : 0 < sqrt 3 / 2 - δ / 2 := by linarith
 have hc' : sqrt 3 - δ ≠ 0 := by intro h; linarith
 refine ⟨hc, by positivity, ?_, by field_simp⟩
 rw [div_le_one (by positivity)]; linarith
theorem main (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) :
  ∀ᶠ m : ℕ in atTop, ∃ B : ℝ,
   B < scaleL m ^ (-(sqrt 3 / 2) + δ) ∧ ∀ K : ℕ,
    (∑ k ∈ range K, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2)) ≤ B := by
 obtain ⟨hc, hθ0, hθ1, hcθ⟩ := afS δ hδ hδ2
 set c := sqrt 3 / 2 - δ / 2 with ahw
 set θ := δ / (4 * c) with am5
 have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
 have hsum := ale (δ/4) (log 2) (by positivity) hl2
 set G := ∑' k : ℕ, Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) with hG
 have hG0 : 0 ≤ G := tsum_nonneg (fun k => (Real.exp_pos _).le)
 set N1 : ℕ := Nat.ceil (Real.exp ((8 * G / δ)^2)) + 16 with hN1
 filter_upwards [eventually_ge_atTop N1] with m hm
 have aki : 16 ≤ m := by omega
 have hm0 : (0:ℝ) < m := by positivity
 set E := Real.exp (-c * (1 - θ) * tt m) with hE
 have hEpos : 0 < E := Real.exp_pos _
 refine ⟨2 * G * E, ?_, ?_⟩
 ·
  have hge := UF m aki
  have hlm : (8 * G / δ)^2 ≤ log m := by
   rw [Real.le_log_iff_exp_le hm0]
   have h1 := Nat.le_ceil (Real.exp ((8 * G / δ)^2))
   have h2 : (Nat.ceil (Real.exp ((8 * G / δ)^2)) : ℝ) ≤ m := by
    exact_mod_cast (by omega : Nat.ceil (Real.exp ((8 * G / δ)^2)) ≤ m)
   linarith
  have LX : 0 < log m := lt_of_lt_of_le (Real.exp_pos 1) hge
  have hll : 1 ≤ log (log m) := by
   rw [Real.le_log_iff_exp_le LX]; exact hge
  have ht1 : sqrt (log m) ≤ tt m := by
   unfold tt
   apply Real.sqrt_le_sqrt
   nlinarith
  have ht2 : 8 * G / δ ≤ sqrt (log m) :=
   (le_abs_self _).trans (Real.abs_le_sqrt hlm)
  have ht3 : 2 * G ≤ δ / 4 * tt m := by
   have : 8 * G / δ ≤ tt m := ht2.trans ht1
   rw [div_le_iff₀ hδ] at this
   nlinarith
  have ht4 : 2 * G < Real.exp (δ / 4 * tt m) := by
   have := Real.add_one_le_exp (δ / 4 * tt m)
   linarith
  rw [YM]
  have e1 : -c * (1 - θ) = -c + δ / 4 := by linear_combination hcθ
  have e2 : (-(sqrt 3 / 2) + δ) * tt m = -c * (1 - θ) * tt m + δ / 4 * tt m := by
   rw [e1, ahw]; ring
  rw [e2, Real.exp_add]
  rw [← hE]
  nlinarith
 ·intro K
  have hterm : ∀ k : ℕ, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2) ≤
    2 * E * Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) := by
   intro k
   rw [YM]
   have e : (-(sqrt 3 / 2) + δ / 2) = -c := by rw [ahw]; ring
   rw [e]
   have := akf m k aki c θ hc hθ0 hθ1
   rw [hcθ] at this
   nlinarith
  calc _ ≤ ∑ k ∈ range K, 2 * E * Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) :=
     Finset.sum_le_sum (fun k _ => hterm k)
   _ = 2 * E * ∑ k ∈ range K, Real.exp (-(δ/4) * sqrt (((k:ℝ)+1) * log 2)) := by
     rw [Finset.mul_sum]
   _ ≤ 2 * E * G := by
     apply mul_le_mul_of_nonneg_left _ (by positivity)
     exact hsum.sum_le_tsum _ (fun i _ => (Real.exp_pos _).le)
   _ = 2 * G * E := by ring
end OMA.Aux
theorem solve : OMA.R1.H2 := by
 intro δ hδ hδ2
 exact OMA.Aux.main δ hδ hδ2
end OMA.L3

theorem OMA.solution : type_of% @Erdos1190.erdos_1190.variants.upper_bound :=
OMA.R1.main (OMA.R2.main OMA.L1.solve OMA.L2.solve) OMA.L3.solve
