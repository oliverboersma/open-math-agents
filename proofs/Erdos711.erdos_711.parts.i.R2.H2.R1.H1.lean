import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1
import Mathlib

/-! Uniform subpolynomial control of the number of divisors. -/
open Filter Finset Real
open scoped Topology

namespace DivisorGrowth

private theorem pointwise (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 0 < y →
      (y.divisors.card : ℝ) ≤ C*(y:ℝ)^ε := by
  have grow : Tendsto (fun p : ℕ => (p:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp (grow.eventually_ge_atTop (2:ℝ))
  let b := (2:ℝ)^ε-1
  have bp : 0 < b := by
    dsimp [b]
    have h := rpow_lt_rpow_of_exponent_lt (show (1:ℝ)<2 by norm_num) he
    simpa using h
  let C := 1+b⁻¹
  have C1 : 1 ≤ C := le_add_of_nonneg_right (inv_nonneg.mpr bp.le)
  have Cb : 1 ≤ C*b := by
    dsimp [C]
    rw [add_mul,one_mul,inv_mul_cancel₀ bp.ne']
    linarith
  refine ⟨C^K,pow_pos (zero_lt_one.trans_le C1) _,?_⟩
  intro y hy
  let P := y.primeFactors
  let W (p : ℕ) := (p:ℝ)^ε
  let u (p : ℕ) : ℝ := if p<K then C else 1
  have hb (p : ℕ) (hp : p ∈ P) : (2:ℝ)^ε ≤ W p :=
    rpow_le_rpow (by norm_num) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) he.le
  have term (p : ℕ) (hp : p ∈ P) :
      (y.factorization p : ℝ)+1 ≤ u p*(W p)^y.factorization p := by
    have Wp : 0 ≤ W p := by dsimp [W]; positivity
    have hbig := hb p hp
    have bern := one_add_mul_sub_le_pow (show -1 ≤ W p by linarith) (y.factorization p)
    have ep : (0:ℝ) ≤ y.factorization p := by positivity
    by_cases small : p<K
    · rw [show u p = C by simp [u,small]]
      have hh : 1 ≤ C*(W p-1) := Cb.trans (mul_le_mul_of_nonneg_left
        (show b ≤ W p-1 by dsimp [b]; linarith) (zero_le_one.trans C1))
      have eHH := mul_le_mul_of_nonneg_left hh ep
      have eBern := mul_le_mul_of_nonneg_left bern (zero_le_one.trans C1)
      nlinarith only [C1,eHH,eBern]
    · simp only [u, if_neg small, one_mul]
      have ht : 2 ≤ W p := hK p (le_of_not_gt small)
      nlinarith only [bern,mul_nonneg ep (show 0 ≤ W p-2 by linarith)]
  have uj : ∏ p ∈ P, u p ≤ C^K := by
    let small := P.filter (fun p => p<K)
    have hh : small ⊆ range K := fun p hp => mem_range.mpr (mem_filter.mp hp).2
    have hc : small.card ≤ K := by simpa using card_le_card hh
    calc
      _ = ∏ _p ∈ small, C := by
        symm
        exact prod_filter (s := P) (fun p => p<K) (fun _ => C)
      _ = C^small.card := prod_const _
      _ ≤ C^K := pow_le_pow_right₀ C1 hc
  have wprod : (∏ p ∈ P, (W p)^y.factorization p) = (y:ℝ)^ε := by
    trans ∏ p ∈ P, ((p:ℝ)^y.factorization p)^ε
    · apply prod_congr rfl
      intro p _
      exact rpow_pow_comm (show (0:ℝ) ≤ p by positivity) _ _
    rw [finsetProd_rpow _ _ (fun _ _ => by positivity)]
    have eq : (∏ p ∈ P, (p:ℝ)^y.factorization p) = (y:ℝ) := by
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hy.ne').symm
    rw [eq]
  calc
    (y.divisors.card:ℝ) = ∏ p ∈ P, ((y.factorization p:ℝ)+1) := by
      rw [Nat.card_divisors hy.ne']
      push_cast
      rfl
    _ ≤ ∏ p ∈ P, u p*(W p)^y.factorization p :=
      prod_le_prod (fun _ _ => by positivity) term
    _ = (∏ p ∈ P,u p)*(y:ℝ)^ε := by rw [prod_mul_distrib,wprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right uj (rpow_nonneg (by positivity) _)

theorem uniform (δ : ℝ) (hd : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℕ, 0 < y → y ≤ n^3 →
    (y.divisors.card : ℝ) ≤ (n:ℝ)^δ := by
  let ε := δ/6
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,hb⟩ := pointwise ε he
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C] with n hn y hy hyn
  have hpow : (y:ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast hyn
  have hp : ((n:ℝ)^3)^ε = (n:ℝ)^(δ/2) := by
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    congr 1
    dsimp [ε]
    ring
  calc
    _ ≤ C*(y:ℝ)^ε := hb y hy
    _ ≤ C*((n:ℝ)^3)^ε := mul_le_mul_of_nonneg_left
      (rpow_le_rpow (by positivity) hpow he.le) hC.le
    _ = C*(n:ℝ)^(δ/2) := by rw [hp]
    _ ≤ (n:ℝ)^(δ/2)*(n:ℝ)^(δ/2) := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by
      rw [← rpow_add' (by positivity) (by linarith : δ/2+δ/2 ≠ 0), show δ/2+δ/2=δ by ring]

end DivisorGrowth

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1.H1 := DivisorGrowth.uniform