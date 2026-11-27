import OMAReductions.R_Erdos143_erdos_143_parts_i_R1
import Mathlib

/-!
# A uniform harmonic bound for primitive sets

This is the little-o consequence of Behrend's classical 1935 bound for primitive
sets (JLMS, DOI 10.1112/jlms/s1-10.37.42). We use the variance of prime
divisibility indicators under Dirichlet weights and let the exponent tend
to one. The target is the integer H1 of the Erdős 143(i) reduction.
-/

open scoped BigOperators
namespace Behrend

noncomputable section

def weight (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

def avg (s : ℝ) (f : ℕ → ℝ) : ℝ := ∑' n, weight s n * f n

def bounded (f : ℕ → ℝ) : Prop := ∃ C : ℝ, ∀ n, |f n| ≤ C

lemma bounded_const (c : ℝ) : bounded (fun _ => c) := ⟨|c|, fun _ => le_rfl⟩

lemma bounded_add {f g : ℕ → ℝ} (hf : bounded f) (hg : bounded g) :
    bounded (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a+b, fun n => (abs_add_le _ _).trans (add_le_add (ha n) (hb n))⟩

lemma bounded_mul {f g : ℕ → ℝ} (hf : bounded f) (hg : bounded g) :
    bounded (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a*b, fun n => (abs_mul _ _).le.trans
    (mul_le_mul (ha n) (hb n) (abs_nonneg _) ((abs_nonneg _).trans (ha n)))⟩

lemma bounded_sum {ι : Type*} (P : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ p ∈ P, bounded (f p)) : bounded (fun n => ∑ p ∈ P, f p n) := by
  choose! C hC using hf
  exact ⟨∑ p ∈ P, C p, fun n => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p hp => hC p hp n)⟩

lemma weight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ weight s n := Real.rpow_nonneg (by positivity) _

lemma weight_mul (s : ℝ) (p n : ℕ) : weight s (p*n) = weight s p * weight s n := by
  simp only [weight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

lemma weight_summable {s : ℝ} (hs : 1 < s) : Summable (weight s) :=
  Real.summable_nat_rpow.mpr (by linarith)

lemma weighted_summable {s : ℝ} (hs : 1 < s) {f : ℕ → ℝ} (hf : bounded f) :
    Summable (fun n => weight s n * f n) := by
  obtain ⟨C, hC⟩ := hf
  refine Summable.of_norm_bounded ((weight_summable hs).mul_right C) fun n => ?_
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg s n)] using
    mul_le_mul_of_nonneg_left (hC n) (weight_nonneg s n)

lemma avg_mono {s : ℝ} (hs : 1 < s) {f g : ℕ → ℝ} (hf : bounded f) (hg : bounded g)
    (h : ∀ n, f n ≤ g n) : avg s f ≤ avg s g :=
  (weighted_summable hs hf).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h n) (weight_nonneg _ _))
    (weighted_summable hs hg)

lemma avg_add {s : ℝ} (hs : 1 < s) {f g : ℕ → ℝ} (hf : bounded f) (hg : bounded g) :
    avg s (fun n => f n + g n) = avg s f + avg s g := by
  simpa only [avg, mul_add] using (weighted_summable hs hf).tsum_add (weighted_summable hs hg)

lemma avg_const_mul (s c : ℝ) (f : ℕ → ℝ) :
    avg s (fun n => c * f n) = c * avg s f := by
  simp only [avg, mul_left_comm (weight s _) c, tsum_mul_left]

lemma avg_sum {s : ℝ} (hs : 1 < s) {ι : Type*} (P : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ p ∈ P, bounded (f p)) :
    avg s (fun n => ∑ p ∈ P, f p n) = ∑ p ∈ P, avg s (f p) := by
  simp only [avg, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun p hp => weighted_summable hs (hf p hp))

def divIndicator (p n : ℕ) : ℝ := if p ∣ n then 1 else 0

lemma bounded_div (p : ℕ) : bounded (divIndicator p) := by
  refine ⟨1, fun n => ?_⟩
  simp only [divIndicator]
  split <;> norm_num

lemma avg_dilate (s : ℝ) {p : ℕ} (hp : p ≠ 0) (f : ℕ → ℝ) :
    avg s (fun n => divIndicator p n * f n) = weight s p * avg s (fun n => f (p*n)) := by
  let g (n : ℕ) := weight s n * (divIndicator p n * f n)
  have hind : Function.Injective (fun n : ℕ => p*n) := fun a b h => (Nat.mul_right_inj hp).mp h
  have hsub : Function.support g ⊆ Set.range (fun n : ℕ => p*n) := by
    intro n hn
    by_contra h
    have hn' : ¬ p ∣ n := by
      rintro ⟨k, hk⟩
      exact h ⟨k, hk.symm⟩
    exact hn (by simp [g, divIndicator, hn'])
  change (∑' n, g n) = _
  rw [← hind.tsum_eq hsub]
  simp only [g, divIndicator, Nat.dvd_mul_right, if_true, one_mul, weight_mul, mul_assoc,
    tsum_mul_left, avg]

def omegaP (P : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ P, divIndicator p n
def mass (s : ℝ) (P : Finset ℕ) : ℝ := ∑ p ∈ P, weight s p

lemma bounded_omega (P : Finset ℕ) : bounded (omegaP P) :=
  bounded_sum _ _ (fun p _ => bounded_div p)

lemma avg_div (s : ℝ) {p : ℕ} (hp : p ≠ 0) :
    avg s (divIndicator p) = weight s p * avg s (fun _ => 1) := by
  simpa using avg_dilate s hp (fun _ => 1)

lemma avg_omega {s : ℝ} (hs : 1 < s) {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    avg s (omegaP P) = mass s P * avg s (fun _ => 1) := by
  unfold omegaP mass
  rw [avg_sum hs P _ (fun p _ => bounded_div p), Finset.sum_mul]
  exact Finset.sum_congr rfl fun p hp => avg_div s (hP p hp).ne_zero

lemma avg_pair_le (s : ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    avg s (fun n => divIndicator p n * divIndicator q n) ≤
      (weight s p * weight s q + (if p = q then weight s p else 0)) * avg s (fun _ => 1) := by
  by_cases hpq : p = q
  · subst q
    have hf (n : ℕ) : divIndicator p n * divIndicator p n = divIndicator p n := by
      by_cases h : p ∣ n <;> simp [divIndicator, h]
    simp only [hf, avg_div s hp.ne_zero, if_true]
    apply mul_le_mul_of_nonneg_right _ (tsum_nonneg fun n => mul_nonneg (weight_nonneg s n) (by norm_num))
    nlinarith [sq_nonneg (weight s p)]
  · have hc := (Nat.coprime_primes hp hq).mpr hpq
    have hf (n : ℕ) : divIndicator p n * divIndicator q n = divIndicator (p*q) n := by
      have hiff : p*q ∣ n ↔ p ∣ n ∧ q ∣ n :=
        ⟨fun h => ⟨(Nat.dvd_mul_right p q).trans h, (Nat.dvd_mul_left q p).trans h⟩,
          fun ⟨h1, h2⟩ => hc.mul_dvd_of_dvd_of_dvd h1 h2⟩
      by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [divIndicator, hiff, h1, h2]
    simp only [hf, avg_div s (Nat.mul_ne_zero hp.ne_zero hq.ne_zero), weight_mul, if_neg hpq, add_zero,
      le_refl]

lemma second_moment {s : ℝ} (hs : 1 < s) {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    avg s (fun n => omegaP P n * omegaP P n) ≤
      (mass s P * mass s P + mass s P) * avg s (fun _ => 1) := by
  let Z := avg s (fun _ => 1)
  have hω (n : ℕ) : omegaP P n * omegaP P n =
      ∑ p ∈ P, ∑ q ∈ P, divIndicator p n * divIndicator q n := by
    simp only [omegaP, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hb (p : ℕ) := bounded_sum P (fun q n => divIndicator p n * divIndicator q n)
    (fun q _ => bounded_mul (bounded_div p) (bounded_div q))
  simp only [hω]
  rw [avg_sum hs P _ (fun p _ => hb p)]
  simp_rw [avg_sum hs P _ (fun q _ => bounded_mul (bounded_div _) (bounded_div q))]
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, (weight s p * weight s q + (if p = q then weight s p else 0)) * Z :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => avg_pair_le s (hP p hp) (hP q hq)
    _ = _ := by
      simp_rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_ite_eq, mass, Finset.sum_mul, Z]

lemma variance_bound {s : ℝ} (hs : 1 < s) {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    avg s (fun n => (omegaP P n - mass s P)^2) ≤ mass s P * avg s (fun _ => 1) := by
  let L := mass s P
  let ω := omegaP P
  have hω : bounded ω := bounded_omega _
  have h1 := avg_add hs (bounded_mul hω hω) (bounded_mul (bounded_const (-2*L)) hω)
  have h2 := avg_add hs (bounded_add (bounded_mul hω hω) (bounded_mul (bounded_const (-2*L)) hω))
    (bounded_mul (bounded_const (L^2)) (bounded_const 1))
  have hsq (n : ℕ) : (omegaP P n - mass s P)^2 = ω n * ω n + (-2*L) * ω n + L^2 * 1 := by
    dsimp [ω, L]
    ring
  simp_rw [hsq]
  rw [h2, h1, avg_const_mul, avg_const_mul, show avg s ω = L * avg s (fun _ => 1) from avg_omega hs hP]
  linarith only [show avg s (fun n => ω n * ω n) ≤ (L*L+L)*avg s (fun _ => 1)
    from second_moment hs hP]

def charFn (T : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if T n then 1 else 0

lemma charFn_eq (T : ℕ → Prop) (n : ℕ) [Decidable (T n)] :
    charFn T n = if T n then 1 else 0 := by classical simp [charFn]

lemma bounded_char (T : ℕ → Prop) : bounded (charFn T) := by
  classical
  exact ⟨1, fun n => by by_cases h : T n <;> simp [charFn_eq, h]⟩

lemma charFinset_avg (s : ℝ) (S : Finset ℕ) :
    avg s (charFn (· ∈ S)) = ∑ a ∈ S, weight s a := by
  classical
  change (∑' n, weight s n * charFn (· ∈ S) n) = _
  rw [tsum_eq_sum (s := S) (fun n hn => by simp [charFn_eq, hn])]
  exact Finset.sum_congr rfl fun n hn => by simp [charFn_eq, hn]

/-- A random prime dilation takes the upward closure of an antichain into its strict upward closure. -/
lemma primitive_shift {s : ℝ} (hs : 1 < s) {P S : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : ∀ a ∈ S, 2 ≤ a) (hprimitive : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b) :
    ∃ v : ℕ → ℝ, bounded v ∧ (∀ n, v n = 0 ∨ v n = 1) ∧
      mass s P * ((∑ a ∈ S, weight s a) + avg s v) ≤ avg s (fun n => omegaP P n * v n) := by
  classical
  let U (n : ℕ) := ∃ a ∈ S, a ∣ n
  let V (n : ℕ) := U n ∧ n ∉ S
  let v := charFn V
  refine ⟨v, bounded_char _, (fun n => by by_cases h : V n <;> simp [v, charFn_eq, h]), ?_⟩
  have hu (n : ℕ) : charFn U n = charFn (· ∈ S) n + v n := by
    by_cases hn : n ∈ S
    · have hU : U n := ⟨n, hn, dvd_rfl⟩
      simp [v, V, charFn_eq, hn, hU]
    · by_cases hU : U n <;> simp [v, V, charFn_eq, hn, hU]
  have hshift {p : ℕ} (hp : p.Prime) (n : ℕ) : charFn U n ≤ v (p*n) := by
    by_cases hu : U n
    · obtain ⟨a, ha, had⟩ := hu
      have hab : a ∣ p*n := had.trans (Nat.dvd_mul_left n p)
      have hV : V (p*n) := by
        refine ⟨⟨a, ha, hab⟩, fun hs' => ?_⟩
        have hpn := hS _ hs'
        have hn : 0 < n := by
          by_contra! hn
          have : n = 0 := by omega
          simp [this] at hpn
        have hal := Nat.le_of_dvd hn had
        have hlt : n < p*n := by nlinarith [hp.two_le]
        exact hprimitive a ha (p*n) hs' (by omega) hab
      simp [v, charFn_eq, show U n from ⟨a, ha, had⟩, hV]
    · by_cases hv : V (p*n) <;> simp [v, charFn_eq, hu, hv]
  have hUavg : avg s (charFn U) = (∑ a ∈ S, weight s a) + avg s v := by
    calc
      _ = avg s (fun n => charFn (· ∈ S) n + v n) := congrArg (avg s) (funext hu)
      _ = _ := by rw [avg_add hs (bounded_char _) (bounded_char _), charFinset_avg]
  rw [← hUavg]
  have hm (p : ℕ) (hp : p ∈ P) :
      weight s p * avg s (charFn U) ≤ avg s (fun n => divIndicator p n * v n) := by
    rw [avg_dilate s (hP p hp).ne_zero]
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg s p)
    exact avg_mono hs (bounded_char _) ⟨1, fun n =>
      by by_cases h : V (p*n) <;> simp [v, charFn_eq, h]⟩ (hshift (hP p hp))
  simp only [mass, omegaP, Finset.sum_mul]
  rw [avg_sum hs P _ (fun p _ => bounded_mul (bounded_div p) (bounded_char _))]
  exact Finset.sum_le_sum hm

/-- The finite-prime Dirichlet-weight bound, uniform over primitive sets. -/
theorem primitive_dirichlet_bound {s K : ℝ} (hs : 1 < s) (hK : 0 < K) {P S : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hL : K^2 ≤ mass s P)
    (hS : ∀ a ∈ S, 2 ≤ a) (hprimitive : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b) :
    K * (∑ a ∈ S, weight s a) ≤ 2 * ∑' n, weight s n := by
  obtain ⟨v, hv, hv01, hshift⟩ := primitive_shift hs hP hS hprimitive
  let L := mass s P
  let w := omegaP P
  let Z := avg s (fun _ => 1)
  have hz : 0 ≤ Z := tsum_nonneg fun n => mul_nonneg (weight_nonneg s n) (by norm_num)
  have hLpos : 0 < L := (sq_pos_of_pos hK).trans_le hL
  have B := bounded_omega P
  have Bc : bounded (fun n => w n - L) := by
    simpa only [sub_eq_add_neg] using bounded_add B (bounded_const (-L))
  have Bsq : bounded (fun n => (w n - L)^2) := by
    simpa only [sq] using bounded_mul Bc Bc
  have Bv := bounded_mul (bounded_const (K*L)) hv
  have Bt := bounded_mul (bounded_const (K^2)) (bounded_const 1)
  have hpt (n : ℕ) : K * (w n * v n) ≤ (K*L) * v n + (w n - L)^2 + K^2 * 1 := by
    obtain h | h := hv01 n
    · rw [h]
      nlinarith only [sq_nonneg (w n - L), sq_nonneg K]
    · rw [h]
      nlinarith only [sq_nonneg (w n - L - K/2), sq_nonneg K]
  have hmajor := avg_mono hs (bounded_mul (bounded_const K) (bounded_mul B hv))
    (bounded_add (bounded_add Bv Bsq) Bt) hpt
  rw [avg_add hs (bounded_add Bv Bsq) Bt, avg_add hs Bv Bsq,
    avg_const_mul, avg_const_mul, avg_const_mul] at hmajor
  have hvar : avg s (fun n => (w n - L)^2) ≤ L * Z := variance_bound hs hP
  have hh := mul_le_mul_of_nonneg_left hshift hK.le
  have hsmall := mul_le_mul_of_nonneg_right hL hz
  have hfinal : L * (K * ∑ a ∈ S, weight s a) ≤ L * (2*Z) := by
    change K * (L * ((∑ a ∈ S, weight s a) + avg s v)) ≤ K * avg s (fun n => w n * v n) at hh
    change K * avg s (fun n => w n * v n) ≤ K*L*avg s v + avg s (fun n => (w n-L)^2) + K^2*Z at hmajor
    change K^2 * Z ≤ L * Z at hsmall
    linarith only [hh, hmajor, hvar, hsmall]
  have h := (mul_le_mul_iff_right₀ hLpos).mp hfinal
  simpa [Z, avg] using h

end
end Behrend

namespace Behrend

/-- Up to the cutoff, moving from reciprocal to Dirichlet weights costs a factor of e. -/
theorem reciprocal_le_dirichlet {a M : ℕ} (ha : 0 < a) (haM : a ≤ M) (hM : 1 < M) :
    (a : ℝ)⁻¹ ≤ Real.exp 1 * weight (1 + 1 / Real.log (M : ℝ)) a := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hM' : 1 < (M : ℝ) := by exact_mod_cast hM
  have hlog := Real.log_pos hM'
  have hr : (a : ℝ)^(1 / Real.log (M : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos ha']
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_one hlog]
    exact Real.log_le_log ha' (by exact_mod_cast haM)
  have hfactor : (a : ℝ)^(1 / Real.log (M : ℝ)) * weight (1 + 1 / Real.log (M : ℝ)) a
      = (a : ℝ)⁻¹ := by
    unfold weight
    rw [← Real.rpow_add ha']
    rw [show (1 / Real.log (M : ℝ) + - (1 + 1 / Real.log (M : ℝ))) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  rw [← hfactor]
  exact mul_le_mul_of_nonneg_right hr (weight_nonneg _ _)

end Behrend

namespace Behrend
open Filter Finset
open scoped Topology

private lemma finite_primes (L : ℝ) : ∃ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) ∧ L < mass 1 P := by
  have exists_large : ∃ T : Finset Nat.Primes, L < ∑ p ∈ T, (1 / p : ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨T,hT⟩ := exists_large
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨T.map e, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := mem_map.mp hp
    exact q.property
  · simp only [mass, sum_map, weight, Real.rpow_neg_one]
    convert hT using 1
    apply sum_congr rfl
    intro p hp
    change ((p.val : ℝ)⁻¹) = 1 / (p : ℝ)
    rw [one_div]

private noncomputable def tilt (M : ℕ) : ℝ := 1 + 1 / Real.log M

private lemma tilt_lim : Tendsto tilt atTop (𝓝[>] 1) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun M : ℕ => 1 + 1 / Real.log (M:ℝ)) atTop (𝓝 1)
    simpa [one_div] using
      ((tendsto_const_nhds (x := (1:ℝ))).add (tendsto_inv_atTop_zero.comp hlog))
  · filter_upwards [eventually_ge_atTop 2] with M hM
    change 1 < 1 + 1 / Real.log (M:ℝ)
    have : 1 < (M:ℝ) := by exact_mod_cast (show 1 < M by omega)
    have := Real.log_pos this
    exact lt_add_of_pos_right _ (one_div_pos.mpr ‹0 < Real.log (M:ℝ)›)

private lemma mass_cont {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Continuous (fun s : ℝ => mass s P) := by
  apply continuous_finsetSum
  intro p hp
  exact (Real.continuous_const_rpow (show (p:ℝ) ≠ 0 by exact_mod_cast (hP p hp).ne_zero)).comp
    continuous_neg

private lemma zeta_lim : Tendsto
    (fun M => (tilt M-1)*(∑' n : ℕ, weight (tilt M) n)) atTop (𝓝 1) := by
  apply (tendsto_sub_mul_tsum_nat_rpow.comp tilt_lim).congr
  intro M
  simp only [Function.comp_apply, weight, Real.rpow_neg (Nat.cast_nonneg _), one_div]

/-- The Dirichlet estimate is uniform over all primitive sets. Choose a fixed finite
prime set of large reciprocal mass, then approach 1 along 1+1/log M. -/
theorem harmonic_endpoint :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ S : Finset ℕ, (∀ a ∈ S, 2 ≤ a ∧ a ≤ M) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b) →
      ∑ a ∈ S, (1:ℝ)/(a:ℝ) ≤ ε * Real.log M := by
  intro ε hε
  let K := 4 * Real.exp 1 / ε
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨P,hP,hm⟩ := finite_primes (K^2)
  have hmass := ((mass_cont hP).continuousAt.tendsto.comp
    (tendsto_nhds_of_tendsto_nhdsWithin tilt_lim)).eventually_const_lt hm
  have hzeta := zeta_lim.eventually_lt_const (show (1:ℝ)<2 by norm_num)
  have both := (hmass.and hzeta).and (eventually_ge_atTop (2:ℕ))
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.mp both
  refine ⟨M₀, ?_⟩
  intro M hM S hS hprim
  obtain ⟨⟨hmM,hzM⟩,hle⟩ := hM₀ M hM
  have hM2 : 1 < M := by omega
  have hlog := Real.log_pos (show 1 < (M:ℝ) by exact_mod_cast hM2)
  have ht : 1 < tilt M := by dsimp [tilt]; linarith [one_div_pos.mpr hlog]
  have bound := primitive_dirichlet_bound ht hK hP hmM.le (fun a ha => (hS a ha).1) hprim
  have hz : (∑' n : ℕ, weight (tilt M) n) ≤ 2 * Real.log M := by
    change (tilt M - 1) * _ < 2 at hzM
    rw [show tilt M-1 = 1 / Real.log M by dsimp [tilt]; ring, one_div_mul_eq_div,
      div_lt_iff₀ hlog] at hzM
    exact hzM.le
  calc
    ∑ a ∈ S, (1:ℝ)/(a:ℝ) ≤ ∑ a ∈ S, Real.exp 1 * weight (tilt M) a := by
      apply sum_le_sum
      intro a ha
      simpa only [tilt, one_div] using reciprocal_le_dirichlet (by have := (hS a ha).1; omega) (hS a ha).2 hM2
    _ = Real.exp 1 * ∑ a ∈ S, weight (tilt M) a := (mul_sum ..).symm
    _ ≤ ε * Real.log M := by
      apply (mul_le_mul_iff_right₀ hK).mp
      have he : ε*K = 4*Real.exp 1 := by dsimp [K]; field_simp
      calc
        K * (Real.exp 1 * ∑ a ∈ S, weight (tilt M) a) =
          Real.exp 1 * (K * ∑ a ∈ S, weight (tilt M) a) := by ring
        _ ≤ Real.exp 1 * (2*(2*Real.log M)) :=
          mul_le_mul_of_nonneg_left (bound.trans (by linarith)) (Real.exp_pos _).le
        _ = K * (ε * Real.log M) := by linear_combination -Real.log M * he

end Behrend

theorem OMA.solution : OMA.R_Erdos143_erdos_143_parts_i_R1.H1 := Behrend.harmonic_endpoint
