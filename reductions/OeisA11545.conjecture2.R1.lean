import FormalConjectures.OEIS.«11545»
import Mathlib
/-! # Decimal collisions in the digits of pi

We certify 512 decimal places of pi by Machin's identity and exact alternating
series bounds. These exclude every exponent from 0 through 510. For the
remaining exponents a two-term arctangent estimate confines the only
possible integer to the next integer above pi times the decimal scale.
The next integer is compared with a seven-place rational enclosure of the
scaled arctangent correction. Below the enclosure an exception is forced.
The remaining boundary comparison has width one ten-millionth. See also
Jianing Song, OEIS A332045, for the classical first-order bounds.
Credit: @Deldor14.
-/
namespace OMA.R_OeisA11545_conjecture2_R1
open Real Finset Filter
open scoped Topology

private theorem atan_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ i ∈ range (2*k), (-1:ℝ)^i * (x^(2*i+1) / (2*i+1))) ≤ arctan x ∧
    arctan x ≤ ∑ i ∈ range (2*k+1), (-1:ℝ)^i * (x^(2*i+1) / (2*i+1)) := by
  let f (i : ℕ) := x^(2*i+1) / (2*i+1 : ℝ)
  have hanti : Antitone f := by
    intro i j hij
    exact div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx hx1.le (by omega)) (by positivity)
      (by exact_mod_cast (show 2*i+1 ≤ 2*j+1 by omega))
  have hsum := (Real.hasSum_arctan (x:=x) (by simp [Real.norm_eq_abs,abs_of_nonneg hx,hx1])).tendsto_sum_nat
  have hlim : Tendsto (fun n => ∑ i ∈ range n, (-1:ℝ)^i * f i) atTop (𝓝 (arctan x)) := by
    simpa only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_div_assoc] using hsum
  exact ⟨hanti.alternating_series_le_tendsto hlim k, hanti.tendsto_le_alternating_series hlim k⟩

private theorem rational_atan (x : ℚ) (hx : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ((∑ i ∈ range (2*k), (-1:ℚ)^i * (x^(2*i+1) / (2*i+1)) : ℚ) : ℝ) ≤ arctan x ∧
    arctan x ≤ ((∑ i ∈ range (2*k+1), (-1:ℚ)^i * (x^(2*i+1) / (2*i+1)) : ℚ) : ℝ) := by
  push_cast
  exact atan_bounds (by exact_mod_cast hx) (by exact_mod_cast hx1) k

private theorem atan_polynomial {x : ℝ} (hx : 0 ≤ x) (h1 : x < 1) :
    x-x^3/3 ≤ arctan x ∧ arctan x ≤ x-x^3/3+x^5/5 := by
  have h := atan_bounds hx h1 1
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

private theorem width_upper {m c : ℝ} (hm : 1 < m) (hc : 0 < c)
    (bound : c < (3*c-π)*m^2) : π / arctan (1/m) < π*m + c/m := by
  have hm0 : 0 < m := by linarith
  have ha := (atan_polynomial (x:=1/m) (by positivity) (by rw [div_lt_one hm0]; exact hm)).1
  have hpos : 0 < π*m+c/m := by positivity
  apply (div_lt_iff₀ (arctan_pos.mpr (by positivity))).mpr
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left ha hpos.le)
  field_simp
  nlinarith only [bound]

private theorem coarse {m : ℝ} (hm : 10 ≤ m) : π / arctan (1/m) < π*m + 2/m := by
  apply width_upper (by linarith) (by norm_num)
  have hsq : 100 ≤ m^2 := by nlinarith [sq_nonneg (m-10)]
  nlinarith [mul_nonneg (show 0 ≤ 4-π by linarith [pi_lt_four]) (sq_nonneg m)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem pi_interval : (((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336244 / 10^512) : ℚ) : ℝ) ≤ π ∧ π ≤ (((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336245 / 10^512) : ℚ) : ℝ) := by
  let s (x : ℚ) (t : ℕ) : ℚ := ∑ i ∈ range t, (-1:ℚ)^i * (x^(2*i+1) / (2*i+1))
  have h5 := rational_atan (1/5) (by norm_num) (by norm_num) 190
  have h239 := rational_atan (1/239) (by norm_num) (by norm_num) 55
  change (s (1/5) 380 : ℝ) ≤ _ ∧ _ ≤ (s (1/5) 381 : ℝ) at h5
  change (s (1/239) 110 : ℝ) ≤ _ ∧ _ ≤ (s (1/239) 111 : ℝ) at h239
  have bot : ((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336244 / 10^512) : ℚ) ≤ 16*s (1/5) 380-4*s (1/239) 111 := by decide +kernel
  have top : 16*s (1/5) 381-4*s (1/239) 110 ≤ ((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336245 / 10^512) : ℚ) := by decide +kernel
  have bot' : (((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336244 / 10^512) : ℚ):ℝ) ≤ ((16*s (1/5) 380-4*s (1/239) 111 : ℚ):ℝ) := Rat.cast_le.mpr bot
  have top' : ((16*s (1/5) 381-4*s (1/239) 110 : ℚ):ℝ) ≤ (((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336245 / 10^512) : ℚ):ℝ) := Rat.cast_le.mpr top
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat] at bot' top'
  have mach := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, one_div] at h5 h239
  constructor <;> linarith only [h5.1,h5.2,h239.1,h239.2,mach,bot',top']

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem first_cases {n : ℕ} (hn : n ≤ 510) :
    ¬ ∃ k : ℤ, π*(10:ℝ)^n < k ∧ (k:ℝ) < π / arctan (1 / (10:ℝ)^n) := by
  rintro ⟨k,hlo,hhi⟩
  cases n with
  | zero =>
    norm_num [arctan_one, pi_ne_zero] at hlo hhi
    have h3 : (3:ℝ) < k := pi_gt_three.trans hlo
    have h4 : (k:ℝ) < 4 := by simpa [div_div_eq_mul_div, pi_ne_zero] using hhi
    have : (3:ℤ)<k := by exact_mod_cast h3
    have : k<(4:ℤ) := by exact_mod_cast h4
    omega
  | succ t =>
    let L : ℚ := (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336244 / 10^512)
    let U : ℚ := (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336245 / 10^512)
    let M : ℚ := 10^(t+1)
    have cert : ∀ s : Fin 510, let m : ℚ := 10^(s.val+1);
        U*m+2/m ≤ (⌊L*m⌋:ℚ)+1 := by decide +kernel
    have bot : (L : ℝ) ≤ π := pi_interval.1
    have top : π ≤ (U : ℝ) := pi_interval.2
    have con : U*M+2/M ≤ (⌊L*M⌋:ℚ)+1 := cert ⟨t,by omega⟩
    have con' : (U:ℝ)*(M:ℝ)+2/(M:ℝ) ≤ (⌊L*M⌋:ℝ)+1 := by exact_mod_cast con
    have leL : (⌊L*M⌋:ℝ) ≤ (L:ℝ)*(M:ℝ) := by exact_mod_cast Int.floor_le (L*M)
    have hpow : (M:ℝ) = (10:ℝ)^(t+1) := by simp [M]
    have hm : 10 ≤ (M:ℝ) := by rw [hpow]; exact le_self_pow₀ (by norm_num) (by omega)
    have lo : (⌊L*M⌋:ℝ) < (k:ℝ) :=
      leL.trans_lt ((mul_le_mul_of_nonneg_right bot (by linarith : (0:ℝ) ≤ M)).trans_lt (by rwa [hpow]))
    have hi : (k:ℝ) < (⌊L*M⌋:ℝ)+1 := by
      apply lt_of_lt_of_le _ con'
      apply lt_of_lt_of_le ((show (k:ℝ) < π / arctan (1/(M:ℝ)) by rwa [hpow]).trans (coarse hm))
      exact add_le_add (mul_le_mul_of_nonneg_right top (by linarith : (0:ℝ) ≤ M)) le_rfl
    have lo' : ⌊L*M⌋ < k := by exact_mod_cast lo
    have hi' : k < ⌊L*M⌋+1 := by exact_mod_cast hi
    omega


private theorem sharp_upper {m : ℝ} (hm : 1000000 ≤ m) :
    π/arctan (1/m) < π*m + 1.0471976/m := by
  apply width_upper (by linarith) (by norm_num)
  have huge : 1000000000000 ≤ m^2 := by nlinarith [sq_nonneg (m-1000000)]
  nlinarith only [huge, mul_nonneg (show 0 ≤ 3.141592654-π by linarith [pi_lt_d20]) (sq_nonneg m)]

private theorem sharp_lower {m : ℝ} (hm : 1000000 ≤ m) :
    π*m + 1.0471975/m < π / arctan (1/m) := by
  have hm0 : 0 < m := by linarith
  have ha := (atan_polynomial (x:=1/m) (by positivity) (by rw [div_lt_one hm0]; linarith)).2
  apply (lt_div_iff₀ (arctan_pos.mpr (by positivity))).mpr
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left ha (by positivity))
  have huge : 1000000000000 ≤ m^2 := by nlinarith [sq_nonneg (m-1000000)]
  have fourth : 1000000000000*m^2 ≤ m^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr huge) (sq_nonneg m)]
  have low : 0 ≤ (π-3.141592653)*m^4 := mul_nonneg (by linarith [pi_gt_d20]) (by positivity)
  have high : 0 ≤ (4-π)*m^2 := mul_nonneg (by linarith [pi_lt_four]) (sq_nonneg m)
  field_simp
  nlinarith only [huge,fourth,low,high]

/-- The lower part of the numerical interval forces an actual collision exception. -/
private theorem forces_exception {m : ℝ} {j : ℤ} (hm : 1000000 ≤ m)
    (near : m*(j:ℝ)-π*m^2 ≤ 1.0471975) : (j:ℝ) < π/arctan (1/m) := by
  have hm0 : 0 < m := by linarith
  apply lt_of_le_of_lt _ (sharp_lower hm)
  rw [← mul_le_mul_iff_left₀ hm0]
  have clear : m*(1.0471975/m)=1.0471975 := by field_simp
  nlinarith only [near,clear]

def H1 : Prop :=
  ∀ n : ℕ, 511 ≤ n → let m : ℤ := 10^n; let j := ⌊π*(m:ℝ)⌋+1;
    1.0471975 < (m:ℝ)*(j:ℝ) - π*(m:ℝ)^2

def H2 : Prop :=
  ∀ n : ℕ, 511 ≤ n → let m : ℤ := 10^n; let j := ⌊π*(m:ℝ)⌋+1;
    1.0471975 < (m:ℝ)*(j:ℝ) - π*(m:ℝ)^2 → (m:ℝ)*(j:ℝ) - π*(m:ℝ)^2 < 1.0471976 →
      π ≤ (j:ℝ)*arctan (1/(m:ℝ))

theorem main : H1 → H2 → type_of% @OeisA11545.conjecture2 := by
  intro away edge n
  simp only [Nat.cast_id]
  by_cases hn : n ≤ 510
  · exact first_cases hn
  have hn' : 511 ≤ n := by omega
  let m : ℤ := 10^n
  have hm : (1000000:ℝ) ≤ m := by
    have h : (10:ℝ)^6 ≤ (10:ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num [m] at h ⊢
    exact h
  have hm0 : (0:ℝ) < m := by linarith
  have bound := sharp_upper hm
  have hmcast : (m:ℝ) = (10:ℝ)^n := by simp [m]
  rw [← hmcast]
  rintro ⟨k,lo,hi⟩
  have se : (1.0471976:ℝ)/(m:ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
  have z : k = ⌊π*(m:ℝ)⌋+1 := by
    have a : ⌊π*(m:ℝ)⌋ < k := Int.floor_lt.mpr lo
    have b := Int.lt_floor_add_one (π*(m:ℝ))
    have c : (k:ℝ) < (⌊π*(m:ℝ)⌋:ℝ)+2 := by linarith [hi.trans bound]
    have d : k < ⌊π*(m:ℝ)⌋+2 := by exact_mod_cast c
    omega
  have d1 : (m:ℝ)*(k:ℝ)-π*(m:ℝ)^2 < 1.0471976 := by
    have hmul := mul_lt_mul_of_pos_left (hi.trans bound) hm0
    have clear : (m:ℝ)*(1.0471976/(m:ℝ))=1.0471976 := by field_simp
    nlinarith only [hmul,clear]
  subst k
  exact (not_lt_of_ge (edge n hn' (away n hn') d1)) ((lt_div_iff₀ (arctan_pos.mpr (by positivity))).mp hi)

end OMA.R_OeisA11545_conjecture2_R1

