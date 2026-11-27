import FormalConjectures.OEIS.«11545»
import Mathlib
/-! # Decimal square prefixes of pi

Machin's formula and alternating rational bounds on the arctangent verify
the first 511 prefixes (including the single digit 3). For each larger
index an integer square can only come from the lower decimal approximation
to the square root of pi or ten times pi. The scaled error is compared with
a rational threshold; only a band of width one ten-millionth needs a more
precise comparison. The conjecture about squares is due to Wolfgang Haken,
as recorded in OEIS A011545. Credit: @Deldor14.
-/
namespace OMA.R_OeisA11545_conjecture1_R1
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

private theorem tight_upper {a B y C : ℝ} (hB : 100000000 ≤ B) (ha : 1 ≤ a) (hy : 0 ≤ y)
    (root : y ≤ a*B) (gap : (a*B)^2 < y^2+1) (lower : 1 ≤ C*(2*a - 1/100000000)) :
    B*(a*B-y) < C := by
  have bpos : 0 < B := by linarith
  have aB : 1 ≤ a*B := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) bpos.le]
  have diff : a*B < y+1 := by
    by_contra! hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ a*B+(y+1) by linarith)]
  have add : (2*a - 1/100000000)*B ≤ a*B+y := by linarith
  have cpos : 0 ≤ 2*a-1/100000000 := by linarith
  by_contra! bad
  have h1 := mul_le_mul_of_nonneg_left add (sub_nonneg.mpr root)
  have h2 := mul_le_mul_of_nonneg_left bad cpos
  nlinarith only [h1,h2,lower,gap]

private theorem tight_lower {a B y D : ℝ} (ha : 0 ≤ a)
    (upper : D*(2*a) < 1) (gap : B*(a*B-y) ≤ D) : (a*B)^2 < y^2+1 := by
  have h1 := mul_le_mul_of_nonneg_left gap (show 0 ≤ 2*a by linarith)
  have h2 := sq_nonneg (a*B-y)
  nlinarith only [h1,h2,upper]

private theorem constants (r : ℕ) (hr : r < 2) :
    let a := √(π*(10:ℝ)^r)
    1 ≤ a ∧ (if r = 0 then (0.2820947:ℝ) else 0.0892062)*(2*a) < 1 ∧
      1 ≤ (if r = 0 then (0.2820948:ℝ) else 0.0892063)*(2*a-1/100000000) := by
  have p := Real.pi_gt_d20
  have q := Real.pi_lt_d20
  interval_cases r
  · dsimp
    norm_num only [pow_zero,mul_one,if_true,reduceCtorEq]
    have root := Real.sq_sqrt (le_of_lt pi_pos)
    have ha : 1.7724538509 ≤ √π := by nlinarith [Real.sqrt_nonneg π]
    have hb : √π ≤ 1.772453851 := by nlinarith [Real.sqrt_nonneg π]
    constructor <;> [linarith; constructor <;> linarith]
  · dsimp
    norm_num only [pow_one,if_false,reduceCtorEq]
    have root := Real.sq_sqrt (show 0 ≤ π*10 by positivity)
    have ha : 5.6049912163 ≤ √(π*10) := by nlinarith [Real.sqrt_nonneg (π*10)]
    have hb : √(π*10) ≤ 5.6049912165 := by nlinarith [Real.sqrt_nonneg (π*10)]
    constructor <;> [linarith; constructor <;> linarith]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem finite_prefix {n : ℕ} (hn : n ≤ 510) : ¬ IsSquare (OeisA11545.a n) := by
  let L : ℚ := (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336244/10^512)
  let U : ℚ := (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912983367336245/10^512)
  have cert : ∀ s : Fin 511, let b : ℚ := 10^s.val;
      ⌊L*b⌋ = ⌊U*b⌋ ∧ ¬ IsSquare ⌊L*b⌋.toNat := by decide +kernel
  have h := cert ⟨n,by omega⟩
  let b : ℚ := 10^n
  change ⌊L*b⌋ = ⌊U*b⌋ ∧ ¬ IsSquare ⌊L*b⌋.toNat at h
  have pos : (0:ℝ) ≤ (b:ℝ) := by dsimp [b]; positivity
  have bl : ((L*b : ℚ):ℝ) ≤ π*(b:ℝ) := by
    rw [Rat.cast_mul]; exact mul_le_mul_of_nonneg_right pi_interval.1 pos
  have bu : π*(b:ℝ) ≤ ((U*b : ℚ):ℝ) := by
    rw [Rat.cast_mul]; exact mul_le_mul_of_nonneg_right pi_interval.2 pos
  have he : ⌊π*(b:ℝ)⌋ = ⌊L*b⌋ := by
    have l := Int.floor_mono bl
    have u := Int.floor_mono bu
    rw [Rat.floor_cast] at l u
    omega
  have val : OeisA11545.a n = ⌊π*(b:ℝ)⌋.toNat := by simp [OeisA11545.a,b]
  rw [val,he]
  exact h.2

def H1 : Prop := ∀ n : ℕ, 511 ≤ n →
  let r := n%2
  let B : ℕ := 10^(n/2)
  let a := √(π*(10:ℝ)^r)
  let y := ⌊a*B⌋₊
  (if r = 0 then (0.2820947:ℝ) else 0.0892062) < B*(a*B-y)

def H2 : Prop := ∀ n : ℕ, 511 ≤ n →
  let r := n%2
  let B : ℕ := 10^(n/2)
  let a := √(π*(10:ℝ)^r)
  let y := ⌊a*B⌋₊
  (if r = 0 then (0.2820947:ℝ) else 0.0892062) < B*(a*B-y) →
  B*(a*B-y) < (if r = 0 then (0.2820948:ℝ) else 0.0892063) →
    (y:ℝ)^2+1 ≤ π*(10:ℝ)^n

theorem main : H1 → H2 → type_of% @OeisA11545.conjecture1 := by
  intro away boundary n
  by_cases hn : n ≤ 510
  · exact finite_prefix hn
  have hn' : 511 ≤ n := by omega
  let r := n%2
  let B : ℕ := 10^(n/2)
  let a := √(π*(10:ℝ)^r)
  let y := ⌊a*B⌋₊
  have hB : (100000000:ℝ) ≤ B := by
    have h : (10:ℝ)^8 ≤ (10:ℝ)^(n/2) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num [B] at h ⊢
    exact h
  have hconst := constants r (Nat.mod_lt n (by decide))
  have ha : 1 ≤ a := hconst.1
  have root : (y:ℝ) ≤ a*B := Nat.floor_le (mul_nonneg (by linarith) (by positivity))
  have hs : (a*(B:ℝ))^2 = π*(10:ℝ)^n := by
    dsimp [a,B]
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    push_cast
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    dsimp [r]
    omega
  rintro ⟨k,hk⟩
  have hk' : ⌊π*(10:ℝ)^n⌋₊ = k*k := by
    simpa [OeisA11545.a,Int.floor_toNat] using hk
  have raw := (Nat.floor_eq_iff (show (0:ℝ) ≤ π*10^n by positivity)).mp hk'
  push_cast at raw
  have kl : (k:ℝ) ≤ a*B := by
    by_contra! big
    have pos : 0 < (k:ℝ) + a*B := by nlinarith [mul_nonneg (show 0 ≤ a by linarith) (B.cast_nonneg (α:=ℝ))]
    nlinarith [mul_pos (sub_pos.mpr big) pos, raw.1]
  have ku : a*B < (k:ℝ)+1 := by
    by_contra! bad
    have pos : 0 ≤ a*B+(k+1) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr bad) pos, raw.2]
  have ky : y=k := (Nat.floor_eq_iff (show 0 ≤ a*B by positivity)).mpr ⟨kl,ku⟩
  have gap : (a*B)^2 < (y:ℝ)^2+1 := by rw [ky,hs]; nlinarith only [raw.2]
  have hi := tight_upper hB ha (Nat.cast_nonneg y) root gap hconst.2.2
  exact (not_lt_of_ge (boundary n hn' (away n hn') hi)) (hs ▸ gap)

end OMA.R_OeisA11545_conjecture1_R1
