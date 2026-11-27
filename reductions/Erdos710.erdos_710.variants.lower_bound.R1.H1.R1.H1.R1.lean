import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1
import Mathlib

/-! Supporting powers for smooth numbers. View a factorization as a lattice
point in the simplex with weights log p. Translation by one unit box in
every coordinate costs at most d log y, where d counts primes below y.
Maximizing the logarithm of the count minus a linear function gives a
supporting power. The scalar deficit u-1-log u locates the maximizer. -/
namespace OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1_H1_R1

open Filter Finset Real
open scoped Topology

/-- Logarithmic form of the inner and outer simplex volume estimates.
The additive constant is the same at all radii. -/
def H1 : Prop := ∀ y : ℕ, 3 ≤ y → ∃ C : ℝ, ∀ v : ℝ, 1 ≤ v →
    let d := (y.primesBelow.card:ℝ)
    let f := log ((Nat.smoothNumbersUpTo ⌊exp v⌋₊ y).card:ℝ)
    C + d*log v ≤ f ∧ f ≤ C + d*log (v+d*log y)

/-- The prime number theorem in dimension-count form. -/
def H2 : Prop := Tendsto (fun y : ℕ => (y.primesBelow.card:ℝ)*log y/y) atTop (𝓝 1)

lemma locate {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 < u → u-1-log u ≤ ε → 1-δ ≤ u ∧ u ≤ 1+δ := by
  have pos (c : ℝ) (hc : 0 < c) (hc1 : c ≠ 1) : 0 < c-1-log c := by
    linarith only [Real.log_lt_sub_one_of_pos hc hc1]
  let ε := min ((1-δ)-1-log (1-δ)) ((1+δ)-1-log (1+δ))/2
  have hl := pos (1-δ) (by linarith) (by linarith)
  have hr := pos (1+δ) (by linarith) (by linarith)
  have mins := lt_min hl hr
  refine ⟨ε,by dsimp [ε]; positivity,?_⟩
  intro u hu hsmall
  have bound (c : ℝ) (hc : 0 < c) (cross : 0 ≤ (u-c)*(c-1)) :
      c-1-log c ≤ u-1-log u := by
    have H := Real.log_le_sub_one_of_pos (div_pos hu hc)
    rw [Real.log_div hu.ne' hc.ne'] at H
    have R : u/c ≤ u-c+1 := (div_le_iff₀ hc).mpr (by nlinarith only [cross])
    linarith only [R,H]
  dsimp [ε] at hsmall
  constructor
  · by_contra! h
    have H := bound (1-δ) (by linarith) (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    linarith only [H,hsmall,min_le_left ((1-δ)-1-log (1-δ)) ((1+δ)-1-log (1+δ)),mins]
  · by_contra! h
    have H := bound (1+δ) (by linarith) (mul_nonneg (by linarith) (by linarith))
    linarith only [H,hsmall,min_le_right ((1-δ)-1-log (1-δ)) ((1+δ)-1-log (1+δ)),mins]

private lemma maximize (y : ℕ) (hy : 3 ≤ y) (hlog : 24 ≤ log y)
    (d C : ℝ) (hd : 1 ≤ d)
    (vol : ∀ v : ℝ, 1 ≤ v →
      C+d*log v ≤ log ((Nat.smoothNumbersUpTo ⌊exp v⌋₊ y).card:ℝ) ∧
      log ((Nat.smoothNumbersUpTo ⌊exp v⌋₊ y).card:ℝ) ≤ C+d*log (v+d*log y))
    (δ : ℝ) (hδ : 0 < δ) (δs : δ < 1/8)
    (loc : ∀ u : ℝ, 0 < u → u-1-log u ≤ 4/log y → 1-δ ≤ u ∧ u ≤ 1+δ)
    (shift : 4/log y ≤ δ) :
    let W := d*(log y)^2/4
    ∃ m : ℕ, 0 < m ∧ (1-2*δ)*W ≤ log m ∧ log m ≤ (1+δ)*W ∧
      ∀ z : ℕ, m/y ≤ z → z ≤ m*y →
        ((Nat.smoothNumbersUpTo z y).card:ℝ) ≤
          (Nat.smoothNumbersUpTo m y).card * ((z:ℝ)/m)^(4/(log y)^2:ℝ) := by
  intro W
  let w := log (y:ℝ)
  let σ := 4/w^2
  let T := d*w
  let F := fun m : ℕ => ((Nat.smoothNumbersUpTo m y).card:ℝ)
  have hw : 0 < w := by dsimp [w]; linarith
  have dpos : 0 < d := by linarith
  have wp : 0 < W := by dsimp [W]; positivity
  have sp : 0 < σ := by dsimp [σ]; positivity
  have sW : σ*W=d := by dsimp [σ,W,w]; field_simp
  have TW : T/W=4/w := by dsimp [T,W,w]; field_simp
  have Wlarge : 6*w ≤ W := by
    change 24 ≤ w at hlog
    have H := mul_le_mul_of_nonneg_right hd (sq_nonneg w)
    change 6*w ≤ d*w^2/4
    nlinarith only [H,mul_nonneg (sub_nonneg.mpr hlog) hw.le]
  have W1 : 2 ≤ W := by dsimp [w] at Wlarge; linarith
  let b := ⌊exp W⌋₊
  let M := ⌊exp (4*W)⌋₊
  have b3 : 3 ≤ b := (Nat.le_floor_iff (Real.exp_pos W).le).mpr (by
    push_cast; linarith [Real.add_one_le_exp W])
  have bM : b ≤ M := Nat.floor_mono (exp_le_exp.mpr (by linarith))
  let G := fun k : ℕ => log (F k) - σ*log k
  obtain ⟨m,hm,maxim⟩ := Finset.exists_max_image (Icc 3 M) G ⟨b,mem_Icc.mpr ⟨b3,bM⟩⟩
  have m3 := (mem_Icc.mp hm).1
  have mp : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have bp : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have logb : log b ≤ W := by
    rw [← Real.log_exp W]
    exact Real.log_le_log bp (Nat.floor_le (exp_pos W).le)
  have lm : 1 ≤ log m := by
    have h3 : Real.exp 1 ≤ (3:ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
    exact (Real.le_log_iff_exp_le mp).mpr (h3.trans (by exact_mod_cast m3))
  have up := (vol (log m) lm).2
  rw [Real.exp_log mp,Nat.floor_natCast] at up
  change log (F m) ≤ C+d*log (log m+T) at up
  have lo := (vol W (by linarith)).1
  change C+d*log W ≤ log (F b) at lo
  have mx := maxim b (mem_Icc.mpr ⟨b3,bM⟩)
  change log (F b)-σ*log b ≤ log (F m)-σ*log m at mx
  let u := (log m + T)/W
  have tp : 0 ≤ T := mul_nonneg dpos.le hw.le
  have upos : 0 < u := div_pos (by linarith) wp
  have ugap : u-1-log u ≤ T/W := by
    have lgu : log (log m+T) = log u + log W := by
      dsimp [u]; rw [Real.log_div (by linarith) wp.ne']; ring
    have us : d*u = σ*(log m+T) := by
      dsimp [u]
      rw [←sW]; field_simp
    have ts : d*(T/W) = σ*T := by rw [←sW]; field_simp
    have loss := mul_le_mul_of_nonneg_left logb sp.le
    apply (mul_le_mul_iff_right₀ dpos).mp
    rw [mul_sub,mul_sub,mul_one,us,ts]
    rw [lgu] at up
    linarith only [mx,up,lo,loss,sW]
  have limits := loc u upos (by rwa [TW] at ugap)
  have ueq : (u-T/W)*W = log m := by dsimp [u]; field_simp; ring
  have lower : (1-2*δ)*W ≤ log m := by
    rw [←ueq]
    apply mul_le_mul_of_nonneg_right _ wp.le
    rw [TW]
    linarith only [limits.1,shift]
  have upper : log m ≤ (1+δ)*W := by
    rw [←ueq]
    exact mul_le_mul_of_nonneg_right (by linarith only [limits.2,div_nonneg tp wp.le]) wp.le
  refine ⟨m,by omega,lower,upper,?_⟩
  intro z hz₁ hz₂
  have ymin : (3:ℝ) ≤ y := by exact_mod_cast hy
  have yp : 0 < (y:ℝ) := by linarith
  have wy3 : 3*(y:ℝ) ≤ m := by
    have lw : log (y:ℝ) ≤ w := le_rfl
    have lg3 : log (3:ℝ) ≤ w := Real.log_le_log (by norm_num) ymin
    have h2 : 2*w ≤ (1-2*δ)*W := by
      have hhalf := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)/2 ≤ 1-2*δ) wp.le
      linarith
    apply (Real.log_le_log_iff (by positivity) mp).mp
    rw [Real.log_mul (by norm_num) yp.ne']; linarith
  have three : 3 ≤ z := (Nat.le_div_iff_mul_le (by omega : 0 < y)).mpr
    (by exact_mod_cast wy3) |>.trans hz₁
  have zp : 0 < (z:ℝ) := by exact_mod_cast (show 0 < z by omega)
  have zM : z ≤ M := by
    apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    apply (Real.log_le_iff_le_exp zp).mp
    have logzy := Real.log_le_log zp (by exact_mod_cast hz₂ : (z:ℝ) ≤ (m:ℝ)*y)
    rw [Real.log_mul mp.ne' yp.ne'] at logzy
    have hu2 := mul_le_mul_of_nonneg_right (by linarith : 1+δ ≤ 2) wp.le
    change log (z:ℝ) ≤ log (m:ℝ)+w at logzy
    linarith
  have fmpos (k : ℕ) (hk : 1 ≤ k) : 0 < F k := by
    dsimp [F]
    exact_mod_cast (Finset.card_pos.mpr ⟨1,Nat.mem_smoothNumbersUpTo.mpr
      ⟨hk,by simp [Nat.mem_smoothNumbers]⟩⟩ : 0 < (Nat.smoothNumbersUpTo k y).card)
  have fm := fmpos m (by omega)
  have fz := fmpos z (by omega)
  have mz := maxim z (mem_Icc.mpr ⟨three,zM⟩)
  change log (F z)-σ*log z ≤ log (F m)-σ*log m at mz
  change F z ≤ F m * ((z:ℝ)/m)^σ
  apply (Real.log_le_log_iff fz (mul_pos fm (Real.rpow_pos_of_pos (div_pos zp mp) σ))).mp
  rw [Real.log_mul fm.ne' (Real.rpow_pos_of_pos (div_pos zp mp) σ).ne',
    Real.log_rpow (div_pos zp mp),Real.log_div zp.ne' mp.ne']
  linarith only [mz]

theorem main : H1 → H2 → OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1.H1 := by
  intro vol primes ξ hp hs
  let δ := ξ/8
  have dp : 0 < δ := by dsimp [δ]; positivity
  have ds : δ < 1/8 := by dsimp [δ]; linarith
  obtain ⟨ε,ep,loc⟩ := locate dp (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun y : ℕ => 4/log y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  filter_upwards [eventually_ge_atTop (3:ℕ),hlog.eventually_ge_atTop 24,
      ht.eventually_lt_const ep,ht.eventually_lt_const dp,
      primes.eventually_const_lt (by linarith : 1-δ < 1),
      primes.eventually_lt_const (by linarith : 1 < 1+δ)] with y hy hw he hδ pmin pmax
  obtain ⟨C,hC⟩ := vol y hy
  let d := (y.primesBelow.card:ℝ)
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Finset.card_pos.mpr ⟨2,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩⟩ :
      1 ≤ y.primesBelow.card)
  obtain ⟨m,hm,lo,hi,support⟩ := maximize y hy hw d C hd hC δ dp ds
    (fun u hu h => loc u hu (h.trans he.le)) hδ.le
  change (1-2*δ)*(d*(log y)^2/4) ≤ log m at lo
  change log m ≤ (1+δ)*(d*(log y)^2/4) at hi
  change 1-δ < d*log y/y at pmin
  change d*log y/y < 1+δ at pmax
  have yp : 0 < (y:ℝ) := by exact_mod_cast (show 0 < y by omega)
  have wpos : 0 ≤ log (y:ℝ) := by change 24 ≤ log y at hw; linarith
  have p₁ := (lt_div_iff₀ yp).mp pmin
  have p₂ := (div_lt_iff₀ yp).mp pmax
  have ul : (1-ξ) ≤ (1-2*δ)*(1-δ) := by dsimp [δ]; nlinarith [sq_nonneg ξ]
  have uu : (1+δ)*(1+δ) ≤ 1+ξ := by
    dsimp [δ]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hs.le)]
  refine ⟨m,hm,?_,?_,support⟩
  · have A := mul_le_mul_of_nonneg_right ul (mul_nonneg yp.le wpos)
    have B := mul_le_mul_of_nonneg_right p₁.le (mul_nonneg (by linarith : 0 ≤ 1-2*δ) wpos)
    linarith only [A,B,lo]
  · have A := mul_le_mul_of_nonneg_right uu (mul_nonneg yp.le wpos)
    have B := mul_le_mul_of_nonneg_right p₂.le (mul_nonneg (by linarith : 0 ≤ 1+δ) wpos)
    linarith only [A,B,hi]

end OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1_H1_R1
