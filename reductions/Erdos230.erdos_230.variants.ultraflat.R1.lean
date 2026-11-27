import FormalConjectures.ErdosProblems.«230»
import Mathlib

/-! # Rounding disk-valued coefficients for ultraflat polynomials

The analytic input asks for approximately flat disk-valued polynomials on a
finite mesh with small total squared-modulus deficit. For each coefficient the
two ends of its perpendicular chord have unit norm. A finite sign-balancing
estimate chooses one end of every chord simultaneously at every mesh point.
An elementary power-difference bound extends the result to the whole circle.
See Bombieri and Bourgain, JEMS 11 (2009), 627–703, in particular Lemma 15. -/

namespace OMA.R_Erdos230_erdos_230_variants_ultraflat_R1

open Finset Real Filter Topology
open scoped Classical



-- A disk-valued polynomial with a small squared-modulus deficit and small
-- normalized error on a mesh of 8(n+1)^2+1 unit-circle sample points.
def H1 : Prop := ∃ (c : (n : ℕ) → Fin n → ℂ) (e : ℕ → ℝ),
    (∀ n k, ‖c n k‖ ≤ 1) ∧ Tendsto e atTop (𝓝 0) ∧
    (∀ n (j : Fin (8*(n+1)^2+1)),
      let z := Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)
      |‖∑ k, c n k*z^(k.val+1)‖/√n-1| ≤ e n) ∧
    Tendsto (fun n => (1+(∑ k, (1-‖c n k‖^2))) *
      log (4*((8*(n+1)^2+1:ℕ):ℝ))/(n:ℝ)) atTop (𝓝 0)

-- A finite real sign-balancing bound, independently provable by averaging
-- exponential moments on the Boolean cube.
def H2 : Prop := ∀ (n : ℕ) (J : Type) [Fintype J] [Nonempty J] (w : J → Fin n → ℝ)
    (V t : ℝ), 0<t → (∀ j, ∑ k,(w j k)^2 ≤ V) →
    ∃ s : Fin n → Bool, ∀ j, t * (∑ k, (if s k then (1:ℝ) else -1)*w j k) ≤
      log (Fintype.card J) + t^2*V/2



lemma grid_unit {n : ℕ} (j : Fin (8*(n+1)^2+1)) :
    ‖Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)‖=1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma grid_near (n : ℕ) {z : ℂ} (hz : ‖z‖=1) :
    ∃ j : Fin (8*(n+1)^2+1), ‖z-Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)‖ ≤ 1/((n+1:ℕ):ℝ)^2 := by
  classical
  let gridSize (n : ℕ) := 8*(n+1)^2+1
  let grid (n : ℕ) (j : Fin (gridSize n)) : ℂ :=
    Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)
  change ∃ j : Fin (gridSize n), ‖z-grid n j‖ ≤ 1/((n+1:ℕ):ℝ)^2
  let N : ℝ := ((n+1:ℕ):ℝ)^2
  have pos : 0 < N := by dsimp [N]; positivity
  let u := (z.arg+4)*N
  have ar := abs_le.mp (Complex.abs_arg_le_pi z)
  have u0 : 0 ≤ u := mul_nonneg (by linarith [Real.pi_lt_four]) pos.le
  have upper : u ≤ 8*N := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) pos.le
  let j : Fin (gridSize n) := ⟨⌊u⌋₊,(Nat.floor_lt u0).mpr (by change u < ((8*((n+1)^2)+1:ℕ):ℝ); push_cast; dsimp [N] at upper; push_cast at upper; linarith)⟩
  let x : ℝ := (j.val:ℝ)/N-4
  have round : |z.arg-x| ≤ 1/N := by
    have a := Nat.floor_le u0
    have b := Nat.lt_floor_add_one u
    change (j.val:ℝ) ≤ (z.arg+4)*N at a
    change (z.arg+4)*N < (j.val:ℝ)+1 at b
    dsimp [x]
    rw [abs_le]
    constructor <;> field_simp [pos.ne'] <;> nlinarith
  refine ⟨j,?_⟩
  have hz' : Complex.exp ((z.arg:ℂ)*Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  have id : z-grid n j =
      (Complex.exp (Complex.I * ((z.arg-x:ℝ):ℂ)) - 1)*Complex.exp ((x:ℂ)*Complex.I) := by
    rw [sub_mul,←Complex.exp_add,one_mul]
    have phase : Complex.I * ((z.arg-x:ℝ):ℂ) + (x:ℂ)*Complex.I = (z.arg:ℂ)*Complex.I := by push_cast; ring
    rw [phase,hz']
  rw [id,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=z.arg-x)).trans (by simpa [N,Real.norm_eq_abs] using round)

lemma power_lip {z w : ℂ} (hz : ‖z‖=1) (hw : ‖w‖=1) (k : ℕ) :
    ‖z^k-w^k‖ ≤ (k:ℝ)*‖z-w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have id : z^(k+1)-w^(k+1) = (z^k-w^k)*z + w^k*(z-w) := by ring
    rw [id]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_pow,hz,hw,one_pow,one_mul,mul_one,Nat.cast_succ]
    linarith

lemma poly_grid {n : ℕ} (a : Fin n → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1) {z w : ℂ}
    (hz : ‖z‖=1) (hw : ‖w‖=1) (h : ‖z-w‖ ≤ 1/((n+1:ℕ):ℝ)^2) :
    ‖(∑ k, a k*z^(k.val+1)) - (∑ k, a k*w^(k.val+1))‖ ≤ 1 := by
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin n, (n:ℝ)*(1/((n+1:ℕ):ℝ)^2) := by
      apply sum_le_sum; intro k _
      rw [←mul_sub,norm_mul]
      have h1 := power_lip hz hw (k.val+1)
      have kn : ((k.val+1:ℕ):ℝ) ≤ n := by exact_mod_cast k.isLt
      calc
        _ ≤ 1*‖z^(k.val+1)-w^(k.val+1)‖ := by gcongr; exact ha k
        _ ≤ (n:ℝ)* (1/((n+1:ℕ):ℝ)^2) := by rw [one_mul]; apply h1.trans; gcongr
    _ ≤ 1 := by
      simp
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma perpendicular_chord (c : ℂ) (hc : ‖c‖≤1) :
    ∃ d : ℂ, ‖d‖^2 = 1-‖c‖^2 ∧
      ∀ b : Bool, ‖c+(Complex.ofReal (if b then 1 else -1))*d‖=1 := by
  let chord (c : ℂ) : ℂ :=
    (Complex.I * (√(1-‖c‖^2):ℝ)) * Complex.exp ((c.arg:ℂ)*Complex.I)
  let signR (b : Bool) : ℝ := if b then 1 else -1
  refine ⟨chord c,?_,?_⟩
  · have h : 0 ≤ 1-‖c‖^2 := by nlinarith [norm_nonneg c]
    simp [chord,Complex.norm_exp_ofReal_mul_I,Real.sq_sqrt h]
  · intro s
    change ‖c+(signR s:ℂ)*chord c‖=1
    let phase := Complex.exp ((c.arg:ℂ)*Complex.I)
    have phase_eq : (‖c‖:ℂ)*phase=c := Complex.norm_mul_exp_arg_mul_I c
    have ph : ‖phase‖=1 := Complex.norm_exp_ofReal_mul_I _
    have hc' : ‖(‖c‖:ℝ)‖ ≤ 1 := by simpa using hc
    have norm_one {v : ℂ} (h : Complex.normSq v=1) : ‖v‖=1 := by
      have sq := (Complex.sq_norm v).trans h
      nlinarith [norm_nonneg v]
    change ‖c+(signR s:ℂ)*((Complex.I * (√(1-‖c‖^2):ℝ))*phase)‖=1
    cases s
    · simp only [signR,Bool.false_eq_true,if_false,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,←sub_eq_add_neg]
      calc
        _ = ‖((‖c‖:ℂ)-Complex.I*(√(1-‖c‖^2):ℝ))*phase‖ := by rw [sub_mul,phase_eq]
        _ = 1 := by rw [norm_mul,ph,mul_one]; exact norm_one (Complex.normSq_ofReal_sub_I_mul_sqrt_one_sub hc')
    · simp only [signR,if_true,Complex.ofReal_one,one_mul]
      calc
        _ = ‖((‖c‖:ℂ)+Complex.I*(√(1-‖c‖^2):ℝ))*phase‖ := by rw [add_mul,phase_eq]
        _ = 1 := by rw [norm_mul,ph,mul_one]; exact norm_one (Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hc')

lemma complex_balance (balance : H2) {n : ℕ} {J : Type} [Fintype J] [Nonempty J]
    (c : J → Fin n → ℂ) (V t : ℝ) (ht : 0<t) (energy : ∀ j, ∑ k, ‖c j k‖^2 ≤ V) :
    ∃ s : Fin n → Bool, ∀ j, t*‖∑ k, (Complex.ofReal (if s k then 1 else -1))*c j k‖ ≤
      2*(log (4*(Fintype.card J:ℝ)) + t^2*V/2) := by
  classical
  let signR (b : Bool) : ℝ := if b then 1 else -1
  let W (j : J × Bool × Bool) (k : Fin n) : ℝ :=
    signR j.2.2 * (if j.2.1 then (c j.1 k).re else (c j.1 k).im)
  have hw (j : J × Bool × Bool) : ∑ k,(W j k)^2 ≤ V := by
    apply le_trans _ (energy j.1)
    apply sum_le_sum; intro k _
    obtain ⟨j,b,d⟩ := j
    cases b <;> cases d <;> simp [W,signR] <;>
      nlinarith [Complex.sq_norm_sub_sq_re (c j k),sq_nonneg (c j k).im,sq_nonneg (c j k).re]
  obtain ⟨s,hs⟩ := balance n (J × Bool × Bool) W V t ht hw
  refine ⟨s,?_⟩
  intro j
  let y := ∑ k, (signR (s k):ℂ)*c j k
  let B := log (4*(Fintype.card J:ℝ))+t^2*V/2
  have card : (Fintype.card (J × Bool × Bool):ℝ) = 4*(Fintype.card J:ℝ) := by simp; ring
  have re : y.re = ∑ k,signR (s k)*(c j k).re := by simp [y,Complex.re_sum,Complex.mul_re]
  have im : y.im = ∑ k,signR (s k)*(c j k).im := by simp [y,Complex.im_sum,Complex.mul_im]
  have xr := hs (j,true,true)
  have xl := hs (j,true,false)
  have yr := hs (j,false,true)
  have yl := hs (j,false,false)
  simp only [W,signR,if_true,Bool.false_eq_true,if_false,one_mul,neg_one_mul,mul_neg,sum_neg_distrib,card] at xr xl yr yl
  change t*‖y‖ ≤ 2*B
  have rx : t*|y.re| ≤ B := by rw [re,←abs_of_pos ht,←abs_mul,abs_le]; constructor <;> dsimp [B,signR] <;> linarith
  have ix : t*|y.im| ≤ B := by rw [im,←abs_of_pos ht,←abs_mul,abs_le]; constructor <;> dsimp [B,signR] <;> linarith
  have h := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im y) ht.le
  linarith

lemma rounded_grid (balance : H2) {n : ℕ} (c : Fin n → ℂ) (hc : ∀ k, ‖c k‖≤1) :
    ∃ a : Fin n → ℂ, (∀ k, ‖a k‖=1) ∧ ∀ j : Fin (8*(n+1)^2+1),
      let z := Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)
      ‖(∑ k, a k*z^(k.val+1)) - (∑ k, c k*z^(k.val+1))‖ ≤
        3*√((1+∑ k, (1-‖c k‖^2))*log (4*((8*(n+1)^2+1:ℕ):ℝ))) := by
  classical
  let signR (b : Bool) : ℝ := if b then 1 else -1
  let gridSize (n : ℕ) := 8*(n+1)^2+1
  let grid (n : ℕ) (j : Fin (gridSize n)) : ℂ :=
    Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)
  let poly {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ := ∑ k, a k*z^(k.val+1)
  let energy {n : ℕ} (c : Fin n → ℂ) : ℝ := ∑ k, (1-‖c k‖^2)
  choose d dSq dUnit using fun k => perpendicular_chord (c k) (hc k)
  change ∃ a : Fin n → ℂ, (∀ k, ‖a k‖=1) ∧ ∀ j : Fin (gridSize n),
    ‖poly a (grid n j) - poly c (grid n j)‖ ≤ 3*√((1+energy c)*log (4*(gridSize n:ℝ)))
  have gu (j : Fin (gridSize n)) : ‖grid n j‖=1 := grid_unit j
  let V := energy c
  have vn : 0≤V := Finset.sum_nonneg (fun i _ => by have := hc i; nlinarith [norm_nonneg (c i)])
  let L := log (4*(gridSize n:ℝ))
  have gpos : 0 < gridSize n := by dsimp [gridSize]; omega
  have gp' : (1:ℝ) ≤ (gridSize n:ℝ) := by exact_mod_cast gpos
  have lp : 0<L := Real.log_pos (by linarith)
  let t := √L / √(1+V)
  have ap : 0<1+V := by linarith
  have tp : 0<t := div_pos (sqrt_pos.mpr lp) (sqrt_pos.mpr ap)
  let w (j : Fin (gridSize n)) (k : Fin n) := d k * (grid n j)^(k.val+1)
  have en (j : Fin (gridSize n)) : ∑ k, ‖w j k‖^2 ≤ V := by
    apply le_of_eq
    simp only [w,norm_mul,norm_pow,gu,one_pow,mul_one,V,energy,dSq]
  let : Nonempty (Fin (gridSize n)) := ⟨⟨0,gpos⟩⟩
  obtain ⟨s,hs⟩ := complex_balance balance w V t tp en
  let a (k : Fin n) := c k + (signR (s k):ℂ)*d k
  refine ⟨a,fun k => dUnit k (s k),?_⟩
  intro j
  have diff : poly a (grid n j) - poly c (grid n j) = ∑ k, (signR (s k):ℂ)*w j k := by
    dsimp only [poly]
    rw [←sum_sub_distrib]
    apply sum_congr rfl; intro k _; dsimp [a,w]; ring
  have h := hs j
  simp only [Fintype.card_fin] at h
  change t*‖∑ k, (signR (s k):ℂ)*w j k‖ ≤ 2*(L+t^2*V/2) at h
  have t2 : t^2*(1+V) = L := by
    dsimp [t]; rw [div_pow,sq_sqrt lp.le,sq_sqrt ap.le]; field_simp
  have bound : t*‖∑ k, (signR (s k):ℂ)*w j k‖ ≤ 3*L := by nlinarith [sq_nonneg t]
  rw [diff]
  change _ ≤ 3*√((1+V)*L)
  apply (le_of_mul_le_mul_left _ tp)
  rw [sqrt_mul ap.le]
  have eq : t*(3*(√(1+V)*√L))=3*L := by
    dsimp [t]; field_simp [(sqrt_pos.mpr ap).ne']; nlinarith [sq_sqrt lp.le]
  rw [eq]; exact bound

lemma transfer {x y : ℂ} {r : ℝ} (hr : 0 < r) :
    |‖x‖/r-1| ≤ ‖x-y‖/r + |‖y‖/r-1| := by
  calc
    _ = |(‖x‖-‖y‖)/r + (‖y‖/r-1)| := by congr 1; ring
    _ ≤ |(‖x‖-‖y‖)/r| + |‖y‖/r-1| := abs_add_le _ _
    _ ≤ _ := by rw [abs_div,abs_of_pos hr]; gcongr; exact abs_norm_sub_norm_le _ _

theorem main : H1 → H2 → type_of% @Erdos230.erdos_230.variants.ultraflat := by
  rintro ⟨c,e,disk,elim,near,small⟩ signs
  classical
  let gridSize (n : ℕ) := 8*(n+1)^2+1
  let grid (n : ℕ) (j : Fin (gridSize n)) : ℂ :=
    Complex.exp (((j.val:ℝ)/((n+1:ℕ):ℝ)^2-4 : ℝ)*Complex.I)
  let poly {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ := ∑ k, a k*z^(k.val+1)
  let energy {n : ℕ} (c : Fin n → ℂ) : ℝ := ∑ k, (1-‖c k‖^2)
  choose a unit close using fun n => rounded_grid signs (c n) (disk n)
  change ∀ n (j : Fin (gridSize n)), ‖poly (a n) (grid n j) - poly (c n) (grid n j)‖ ≤ 3*√((1+energy (c n))*log (4*(gridSize n:ℝ))) at close
  change ∀ n (j : Fin (gridSize n)), |‖poly (c n) (grid n j)‖/√n-1| ≤ e n at near
  refine ⟨a,unit,?_⟩
  let v (n : ℕ) := (1+energy (c n))*log (4*(gridSize n:ℝ))
  let B (n : ℕ) := 1/√(n:ℝ) + 3*√(v n/(n:ℝ)) + e n
  have lim1 : Tendsto (fun n : ℕ => 1/√(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have lim2 : Tendsto (fun n : ℕ => 3*√(v n/(n:ℝ))) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => v n/(n:ℝ)) atTop (𝓝 0) at small
    simpa only [Real.sqrt_zero,mul_zero] using (small.sqrt.const_mul 3)
  have lim : Tendsto B atTop (𝓝 0) := by simpa [B] using (lim1.add lim2).add elim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
  · filter_upwards with n
    exact Real.iSup_nonneg (fun z => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast hn
    have rt := sqrt_pos.mpr hp
    apply ciSup_le
    intro z
    have hz : ‖(z:ℂ)‖=1 := by simpa using z.property
    obtain ⟨j,hj⟩ := grid_near n hz
    have gridErr := poly_grid (a n) (fun k => (unit n k).le) hz (grid_unit j) hj
    have tr := dist_triangle (poly (a n) z) (poly (a n) (grid n j)) (poly (c n) (grid n j))
    simp only [dist_eq_norm] at tr
    have df : ‖poly (a n) z-poly (c n) (grid n j)‖ ≤ 1+3*√(v n) :=
      tr.trans (add_le_add gridErr (close n j))
    change |‖poly (a n) z‖/√(n:ℝ)-1| ≤ B n
    apply (transfer (x:=poly (a n) z) (y:=poly (c n) (grid n j)) rt).trans
    apply (add_le_add (div_le_div_of_nonneg_right df rt.le) (near n j)).trans
    have posv : 0 ≤ v n := by
      have en : 0 ≤ energy (c n) := Finset.sum_nonneg (fun k _ => by have := disk n k; nlinarith [norm_nonneg (c n k)])
      have gp : 0 < gridSize n := by dsimp [gridSize]; omega
      have gp' : (1:ℝ) ≤ (gridSize n:ℝ) := by exact_mod_cast gp
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    dsimp only [B]
    rw [sqrt_div posv]
    ring_nf
    exact le_rfl


end OMA.R_Erdos230_erdos_230_variants_ultraflat_R1
