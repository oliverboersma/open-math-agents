import OMAReductions.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1
import Mathlib

/-!
# Exceptional primes for a logarithmic least quadratic nonresidue

We use the second moment of quadratic characters and bound an incomplete sum
for two distinct primes by its full period, using only the Chinese remainder
theorem. As amplifiers we take squarefree products of about
7 log(x)/(24 log(log(x))) primes below log(x)^8. Chebyshev's elementary
prime-counting bound supplies enough distinct products.

Source problem: Erdős 980, quadratic variant. Credit: @physbuzz.
-/

namespace OMA.Nonresidue
open Finset

/-- A finite family of bounded vectors cannot agree on a large set if all pairwise
correlations are small. The diagonal and off-diagonal contributions are separated. -/
theorem moment {α : Type} [DecidableEq α] (P : Finset α) (S : Finset ℕ) (N : ℕ)
    (f : α → ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hS : S ⊆ range N)
    (h1 : ∀ p ∈ P, ∀ m ∈ S, f p m = 1)
    (hd : ∀ p ∈ P, ∑ m ∈ range N, f p m * f p m ≤ N)
    (hc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∑ m ∈ range N, f p m * f q m ≤ M) :
    (S.card:ℝ) * P.card^2 ≤ P.card*N + P.card^2*M := by
  let T (m : ℕ) := ∑ p ∈ P, f p m
  have full : (∑ m ∈ S, T m ^ 2) = (S.card:ℝ)*P.card^2 := by
    have on (m) (hm : m ∈ S) : T m = (P.card:ℝ) := by
      simp [T,sum_congr rfl (fun p hp => h1 p hp m hm)]
    rw [sum_congr rfl (fun m hm => congrArg (fun z : ℝ => z^2) (on m hm))]
    simp
  have lb := sum_le_sum_of_subset_of_nonneg (f := fun m => T m ^ 2) hS (fun _ _ _ => sq_nonneg _)
  rw [full] at lb
  have expan : (∑ m ∈ range N, T m^2) = ∑ p ∈ P, ∑ q ∈ P, ∑ m ∈ range N, f p m*f q m := by
    simp_rw [T,pow_two,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [sum_comm]
  rw [expan] at lb
  have lineBound (p) (hp : p ∈ P) : (∑ q ∈ P, ∑ m ∈ range N, f p m*f q m) ≤ N + P.card*M := by
    have h := sum_le_sum (s := P.erase p) (g := fun _ => M) (fun q hq =>
      hc p hp q (mem_erase.mp hq).2 (mem_erase.mp hq).1.symm)
    rw [sum_const,nsmul_eq_mul] at h
    have size : ((P.erase p).card:ℝ) ≤ P.card := by exact_mod_cast card_le_card (erase_subset p P)
    have ee := sum_erase_add (s := P) (fun q => ∑ m ∈ range N, f p m*f q m) hp
    linarith [hd p hp, mul_le_mul_of_nonneg_right size hM]
  have top := sum_le_sum (s := P) (fun p hp => lineBound p hp)
  rw [sum_const,nsmul_eq_mul] at top
  nlinarith only [lb,top]

/-- A bounded, zero-average periodic sequence has partial sums at most its period. -/
theorem interval_bound (f : ℕ → ℤ) {L : ℕ} (hL : 0 < L)
    (per : Function.Periodic f L) (cancel : ∑ i ∈ range L, f i = 0)
    (hh : ∀ i, f i ≤ 1) (N : ℕ) : ∑ i ∈ range N, f i ≤ (L:ℤ) := by
  have block (k : ℕ) : ∑ i ∈ range (k*L), f i = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul,sum_range_add,ih,zero_add]
      convert cancel using 2 with i
      rw [Nat.add_comm]
      exact (per.nat_mul k) i
  have decomp : N = (N/L)*L+N%L := by simpa only [Nat.mul_comm] using (Nat.div_add_mod N L).symm
  conv_lhs => rw [decomp,sum_range_add,block,zero_add]
  have h := sum_le_sum (s := range (N%L)) (g := fun _ => (1:ℤ)) (fun i _ => hh ((N/L)*L+i))
  simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at h
  have := Nat.mod_lt N hL
  omega

/-- Lifting a function on residues to the first complete interval preserves its sum. -/
lemma sum_mod {L : ℕ} [NeZero L] (g : ZMod L → ℤ) :
    ∑ i ∈ range L, g i = ∑ a : ZMod L, g a := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => g i)]
  have agree (i : Fin L) : (i.val : ZMod L) = ZMod.finEquiv L i := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    exact ZMod.natCast_zmod_val (ZMod.finEquiv (k+1) i)
  simp_rw [agree]
  exact (ZMod.finEquiv L).toEquiv.sum_comp g

noncomputable def chi (p m : ℕ) : ℤ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    quadraticChar (ZMod p) (m : ZMod p)
  else 0

lemma chi_range (p m : ℕ) : chi p m = 0 ∨ chi p m = 1 ∨ chi p m = -1 := by
  unfold chi
  split_ifs with h
  · letI : Fact p.Prime := ⟨h⟩
    exact quadraticChar_isQuadratic (ZMod p) _
  · simp

lemma correlation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hodd : p ≠ 2)
    (hne : p ≠ q) (N : ℕ) :
    ∑ m ∈ range N, chi p m * chi q m ≤ (p*q:ℕ) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let e := ZMod.chineseRemainder (hp.coprime_iff_not_dvd.mpr (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)))
  let F (u : ZMod p × ZMod q) := quadraticChar (ZMod p) u.1 * quadraticChar (ZMod q) u.2
  let G (z : ZMod (p*q)) := F (e z)
  have eq (m : ℕ) : chi p m * chi q m = G m := by
    simp [chi,hp,hq,G,F]
  have periodic : Function.Periodic (fun m : ℕ => G m) (p*q) := by
    intro m
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  have cz : ∑ a : ZMod p, quadraticChar (ZMod p) a = 0 :=
    quadraticChar_sum_zero (by simpa only [ZMod.ringChar_zmod_n] using hodd)
  have cancel : ∑ m ∈ range (p*q), G m = 0 := by
    rw [sum_mod,show (∑ z, G z) = ∑ u, F u from e.toEquiv.sum_comp F]
    simp only [F,Fintype.sum_prod_type,← mul_sum,← sum_mul,cz,zero_mul]
  simp_rw [eq]
  apply interval_bound _ (Nat.mul_pos hp.pos hq.pos) periodic cancel _ N
  intro m
  rw [← eq]
  rcases chi_range p m with h|h|h <;> rcases chi_range q m with k|k|k <;> rw [h,k] <;> decide

open Erdos980 Filter

private def products (y k : ℕ) : Finset ℕ :=
  ((Nat.primesLE y).powersetCard k).image (fun t => ∏ q ∈ t, q)

lemma card_products (y k : ℕ) : (products y k).card = (Nat.primeCounting y).choose k := by
  have contains {s t : Finset ℕ} (ps : s ⊆ Nat.primesLE y) (pt : t ⊆ Nat.primesLE y)
      (he : (∏ q ∈ s, q) = ∏ q ∈ t, q) : s ⊆ t := by
    intro a ha
    have ap := (Nat.mem_primesLE.mp (ps ha)).2
    have hd := Finset.dvd_prod_of_mem (fun x : ℕ => x) ha
    rw [he] at hd
    obtain ⟨b,hb,hab⟩ := (ap.prime.dvd_finsetProd_iff id).mp hd
    have bp := (Nat.mem_primesLE.mp (pt hb)).2
    exact (Nat.prime_dvd_prime_iff_eq ap bp).mp hab ▸ hb
  unfold products
  rw [card_image_of_injOn,card_powersetCard,Nat.primesLE_card_eq_primeCounting]
  intro s hs t ht he
  exact Subset.antisymm (contains (mem_powersetCard.mp hs).1 (mem_powersetCard.mp ht).1 he)
    (contains (mem_powersetCard.mp ht).1 (mem_powersetCard.mp hs).1 he.symm)

lemma products_size (y k : ℕ) : products y k ⊆ range (y^k+1) := by
  intro m hm
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
  obtain ⟨hs,hk⟩ := mem_powersetCard.mp ht
  have h := t.prod_le_pow_card id y (fun q hq => (Nat.mem_primesLE.mp (hs hq)).1)
  simpa [hk] using h

lemma smaller (p q : ℕ) (hq : q.Prime) (hlt : q < leastNonresidue 2 p) :
    ∃ z : ZMod p, z^2 = (q:ZMod p) := by
  by_contra h
  exact hlt.not_ge (Nat.sInf_le (s := {n : ℕ | 0 < n ∧ ¬∃ z : ZMod p, z^2=(n:ZMod p)}) ⟨hq.pos,h⟩)

lemma products_one {y k p : ℕ} (hp : p.Prime) (hy : y < leastNonresidue 2 p)
    {m : ℕ} (hm : m ∈ products y k) : chi p m = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have cap := OMA.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1.pointwise p hp
  let a := leastNonresidue 2 p
  change a*(a-1) < p at cap
  have ay : y < a := hy
  have yp : y < p := by
    by_cases ha : 2 ≤ a
    · have h := Nat.le_mul_of_pos_right a (show 0 < a-1 by omega)
      omega
    · have := hp.two_le
      omega
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hm
  obtain ⟨hs,_⟩ := mem_powersetCard.mp ht
  simp only [chi,dif_pos hp,Nat.cast_prod,map_prod]
  apply prod_eq_one
  intro q hq
  obtain ⟨hsmall,hprime⟩ := Nat.mem_primesLE.mp (hs hq)
  have hpos := hprime.pos
  have nz : (q : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
    have := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨z,hz⟩ := smaller p q hprime (hsmall.trans_lt hy)
  exact (quadraticChar_one_iff_isSquare nz).mpr ⟨z,by rw [← hz,pow_two]⟩

/-- The remaining numerical estimates involve only the prime counting function and binomial coefficients. -/
def SmoothInput : Prop := ∀ᶠ x : ℝ in atTop, ∃ y k : ℕ,
    (y:ℝ) ≤ (Real.log x)^8 ∧ ((y^k+1:ℕ):ℝ) ≤ 2*x^((7:ℝ)/3) ∧
    4*x^2 ≤ ((Nat.primeCounting y).choose k : ℝ)

theorem exceptional_of_products (smooth : SmoothInput) :
    OMA.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1.H2 := by
  classical
  filter_upwards [smooth,eventually_ge_atTop (1:ℝ)] with x hs hx
  obtain ⟨y,k,hy,hN,hB⟩ := hs
  let P := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p%2=1 ∧
      (Real.log x)^8 < (leastNonresidue 2 p : ℝ))
  change (P.card:ℝ) ≤ _
  have props (p) (hp : p ∈ P) : p.Prime ∧ p≠2 ∧ (p:ℝ) ≤ x ∧ y < leastNonresidue 2 p := by
    obtain ⟨hpr,odd,lt⟩ := mem_filter.mp hp
    obtain ⟨hpx,prime⟩ := Nat.mem_primesBelow.mp hpr
    exact ⟨prime,by omega,(Nat.lt_ceil.mp hpx).le,by exact_mod_cast hy.trans_lt lt⟩
  let N := y^k+1
  have aux := moment P (products y k) N (fun p m => (chi p m:ℝ)) (x^2) (sq_nonneg x)
    (products_size y k) (by
      intro p hp m hm
      rw [products_one (props p hp).1 (props p hp).2.2.2 hm]
      norm_num) (by
      intro p hp
      have h := sum_le_sum (s := range N) (g := fun _ => (1:ℝ)) (fun m _ => show
          (chi p m:ℝ)*(chi p m:ℝ) ≤ 1 by rcases chi_range p m with h|h|h <;> rw [h] <;> norm_num)
      simpa using h) (by
      intro p hp q hq hne
      have prod := correlation (props p hp).1 (props q hq).1 (props p hp).2.1 hne N
      have pr : (∑ m ∈ range N, (chi p m:ℝ)*(chi q m:ℝ)) ≤ (p:ℝ)*q := by exact_mod_cast prod
      exact pr.trans (by rw [sq]; gcongr <;> first | exact (props p hp).2.2.1 | exact (props q hq).2.2.1))
  rw [card_products] at aux
  have xp : 0 < x := by linarith
  have er : x^((7:ℝ)/3) = x^2 * x^((1:ℝ)/3) := by
    rw [show (7:ℝ)/3 = 2+(1:ℝ)/3 by norm_num,Real.rpow_add xp,Real.rpow_two]
  rw [er] at hN
  by_contra! bad
  have pos := Real.rpow_pos_of_pos xp ((1:ℝ)/3)
  have pp : (0:ℝ) < P.card := lt_trans pos bad
  have impossible := mul_pos (mul_pos (sq_pos_of_pos xp) pp) (sub_pos.mpr bad)
  dsimp [N] at aux
  nlinarith only [aux, mul_le_mul_of_nonneg_right hB (sq_nonneg (P.card:ℝ)),
    mul_le_mul_of_nonneg_left hN pp.le, impossible, mul_nonneg (sq_nonneg x) (sq_nonneg (P.card:ℝ))]


open Real Filter

private lemma choose_lower {n k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : (k:ℝ)*b+k ≤ n) : b^k ≤ (n.choose k : ℝ) := by
  have hk : k ≤ n := by exact_mod_cast (show (k:ℝ) ≤ n by nlinarith)
  refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) k n)
  apply (le_div_iff₀ (show (0:ℝ) < k.factorial by exact_mod_cast k.factorial_pos)).mpr
  have fac : (k.factorial:ℝ) ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    b^k * (k.factorial:ℝ) ≤ b^k * (k:ℝ)^k := by gcongr
    _ = (b*k)^k := (mul_pow ..).symm
    _ ≤ _ := by
      gcongr
      rw [Nat.cast_sub (by omega : k ≤ n+1)]
      push_cast
      linarith

private lemma many_primes {t l : ℝ} (ht : 2 ≤ t) (hl : 100 ≤ l)
    (eq : log t = l) (htl : 1000*l ≤ t) :
    t^8/(32*l) ≤ (Nat.primeCounting ⌊t^8⌋₊ : ℝ) := by
  have positive : 0 < t := by linarith
  have L : log (t^8) = 8*l := by rw [log_pow,eq]; norm_num
  have t8 : t ≤ t^8 := by simpa using (pow_le_pow_right₀ (by linarith : 1 ≤ t) (by decide : 1 ≤ 8))
  have logbound : log (t^8+2) ≤ 1+8*l := by
    calc
      _ ≤ log (2*t^8) := Real.log_le_log (by positivity) (by linarith)
      _ = log 2 + 8*l := by rw [log_mul (by norm_num) (by positivity),L]
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have numerator : t^8/4 ≤ (t^8-1)*log 2 - log (t^8+2) := by
    have := mul_nonneg (show 0 ≤ t^8-1 by linarith) (show 0 ≤ log 2-1/2 by linarith [Real.log_two_gt_d9])
    nlinarith
  have bound := Chebyshev.pi_ge' (show 1 < t^8 by linarith)
  rw [L] at bound
  apply le_trans _ bound
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right numerator (show 0 ≤ 32*l by linarith)]

theorem smooth_numeric : ∀ᶠ x : ℝ in atTop, ∃ y k : ℕ,
    (y:ℝ) ≤ (Real.log x)^8 ∧ ((y^k+1:ℕ):ℝ) ≤ 2*x^((7:ℝ)/3) ∧
    4*x^2 ≤ ((Nat.primeCounting y).choose k : ℝ) := by
  have little := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/1000)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1000,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 100,
    Real.tendsto_log_atTop.eventually little,eventually_ge_atTop (2:ℝ)] with x ht hl small hx
  let t := log x
  let l := log t
  change 1000 ≤ t at ht
  change 100 ≤ l at hl
  change ‖l‖ ≤ 1/1000*‖t^(1:ℝ)‖ at small
  rw [Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith)] at small
  have htl : 1000*l ≤ t := by linarith
  have lt0 : 0 < l := by linarith
  have tt0 : 0 < t := by linarith
  have xp : 0 < x := by linarith
  let y := ⌊t^8⌋₊
  let k := ⌊7*t/(24*l)⌋₊
  let b := t^7/32
  have hku : (k:ℝ)*(24*l) ≤ 7*t :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hkl : 7*t < ((k:ℝ)+1)*(24*l) :=
    (div_lt_iff₀ (by positivity)).mp (Nat.lt_floor_add_one _)
  have price := many_primes (by linarith : 2 ≤ t) hl (rfl : log t=l) htl
  change t^8/(32*l) ≤ (Nat.primeCounting y : ℝ) at price
  have t7 : 32 ≤ t^7 := by
    have := pow_le_pow_right₀ (by linarith : 1 ≤ t) (by decide : 1 ≤ 7)
    simp only [pow_one] at this
    linarith
  have hchoice : b^k ≤ ((Nat.primeCounting y).choose k : ℝ) := by
    apply choose_lower (by dsimp [b]; positivity)
    apply le_trans _ price
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp [b]
    have a := mul_le_mul_of_nonneg_right hku (show 0 ≤ t^7 by positivity)
    have c := mul_nonneg (show 0 ≤ (k:ℝ)*l by positivity) (show 0 ≤ t^7-32 by linarith)
    nlinarith only [a,c,show 0 ≤ t^8 by positivity]
  have lbLog : (139/20:ℝ)*l ≤ log b := by
    have log32 : log 32 = 5*log 2 := by rw [show (32:ℝ)=2^5 by norm_num,log_pow]; norm_num
    rw [show log b = 7*l-log 32 by dsimp [b,l]; rw [log_div (by positivity) (by norm_num),log_pow]; norm_num,log32]
    linarith [Real.log_two_lt_d9]
  have lo : 4*x^2 ≤ b^k := by
    apply (Real.log_le_log_iff (by positivity) (by dsimp [b]; positivity)).mp
    rw [log_mul (by norm_num) (by positivity),log_pow,log_pow]
    have log4 : log 4 = 2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
    rw [log4]
    change 2*log 2+2*t ≤ (k:ℝ)*log b
    nlinarith only [hkl,htl,ht,Real.log_two_lt_d9,
      mul_le_mul_of_nonneg_left lbLog (show 0 ≤ (k:ℝ) by positivity)]
  have yupper : (y:ℝ) ≤ t^8 := Nat.floor_le (by positivity)
  refine ⟨y,k,yupper,?_,lo.trans hchoice⟩
  have size : (t^8)^k ≤ x^((7:ℝ)/3) := by
    rw [Real.rpow_def_of_pos xp]
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [log_pow,log_pow]
    change (k:ℝ)*(8*l) ≤ t*(7/3)
    linarith
  have one : 1 ≤ x^((7:ℝ)/3) := Real.one_le_rpow (by linarith) (by norm_num)
  push_cast
  have le' := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ y) yupper k
  linarith


end OMA.Nonresidue

theorem OMA.solution : OMA.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1.H2 :=
  OMA.Nonresidue.exceptional_of_products OMA.Nonresidue.smooth_numeric
