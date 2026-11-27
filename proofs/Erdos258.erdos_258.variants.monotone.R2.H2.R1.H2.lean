import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1
import Mathlib

/-! A square array of distinct primes prescribes exact valuations in an
initial block. Later shifts are coprime to the CRT modulus, so counting
small divisor pairs on one progression bounds their first moment.
The summability and pointwise geometric majorant are reused from
@marcusbuffett's merged companion proof of Erdős 258, monotone H1. -/
open Finset Real
namespace Window258
-- The polynomial nth-prime estimate is adapted from @loremcdmx's merged Erdős 5
-- proof via @marcusbuffett's Erdős 980 quadratic reduction.

lemma key (m : ℕ) (hm : 16 ≤ m) : Nat.nth Nat.Prime m ≤ m ^ 2 := by
  have hm' : (16:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Chebyshev.pi_ge (m ^ 2)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2 : Real.log (((m ^ 2 : ℕ) : ℝ)) = 2 * Real.log m := by
    push_cast; rw [Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hA : Real.log (m : ℝ) ≤ m / 8 + 3 := by
    have h8 : Real.log ((m:ℝ) / 8) ≤ m / 8 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h2' := Real.log_two_lt_d9
    linarith
  have h2' := Real.log_two_lt_d9
  have hB : Real.log (((m ^ 2 : ℕ) : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log m := by
    have e : Real.log (2 * (m:ℝ) ^ 2) = Real.log 2 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    rw [← e]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have h3 : (m:ℝ) * Real.log m ≤ (m:ℝ) * (m / 8 + 3) := mul_le_mul_of_nonneg_left hA hm0
  have h4 : (m:ℝ)^2 * 0.69 ≤ (m:ℝ)^2 * Real.log 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlt : (m : ℝ) < (((m ^ 2 : ℕ) : ℝ) * Real.log 2 - Real.log (((m ^ 2 : ℕ) : ℝ) + 1)) / Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    rw [hl2, lt_div_iff₀ (by linarith)]
    push_cast at hB ⊢
    nlinarith
  have hcnt : (m : ℝ) < (Nat.primeCounting (m ^ 2) : ℝ) := lt_of_lt_of_le hlt hpi
  have hcnt' : m < Nat.primeCounting (m ^ 2) := by exact_mod_cast hcnt
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m ^ 2 + 1) (k := m) hcnt'
  omega

lemma windowCRT (k J t : ℕ) (ht : 2 ≤ t) : ∃ M a : ℕ,
    a < M ∧ M ≤ (J+k+20+k*k)^(2*t*(k*k)) ∧ ∀ N : ℕ, N ≡ a [MOD M] →
    (∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧
    (∀ i < J, (i+(N+k)+1).Coprime M) := by
  classical
  let L := Fin k × Fin k
  let base := J+k+20
  let idx (x : L) : ℕ := base + (finProdFinEquiv x).val
  let p (x : L) := Nat.nth Nat.Prime (idx x)
  have pp (x : L) : (p x).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have pinj : Function.Injective p := by
    intro x y he
    have he' := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective he
    exact finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel he'))
  have plo (x : L) : J+k+1 < p x := by
    have hl : idx x ≤ p x := Nat.le_nth (fun h => (Nat.infinite_setOfPred_prime h).elim)
    dsimp [idx,base] at hl
    omega
  have phi (x : L) : p x ≤ (base+k*k)^2 := by
    refine (key _ (by dsimp [idx,base]; omega)).trans (Nat.pow_le_pow_left ?_ 2)
    exact Nat.add_le_add_left (finProdFinEquiv x).isLt.le _
  let m (x : L) := p x ^ t
  let v (x : L) := p x ^ (t-1) - (x.1.val+1)
  let M := ∏ x, m x
  have hm (x : L) (_ : x ∈ (univ : Finset L)) : m x ≠ 0 := pow_ne_zero _ (pp x).ne_zero
  have pair : Set.Pairwise (↑(univ : Finset L)) (fun x y => (m x).Coprime (m y)) := by
    intro x _ y _ h
    exact (((Nat.coprime_primes (pp x) (pp y)).mpr (pinj.ne h)).pow_left _).pow_right _
  let a := Nat.chineseRemainderOfFinset v m univ hm pair
  refine ⟨M,a,Nat.chineseRemainderOfFinset_lt_prod v m hm pair,?_,?_⟩
  · calc
      M ≤ ∏ _x : L, ((base+k*k)^2)^t := prod_le_prod' fun x _ => Nat.pow_le_pow_left (phi x) _
      _ = _ := by simp [L,base,←pow_mul]
  intro N hN
  have congru (x : L) : N+(x.1.val+1) ≡ p x^(t-1) [MOD m x] := by
    have h := ((hN.of_dvd (dvd_prod_of_mem m (mem_univ x))).trans (a.2 x (mem_univ x))).add_right (x.1.val+1)
    have hsmall : x.1.val+1 ≤ p x ^ (t-1) :=
      (by have := plo x; have := x.1.isLt; omega : x.1.val+1 ≤ p x).trans (Nat.le_self_pow (by omega : t-1≠0) _)
    simpa [v,Nat.sub_add_cancel hsmall] using h
  have val (x : L) : (N+(x.1.val+1)).factorization (p x) = t-1 := by
    have h := congru x
    have hne : N+(x.1.val+1) ≠ 0 := by omega
    have lo := ((pp x).pow_dvd_iff_le_factorization hne).mp ((h.dvd_iff (pow_dvd_pow _ (Nat.sub_le t 1))).mpr dvd_rfl)
    have hi : ¬p x^t ∣ N+(x.1.val+1) := by
      rw [h.dvd_iff (dvd_refl (m x)),Nat.pow_dvd_pow_iff_le_right (pp x).one_lt]
      omega
    rw [(pp x).pow_dvd_iff_le_factorization hne] at hi
    omega
  have dvd (x : L) : p x ∣ N+(x.1.val+1) := by
    apply (Nat.Prime.dvd_iff_one_le_factorization (pp x) (by omega)).mpr
    rw [val]; omega
  constructor
  · intro j hj
    obtain ⟨hj0,hjk⟩ := mem_Icc.mp hj
    let u : Fin k := ⟨j-1,by omega⟩
    have eu : u.val+1=j := by dsimp [u]; omega
    let S := univ.image (fun l : Fin k => p (u,l))
    have hsub : S ⊆ (N+j).primeFactors := by
      intro n hn
      obtain ⟨l,_,rfl⟩ := mem_image.mp hn
      exact Nat.mem_primeFactors.mpr ⟨pp _,by simpa [eu] using dvd (u,l),by omega⟩
    have prodS : S.prod (fun n => (N+j).factorization n+1) = t^k := by
      rw [show S = univ.image (fun l : Fin k => p (u,l)) by rfl,
        prod_image (fun x _ y _ h => congrArg Prod.snd (pinj h))]
      have H (l : Fin k) : (N+j).factorization (p (u,l))+1=t := by
        have := val (u,l); simp only [eu] at this; omega
      simp [H]
    rw [Nat.card_divisors (by omega : N+j≠0)]
    exact (pow_dvd_pow _ hjk).trans (prodS ▸ prod_dvd_prod_of_subset S _ (fun n => (N+j).factorization n+1) hsub)
  · intro i hi
    apply Nat.coprime_prod_right_iff.mpr
    intro x _
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (pp x).coprime_iff_not_dvd.mpr
    intro hd
    have hdiff := Nat.dvd_sub hd (dvd x)
    have e : i+(N+k)+1-(N+(x.1.val+1))=i+k-x.1.val := by omega
    rw [e] at hdiff
    have hx := x.1.isLt
    have hpos : 0 < i+k-x.1.val := by omega
    have := Nat.le_of_dvd hpos hdiff
    have := plo x
    omega
end Window258
open Finset Real
namespace Window258
lemma hyperbola {n D : ℕ} (hn : n ≠ 0) (hD : n ≤ D * D) :
    n.divisors.card ≤ 2 * ((Icc 1 D).filter (· ∣ n)).card := by
  classical
  let S := (Icc 1 D).filter (· ∣ n)
  have sub : n.divisors ⊆ S ∪ S.image (n / ·) := by
    intro d hd
    obtain ⟨hdn,_⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
    by_cases h : d ≤ D
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,h⟩,hdn⟩)
    · have hdq := Nat.div_mul_cancel hdn
      have hq : n / d ≤ D := by
        by_contra! hh
        nlinarith only [Nat.mul_lt_mul_of_lt_of_lt hh (lt_of_not_ge h),hdq,hD]
      have hdvd := Nat.div_dvd_of_dvd hdn
      exact mem_union_right _ (mem_image.mpr ⟨n/d,mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn),hq⟩,hdvd⟩,
        Nat.div_div_self hdn hn⟩)
  calc
    _ ≤ (S ∪ S.image (n / ·)).card := card_le_card sub
    _ ≤ S.card + (S.image (n / ·)).card := card_union_le ..
    _ ≤ _ := by have h := card_image_le (f := (n / ·)) (s := S); dsimp [S] at *; omega

lemma hits (A M B d : ℕ) (hc : ∀ r < B, (A+M*r).Coprime M) :
    ((range B).filter (fun r => d ∣ A+M*r)).card ≤ B/d+1 := by
  classical
  rw [← card_range (B/d+1)]
  apply card_le_card_of_injOn (fun r => r/d)
  · intro r hr
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hr).1).le))
  · intro r hr s hs he
    obtain ⟨hrB,hrd⟩ := mem_filter.mp hr
    obtain ⟨hsB,hsd⟩ := mem_filter.mp hs
    have h1 := (Nat.modEq_zero_iff_dvd.mpr hrd).trans (Nat.modEq_zero_iff_dvd.mpr hsd).symm
    have hm := Nat.ModEq.add_left_cancel' A h1
    have hc' := (hc r (mem_range.mp hrB)).coprime_dvd_left hrd
    have h2 := Nat.ModEq.cancel_left_of_coprime hc' hm
    change r % d = s % d at h2
    change r / d = s / d at he
    have h3 := Nat.mod_add_div r d
    rw [h2,he,Nat.mod_add_div] at h3
    exact h3.symm

lemma mean (A M B : ℕ) (hc : ∀ r < B, (A+M*r).Coprime M)
    (hB : ∀ r < B, 0 < A+M*r ∧ A+M*r ≤ B*B) :
    (∑ r ∈ range B, ((A+M*r).divisors.card : ℝ)) ≤ 2*B*(2+log B) := by
  classical
  let I := Icc 1 B
  have count : (∑ r ∈ range B, (((I.filter (· ∣ A+M*r)).card):ℝ)) =
      ∑ d ∈ I, (((range B).filter (fun r => d ∣ A+M*r)).card:ℝ) := by
    calc
      _ = ∑ r ∈ range B, ∑ d ∈ I, if d ∣ A+M*r then (1:ℝ) else 0 := by
        apply sum_congr rfl; intro r hr; rw [←sum_filter]; simp
      _ = _ := by
        rw [sum_comm]; apply sum_congr rfl; intro d hd; rw [←sum_filter]; simp
  have har := harmonic_le_one_add_log B
  rw [harmonic_eq_sum_Icc] at har
  push_cast at har
  calc
    _ ≤ ∑ r ∈ range B, 2 * (((I.filter (· ∣ A+M*r)).card):ℝ) := by
      apply sum_le_sum; intro r hr
      obtain ⟨h1,h2⟩ := hB r (mem_range.mp hr)
      exact_mod_cast hyperbola h1.ne' h2
    _ = 2 * ∑ d ∈ I, (((range B).filter (fun r => d ∣ A+M*r)).card:ℝ) := by rw [←mul_sum,count]
    _ ≤ 2 * ∑ d ∈ I, ((B:ℝ)*(d:ℝ)⁻¹+1) := by
      gcongr with d hd
      have hd0 : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
      have hdiv : ((B/d:ℕ):ℝ) ≤ (B:ℝ)/d := by
        apply (le_div_iff₀ hd0).mpr; exact_mod_cast Nat.div_mul_le_self B d
      have h := hits A M B d hc
      rw [←div_eq_mul_inv]
      exact (by exact_mod_cast h : _ ≤ ((B/d:ℕ):ℝ)+1) |>.trans (by linarith)
    _ ≤ _ := by
      rw [sum_add_distrib, ←mul_sum]
      simp [I] at *
      nlinarith only [mul_le_mul_of_nonneg_left har (Nat.cast_nonneg B : (0:ℝ)≤B)]
noncomputable def G (n : ℕ) : ℝ := ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
noncomputable def b (k : ℕ) : ℝ := ((k:ℝ)+1)*((1:ℝ)/2)^k

lemma bsum : Summable b := by
  have h : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 1 (r:=1/2) (by norm_num)
  change Summable (fun k : ℕ => b k)
  simpa [b,add_mul] using h.add (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))

lemma dom (n k : ℕ) : ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k ≤ ((n:ℝ)+1)*b k := by
  have h : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
  push_cast at h
  unfold b
  rw [div_pow,one_pow,←mul_assoc,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [h,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg k : (0:ℝ)≤k)]

lemma gs (n : ℕ) : Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (dom n) (bsum.mul_left _)

lemma tail_select (A M B k J : ℕ) (hBp : 0 < B)
    (hc : ∀ i < J, ∀ r < B, (i+(A+M*r+k)+1).Coprime M)
    (hn : ∀ i < J, ∀ r < B, i+(A+M*r+k)+1 ≤ B*B)
    (hcut : ∀ r < B, J+(A+M*r+k)+1 ≤ 2^J) :
    ∃ r < B, G (A+M*r+k) ≤ 4*(2+log B) + ∑' i, b i := by
  classical
  let f (r i : ℕ) : ℝ := ((i+(A+M*r+k)+1).divisors.card:ℝ) / 2^i
  have m (i : ℕ) (hi : i < J) : (∑ r ∈ range B, f r i) ≤ 2*B*(2+log B)/(2:ℝ)^i := by
    dsimp [f]; rw [←sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      mean (i+A+k+1) M B (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc i hi)
        (fun r hr => ⟨by omega, by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn i hi r hr⟩)
  have g : (∑ i ∈ range J, (2:ℝ)⁻¹^i) ≤ 2 := by
    have h := (summable_geometric_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)).sum_le_tsum
      (range J) (fun _ _ => by positivity)
    rwa [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num),show (1-(2:ℝ)⁻¹)⁻¹=2 by norm_num] at h
  have p : 0 ≤ 2*(B:ℝ)*(2+log B) := by
    have := Real.log_nonneg (show 1 ≤ (B:ℝ) by exact_mod_cast hBp); positivity
  have mainSum : (∑ r ∈ range B, ∑ i ∈ range J, f r i) ≤ ∑ _r ∈ range B, 4*(2+log (B:ℝ)) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ i ∈ range J, (2*(B:ℝ)*(2+log B)) * ((2:ℝ)⁻¹)^i :=
        sum_le_sum fun i hi => by simpa only [div_eq_mul_inv,inv_pow] using m i (mem_range.mp hi)
      _ ≤ _ := by
        rw [←mul_sum]
        simp only [sum_const,card_range,nsmul_eq_mul]
        nlinarith only [mul_le_mul_of_nonneg_left g p]
  obtain ⟨r,hr,hs⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr hBp.ne') mainSum
  refine ⟨r,mem_range.mp hr,?_⟩
  have tail (i : ℕ) : f r (i+J) ≤ b i := by
    change ((i+J+(A+M*r+k)+1).divisors.card:ℝ)/(2:ℝ)^(i+J) ≤ _
    rw [show i+J+(A+M*r+k)+1=i+(J+(A+M*r+k))+1 by omega,pow_add,←div_div]
    apply (div_le_iff₀ (by positivity)).mpr
    have H := dom (J+(A+M*r+k)) i
    have hcap : ((J+(A+M*r+k):ℕ):ℝ)+1 ≤ (2:ℝ)^J := by exact_mod_cast hcut r (mem_range.mp hr)
    exact H.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hcap (by dsimp [b]; positivity : 0 ≤ b i))
  change (∑' i, f r i) ≤ _
  have sf : Summable (f r) := gs _
  rw [←sf.sum_add_tsum_nat_add J]
  exact add_le_add hs (((summable_nat_add_iff J).mpr sf).tsum_le_tsum tail bsum)
end Window258
namespace Window258
open Filter
lemma assemble (q X t k J B : ℕ) (ht : 2 ≤ t) (hBp : 0 < B)
    (hroom : ((B+2)*(J+k+20+k*k)^(2*t*(k*k))+k+1)*⌊(log X)^(7/8:ℝ)⌋₊ ≤ X)
    (hbase : 0 < ⌊(log X)^(7/8:ℝ)⌋₊)
    (hsq : J+X+1 ≤ B*B) (hcut : J+X+1 ≤ 2^J)
    (hgoal : (q:ℝ)*(4*(2+log B)+∑' i,b i) < (2:ℝ)^k)
    (I : Finset ℕ) (hI : I ⊆ Icc 1 X) (convex : ∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I)
    (hsize : X/⌊(log X)^(7/8:ℝ)⌋₊ ≤ I.card) :
    ∃ N k : ℕ, Icc (N+1) (N+k) ⊆ I ∧ (∀ j ∈ Icc 1 k,t^j ∣ (N+j).divisors.card) ∧
       (q:ℝ)*G (N+k) < (t:ℝ)^k := by
  obtain ⟨M,a,ha,hM,good⟩ := windowCRT k J t ht
  have span : (B+2)*M+k+1 ≤ I.card := by
    refine le_trans ?_ ((Nat.le_div_iff_mul_le hbase).mpr hroom |>.trans hsize)
    gcongr
  have ne : I.Nonempty := card_pos.mp (by omega)
  let lo := I.min' ne
  let hi := I.max' ne
  have hlo : lo ∈ I := I.min'_mem ne
  have hhi : hi ∈ I := I.max'_mem ne
  have len : I.card ≤ hi+1-lo := by
    rw [←Nat.card_Icc]
    exact card_le_card (fun i h => mem_Icc.mpr ⟨I.min'_le i h,I.le_max' i h⟩)
  have lh : lo ≤ hi := I.min'_le _ hhi
  let A := a+M*(lo/M+1)
  have hmp : M ≠ 0 := by omega
  have lb : lo ≤ A := by
    have h := Nat.mod_add_div lo M
    have := Nat.mod_lt lo (Nat.pos_of_ne_zero hmp)
    dsimp [A]; rw [Nat.mul_add]; omega
  have ub : A ≤ lo+2*M := by
    have := Nat.div_mul_le_self lo M
    dsimp [A]; rw [Nat.mul_add,Nat.mul_comm M (lo/M)]; omega
  have con (r : ℕ) : A+M*r ≡ a [MOD M] := by
    simp [A,Nat.ModEq,Nat.add_mod]
  have endpt (r : ℕ) (hr : r < B) : A+M*r+k ≤ hi := by
    have H := Nat.mul_le_mul_left M hr.le
    rw [Nat.add_mul,Nat.mul_comm B M] at span
    omega
  have endX (r : ℕ) (hr : r < B) := (endpt r hr).trans (mem_Icc.mp (hI hhi)).2
  obtain ⟨r,hr,hgood⟩ := tail_select A M B k J hBp
    (fun i hi r _ => (good _ (con r)).2 _ hi)
    (fun i hi r hr => by have := endX r hr; omega)
    (fun r hr => by have := endX r hr; omega)
  refine ⟨A+M*r,k,fun n hn => convex lo hlo hi hhi ?_,(good _ (con r)).1,?_⟩
  · have hn' := mem_Icc.mp hn
    have := endpt r hr
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · exact (mul_le_mul_of_nonneg_left hgood (Nat.cast_nonneg q)).trans_lt
      (hgoal.trans_le (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast ht) k))

end Window258
namespace Window258
open Filter Asymptotics
lemma parameters (q : ℕ) (C : ℝ) : ∀ᶠ X : ℕ in atTop, ∀ t : ℕ, (t:ℝ) ≤ (log X)^(7/8:ℝ) →
    ∃ k J B : ℕ, 0 < B ∧
    ((B+2)*(J+k+20+k*k)^(2*t*(k*k))+k+1)*⌊(log X)^(7/8:ℝ)⌋₊ ≤ X ∧
    0 < ⌊(log X)^(7/8:ℝ)⌋₊ ∧ J+X+1 ≤ B*B ∧ J+X+1 ≤ 2^J ∧
    (q:ℝ)*(4*(2+log B)+C) < (2:ℝ)^k := by
  have hX := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hY := Real.tendsto_log_atTop.comp hX
  have hW := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp hY
  have hZ := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp hX
  have evW := hY.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/32)).bound
    (by norm_num : (0:ℝ)<1/8))
  have evZ := hX.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/8)).bound
    (by norm_num : (0:ℝ)<1))
  filter_upwards [hW.eventually_ge_atTop 64,hZ.eventually_ge_atTop 64,hY.eventually_ge_atTop 32,
    hY.eventually_gt_atTop ((q:ℝ)*(12+|C|)),evW,evZ,eventually_ge_atTop 1]
    with X hw hz hy hq ew ez hXp t ht
  let y := log (X:ℝ)
  let w := y^(1/32:ℝ)
  let z := (X:ℝ)^(1/8:ℝ)
  change 64 ≤ w at hw
  change 64 ≤ z at hz
  change 32 ≤ y at hy
  change (q:ℝ)*(12+|C|)<y at hq
  change (t:ℝ) ≤ y^(7/8:ℝ) at ht
  change ‖log y‖ ≤ (1/8:ℝ)*‖w‖ at ew
  change ‖y‖ ≤ 1*‖z‖ at ez
  have ly := log_nonneg (show 1 ≤ y by linarith)
  rw [Real.norm_of_nonneg ly,Real.norm_of_nonneg (by linarith)] at ew
  rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith),one_mul] at ez
  have wp : 0 ≤ w := by linarith
  have zp : 0 ≤ z := by linarith
  have wpow (n : ℕ) : w^n = y^((1/32:ℝ)*n) := (rpow_mul_natCast (by linarith : 0≤y) _ _).symm
  have yw : w^32 = y := by rw [wpow]; norm_num
  have tw : y^(7/8:ℝ) = w^28 := by rw [wpow]; norm_num
  have zx : z^8 = (X:ℝ) := by dsimp [z]; rw [←rpow_mul_natCast (Nat.cast_nonneg X)]; norm_num
  have incw {a b : ℕ} (h : a ≤ b) : w^a ≤ w^b := pow_le_pow_right₀ (by linarith) h
  have incz {a b : ℕ} (h : a ≤ b) : z^a ≤ z^b := pow_le_pow_right₀ (by linarith) h
  let k := ⌈4*log y⌉₊
  let J := ⌈4*y⌉₊
  let B := ⌈z^5⌉₊
  have kw : (k:ℝ) ≤ w := by
    have h : (k:ℝ) < 4*log y+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have Jy : (J:ℝ) ≤ 5*y := by
    have h : (J:ℝ) < 4*y+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have Jlo : 4*y ≤ (J:ℝ) := Nat.le_ceil _
  have klo : 4*log y ≤ (k:ℝ) := Nat.le_ceil _
  have Blo : z^5 ≤ (B:ℝ) := Nat.le_ceil _
  have Bhi : (B:ℝ) < z^5+1 := Nat.ceil_lt_add_one (by positivity)
  have Bp : 0 < B := by
    have : 0 < (B:ℝ) := (pow_pos (by linarith : 0<z) 5).trans_le Blo
    exact_mod_cast this
  have wy : w ≤ y := by simpa [yw] using incw (show 1≤32 by decide)
  have w2y : w*w ≤ y := by simpa [←pow_two,yw] using incw (show 2≤32 by decide)
  let base := J+k+20+k*k
  have Hbase : (base:ℝ) ≤ 8*y := by
    dsimp [base]; push_cast
    have hkk := mul_self_le_mul_self (Nat.cast_nonneg k : (0:ℝ)≤k) kw
    linarith
  have HBpos : 0 < (base:ℝ) := by dsimp [base]; positivity
  have logbase : log (base:ℝ) ≤ 2*w := by
    have H := Real.log_le_log HBpos Hbase
    rw [log_mul (by norm_num : (8:ℝ)≠0) (by linarith : y≠0)] at H
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
  have ht' : (t:ℝ) ≤ w^28 := tw ▸ ht
  have Mz : ((base^(2*t*(k*k)):ℕ):ℝ) ≤ z := by
    push_cast
    apply (Real.log_le_log_iff (pow_pos HBpos _) (by linarith)).mp
    rw [Real.log_pow,show log z = (1/8:ℝ)*y by exact Real.log_rpow (by exact_mod_cast hXp : (0:ℝ)<X) _]
    push_cast
    calc
      _ ≤ (2*w^28*(w*w))*(2*w) := by
        gcongr
      _ = 4*w^31 := by ring
      _ ≤ _ := by
        rw [←yw,show w^32=w^31*w by ring]
        nlinarith only [mul_nonneg (pow_nonneg wp 31) (show 0≤w-32 by linarith)]
  have z5 : 1 ≤ z^5 := one_le_pow₀ (by linarith)
  have zpwr (i : ℕ) : 32*z^i ≤ z^(i+1) := by
    rw [pow_succ]; nlinarith only [mul_nonneg (pow_nonneg zp i) (show 0≤z-32 by linarith)]
  have z56 : 32*z^5 ≤ z^6 := zpwr 5
  have z67 : 32*z^6 ≤ z^7 := zpwr 6
  have z78 : 32*z^7 ≤ z^8 := zpwr 7
  have z89 : 32*z^8 ≤ z^9 := zpwr 8
  have Bx : (B:ℝ) ≤ X := by
    rw [←zx]; linarith only [Bhi,z5,z56,incz (show 6≤8 by decide)]
  have floorle : (⌊y^(7/8:ℝ)⌋₊:ℝ) ≤ z := by
    refine (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans ?_
    rw [tw]; exact (incw (by decide : 28≤32)).trans (yw ▸ ez)
  have room : ((((B+2)*base^(2*t*(k*k))+k+1)*⌊y^(7/8:ℝ)⌋₊:ℕ):ℝ) ≤ X := by
    push_cast
    calc
      _ ≤ (((z^5+1)+2)*z+z+1)*z := by
        gcongr
        · exact_mod_cast Mz
        · exact kw.trans (wy.trans ez)
      _ ≤ z^8 := by
        have zs : z ≤ z^6 := by simpa using incz (show 1≤6 by decide)
        nlinarith only [z78,z67,incz (show 2≤6 by decide),zs,hz]
      _ = _ := zx
  have X2 : (J:ℝ)+1 ≤ X := by
    have zs : z ≤ z^7 := by simpa using incz (show 1≤7 by decide)
    linarith only [Jy,ez,zs,z78,zx,hz]
  have sqcap : (J:ℝ)+X+1 ≤ (B:ℝ)*B := by
    have hbb := mul_self_le_mul_self (pow_nonneg zp 5) Blo
    have e : z^5*z^5=z^10 := by ring
    linarith only [X2,zx,z89,incz (by decide : 9≤10),hbb,e,Nat.cast_nonneg X (α:=ℝ)]
  have expo : 2*(X:ℝ) ≤ (2:ℝ)^J := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by exact_mod_cast hXp : (0:ℝ)<X).ne',Real.log_pow]
    change log 2+y ≤ (J:ℝ)*log 2
    have e2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
    nlinarith only [mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg J),Jlo,hy,log_two_lt_d9]
  have scale : y^2 ≤ (2:ℝ)^k := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have e2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
    nlinarith only [mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg k),klo]
  have fp : 0 < ⌊y^(7/8:ℝ)⌋₊ := by
    apply Nat.floor_pos.mpr
    rw [tw]; exact one_le_pow₀ (by linarith)
  refine ⟨k,J,B,Bp,by exact_mod_cast room,fp,by exact_mod_cast sqcap,?_,?_⟩
  · exact_mod_cast (show (J:ℝ)+X+1 ≤ (2:ℝ)^J by linarith only [expo,X2])
  · have hlogB : log (B:ℝ) ≤ y := Real.log_le_log (by exact_mod_cast Bp) Bx
    have hfac : 4*(2+log B)+C ≤ (12+|C|)*y := by
      nlinarith only [hlogB,le_abs_self C,abs_nonneg C,hy,
        mul_nonneg (abs_nonneg C) (show 0≤y-1 by linarith)]
    calc
      _ ≤ (q:ℝ)*((12+|C|)*y) := mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg q)
      _ < y^2 := by nlinarith only [mul_lt_mul_of_pos_right hq (by linarith : 0<y)]
      _ ≤ _ := scale
end Window258

theorem OMA.solution : OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.H2 := by
  intro q _
  filter_upwards [Window258.parameters q (∑' i, Window258.b i)] with X hX t ht ht' I hI hconv hsize
  obtain ⟨k,J,B,hB,hroom,hfloor,hsq,hcut,hgoal⟩ := hX t ht'
  exact Window258.assemble q X t k J B ht hB hroom hfloor hsq hcut hgoal I hI hconv hsize
