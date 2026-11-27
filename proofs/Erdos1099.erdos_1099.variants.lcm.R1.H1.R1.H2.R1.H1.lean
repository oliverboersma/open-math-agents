import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1
import Mathlib

/-! Angular concentration for a large set of primes would give too many distinct
products of fixed length in the short intervals where the logarithmic phases
are close to multiples of two pi. The binomial lower bound is adapted from
OpenAI, TotientFibers/FiniteFiber.lean at adc7f1241b42e322a6451854ab7e4b4c146bf78a
(Apache-2.0). -/
open Finset Filter Real
open scoped Classical Topology

namespace LogPrimePacking

lemma log_separation {a n : ℕ} (ha : 0<a) (han : a≤n) :
    (n:ℝ)-(a:ℝ) ≤ (n:ℝ)*(log (n:ℝ)-log (a:ℝ)) := by
  have ap : (0:ℝ)<a := by exact_mod_cast ha
  have np : (0:ℝ)<n := by exact_mod_cast ha.trans_le han
  have h := Real.log_le_sub_one_of_pos (div_pos ap np)
  rw [Real.log_div ap.ne' np.ne'] at h
  have hh := mul_le_mul_of_nonneg_right h np.le
  simp only [sub_mul,div_mul_cancel₀ _ np.ne',one_mul] at hh
  linarith only [hh]

lemma pack (S : Finset ℕ) (z : ℕ → ℕ) (q Y H : ℝ) (hq : 0<q) (Y1 : 1≤Y) (H0 : 0≤H)
    (hS : ∀ n ∈ S, 0<n ∧ (n:ℝ)≤Y ∧ |q*log n-2*π*(z n)|≤H) :
    (S.card:ℝ) ≤ (q*log Y+H+1)*(2*H*Y/q+1) := by
  let K := ⌊q*log Y+H⌋₊
  have dest (n : ℕ) (hn : n∈S) : z n ∈ range (K+1) := by
    obtain ⟨np,ny,bd⟩ := hS n hn
    have logle := log_le_log (by exact_mod_cast np) ny
    have zm : (z n:ℝ) ≤ 2*π*(z n) := le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    linarith [(abs_le.mp bd).1,mul_le_mul_of_nonneg_left logle hq.le]
  have fiber (j : ℕ) : ((S.filter (fun n=>z n=j)).card:ℝ) ≤ 2*H*Y/q+1 := by
    let T := S.filter (fun n=>z n=j)
    have non : 0 ≤ 2*H*Y/q := by positivity
    by_cases ne : T.Nonempty
    · let a := T.min' ne
      have am : a∈T := min'_mem _ _
      obtain ⟨as,az⟩ := mem_filter.mp am
      obtain ⟨ap,_,ab⟩ := hS a as
      have inj : T.card ≤ (range (⌊2*H*Y/q⌋₊ + 1)).card := by
        apply card_le_card_of_injOn (fun n : ℕ => n-a)
        · intro n hn
          obtain ⟨ns,nz⟩ := mem_filter.mp hn
          obtain ⟨np,ny,nb⟩ := hS n ns
          have an : a≤n := min'_le _ _ hn
          have both : q*(log n-log a)≤2*H := by
            rw [az] at ab
            rw [nz] at nb
            linarith [(abs_le.mp nb).2,(abs_le.mp ab).1]
          have lp : 0≤log n-log a := sub_nonneg.mpr (log_le_log (by exact_mod_cast ap) (by exact_mod_cast an))
          have eq := log_separation ap an
          have dist : (n:ℝ)-(a:ℝ)≤ Y*(2*H/q) :=
            eq.trans (mul_le_mul ny ((le_div_iff₀ hq).2 (by linarith only [both])) lp (by linarith))
          apply mem_range.mpr
          apply Nat.lt_succ_of_le
          apply Nat.le_floor
          rw [Nat.cast_sub an]
          exact dist.trans_eq (by ring)
        · intro n hn m hm e
          have := min'_le T n hn
          have := min'_le T m hm
          change n-a=m-a at e
          omega
      have cast : (T.card:ℝ) ≤ (⌊2*H*Y/q⌋₊:ℝ)+1 := by exact_mod_cast (by simpa using inj : T.card ≤ ⌊2*H*Y/q⌋₊+1)
      exact cast.trans (by linarith [Nat.floor_le non])
    · have te := not_nonempty_iff_eq_empty.mp ne
      change (T.card:ℝ) ≤ _
      simp only [te,card_empty,Nat.cast_zero]
      linarith
  have count := Finset.card_eq_sum_card_fiberwise dest
  have up : (S.card:ℝ) ≤ (K+1:ℝ)*(2*H*Y/q+1) := by
    rw [count,Nat.cast_sum]
    calc
      _ ≤ ∑ _j ∈ range (K+1), (2*H*Y/q+1) := sum_le_sum fun j _ => fiber j
      _ = _ := by simp <;> ring
  refine up.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have bn : 0 ≤ q*log Y+H := add_nonneg (mul_nonneg hq.le (Real.log_nonneg Y1)) H0
  linarith only [show (K:ℝ)≤q*log Y+H from Nat.floor_le bn]

lemma product_packing (G : Finset ℕ) (k d : ℕ) (q η : ℝ) (hq : 0<q) (he : 0≤η) (he1 : η≤1)
    (k1 : 1≤k) (hG : ∀ p∈G, p.Prime ∧ p≤k ∧ ∃ z : ℤ, |q*log p-2*π*z|≤η) :
    (G.card.choose d : ℝ) ≤ (q*log ((k:ℝ)^d) + d*η+1)*(2*(d*η)*(k:ℝ)^d/q+1) := by
  classical
  let prodP (Q : Finset ℕ) := ∏ p ∈ Q, p
  let S := (G.powersetCard d).image prodP
  have unique {Q W : Finset ℕ} (hQ : Q⊆G) (hW : W⊆G) (e : prodP Q=prodP W) : Q=W := by
    simpa only [prodP,Nat.primeFactors_prod (fun p hp => (hG p (hQ hp)).1),
      Nat.primeFactors_prod (fun p hp => (hG p (hW hp)).1)] using congrArg Nat.primeFactors e
  have cardS : S.card=G.card.choose d := by
    dsimp only [S]
    rw [card_image_of_injOn,card_powersetCard]
    intro Q hQ W hW e
    exact unique (mem_powersetCard.mp hQ).1 (mem_powersetCard.mp hW).1 e
  have each (p : ℕ) (hp : p∈G) : ∃ z : ℕ, |q*log p-2*π*z|≤η := by
    obtain ⟨pr,_,z,hz⟩ := hG p hp
    have zn : 0≤z := by
      by_contra! neg
      have zz : (z:ℝ)≤ -1 := by exact_mod_cast (by omega : z ≤ -1)
      have ql := mul_nonneg hq.le (Real.log_natCast_nonneg p)
      have := mul_le_mul_of_nonneg_left zz (show 0≤2*π by positivity)
      linarith [(abs_le.mp hz).2,pi_gt_three]
    refine ⟨z.toNat,?_⟩
    have eq : (z.toNat:ℝ) = (z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg zn
    rwa [eq]
  have existZ (n : ℕ) (hn : n∈S) : ∃ z : ℕ, 0<n ∧ (n:ℝ)≤(k:ℝ)^d ∧ |q*log n-2*π*z|≤d*η := by
    obtain ⟨Q,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨sub,cs⟩ := mem_powersetCard.mp hm
    let f (p : ℕ) := if h : p∈G then (each p h).choose else 0
    have pz (p : ℕ) (hp : p∈Q) : |q*log p-2*π*(f p)|≤η := by simpa [f,sub hp] using (each p (sub hp)).choose_spec
    have pp (p : ℕ) (hp : p∈Q) : 0<p := (hG p (sub hp)).1.pos
    have nn : 0<prodP Q := Finset.prod_pos pp
    refine ⟨∑ p∈Q,f p,nn,?_,?_⟩
    · have u : prodP Q ≤ k^Q.card := Finset.prod_le_pow_card _ _ _ (fun p hp => (hG p (sub hp)).2.1)
      rw [cs] at u
      exact_mod_cast u
    · have logprod : log (prodP Q) = ∑ p∈Q,log p := by
        simp only [prodP,Nat.cast_prod]
        exact Real.log_prod (fun p hp => (Nat.cast_ne_zero.mpr (pp p hp).ne' : (p:ℝ)≠0))
      rw [logprod,Nat.cast_sum,Finset.mul_sum,Finset.mul_sum,←sum_sub_distrib]
      calc
        _ ≤ ∑ p∈Q,|q*log p-2*π*(f p)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p∈Q,η := sum_le_sum pz
        _ = _ := by simp [cs]
  let z (n : ℕ) := if h : n∈S then (existZ n h).choose else 0
  have result := pack S z q ((k:ℝ)^d) (d*η) hq (one_le_pow₀ (by exact_mod_cast k1)) (by positivity)
    (fun n hn => by simpa [z,hn] using (existZ n hn).choose_spec)
  simpa only [cardS] using result
lemma polylog_small (C : ℝ) (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, C*(1+log k)^m ≤ (k:ℝ) := by
  let c := (max C 1)*2^m
  have cp : 0<c := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by positivity)
  have natlim := tendsto_natCast_atTop_atTop (R:=ℝ)
  have H := (isLittleO_log_rpow_rpow_atTop (m:ℝ) (show (0:ℝ)<1 by norm_num)).bound (inv_pos.mpr cp)
  filter_upwards [natlim.eventually H,(tendsto_log_atTop.comp natlim).eventually_ge_atTop 1] with k H L
  change 1 ≤ log (k:ℝ) at L
  change ‖(log (k:ℝ))^(m:ℝ)‖ ≤ c⁻¹*‖(k:ℝ)^(1:ℝ)‖ at H
  rw [rpow_natCast,rpow_one,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg _)] at H
  calc
    _ ≤ (max C 1)*((2*log k)^m) := mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (le_trans zero_le_one (le_max_right _ _))
    _ = c*(log k)^m := by dsimp [c]; ring
    _ ≤ c*(c⁻¹*(k:ℝ)) := mul_le_mul_of_nonneg_left H cp.le
    _ = _ := by field_simp

lemma prime_mass : ∀ᶠ k : ℕ in atTop, (k:ℝ) ≤
    4*((((Ioc k.sqrt k).filter Nat.Prime).card:ℝ)*(1+log k)) := by
  filter_upwards [polylog_small 10000 2,eventually_ge_atTop 2] with k small hk
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let U := k.sqrt.primesLE
  have ku : k.sqrt≤k := Nat.sqrt_le_self _
  have sub : U ⊆ k.primesLE := by
    intro p hp
    obtain ⟨pl,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨pl.trans ku,pr⟩
  have setId : k.primesLE \ U = P := by
    apply Finset.ext
    intro p
    change p ∈ (k.primesLE \ k.sqrt.primesLE : Finset ℕ) ↔ p ∈ (Ioc k.sqrt k).filter Nat.Prime
    rw [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨pk,pp⟩,bad⟩
      exact ⟨⟨lt_of_not_ge (fun h => bad ⟨h,pp⟩),pk⟩,pp⟩
    · rintro ⟨⟨lt,pk⟩,pp⟩
      exact ⟨⟨pk,pp⟩,fun h => lt.not_ge h.1⟩
  have full : U.card + P.card = k.primeCounting := by
    rw [←Nat.primesLE_card_eq_primeCounting,←setId,add_comm,card_sdiff_add_card_eq_card sub]
  have uBound : U.card ≤ k.sqrt := by
    dsimp [U]
    rw [Nat.primesLE_eq_filter_Icc_one]
    simpa using card_filter_le (Icc 1 k.sqrt) Nat.Prime
  have xp : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  have lpos := log_pos xp
  have lower := (div_le_iff₀ lpos).mp (Chebyshev.pi_ge k)
  have upperLog : log ((k:ℝ)+1) ≤ 1+log k := by
    calc _ ≤ log ((k:ℝ)*2) := log_le_log (by positivity) (by linarith)
         _ ≤ _ := by rw [log_mul (by positivity) (by norm_num)]; linarith [log_two_lt_d9]
  have rootsq : (k.sqrt:ℝ)^2 ≤ (k:ℝ) := by exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le k)
  have sqrtMul : (U.card:ℝ)*(1+log k) ≤ (k:ℝ)/10 := by
    have cu : (U.card:ℝ) ≤ k.sqrt := by exact_mod_cast uBound
    have cs := mul_le_mul_of_nonneg_right cu (show 0≤1+log k by linarith)
    nlinarith only [cs,rootsq,small,sq_nonneg ((k.sqrt:ℝ)-10*(1+log k)),sq_nonneg (1+log (k:ℝ))]
  have ctot : (U.card:ℝ)+(P.card:ℝ) = k.primeCounting := by exact_mod_cast full
  have l2 := mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg k)
  have smallL : 1+log k ≤ (k:ℝ)/10 := by nlinarith [sq_nonneg (log (k:ℝ))]
  change (k:ℝ) ≤ 4*((P.card:ℝ)*(1+log k))
  rw [←ctot] at lower
  nlinarith only [lower,upperLog,l2,smallL,sqrtMul,Nat.cast_nonneg U.card (α:=ℝ),Nat.cast_nonneg P.card (α:=ℝ)]

lemma lattice_phase (w : ℝ) : ∃ j : ℤ, |w-2*π*j|^2 ≤ 2*π^2*(1-|cos (w/2)|) := by
  let u := w/(2*π)
  let j := round u
  let v := π*(u-j)
  have near := abs_sub_round u
  have vb : |v| ≤ π/2 := by
    dsimp [v]
    rw [abs_mul,abs_of_pos pi_pos]
    linarith [mul_le_mul_of_nonneg_left near pi_pos.le]
  have cs := cos_nonneg_of_mem_Icc ⟨(abs_le.mp vb).1,(abs_le.mp vb).2⟩
  have eq : w/2 = v+(j:ℝ)*π := by dsimp [u,v]; field_simp <;> ring
  have cosEq : |cos (w/2)|=cos v := by
    simp only [eq,cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,abs_of_nonneg cs]
  have bound := cos_le_one_sub_mul_cos_sq (vb.trans (by linarith [pi_pos]))
  have hj : w-2*π*(j:ℝ)=2*v := by linarith only [eq]
  refine ⟨j,?_⟩
  rw [hj,sq_abs,cosEq]
  have pb := mul_le_mul_of_nonneg_left bound (sq_nonneg π)
  field_simp at pb
  nlinarith only [pb]
theorem binomial_ge_ratio {M k : ℕ} (hkM : k ≤ M) :
    ((M : ℝ) / k) ^ k ≤ (M.choose k : ℝ) := by
  have hid : (∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ)) =
      (M.choose k : ℝ) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_div_cancel_left₀ _ hfact
  calc
    ((M : ℝ) / k) ^ k = ∏ j ∈ Finset.range k, ((M : ℝ) / k) := by simp [div_pow]
    _ ≤ ∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ) := by
      apply Finset.prod_le_prod (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjM : j ≤ M := hjk.le.trans hkM
      have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
      have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
      rw [Nat.cast_sub hjM, Nat.cast_sub hjk.le, div_le_div_iff₀ hkpos (sub_pos.mpr hjk')]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkM') (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (M.choose k : ℝ) := hid



lemma packing_contradiction {K R d q η A Y V Z : ℝ} (kp : 0<K) (r1 : 1≤R)
    (dp : 0≤d) (qp : 0<q) (ep : 0≤η) (ap : 0≤A) (yp : 0<Y) (oneV : 1≤V)
    (dy : d*η ≤ 1) (yid : Y=K*V) (ql : 1/R^2≤q) (qu : q≤V)
    (tol : A*(2*d^2*R+4*d*R^2)*η ≤ 1/4) (cut : A*(d*R+2) ≤ K/4)
    (lo : Y ≤ A*Z) (hi : Z ≤ (q*d*R+d*η+1)*(2*(d*η)*Y/q+1)) : False := by
  have rp : 0<R := by linarith
  have invq : 1/q ≤ R^2 := (div_le_iff₀ qp).2 (by
    have hh := (div_le_iff₀ (sq_pos_of_pos rp)).mp ql
    linarith only [hh])
  have w0 : 0 ≤ 2*(d*η)*Y/q+1 := by positivity
  have hi' := hi.trans (mul_le_mul_of_nonneg_right (show q*d*R+d*η+1 ≤ q*d*R+2 by linarith) w0)
  have norm : (q*d*R+2)*(2*(d*η)*Y/q+1) =
      (2*d^2*R)*η*Y + (4*d*η*Y)*(1/q) + q*d*R+2 := by field_simp; ring
  rw [norm] at hi'
  have mid := mul_le_mul_of_nonneg_left invq (show 0≤4*d*η*Y by positivity)
  have big := mul_le_mul_of_nonneg_right qu (show 0≤d*R by positivity)
  have vp := zero_le_one.trans oneV
  have coarse : Z ≤ (2*d^2*R+4*d*R^2)*η*Y + (d*R+2)*V := by linarith only [hi',mid,big,oneV]
  have all := lo.trans (mul_le_mul_of_nonneg_left coarse ap)
  have h1 := mul_le_mul_of_nonneg_right tol yp.le
  have h2 := mul_le_mul_of_nonneg_right cut vp
  rw [yid] at all h1 yp
  linarith only [all,h1,h2,yp]

lemma good_count (P : Finset ℕ) (q M R K L : ℝ) (A : ℕ) (qp : 0<q) (lp : 0<L)
    (r1 : 1≤R) (pcount : K ≤ 4*((P.card:ℝ)*R))
    (saving : (16*π^2*M*L^2)*R^(2*A+2) ≤ K)
    (low : ∑ p∈P,(1-|cos (q*log p/2)|) < M*R) :
    let η := 1/(L*R^A)
    let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
    K ≤ 8*((G.card:ℝ)*R) := by
  let η := 1/(L*R^A)
  let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
  let V := P \ G
  have ep : 0<η := by dsimp [η]; positivity
  have cost : (V.card:ℝ)*η^2 ≤ 2*π^2*(M*R) := by
    calc
      _ = ∑ _p∈V,η^2 := by simp
      _ ≤ ∑ p∈V,(2*π^2)*(1-|cos (q*log p/2)|) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨pp,pg⟩ := mem_sdiff.mp hp
        obtain ⟨z,hz⟩ := lattice_phase (q*log p)
        have far : η < |q*log p-2*π*z| := lt_of_not_ge fun a => pg (mem_filter.mpr ⟨pp,z,a⟩)
        exact (pow_le_pow_left₀ ep.le far.le _).trans hz
      _ ≤ _ := by
        rw [←mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ => sub_nonneg.mpr (abs_cos_le_one _))).trans low.le
  have total : (V.card:ℝ)+G.card=P.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (fun p:ℕ=>∃z:ℤ,|q*log p-2*π*z|≤η) P)
  have identity : η^2*(L^2*R^(2*A)*R)=R := by
    dsimp [η]; rw [Nat.mul_comm 2 A,pow_mul]; field_simp
  have tmp := mul_le_mul_of_nonneg_right cost (show 0≤L^2*R^(2*A)*R by positivity)
  rw [mul_assoc (V.card:ℝ),identity] at tmp
  rw [pow_add,pow_two] at saving
  change K≤8*((G.card:ℝ)*R)
  nlinarith only [tmp,saving,pcount,congrArg (fun x:ℝ=>x*R) total]

end LogPrimePacking
open LogPrimePacking

theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H1 := by
  intro M
  let d := M+1
  let C := (8*(d:ℝ))^d
  let L := 32*C*((d:ℝ)+1)^2
  let A := d+2
  have dn : 0<d := Nat.succ_pos M
  have dr : (0:ℝ)<d := by exact_mod_cast dn
  have d1 : (1:ℝ)≤d := by exact_mod_cast dn
  have c1 : 1≤C := one_le_pow₀ (by linarith)
  have cp : 0<C := by linarith
  have lp : 0<L := by dsimp [L]; positivity
  filter_upwards [prime_mass,polylog_small (16*π^2*M*L^2) (2*A+2),
    polylog_small (4*C*((d:ℝ)+2)) (d+1),polylog_small (8*(d:ℝ)) 1,
    eventually_ge_atTop 2] with k mass saving cutoff enough k2
  intro s hl hu
  let R := 1+log (k:ℝ)
  let η := 1/(L*R^A)
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let q := |s|
  have r1 : 1≤R := by dsimp [R]; linarith [log_natCast_nonneg k]
  have rp : 0<R := by linarith
  have kp : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have k1 : (1:ℝ)≤k := by exact_mod_cast (by omega : 1≤k)
  have qp : 0<q := lt_of_lt_of_le (by positivity : 0<1/R^2) hl
  have ep : 0<η := by dsimp [η]; positivity
  have eD : (d:ℝ)*η≤1 := by
    dsimp [η]
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    have dpow := one_le_pow₀ (n:=A) r1
    have hL : (d:ℝ) ≤ L := by
      have h := mul_le_mul_of_nonneg_right c1 (sq_nonneg ((d:ℝ)+1))
      dsimp [L]; nlinarith [sq_nonneg (d:ℝ)]
    linarith [mul_le_mul_of_nonneg_left dpow lp.le]
  have e1 : η≤1 := (le_mul_of_one_le_left ep.le d1).trans eD
  have eqL (p : ℕ) : |cos (s*log p/2)|=|cos (q*log p/2)| := by
    rcases le_or_gt 0 s with hs|hs
    · simp [q,abs_of_nonneg hs]
    · simp [q,abs_of_neg hs,neg_mul,neg_div,cos_neg]
  change (M:ℝ)*log k ≤ ∑ p∈P,(1-|cos (s*log p/2)|)
  simp_rw [eqL]
  by_contra! bad
  have badR := bad.trans_le (mul_le_mul_of_nonneg_left (by dsimp [R]; linarith : log (k:ℝ)≤R) (Nat.cast_nonneg M))
  let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
  have many : (k:ℝ)≤8*((G.card:ℝ)*R) := good_count P q M R k L A qp lp r1 mass saving badR
  have gd : d≤G.card := by
    change 8*(d:ℝ)*R^1≤k at enough
    rw [pow_one] at enough
    exact_mod_cast (le_of_not_gt (fun h : (G.card:ℝ)<d => by nlinarith only [many,enough,mul_lt_mul_of_pos_right h rp]) : (d:ℝ)≤G.card)
  have ratio : (k:ℝ) ≤ (8*d*R)*((G.card:ℝ)/d) := many.trans_eq (by field_simp)
  have raised := pow_le_pow_left₀ kp.le ratio d
  rw [mul_pow,mul_pow] at raised
  have comb := binomial_ge_ratio gd
  have low : (k:ℝ)^d ≤ (C*R^d)*(G.card.choose d:ℝ) := by
    change (k:ℝ)^d ≤ (C*R^d)*((G.card:ℝ)/d)^d at raised
    exact raised.trans (mul_le_mul_of_nonneg_left comb (by positivity))
  have up := product_packing G k d q η qp ep.le e1 (by omega)
    (fun p hp => by
      obtain ⟨hP,z,hz⟩ := mem_filter.mp hp
      obtain ⟨hi,pp⟩ := mem_filter.mp hP
      exact ⟨pp,(mem_Ioc.mp hi).2,z,hz⟩)
  rw [Real.log_pow] at up
  have up' : (G.card.choose d:ℝ) ≤ (q*d*R+d*η+1)*(2*(d*η)*(k:ℝ)^d/q+1) := up.trans (by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hR : log (k:ℝ) ≤ R := by dsimp [R]; linarith
    linarith only [mul_le_mul_of_nonneg_left hR (show 0 ≤ q*d by positivity)])
  have tol : (C*R^d)*(2*(d:ℝ)^2*R+4*d*R^2)*η ≤ 1/4 := by
    dsimp only [η,L,A]
    rw [pow_add R d 2,mul_one_div,div_le_iff₀ (by positivity)]
    have t1 := mul_le_mul_of_nonneg_left (show R≤R^2 by nlinarith only [mul_le_mul_of_nonneg_left r1 rp.le])
      (show 0≤2*(d:ℝ)^2 by positivity)
    have h : 2*(d:ℝ)^2*R+4*d*R^2 ≤ 8*((d:ℝ)+1)^2*R^2 := by nlinarith only [t1,sq_nonneg ((d:ℝ)*R),sq_nonneg R,mul_nonneg dr.le (sq_nonneg R)]
    linarith only [mul_le_mul_of_nonneg_left h (show 0≤C*R^d by positivity)]
  have cut : (C*R^d)*((d:ℝ)*R+2)≤(k:ℝ)/4 := by
    change 4*C*((d:ℝ)+2)*R^(d+1) ≤ k at cutoff
    rw [pow_succ] at cutoff
    linarith only [cutoff,mul_le_mul_of_nonneg_left r1 (show 0≤C*R^d by positivity)]
  exact packing_contradiction kp r1 dr.le qp ep.le (by positivity) (by positivity)
    (one_le_pow₀ k1) eD (show (k:ℝ)^d=(k:ℝ)*(k:ℝ)^M by dsimp [d]; ring)
    hl hu tol cut low up'
